import { app, BrowserWindow } from 'electron'
import { basename, dirname, extname, join } from 'path'
import { pathToFileURL } from 'url'
import { existsSync, mkdirSync, readdirSync, readFileSync, statSync, appendFileSync } from 'fs'
import { writeFile, rm, readdir } from 'fs/promises'
import { homedir, tmpdir } from 'os'
import crypto from 'crypto'
import { ConfigService } from './config'
import { wcdbService } from './wcdbService'
import { decryptDatViaNative, nativeAddonLocation } from './nativeImageDecrypt'

// 获取 ffmpeg-static 的路径
function getStaticFfmpegPath(): string | null {
  try {
    // 方法1: 直接 require ffmpeg-static
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const ffmpegStatic = require('ffmpeg-static')

    if (typeof ffmpegStatic === 'string') {
      // 修复：如果路径包含 app.asar（打包后），自动替换为 app.asar.unpacked
      let fixedPath = ffmpegStatic
      if (fixedPath.includes('app.asar') && !fixedPath.includes('app.asar.unpacked')) {
        fixedPath = fixedPath.replace('app.asar', 'app.asar.unpacked')
      }

      if (existsSync(fixedPath)) {
        return fixedPath
      }
    }

    // 方法2: 手动构建路径（开发环境）
    const devPath = join(process.cwd(), 'node_modules', 'ffmpeg-static', 'ffmpeg.exe')
    if (existsSync(devPath)) {
      return devPath
    }

    // 方法3: 打包后的路径
    if (app?.isPackaged) {
      const resourcesPath = process.resourcesPath
      const packedPath = join(resourcesPath, 'app.asar.unpacked', 'node_modules', 'ffmpeg-static', 'ffmpeg.exe')
      if (existsSync(packedPath)) {
        return packedPath
      }
    }

    return null
  } catch {
    return null
  }
}

type DecryptResult = {
  success: boolean
  localPath?: string
  error?: string
  isThumb?: boolean  // 是否是缩略图（没有高清图时返回缩略图）
}

type DecryptProgressStage = 'queued' | 'locating' | 'decrypting' | 'writing' | 'done' | 'failed'

type CachedImagePayload = {
  sessionId?: string
  imageMd5?: string
  imageDatName?: string
  createTime?: number
  preferFilePath?: boolean
  hardlinkOnly?: boolean
  disableUpdateCheck?: boolean
  allowCacheIndex?: boolean
}

type DecryptImagePayload = CachedImagePayload & {
  force?: boolean
}

export class ImageDecryptService {
  private configService = new ConfigService()
  private resolvedCache = new Map<string, string>()
  private pending = new Map<string, Promise<DecryptResult>>()
  private updateFlags = new Map<string, boolean>()
  private nativeLogged = false
  private datNameScanMissAt = new Map<string, number>()
  private readonly datNameScanMissTtlMs = 1200

  private logInfo(message: string, meta?: Record<string, unknown>): void {
    if (!this.configService.get('logEnabled')) return
    const timestamp = new Date().toISOString()
    const metaStr = meta ? ` ${JSON.stringify(meta)}` : ''
    const logLine = `[${timestamp}] [ImageDecrypt] ${message}${metaStr}\n`

    // 只写入文件，不输出到控制台
    this.writeLog(logLine)
  }

  private logError(message: string, error?: unknown, meta?: Record<string, unknown>): void {
    if (!this.configService.get('logEnabled')) return
    const timestamp = new Date().toISOString()
    const errorStr = error ? ` Error: ${String(error)}` : ''
    const metaStr = meta ? ` ${JSON.stringify(meta)}` : ''
    const logLine = `[${timestamp}] [ImageDecrypt] ERROR: ${message}${errorStr}${metaStr}\n`

    // 同时输出到控制台
    console.error(message, error, meta)

    // 写入日志文件
    this.writeLog(logLine)
  }

  private writeLog(line: string): void {
    try {
      const logDir = join(this.getUserDataPath(), 'logs')
      if (!existsSync(logDir)) {
        mkdirSync(logDir, { recursive: true })
      }
      appendFileSync(join(logDir, 'wcdb.log'), line, { encoding: 'utf8' })
    } catch (err) {
      console.error('写入日志失败:', err)
    }
  }

  async resolveCachedImage(payload: CachedImagePayload): Promise<DecryptResult & { hasUpdate?: boolean }> {
    const cacheKeys = this.getCacheKeys(payload)
    const cacheKey = cacheKeys[0]
    if (!cacheKey) {
      return { success: false, error: '缺少图片标识' }
    }
    for (const key of cacheKeys) {
      const cached = this.resolvedCache.get(key)
      if (cached && existsSync(cached) && this.isImageFile(cached)) {
        const upgraded = this.isThumbnailPath(cached)
          ? await this.tryPromoteThumbnailCache(payload, key, cached)
          : null
        const finalPath = upgraded || cached
        const localPath = this.resolveLocalPathForPayload(finalPath, payload.preferFilePath)
        const isThumb = this.isThumbnailPath(finalPath)
        const hasUpdate = isThumb ? (this.updateFlags.get(key) ?? false) : false
        if (isThumb) {
          if (!payload.disableUpdateCheck) {
            this.triggerUpdateCheck(payload, key, finalPath)
          }
        } else {
          this.updateFlags.delete(key)
        }
        this.emitCacheResolved(payload, key, this.resolveEmitPath(finalPath, payload.preferFilePath))
        return { success: true, localPath, hasUpdate }
      }
      if (cached && !this.isImageFile(cached)) {
        this.resolvedCache.delete(key)
      }
    }

    const accountDir = this.resolveCurrentAccountDir()
    if (accountDir) {
      const datPath = await this.resolveDatPath(
        accountDir,
        payload.imageMd5,
        payload.imageDatName,
        payload.sessionId,
        payload.createTime,
        {
          allowThumbnail: true,
          skipResolvedCache: false,
          hardlinkOnly: true
        }
      )
      if (datPath) {
        const existing = this.findCachedOutputByDatPath(datPath, payload.sessionId, false)
        if (existing) {
          const upgraded = this.isThumbnailPath(existing)
            ? await this.tryPromoteThumbnailCache(payload, cacheKey, existing)
            : null
          const finalPath = upgraded || existing
          this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, finalPath)
          const localPath = this.resolveLocalPathForPayload(finalPath, payload.preferFilePath)
          const isThumb = this.isThumbnailPath(finalPath)
          const hasUpdate = isThumb ? (this.updateFlags.get(cacheKey) ?? false) : false
          if (isThumb) {
            if (!payload.disableUpdateCheck) {
              this.triggerUpdateCheck(payload, cacheKey, finalPath)
            }
          } else {
            this.updateFlags.delete(cacheKey)
          }
          this.emitCacheResolved(payload, cacheKey, this.resolveEmitPath(finalPath, payload.preferFilePath))
          return { success: true, localPath, hasUpdate }
        }
      }
    }
    this.logInfo('未找到缓存', { md5: payload.imageMd5, datName: payload.imageDatName })
    return { success: false, error: '未找到缓存图片' }
  }

  async decryptImage(payload: DecryptImagePayload): Promise<DecryptResult> {
    const cacheKeys = this.getCacheKeys(payload)
    const cacheKey = cacheKeys[0]
    if (!cacheKey) {
      return { success: false, error: '缺少图片标识' }
    }
    this.emitDecryptProgress(payload, cacheKey, 'queued', 4, 'running')

    if (payload.force) {
      for (const key of cacheKeys) {
        const cached = this.resolvedCache.get(key)
        if (cached && existsSync(cached) && this.isImageFile(cached) && !this.isThumbnailPath(cached)) {
          this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, cached)
          this.clearUpdateFlags(cacheKey, payload.imageMd5, payload.imageDatName)
          const localPath = this.resolveLocalPathForPayload(cached, payload.preferFilePath)
          this.emitCacheResolved(payload, cacheKey, this.resolveEmitPath(cached, payload.preferFilePath))
          this.emitDecryptProgress(payload, cacheKey, 'done', 100, 'done')
          return { success: true, localPath }
        }
        if (cached && !this.isImageFile(cached)) {
          this.resolvedCache.delete(key)
        }
      }

    }

    if (!payload.force) {
      const cached = this.resolvedCache.get(cacheKey)
      if (cached && existsSync(cached) && this.isImageFile(cached)) {
        const upgraded = this.isThumbnailPath(cached)
          ? await this.tryPromoteThumbnailCache(payload, cacheKey, cached)
          : null
        const finalPath = upgraded || cached
        const localPath = this.resolveLocalPathForPayload(finalPath, payload.preferFilePath)
        this.emitCacheResolved(payload, cacheKey, this.resolveEmitPath(finalPath, payload.preferFilePath))
        this.emitDecryptProgress(payload, cacheKey, 'done', 100, 'done')
        return { success: true, localPath }
      }
      if (cached && !this.isImageFile(cached)) {
        this.resolvedCache.delete(cacheKey)
      }
    }

    const pending = this.pending.get(cacheKey)
    if (pending) {
      this.emitDecryptProgress(payload, cacheKey, 'queued', 8, 'running')
      return pending
    }

    const task = this.decryptImageInternal(payload, cacheKey)
    this.pending.set(cacheKey, task)
    try {
      return await task
    } finally {
      this.pending.delete(cacheKey)
    }
  }

  async preloadImageHardlinkMd5s(md5List: string[]): Promise<void> {
    const normalizedList = Array.from(
      new Set((md5List || []).map((item) => String(item || '').trim().toLowerCase()).filter(Boolean))
    )
    if (normalizedList.length === 0) return

    const wxid = this.configService.get('myWxid')
    const dbPath = this.configService.get('dbPath')
    if (!wxid || !dbPath) return

    const accountDir = this.resolveAccountDir(dbPath, wxid)
    if (!accountDir) return

    try {
      const ready = await this.ensureWcdbReady()
      if (!ready) return
      const requests = normalizedList.map((md5) => ({ md5, accountDir }))
      const result = await wcdbService.resolveImageHardlinkBatch(requests)
      if (!result.success || !Array.isArray(result.rows)) return

      for (const row of result.rows) {
        const md5 = String(row?.md5 || '').trim().toLowerCase()
        if (!md5) continue
        const fileName = String(row?.data?.file_name || '').trim().toLowerCase()
        const fullPath = String(row?.data?.full_path || '').trim()
        if (!fileName || !fullPath) continue
        const selectedPath = this.normalizeHardlinkDatPathByFileName(fullPath, fileName)
        if (!selectedPath || !existsSync(selectedPath)) continue
        this.cacheDatPath(accountDir, md5, selectedPath)
        this.cacheDatPath(accountDir, fileName, selectedPath)
      }
    } catch {
      // ignore preload failures
    }
  }

  private async decryptImageInternal(
    payload: DecryptImagePayload,
    cacheKey: string
  ): Promise<DecryptResult> {
    this.logInfo('开始解密图片', { md5: payload.imageMd5, datName: payload.imageDatName, force: payload.force, hardlinkOnly: payload.hardlinkOnly === true })
    this.emitDecryptProgress(payload, cacheKey, 'locating', 14, 'running')
    try {
      const wxid = this.configService.get('myWxid')
      const dbPath = this.configService.get('dbPath')
      if (!wxid || !dbPath) {
        this.logError('配置缺失', undefined, { wxid: !!wxid, dbPath: !!dbPath })
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', '配置缺失')
        return { success: false, error: '未配置账号或数据库路径' }
      }

      const accountDir = this.resolveAccountDir(dbPath, wxid)
      if (!accountDir) {
        this.logError('未找到账号目录', undefined, { dbPath, wxid })
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', '账号目录缺失')
        return { success: false, error: '未找到账号目录' }
      }

      let datPath: string | null = null
      let usedHdAttempt = false
      let fallbackToThumbnail = false

      // force=true 时先尝试高清；若高清缺失则回退到缩略图，避免直接失败。
      if (payload.force) {
        usedHdAttempt = true
        datPath = await this.resolveDatPath(
          accountDir,
          payload.imageMd5,
          payload.imageDatName,
          payload.sessionId,
          payload.createTime,
          {
            allowThumbnail: false,
            skipResolvedCache: true,
            hardlinkOnly: payload.hardlinkOnly === true
          }
        )
        if (!datPath) {
          datPath = await this.resolveDatPath(
            accountDir,
            payload.imageMd5,
            payload.imageDatName,
            payload.sessionId,
            payload.createTime,
            {
              allowThumbnail: true,
              skipResolvedCache: true,
              hardlinkOnly: payload.hardlinkOnly === true
            }
          )
          fallbackToThumbnail = Boolean(datPath)
          if (fallbackToThumbnail) {
            this.logInfo('高清缺失，回退解密缩略图', {
              md5: payload.imageMd5,
              datName: payload.imageDatName
            })
          }
        }
      } else {
        datPath = await this.resolveDatPath(
          accountDir,
          payload.imageMd5,
          payload.imageDatName,
          payload.sessionId,
          payload.createTime,
          {
            allowThumbnail: true,
            skipResolvedCache: false,
            hardlinkOnly: payload.hardlinkOnly === true
          }
        )
      }

      if (!datPath) {
        this.logError('未找到DAT文件', undefined, { md5: payload.imageMd5, datName: payload.imageDatName })
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', '未找到DAT文件')
        if (usedHdAttempt) {
          return { success: false, error: '未找到图片文件，请在微信中点开该图片后重试' }
        }
        return { success: false, error: '未找到图片文件' }
      }

      this.logInfo('找到DAT文件', { datPath })
      this.emitDecryptProgress(payload, cacheKey, 'locating', 34, 'running')

      if (!extname(datPath).toLowerCase().includes('dat')) {
        this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, datPath)
        const localPath = this.resolveLocalPathForPayload(datPath, payload.preferFilePath)
        const isThumb = this.isThumbnailPath(datPath)
        this.emitCacheResolved(payload, cacheKey, this.resolveEmitPath(datPath, payload.preferFilePath))
        this.emitDecryptProgress(payload, cacheKey, 'done', 100, 'done')
        return { success: true, localPath, isThumb }
      }

      const preferHdCache = Boolean(payload.force && !fallbackToThumbnail)
      const existingFast = this.findCachedOutputByDatPath(datPath, payload.sessionId, preferHdCache)
      if (existingFast) {
        this.logInfo('找到已解密文件(按DAT快速命中)', { existing: existingFast, isHd: this.isHdPath(existingFast) })
        const isHd = this.isHdPath(existingFast)
        if (!(payload.force && !isHd)) {
          this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, existingFast)
          const localPath = this.resolveLocalPathForPayload(existingFast, payload.preferFilePath)
          const isThumb = this.isThumbnailPath(existingFast)
          this.emitCacheResolved(payload, cacheKey, this.resolveEmitPath(existingFast, payload.preferFilePath))
          this.emitDecryptProgress(payload, cacheKey, 'done', 100, 'done')
          return { success: true, localPath, isThumb }
        }
      }

      // 优先使用当前 wxid 对应的密钥，找不到则回退到全局配置
      const imageKeys = this.configService.getImageKeysForCurrentWxid()
      const xorKeyRaw = imageKeys.xorKey
      // 支持十六进制格式（如 0x53）和十进制格式
      let xorKey: number
      if (typeof xorKeyRaw === 'number') {
        xorKey = xorKeyRaw
      } else {
        const trimmed = String(xorKeyRaw ?? '').trim()
        if (trimmed.toLowerCase().startsWith('0x')) {
          xorKey = parseInt(trimmed, 16)
        } else {
          xorKey = parseInt(trimmed, 10)
        }
      }
      if (Number.isNaN(xorKey) || (!xorKey && xorKey !== 0)) {
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', '缺少解密密钥')
        return { success: false, error: '未配置图片解密密钥' }
      }

      const aesKeyRaw = imageKeys.aesKey
      const aesKeyText = typeof aesKeyRaw === 'string' ? aesKeyRaw.trim() : ''
      const aesKeyForNative = aesKeyText || undefined

      this.logInfo('开始解密DAT文件(仅Rust原生)', { datPath, xorKey, hasAesKey: Boolean(aesKeyForNative) })
      this.emitDecryptProgress(payload, cacheKey, 'decrypting', 58, 'running')
      const nativeResult = this.tryDecryptDatWithNative(datPath, xorKey, aesKeyForNative)
      if (!nativeResult) {
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', 'Rust原生解密不可用')
        return { success: false, error: 'Rust原生解密不可用或解密失败，请检查 native 模块与密钥配置' }
      }
      let decrypted: Buffer = nativeResult.data
      this.emitDecryptProgress(payload, cacheKey, 'decrypting', 78, 'running')

      // 统一走原有 wxgf/ffmpeg 流程，确保行为与历史版本一致
      const wxgfResult = await this.unwrapWxgf(decrypted)
      decrypted = wxgfResult.data

      let ext = this.detectImageExtension(decrypted)

      // 如果是 wxgf 格式且没检测到扩展名
      if (wxgfResult.isWxgf && !ext) {
        ext = '.hevc'
      }

      const finalExt = ext || '.jpg'

      const outputPath = this.getCacheOutputPathFromDat(datPath, finalExt, payload.sessionId)
      this.emitDecryptProgress(payload, cacheKey, 'writing', 90, 'running')
      await writeFile(outputPath, decrypted)
      this.logInfo('解密成功', { outputPath, size: decrypted.length })

      if (finalExt === '.hevc') {
        this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', 'wxgf转换失败')
        return {
          success: false,
          error: '此图片为微信新格式(wxgf)，ffmpeg 转换失败，请检查日志',
          isThumb: this.isThumbnailPath(datPath)
        }
      }

      const isThumb = this.isThumbnailPath(datPath)
      this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, outputPath)
      if (!isThumb) {
        this.clearUpdateFlags(cacheKey, payload.imageMd5, payload.imageDatName)
      } else {
        this.triggerUpdateCheck(payload, cacheKey, outputPath)
      }
      const localPath = payload.preferFilePath
        ? outputPath
        : (this.bufferToDataUrl(decrypted, finalExt) || this.filePathToUrl(outputPath))
      const emitPath = this.resolveEmitPath(outputPath, payload.preferFilePath)
      this.emitCacheResolved(payload, cacheKey, emitPath)
      this.emitDecryptProgress(payload, cacheKey, 'done', 100, 'done')
      return { success: true, localPath, isThumb }
    } catch (e) {
      this.logError('解密失败', e, { md5: payload.imageMd5, datName: payload.imageDatName })
      this.emitDecryptProgress(payload, cacheKey, 'failed', 100, 'error', String(e))
      return { success: false, error: String(e) }
    }
  }

  private resolveAccountDir(dbPath: string, wxid: string): string | null {
    const cleanedWxid = this.cleanAccountDirName(wxid)
    const normalized = dbPath.replace(/[\\/]+$/, '')

    const direct = join(normalized, cleanedWxid)
    if (existsSync(direct)) return direct

    if (this.isAccountDir(normalized)) return normalized

    try {
      const entries = readdirSync(normalized)
      const lowerWxid = cleanedWxid.toLowerCase()
      for (const entry of entries) {
        const entryPath = join(normalized, entry)
        if (!this.isDirectory(entryPath)) continue
        const lowerEntry = entry.toLowerCase()
        if (lowerEntry === lowerWxid || lowerEntry.startsWith(`${lowerWxid}_`)) {
          if (this.isAccountDir(entryPath)) return entryPath
        }
      }
    } catch { }

    return null
  }

  private resolveCurrentAccountDir(): string | null {
    const wxid = this.configService.get('myWxid')
    const dbPath = this.configService.get('dbPath')
    if (!wxid || !dbPath) return null
    return this.resolveAccountDir(dbPath, wxid)
  }

  /**
   * 获取解密后的缓存目录（用于查找 hardlink.db）
   */
  private getDecryptedCacheDir(wxid: string): string | null {
    const cachePath = this.configService.get('cachePath')
    if (!cachePath) return null

    const cleanedWxid = this.cleanAccountDirName(wxid)
    const cacheAccountDir = join(cachePath, cleanedWxid)

    // 检查缓存目录下是否有 hardlink.db
    if (existsSync(join(cacheAccountDir, 'hardlink.db'))) {
      return cacheAccountDir
    }
    if (existsSync(join(cachePath, 'hardlink.db'))) {
      return cachePath
    }
    const cacheHardlinkDir = join(cacheAccountDir, 'db_storage', 'hardlink')
    if (existsSync(join(cacheHardlinkDir, 'hardlink.db'))) {
      return cacheHardlinkDir
    }
    return null
  }

  private isAccountDir(dirPath: string): boolean {
    return (
      existsSync(join(dirPath, 'hardlink.db')) ||
      existsSync(join(dirPath, 'db_storage')) ||
      existsSync(join(dirPath, 'FileStorage', 'Image')) ||
      existsSync(join(dirPath, 'FileStorage', 'Image2'))
    )
  }

  private isDirectory(path: string): boolean {
    try {
      return statSync(path).isDirectory()
    } catch {
      return false
    }
  }

  private cleanAccountDirName(dirName: string): string {
    const trimmed = dirName.trim()
    if (!trimmed) return trimmed

    if (trimmed.toLowerCase().startsWith('wxid_')) {
      const match = trimmed.match(/^(wxid_[^_]+)/i)
      if (match) return match[1]
      return trimmed
    }

    const suffixMatch = trimmed.match(/^(.+)_([a-zA-Z0-9]{4})$/)
    const cleaned = suffixMatch ? suffixMatch[1] : trimmed

    return cleaned
  }

  private async resolveDatPath(
    accountDir: string,
    imageMd5?: string,
    imageDatName?: string,
    sessionId?: string,
    createTime?: number,
    options?: { allowThumbnail?: boolean; skipResolvedCache?: boolean; hardlinkOnly?: boolean }
  ): Promise<string | null> {
    const allowThumbnail = options?.allowThumbnail ?? true
    const skipResolvedCache = options?.skipResolvedCache ?? false
    const hardlinkOnly = options?.hardlinkOnly ?? false
    this.logInfo('[ImageDecrypt] resolveDatPath', {
      imageMd5,
      imageDatName,
      createTime,
      allowThumbnail,
      skipResolvedCache,
      hardlinkOnly
    })

    const lookupMd5s = this.collectHardlinkLookupMd5s(imageMd5, imageDatName)
    if (lookupMd5s.length === 0) {
      const packedDatFallback = this.resolveDatPathFromParsedDatName(accountDir, imageDatName, sessionId, createTime, allowThumbnail)
      if (packedDatFallback) {
        if (imageMd5) this.cacheDatPath(accountDir, imageMd5, packedDatFallback)
        if (imageDatName) this.cacheDatPath(accountDir, imageDatName, packedDatFallback)
        const normalizedFileName = basename(packedDatFallback).toLowerCase()
        if (normalizedFileName) this.cacheDatPath(accountDir, normalizedFileName, packedDatFallback)
        this.logInfo('[ImageDecrypt] datName fallback hit (no hardlink md5)', {
          imageMd5,
          imageDatName,
          selectedPath: packedDatFallback
        })
        return packedDatFallback
      }
      this.logInfo('[ImageDecrypt] resolveDatPath miss (no hardlink md5)', { imageMd5, imageDatName })
      return null
    }

    if (!skipResolvedCache) {
      const cacheCandidates = Array.from(new Set([
        ...lookupMd5s,
        String(imageMd5 || '').trim().toLowerCase(),
        String(imageDatName || '').trim().toLowerCase()
      ].filter(Boolean)))
      for (const cacheKey of cacheCandidates) {
        const scopedKey = `${accountDir}|${cacheKey}`
        const cached = this.resolvedCache.get(scopedKey)
        if (!cached) continue
        if (!existsSync(cached)) continue
        if (!allowThumbnail && this.isThumbnailPath(cached)) continue
        return cached
      }
    }

    for (const lookupMd5 of lookupMd5s) {
      this.logInfo('[ImageDecrypt] hardlink lookup', { lookupMd5, sessionId, hardlinkOnly })
      const hardlinkPath = await this.resolveHardlinkPath(accountDir, lookupMd5, sessionId)
      if (!hardlinkPath) continue
      if (!allowThumbnail && this.isThumbnailPath(hardlinkPath)) continue

      this.cacheDatPath(accountDir, lookupMd5, hardlinkPath)
      if (imageMd5) this.cacheDatPath(accountDir, imageMd5, hardlinkPath)
      if (imageDatName) this.cacheDatPath(accountDir, imageDatName, hardlinkPath)
      const normalizedFileName = basename(hardlinkPath).toLowerCase()
      if (normalizedFileName) this.cacheDatPath(accountDir, normalizedFileName, hardlinkPath)
      return hardlinkPath
    }

    const packedDatFallback = this.resolveDatPathFromParsedDatName(accountDir, imageDatName, sessionId, createTime, allowThumbnail)
    if (packedDatFallback) {
      if (imageMd5) this.cacheDatPath(accountDir, imageMd5, packedDatFallback)
      if (imageDatName) this.cacheDatPath(accountDir, imageDatName, packedDatFallback)
      const normalizedFileName = basename(packedDatFallback).toLowerCase()
      if (normalizedFileName) this.cacheDatPath(accountDir, normalizedFileName, packedDatFallback)
      this.logInfo('[ImageDecrypt] datName fallback hit (hardlink miss)', {
        imageMd5,
        imageDatName,
        lookupMd5s,
        selectedPath: packedDatFallback
      })
      return packedDatFallback
    }

    this.logInfo('[ImageDecrypt] resolveDatPath miss (hardlink + datName fallback)', {
      imageMd5,
      imageDatName,
      lookupMd5s
    })
    return null
  }

  private async checkHasUpdate(
    payload: { sessionId?: string; imageMd5?: string; imageDatName?: string; createTime?: number },
    _cacheKey: string,
    cachedPath: string
  ): Promise<boolean> {
    if (!cachedPath || !existsSync(cachedPath)) return false
    const isThumbnail = this.isThumbnailPath(cachedPath)
    if (!isThumbnail) return false
    const wxid = this.configService.get('myWxid')
    const dbPath = this.configService.get('dbPath')
    if (!wxid || !dbPath) return false
    const accountDir = this.resolveAccountDir(dbPath, wxid)
    if (!accountDir) return false

    const hdPath = await this.resolveDatPath(
      accountDir,
      payload.imageMd5,
      payload.imageDatName,
      payload.sessionId,
      payload.createTime,
      { allowThumbnail: false, skipResolvedCache: true, hardlinkOnly: true }
    )
    return Boolean(hdPath)
  }

  private async tryPromoteThumbnailCache(
    payload: { sessionId?: string; imageMd5?: string; imageDatName?: string; createTime?: number; preferFilePath?: boolean },
    cacheKey: string,
    cachedPath: string
  ): Promise<string | null> {
    if (!cachedPath || !existsSync(cachedPath)) return null
    if (!this.isImageFile(cachedPath)) return null
    if (!this.isThumbnailPath(cachedPath)) return null

    const accountDir = this.resolveCurrentAccountDir()
    if (!accountDir) return null

    const hdDatPath = await this.resolveDatPath(
      accountDir,
      payload.imageMd5,
      payload.imageDatName,
      payload.sessionId,
      payload.createTime,
      { allowThumbnail: false, skipResolvedCache: true, hardlinkOnly: true }
    )
    if (!hdDatPath) return null

    const existingHd = this.findCachedOutputByDatPath(hdDatPath, payload.sessionId, true)
    if (existingHd && existsSync(existingHd) && this.isImageFile(existingHd) && !this.isThumbnailPath(existingHd)) {
      this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, existingHd)
      this.clearUpdateFlags(cacheKey, payload.imageMd5, payload.imageDatName)
      this.removeThumbnailCacheFile(cachedPath, existingHd)
      this.logInfo('[ImageDecrypt] thumbnail cache upgraded', {
        cacheKey,
        oldPath: cachedPath,
        newPath: existingHd,
        mode: 'existing'
      })
      return existingHd
    }

    const upgraded = await this.decryptImage({
      sessionId: payload.sessionId,
      imageMd5: payload.imageMd5,
      imageDatName: payload.imageDatName,
      createTime: payload.createTime,
      preferFilePath: true,
      force: true,
      hardlinkOnly: true,
      disableUpdateCheck: true
    })
    if (!upgraded.success) return null

    const cachedResult = this.resolvedCache.get(cacheKey)
    const upgradedPath = (cachedResult && existsSync(cachedResult))
      ? cachedResult
      : String(upgraded.localPath || '').trim()
    if (!upgradedPath || !existsSync(upgradedPath)) return null
    if (!this.isImageFile(upgradedPath) || this.isThumbnailPath(upgradedPath)) return null

    this.cacheResolvedPaths(cacheKey, payload.imageMd5, payload.imageDatName, upgradedPath)
    this.clearUpdateFlags(cacheKey, payload.imageMd5, payload.imageDatName)
    this.removeThumbnailCacheFile(cachedPath, upgradedPath)
    this.logInfo('[ImageDecrypt] thumbnail cache upgraded', {
      cacheKey,
      oldPath: cachedPath,
      newPath: upgradedPath,
      mode: 're-decrypt'
    })
    return upgradedPath
  }

  private removeThumbnailCacheFile(oldPath: string, keepPath?: string): void {
    if (!oldPath) return
    if (keepPath && oldPath === keepPath) return
    if (!existsSync(oldPath)) return
    if (!this.isThumbnailPath(oldPath)) return
    void rm(oldPath, { force: true }).catch(() => { })
  }

  private triggerUpdateCheck(
    payload: { sessionId?: string; imageMd5?: string; imageDatName?: string; createTime?: number },
    cacheKey: string,
    cachedPath: string
  ): void {
    if (this.updateFlags.get(cacheKey)) return
    void this.checkHasUpdate(payload, cacheKey, cachedPath).then((hasUpdate) => {
      if (!hasUpdate) return
      this.updateFlags.set(cacheKey, true)
      this.emitImageUpdate(payload, cacheKey)
    }).catch(() => { })
  }



  private collectHardlinkLookupMd5s(imageMd5?: string, imageDatName?: string): string[] {
    const keys: string[] = []
    const pushMd5 = (value?: string) => {
      const normalized = String(value || '').trim().toLowerCase()
      if (!normalized) return
      if (!this.looksLikeMd5(normalized)) return
      if (!keys.includes(normalized)) keys.push(normalized)
    }

    pushMd5(imageMd5)

    const datNameRaw = String(imageDatName || '').trim().toLowerCase()
    if (!datNameRaw) return keys
    pushMd5(datNameRaw)
    const datNameNoExt = datNameRaw.endsWith('.dat') ? datNameRaw.slice(0, -4) : datNameRaw
    pushMd5(datNameNoExt)
    pushMd5(this.normalizeDatBase(datNameNoExt))
    return keys
  }

  private resolveDatPathFromParsedDatName(
    accountDir: string,
    imageDatName?: string,
    sessionId?: string,
    createTime?: number,
    allowThumbnail = true
  ): string | null {
    const datNameRaw = String(imageDatName || '').trim().toLowerCase()
    if (!datNameRaw) return null
    const datNameNoExt = datNameRaw.endsWith('.dat') ? datNameRaw.slice(0, -4) : datNameRaw
    const baseMd5 = this.normalizeDatBase(datNameNoExt)
    if (!this.looksLikeMd5(baseMd5)) return null

    const monthKey = this.resolveYearMonthFromCreateTime(createTime)
    const missKey = `${accountDir}|scan|${String(sessionId || '').trim()}|${monthKey}|${baseMd5}|${allowThumbnail ? 'all' : 'hd'}`
    const lastMiss = this.datNameScanMissAt.get(missKey) || 0
    if (lastMiss && (Date.now() - lastMiss) < this.datNameScanMissTtlMs) {
      return null
    }

    const sessionMonthCandidates = this.collectDatCandidatesFromSessionMonth(accountDir, baseMd5, sessionId, createTime)
    if (sessionMonthCandidates.length > 0) {
      const orderedSessionMonth = this.sortDatCandidatePaths(sessionMonthCandidates, baseMd5)
      for (const candidatePath of orderedSessionMonth) {
        if (!allowThumbnail && this.isThumbnailPath(candidatePath)) continue
        this.datNameScanMissAt.delete(missKey)
        this.logInfo('[ImageDecrypt] datName fallback selected (session-month)', {
          accountDir,
          sessionId,
          imageDatName: datNameRaw,
          createTime,
          monthKey,
          baseMd5,
          allowThumbnail,
          selectedPath: candidatePath
        })
        return candidatePath
      }
    }

    const hasPreciseContext = Boolean(String(sessionId || '').trim() && monthKey)
    if (hasPreciseContext) {
      this.datNameScanMissAt.set(missKey, Date.now())
      this.logInfo('[ImageDecrypt] datName fallback precise scan miss', {
        accountDir,
        sessionId,
        imageDatName: datNameRaw,
        createTime,
        monthKey,
        baseMd5,
        allowThumbnail
      })
      return null
    }

    const candidates = this.collectDatCandidatesFromAccountDir(accountDir, baseMd5)
    if (candidates.length === 0) {
      this.datNameScanMissAt.set(missKey, Date.now())
      this.logInfo('[ImageDecrypt] datName fallback scan miss', {
        accountDir,
        sessionId,
        imageDatName: datNameRaw,
        createTime,
        monthKey,
        baseMd5,
        allowThumbnail
      })
      return null
    }

    const ordered = this.sortDatCandidatePaths(candidates, baseMd5)
    for (const candidatePath of ordered) {
      if (!allowThumbnail && this.isThumbnailPath(candidatePath)) continue
      this.datNameScanMissAt.delete(missKey)
      this.logInfo('[ImageDecrypt] datName fallback selected', {
        accountDir,
        sessionId,
        imageDatName: datNameRaw,
        createTime,
        monthKey,
        baseMd5,
        allowThumbnail,
        selectedPath: candidatePath
      })
      return candidatePath
    }

    this.datNameScanMissAt.set(missKey, Date.now())
    return null
  }

  private resolveYearMonthFromCreateTime(createTime?: number): string {
    const raw = Number(createTime)
    if (!Number.isFinite(raw) || raw <= 0) return ''
    const ts = raw > 1e12 ? raw : raw * 1000
    const d = new Date(ts)
    if (Number.isNaN(d.getTime())) return ''
    const y = d.getFullYear()
    const m = String(d.getMonth() + 1).padStart(2, '0')
    return `${y}-${m}`
  }

  private collectDatCandidatesFromSessionMonth(
    accountDir: string,
    baseMd5: string,
    sessionId?: string,
    createTime?: number
  ): string[] {
    const normalizedSessionId = String(sessionId || '').trim()
    const monthKey = this.resolveYearMonthFromCreateTime(createTime)
    if (!normalizedSessionId || !monthKey) return []

    const attachRoots = this.getAttachScanRoots(accountDir)
    const cacheRoots = this.getMessageCacheScanRoots(accountDir)
    const sessionDirs = this.getAttachSessionDirCandidates(normalizedSessionId)
    const candidates = new Set<string>()
    const budget = { remaining: 600 }
    const targetDirs: Array<{ dir: string; depth: number }> = []

    for (const root of attachRoots) {
      for (const sessionDir of sessionDirs) {
        targetDirs.push({ dir: join(root, sessionDir, monthKey), depth: 2 })
        targetDirs.push({ dir: join(root, sessionDir, monthKey, 'Img'), depth: 1 })
        targetDirs.push({ dir: join(root, sessionDir, monthKey, 'Image'), depth: 1 })
      }
    }

    for (const root of cacheRoots) {
      for (const sessionDir of sessionDirs) {
        targetDirs.push({ dir: join(root, monthKey, 'Message', sessionDir, 'Bubble'), depth: 1 })
        targetDirs.push({ dir: join(root, monthKey, 'Message', sessionDir), depth: 2 })
      }
    }

    for (const target of targetDirs) {
      if (budget.remaining <= 0) break
      this.scanDatCandidatesUnderRoot(target.dir, baseMd5, target.depth, candidates, budget)
    }

    return Array.from(candidates)
  }

  private getAttachScanRoots(accountDir: string): string[] {
    const roots: string[] = []
    const push = (value: string) => {
      const normalized = String(value || '').trim()
      if (!normalized) return
      if (!roots.includes(normalized)) roots.push(normalized)
    }

    push(join(accountDir, 'msg', 'attach'))
    push(join(accountDir, 'attach'))
    const parent = dirname(accountDir)
    if (parent && parent !== accountDir) {
      push(join(parent, 'msg', 'attach'))
      push(join(parent, 'attach'))
    }
    return roots
  }

  private getMessageCacheScanRoots(accountDir: string): string[] {
    const roots: string[] = []
    const push = (value: string) => {
      const normalized = String(value || '').trim()
      if (!normalized) return
      if (!roots.includes(normalized)) roots.push(normalized)
    }

    push(join(accountDir, 'cache'))
    const parent = dirname(accountDir)
    if (parent && parent !== accountDir) {
      push(join(parent, 'cache'))
    }
    return roots
  }

  private getAttachSessionDirCandidates(sessionId: string): string[] {
    const normalized = String(sessionId || '').trim()
    if (!normalized) return []
    const lower = normalized.toLowerCase()
    const cleaned = this.cleanAccountDirName(normalized)
    const inputs = Array.from(new Set([normalized, lower, cleaned, cleaned.toLowerCase()].filter(Boolean)))
    const results: string[] = []
    const push = (value: string) => {
      if (!value) return
      if (!results.includes(value)) results.push(value)
    }

    for (const item of inputs) {
      push(item)
      const md5 = crypto.createHash('md5').update(item).digest('hex').toLowerCase()
      push(md5)
      push(md5.slice(0, 16))
    }
    return results
  }

  private collectDatCandidatesFromAccountDir(accountDir: string, baseMd5: string): string[] {
    const roots = this.getDatScanRoots(accountDir)
    const candidates = new Set<string>()
    const budget = { remaining: 1400 }

    for (const item of roots) {
      if (budget.remaining <= 0) break
      this.scanDatCandidatesUnderRoot(item.root, baseMd5, item.maxDepth, candidates, budget)
    }

    if (candidates.size === 0 && budget.remaining <= 0) {
      this.logInfo('[ImageDecrypt] datName fallback budget exhausted', {
        accountDir,
        baseMd5,
        roots: roots.map((item) => item.root)
      })
    }

    return Array.from(candidates)
  }

  private getDatScanRoots(accountDir: string): Array<{ root: string; maxDepth: number }> {
    const roots: Array<{ root: string; maxDepth: number }> = []
    const push = (root: string, maxDepth: number) => {
      const normalized = String(root || '').trim()
      if (!normalized) return
      if (roots.some((item) => item.root === normalized)) return
      roots.push({ root: normalized, maxDepth })
    }

    push(join(accountDir, 'attach'), 4)
    push(join(accountDir, 'msg', 'attach'), 4)
    push(join(accountDir, 'FileStorage', 'Image'), 3)
    push(join(accountDir, 'FileStorage', 'Image2'), 3)
    push(join(accountDir, 'FileStorage', 'MsgImg'), 3)

    return roots
  }

  private scanDatCandidatesUnderRoot(
    rootDir: string,
    baseMd5: string,
    maxDepth: number,
    out: Set<string>,
    budget: { remaining: number }
  ): void {
    if (!rootDir || maxDepth < 0 || budget.remaining <= 0) return
    if (!existsSync(rootDir) || !this.isDirectory(rootDir)) return

    const stack: Array<{ dir: string; depth: number }> = [{ dir: rootDir, depth: 0 }]
    while (stack.length > 0 && budget.remaining > 0) {
      const current = stack.pop()
      if (!current) break
      budget.remaining -= 1

      let entries: Array<{ name: string; isFile: () => boolean; isDirectory: () => boolean }>
      try {
        entries = readdirSync(current.dir, { withFileTypes: true })
      } catch {
        continue
      }

      for (const entry of entries) {
        if (!entry.isFile()) continue
        const name = String(entry.name || '')
        if (!this.isHardlinkCandidateName(name, baseMd5)) continue
        const fullPath = join(current.dir, name)
        if (existsSync(fullPath)) out.add(fullPath)
      }

      if (current.depth >= maxDepth) continue
      for (const entry of entries) {
        if (!entry.isDirectory()) continue
        const name = String(entry.name || '')
        if (!name || name === '.' || name === '..') continue
        if (name.startsWith('.')) continue
        stack.push({ dir: join(current.dir, name), depth: current.depth + 1 })
      }
    }
  }

  private sortDatCandidatePaths(paths: string[], baseMd5: string): string[] {
    const list = Array.from(new Set(paths.filter(Boolean)))
    list.sort((a, b) => {
      const nameA = basename(a).toLowerCase()
      const nameB = basename(b).toLowerCase()
      const priorityA = this.getHardlinkCandidatePriority(nameA, baseMd5)
      const priorityB = this.getHardlinkCandidatePriority(nameB, baseMd5)
      if (priorityA !== priorityB) return priorityA - priorityB

      let mtimeA = 0
      let mtimeB = 0
      try {
        mtimeA = statSync(a).mtimeMs
      } catch { }
      try {
        mtimeB = statSync(b).mtimeMs
      } catch { }
      if (mtimeA !== mtimeB) return mtimeB - mtimeA
      return nameA.localeCompare(nameB)
    })
    return list
  }

  private isPlainMd5DatName(fileName: string): boolean {
    const lower = String(fileName || '').trim().toLowerCase()
    if (!lower.endsWith('.dat')) return false
    const base = lower.slice(0, -4)
    return this.looksLikeMd5(base)
  }

  private isHardlinkCandidateName(fileName: string, baseMd5: string): boolean {
    const lower = String(fileName || '').trim().toLowerCase()
    if (!lower.endsWith('.dat')) return false
    const base = lower.slice(0, -4)
    if (base === baseMd5) return true
    if (base.startsWith(`${baseMd5}_`) || base.startsWith(`${baseMd5}.`)) return true
    if (base.length === baseMd5.length + 1 && base.startsWith(baseMd5)) return true
    return this.normalizeDatBase(base) === baseMd5
  }

  private getHardlinkCandidatePriority(fileName: string, baseMd5: string): number {
    const lower = String(fileName || '').trim().toLowerCase()
    if (!lower.endsWith('.dat')) return 999
    const base = lower.slice(0, -4)

    // 无后缀 DAT 最后兜底；优先尝试变体 DAT。
    if (base === baseMd5) return 20
    // _t / .t / _thumb 等缩略图 DAT 仅作次级回退。
    if (this.isThumbnailDat(lower)) return 10
    // 其他非缩略图变体优先。
    return 0
  }

  private resolveHardlinkDatVariants(fullPath: string, baseMd5: string): string[] {
    const dirPath = dirname(fullPath)
    try {
      const entries = readdirSync(dirPath, { withFileTypes: true })
      const candidates = entries
        .filter((entry) => entry.isFile())
        .map((entry) => entry.name)
        .filter((name) => this.isHardlinkCandidateName(name, baseMd5))
        .map((name) => join(dirPath, name))
        .filter((candidatePath) => existsSync(candidatePath))
      return this.sortDatCandidatePaths(candidates, baseMd5)
    } catch {
      return []
    }
  }

  private normalizeHardlinkDatPathByFileName(fullPath: string, fileName: string): string {
    const normalizedPath = String(fullPath || '').trim()
    const normalizedFileName = String(fileName || '').trim().toLowerCase()
    if (!normalizedPath || !normalizedFileName.endsWith('.dat')) {
      return normalizedPath
    }

    // hardlink 记录到具体后缀时（如 _b/.b/_t），直接按记录路径解密。
    if (!this.isPlainMd5DatName(normalizedFileName)) {
      return normalizedPath
    }

    const base = normalizedFileName.slice(0, -4)
    if (!this.looksLikeMd5(base)) {
      return normalizedPath
    }

    const candidates = this.resolveHardlinkDatVariants(normalizedPath, base)
    if (candidates.length > 0) {
      return candidates[0]
    }

    return normalizedPath
  }

  private async resolveHardlinkPath(accountDir: string, md5: string, _sessionId?: string): Promise<string | null> {
    try {
      const normalizedMd5 = String(md5 || '').trim().toLowerCase()
      if (!this.looksLikeMd5(normalizedMd5)) return null
      const ready = await this.ensureWcdbReady()
      if (!ready) {
        this.logInfo('[ImageDecrypt] hardlink db not ready')
        return null
      }

      const resolveResult = await wcdbService.resolveImageHardlink(normalizedMd5, accountDir)
      if (!resolveResult.success || !resolveResult.data) return null
      const fileName = String(resolveResult.data.file_name || '').trim()
      const fullPath = String(resolveResult.data.full_path || '').trim()
      if (!fileName || !fullPath) return null

      const lowerFileName = String(fileName).toLowerCase()
      if (lowerFileName.endsWith('.dat')) {
        const normalizedBase = this.normalizeDatBase(lowerFileName.slice(0, -4))
        if (!this.looksLikeMd5(normalizedBase)) {
          this.logInfo('[ImageDecrypt] hardlink fileName rejected', { fileName })
          return null
        }
      }

      const selectedPath = this.normalizeHardlinkDatPathByFileName(fullPath, fileName)
      if (existsSync(selectedPath)) {
        this.logInfo('[ImageDecrypt] hardlink path hit', { md5: normalizedMd5, fileName, fullPath, selectedPath })
        return selectedPath
      }
      this.logInfo('[ImageDecrypt] hardlink path miss', { md5: normalizedMd5, fileName, fullPath, selectedPath })
      return null
    } catch {
      // ignore
    }
    return null
  }

  private async ensureWcdbReady(): Promise<boolean> {
    if (wcdbService.isReady()) return true
    const dbPath = this.configService.get('dbPath')
    const decryptKey = this.configService.get('decryptKey')
    const wxid = this.configService.get('myWxid')
    if (!dbPath || !decryptKey || !wxid) return false
    const cleanedWxid = this.cleanAccountDirName(wxid)
    return await wcdbService.open(dbPath, decryptKey, cleanedWxid)
  }

  private getRowValue(row: any, column: string): any {
    if (!row) return undefined
    if (Object.prototype.hasOwnProperty.call(row, column)) return row[column]
    const target = column.toLowerCase()
    for (const key of Object.keys(row)) {
      if (key.toLowerCase() === target) return row[key]
    }
    return undefined
  }

  private escapeSqlString(value: string): string {
    return value.replace(/'/g, "''")
  }

  private stripDatVariantSuffix(base: string): string {
    const lower = base.toLowerCase()
    const suffixes = ['_thumb', '.thumb', '_hd', '.hd', '_h', '.h', '_b', '.b', '_w', '.w', '_t', '.t', '_c', '.c']
    for (const suffix of suffixes) {
      if (lower.endsWith(suffix)) {
        return lower.slice(0, -suffix.length)
      }
    }
    if (/[._][a-z]$/.test(lower)) {
      return lower.slice(0, -2)
    }
    return lower
  }

  private normalizeDatBase(name: string): string {
    let base = name.toLowerCase()
    if (base.endsWith('.dat') || base.endsWith('.jpg')) {
      base = base.slice(0, -4)
    }
    for (;;) {
      const stripped = this.stripDatVariantSuffix(base)
      if (stripped === base) {
        return base
      }
      base = stripped
    }
  }

  private getCacheOutputPathFromDat(datPath: string, ext: string, sessionId?: string): string {
    const name = basename(datPath)
    const lower = name.toLowerCase()
    const base = lower.endsWith('.dat') ? name.slice(0, -4) : name

    // 提取基础名称（去掉 _t, _h 等后缀）
    const normalizedBase = this.normalizeDatBase(base)

    // 判断是缩略图还是高清图
    const isThumb = this.isThumbnailDat(lower)
    const suffix = isThumb ? '_thumb' : '_hd'

    const contactDir = this.sanitizeDirName(sessionId || 'unknown')
    const timeDir = this.resolveTimeDir(datPath)
    const outputDir = join(this.getCacheRoot(), contactDir, timeDir)
    if (!existsSync(outputDir)) {
      mkdirSync(outputDir, { recursive: true })
    }

    return join(outputDir, `${normalizedBase}${suffix}${ext}`)
  }

  private buildCacheOutputCandidatesFromDat(datPath: string, sessionId?: string, preferHd = false): string[] {
    const name = basename(datPath)
    const lower = name.toLowerCase()
    const base = lower.endsWith('.dat') ? name.slice(0, -4) : name
    const normalizedBase = this.normalizeDatBase(base)
    const suffixes = preferHd ? ['_hd', '_thumb'] : ['_thumb', '_hd']
    const extensions = ['.jpg', '.jpeg', '.png', '.gif', '.webp']

    const root = this.getCacheRoot()
    const contactDir = this.sanitizeDirName(sessionId || 'unknown')
    const timeDir = this.resolveTimeDir(datPath)
    const currentDir = join(root, contactDir, timeDir)
    const legacyDir = join(root, normalizedBase)
    const candidates: string[] = []

    for (const suffix of suffixes) {
      for (const ext of extensions) {
        candidates.push(join(currentDir, `${normalizedBase}${suffix}${ext}`))
      }
    }

    // 兼容旧目录结构
    for (const suffix of suffixes) {
      for (const ext of extensions) {
        candidates.push(join(legacyDir, `${normalizedBase}${suffix}${ext}`))
      }
    }

    // 兼容最旧平铺结构
    for (const ext of extensions) {
      candidates.push(join(root, `${normalizedBase}${ext}`))
      candidates.push(join(root, `${normalizedBase}_t${ext}`))
      candidates.push(join(root, `${normalizedBase}_hd${ext}`))
    }

    return candidates
  }

  private findCachedOutputByDatPath(datPath: string, sessionId?: string, preferHd = false): string | null {
    const candidates = this.buildCacheOutputCandidatesFromDat(datPath, sessionId, preferHd)
    for (const candidate of candidates) {
      if (existsSync(candidate)) return candidate
    }
    return null
  }

  private cacheResolvedPaths(cacheKey: string, imageMd5: string | undefined, imageDatName: string | undefined, outputPath: string): void {
    this.resolvedCache.set(cacheKey, outputPath)
    if (imageMd5 && imageMd5 !== cacheKey) {
      this.resolvedCache.set(imageMd5, outputPath)
    }
    if (imageDatName && imageDatName !== cacheKey && imageDatName !== imageMd5) {
      this.resolvedCache.set(imageDatName, outputPath)
    }
  }

  private getCacheKeys(payload: { imageMd5?: string; imageDatName?: string }): string[] {
    const keys: string[] = []
    const addKey = (value?: string) => {
      if (!value) return
      const lower = value.toLowerCase()
      if (!keys.includes(value)) keys.push(value)
      if (!keys.includes(lower)) keys.push(lower)
      const normalized = this.normalizeDatBase(lower)
      if (normalized && !keys.includes(normalized)) keys.push(normalized)
    }
    addKey(payload.imageMd5)
    if (payload.imageDatName && payload.imageDatName !== payload.imageMd5) {
      addKey(payload.imageDatName)
    }
    return keys
  }

  private cacheDatPath(accountDir: string, datName: string, datPath: string): void {
    const key = `${accountDir}|${datName}`
    this.resolvedCache.set(key, datPath)
    const normalized = this.normalizeDatBase(datName)
    if (normalized && normalized !== datName.toLowerCase()) {
      this.resolvedCache.set(`${accountDir}|${normalized}`, datPath)
    }
  }

  private clearUpdateFlags(cacheKey: string, imageMd5?: string, imageDatName?: string): void {
    this.updateFlags.delete(cacheKey)
    if (imageMd5) this.updateFlags.delete(imageMd5)
    if (imageDatName) this.updateFlags.delete(imageDatName)
  }

  private getActiveWindowsSafely(): Array<{ isDestroyed: () => boolean; webContents: { send: (channel: string, payload: unknown) => void } }> {
    try {
      const getter = (BrowserWindow as unknown as { getAllWindows?: () => any[] } | undefined)?.getAllWindows
      if (typeof getter !== 'function') return []
      const windows = getter()
      if (!Array.isArray(windows)) return []
      return windows.filter((win) => (
        win &&
        typeof win.isDestroyed === 'function' &&
        win.webContents &&
        typeof win.webContents.send === 'function'
      ))
    } catch {
      return []
    }
  }

  private emitImageUpdate(payload: { sessionId?: string; imageMd5?: string; imageDatName?: string }, cacheKey: string): void {
    const message = { cacheKey, imageMd5: payload.imageMd5, imageDatName: payload.imageDatName }
    for (const win of this.getActiveWindowsSafely()) {
      if (!win.isDestroyed()) {
        win.webContents.send('image:updateAvailable', message)
      }
    }
  }

  private emitCacheResolved(payload: { sessionId?: string; imageMd5?: string; imageDatName?: string }, cacheKey: string, localPath: string): void {
    const message = { cacheKey, imageMd5: payload.imageMd5, imageDatName: payload.imageDatName, localPath }
    for (const win of this.getActiveWindowsSafely()) {
      if (!win.isDestroyed()) {
        win.webContents.send('image:cacheResolved', message)
      }
    }
  }

  private emitDecryptProgress(
    payload: { sessionId?: string; imageMd5?: string; imageDatName?: string },
    cacheKey: string,
    stage: DecryptProgressStage,
    progress: number,
    status: 'running' | 'done' | 'error',
    message?: string
  ): void {
    const safeProgress = Math.max(0, Math.min(100, Math.floor(progress)))
    const event = {
      cacheKey,
      imageMd5: payload.imageMd5,
      imageDatName: payload.imageDatName,
      stage,
      progress: safeProgress,
      status,
      message: message || ''
    }
    for (const win of this.getActiveWindowsSafely()) {
      if (!win.isDestroyed()) {
        win.webContents.send('image:decryptProgress', event)
      }
    }
  }

  private getCacheRoot(): string {
    const configured = this.configService.get('cachePath')
    const root = configured
      ? join(configured, 'Images')
      : join(this.getDocumentsPath(), 'WeFlow', 'Images')
    if (!existsSync(root)) {
      mkdirSync(root, { recursive: true })
    }
    return root
  }

  private tryDecryptDatWithNative(
    datPath: string,
    xorKey: number,
    aesKey?: string
  ): { data: Buffer; ext: string; isWxgf: boolean } | null {
    const result = decryptDatViaNative(datPath, xorKey, aesKey)
    if (!this.nativeLogged) {
      this.nativeLogged = true
      if (result) {
        this.logInfo('Rust 原生解密已启用', {
          addonPath: nativeAddonLocation(),
          source: 'native'
        })
      } else {
        this.logInfo('Rust 原生解密不可用', {
          addonPath: nativeAddonLocation(),
          source: 'native_unavailable'
        })
      }
    }
    return result
  }

  private detectImageExtension(buffer: Buffer): string | null {
    if (buffer.length < 12) return null
    if (buffer[0] === 0x47 && buffer[1] === 0x49 && buffer[2] === 0x46) return '.gif'
    if (buffer[0] === 0x89 && buffer[1] === 0x50 && buffer[2] === 0x4e && buffer[3] === 0x47) return '.png'
    if (buffer[0] === 0xff && buffer[1] === 0xd8 && buffer[2] === 0xff) return '.jpg'
    if (buffer[0] === 0x52 && buffer[1] === 0x49 && buffer[2] === 0x46 && buffer[3] === 0x46 &&
      buffer[8] === 0x57 && buffer[9] === 0x45 && buffer[10] === 0x42 && buffer[11] === 0x50) {
      return '.webp'
    }
    return null
  }

  private bufferToDataUrl(buffer: Buffer, ext: string): string | null {
    const mimeType = this.mimeFromExtension(ext)
    if (!mimeType) return null
    return `data:${mimeType};base64,${buffer.toString('base64')}`
  }

  private resolveLocalPathForPayload(filePath: string, preferFilePath?: boolean): string {
    if (preferFilePath) return filePath
    return this.resolveEmitPath(filePath, false)
  }

  private resolveEmitPath(filePath: string, preferFilePath?: boolean): string {
    if (preferFilePath) return this.filePathToUrl(filePath)
    return this.fileToDataUrl(filePath) || this.filePathToUrl(filePath)
  }

  private fileToDataUrl(filePath: string): string | null {
    try {
      const ext = extname(filePath).toLowerCase()
      const mimeType = this.mimeFromExtension(ext)
      if (!mimeType) return null
      const data = readFileSync(filePath)
      return `data:${mimeType};base64,${data.toString('base64')}`
    } catch {
      return null
    }
  }

  private mimeFromExtension(ext: string): string | null {
    switch (ext.toLowerCase()) {
      case '.gif':
        return 'image/gif'
      case '.png':
        return 'image/png'
      case '.jpg':
      case '.jpeg':
        return 'image/jpeg'
      case '.webp':
        return 'image/webp'
      default:
        return null
    }
  }

  private filePathToUrl(filePath: string): string {
    const url = pathToFileURL(filePath).toString()
    try {
      const mtime = statSync(filePath).mtimeMs
      return `${url}?v=${Math.floor(mtime)}`
    } catch {
      return url
    }
  }

  private isImageFile(filePath: string): boolean {
    const ext = extname(filePath).toLowerCase()
    return ext === '.gif' || ext === '.png' || ext === '.jpg' || ext === '.jpeg' || ext === '.webp'
  }

  /**
   * 解包 wxgf 格式
   * wxgf 是微信的图片格式，内部使用 HEVC 编码
   */
  private async unwrapWxgf(buffer: Buffer): Promise<{ data: Buffer; isWxgf: boolean }> {
    // 检查是否是 wxgf 格式 (77 78 67 66 = "wxgf")
    if (buffer.length < 20 ||
      buffer[0] !== 0x77 || buffer[1] !== 0x78 ||
      buffer[2] !== 0x67 || buffer[3] !== 0x66) {
      return { data: buffer, isWxgf: false }
    }

    // 先尝试搜索内嵌的传统图片签名
    for (let i = 4; i < Math.min(buffer.length - 12, 4096); i++) {
      if (buffer[i] === 0xff && buffer[i + 1] === 0xd8 && buffer[i + 2] === 0xff) {
        return { data: buffer.subarray(i), isWxgf: false }
      }
      if (buffer[i] === 0x89 && buffer[i + 1] === 0x50 &&
        buffer[i + 2] === 0x4e && buffer[i + 3] === 0x47) {
        return { data: buffer.subarray(i), isWxgf: false }
      }
    }

    // 提取 HEVC NALU 裸流
    const hevcData = this.extractHevcNalu(buffer)
    // 优先用提取的 NALU 裸流，提取失败则跳过 wxgf 头部直接用原始数据
    const feedData = (hevcData && hevcData.length >= 100) ? hevcData : buffer.subarray(4)
    this.logInfo('unwrapWxgf: 准备 ffmpeg 转换', {
      naluExtracted: !!(hevcData && hevcData.length >= 100),
      feedSize: feedData.length
    })

    // 尝试用 ffmpeg 转换
    try {
      const jpgData = await this.convertHevcToJpg(feedData)
      if (jpgData && jpgData.length > 0) {
        return { data: jpgData, isWxgf: false }
      }
    } catch (e) {
      this.logError('unwrapWxgf: ffmpeg 转换失败', e)
    }

    return { data: feedData, isWxgf: true }
  }

  /**
   * 从 wxgf 数据中提取 HEVC NALU 裸流
   */
  private extractHevcNalu(buffer: Buffer): Buffer | null {
    const starts: number[] = []
    let i = 4

    while (i < buffer.length - 3) {
      const hasPrefix4 = buffer[i] === 0x00 && buffer[i + 1] === 0x00 &&
        buffer[i + 2] === 0x00 && buffer[i + 3] === 0x01
      const hasPrefix3 = buffer[i] === 0x00 && buffer[i + 1] === 0x00 &&
        buffer[i + 2] === 0x01

      if (hasPrefix4 || hasPrefix3) {
        starts.push(i)
        i += hasPrefix4 ? 4 : 3
        continue
      }
      i += 1
    }

    if (starts.length === 0) return null

    const nalUnits: Buffer[] = []
    for (let index = 0; index < starts.length; index += 1) {
      const start = starts[index]
      const end = index + 1 < starts.length ? starts[index + 1] : buffer.length
      const hasPrefix4 = buffer[start] === 0x00 && buffer[start + 1] === 0x00 &&
        buffer[start + 2] === 0x00 && buffer[start + 3] === 0x01
      const prefixLength = hasPrefix4 ? 4 : 3
      const payloadStart = start + prefixLength
      if (payloadStart >= end) continue
      nalUnits.push(Buffer.from([0x00, 0x00, 0x00, 0x01]))
      nalUnits.push(buffer.subarray(payloadStart, end))
    }

    if (nalUnits.length === 0) return null
    return Buffer.concat(nalUnits)
  }

  /**
   * 获取 ffmpeg 可执行文件路径
   */
  private getFfmpegPath(): string {
    const staticPath = getStaticFfmpegPath()
    this.logInfo('ffmpeg 路径检测', { staticPath, exists: staticPath ? existsSync(staticPath) : false })

    if (staticPath) {
      return staticPath
    }

    // 回退到系统 ffmpeg
    return 'ffmpeg'
  }

  /**
   * 使用 ffmpeg 将 HEVC 裸流转换为 JPG
   */
  private async convertHevcToJpg(hevcData: Buffer): Promise<Buffer | null> {
    const ffmpeg = this.getFfmpegPath()
    this.logInfo('ffmpeg 转换开始', { ffmpegPath: ffmpeg, hevcSize: hevcData.length })

    const tmpDir = join(this.getTempPath(), 'weflow_hevc')
    if (!existsSync(tmpDir)) mkdirSync(tmpDir, { recursive: true })
    const uniqueId = `${process.pid}_${Date.now()}_${crypto.randomBytes(4).toString('hex')}`
    const tmpInput = join(tmpDir, `hevc_${uniqueId}.hevc`)
    const tmpOutput = join(tmpDir, `hevc_${uniqueId}.jpg`)

    try {
      await writeFile(tmpInput, hevcData)

      // 依次尝试: 1) -f hevc 裸流  2) 不指定格式让 ffmpeg 自动检测
      const attempts: { label: string; inputArgs: string[] }[] = [
        { label: 'hevc raw', inputArgs: ['-f', 'hevc', '-i', tmpInput] },
        { label: 'h265 raw', inputArgs: ['-f', 'h265', '-i', tmpInput] },
        { label: 'auto detect', inputArgs: ['-i', tmpInput] },
      ]

      for (const attempt of attempts) {
        // 清理上一轮的输出
        try { if (existsSync(tmpOutput)) require('fs').unlinkSync(tmpOutput) } catch {}

        const result = await this.runFfmpegConvert(ffmpeg, attempt.inputArgs, tmpOutput, attempt.label)
        if (result) return result
      }

      return null
    } catch (e) {
      this.logError('ffmpeg 转换异常', e)
      return null
    } finally {
      try { if (existsSync(tmpInput)) require('fs').unlinkSync(tmpInput) } catch {}
      try { if (existsSync(tmpOutput)) require('fs').unlinkSync(tmpOutput) } catch {}
    }
  }

  private runFfmpegConvert(ffmpeg: string, inputArgs: string[], tmpOutput: string, label: string): Promise<Buffer | null> {
    return new Promise((resolve) => {
      const { spawn } = require('child_process')
      const errChunks: Buffer[] = []

      const args = [
        '-hide_banner', '-loglevel', 'error',
        '-y',
        ...inputArgs,
        '-vframes', '1', '-q:v', '2', '-f', 'image2', tmpOutput
      ]
      this.logInfo(`ffmpeg 尝试 [${label}]`, { args: args.join(' ') })

      const proc = spawn(ffmpeg, args, {
        stdio: ['ignore', 'ignore', 'pipe'],
        windowsHide: true
      })

      proc.stderr.on('data', (chunk: Buffer) => errChunks.push(chunk))

      const timer = setTimeout(() => {
        proc.kill('SIGKILL')
        this.logError(`ffmpeg [${label}] 超时(15s)`)
        resolve(null)
      }, 15000)

      proc.on('close', (code: number) => {
        clearTimeout(timer)
        if (code === 0 && existsSync(tmpOutput)) {
          try {
            const jpgBuf = readFileSync(tmpOutput)
            if (jpgBuf.length > 0) {
              this.logInfo(`ffmpeg [${label}] 成功`, { outputSize: jpgBuf.length })
              resolve(jpgBuf)
              return
            }
          } catch (e) {
            this.logError(`ffmpeg [${label}] 读取输出失败`, e)
          }
        }
        const errMsg = Buffer.concat(errChunks).toString().trim()
        this.logInfo(`ffmpeg [${label}] 失败`, { code, error: errMsg })
        resolve(null)
      })

      proc.on('error', (err: Error) => {
        clearTimeout(timer)
        this.logError(`ffmpeg [${label}] 进程错误`, err)
        resolve(null)
      })
    })
  }

  private looksLikeMd5(s: string): boolean {
    return /^[a-f0-9]{32}$/i.test(s)
  }

  private isThumbnailDat(name: string): boolean {
    const lower = name.toLowerCase()
    return lower.includes('_t.dat') || lower.includes('.t.dat') || lower.includes('_thumb.dat')
  }

  private isHdPath(p: string): boolean {
    return p.toLowerCase().includes('_hd') || p.toLowerCase().includes('_h')
  }

  private isThumbnailPath(p: string): boolean {
    const lower = p.toLowerCase()
    return lower.includes('_thumb') || lower.includes('_t') || lower.includes('.t.')
  }

  private sanitizeDirName(s: string): string {
    return s.replace(/[<>:"/\\|?*]/g, '_').trim() || 'unknown'
  }

  private resolveTimeDir(filePath: string): string {
    try {
      const stats = statSync(filePath)
      const d = new Date(stats.mtime)
      return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}`
    } catch {
      const d = new Date()
      return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}`
    }
  }

  private getElectronPath(name: 'userData' | 'documents' | 'temp'): string | null {
    try {
      const getter = (app as unknown as { getPath?: (n: string) => string } | undefined)?.getPath
      if (typeof getter !== 'function') return null
      const value = getter(name)
      return typeof value === 'string' && value.trim() ? value : null
    } catch {
      return null
    }
  }

  private getUserDataPath(): string {
    const workerUserDataPath = String(process.env.WEFLOW_USER_DATA_PATH || process.env.WEFLOW_CONFIG_CWD || '').trim()
    if (workerUserDataPath) return workerUserDataPath
    return this.getElectronPath('userData') || process.cwd()
  }

  private getDocumentsPath(): string {
    return this.getElectronPath('documents') || join(homedir(), 'Documents')
  }

  private getTempPath(): string {
    return this.getElectronPath('temp') || tmpdir()
  }

  async clearCache(): Promise<{ success: boolean; error?: string }> {
    this.resolvedCache.clear()
    this.pending.clear()
    this.updateFlags.clear()

    const configured = this.configService.get('cachePath')
    const root = configured
      ? join(configured, 'Images')
      : join(this.getDocumentsPath(), 'WeFlow', 'Images')

    try {
      if (!existsSync(root)) {
        return { success: true }
      }
      const monthPattern = /^\d{4}-\d{2}$/
      const clearFilesInDir = async (dirPath: string): Promise<void> => {
        let entries: Array<{ name: string; isDirectory: () => boolean }>
        try {
          entries = await readdir(dirPath, { withFileTypes: true })
        } catch {
          return
        }
        for (const entry of entries) {
          const fullPath = join(dirPath, entry.name)
          if (entry.isDirectory()) {
            await clearFilesInDir(fullPath)
            continue
          }
          try {
            await rm(fullPath, { force: true })
          } catch { }
        }
      }
      const traverse = async (dirPath: string): Promise<void> => {
        let entries: Array<{ name: string; isDirectory: () => boolean }>
        try {
          entries = await readdir(dirPath, { withFileTypes: true })
        } catch {
          return
        }
        for (const entry of entries) {
          const fullPath = join(dirPath, entry.name)
          if (entry.isDirectory()) {
            if (monthPattern.test(entry.name)) {
              await clearFilesInDir(fullPath)
            } else {
              await traverse(fullPath)
            }
            continue
          }
          try {
            await rm(fullPath, { force: true })
          } catch { }
        }
      }
      await traverse(root)
      return { success: true }
    } catch (e) {
      return { success: false, error: String(e) }
    }
  }
}

export const imageDecryptService = new ImageDecryptService()
