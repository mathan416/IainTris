-- IainTris: game implementation
import "CoreLibs/graphics"

local gfx = playdate.graphics
local defaultFont = gfx.getFont()

-- === Layout ===
local COLS, ROWS = 10, 20
local CELL_SIZE = 11
local SCREEN_W, SCREEN_H = 400, 240
local OFFSET_X = (SCREEN_W - (COLS * CELL_SIZE)) // 2
local PLAYFIELD_TOP = (SCREEN_H - (ROWS * CELL_SIZE)) // 2

-- === Tuning ===
local CRANK_DROP_SENSITIVITY = 6   -- deg per frame to count as "dropping"
local CRANK_DEGREES_PER_DROP = 20  -- accumulated crank degrees to drop one row
local MOVE_INITIAL_DELAY = 200     -- ms before horizontal auto-repeat starts
local MOVE_REPEAT_DELAY  = 50      -- ms between auto-repeats
local LOCK_DELAY_MS = 450          -- time a grounded piece waits before locking
local MAX_LOCK_RESETS = 15         -- moves/rotations that may restart the lock timer
local SOFT_DROP_FACTOR = 0.15      -- soft drop makes gravity ~6-7x faster
local MIN_SOFT_DELAY   = 30
local HARD_DROP_POINTS_PER_CELL = 2
local CLEAR_ANIM_MS = 420
local GAME_OVER_SCREEN_MS = 5000   -- auto-return to title after this long
local GAME_OVER_SKIP_MS = 1500     -- A/B may skip the stats after this long
local TITLE_INPUT_GRACE_MS = 400   -- ignore A/B briefly when the title appears
local SAVE_FILE = "tetris_save"

-- === Settings (persisted) ===
local SHOW_GHOST = true
local USE_SEVEN_BAG = false
local BLOCK_STYLES = { "shaded", "hatched" }
local blockStyle = "shaded"
local bestScore = 0

-- === State ===
-- "title" | "game" | "gameover" | "credits"
local state = "title"
local creditsReturnState = "title"
local inputReadyAt = 0

local board = {}
local currentPiece = nil
local nextPiece = nil
local score = 0
local linesClearedTotal = 0
local level = 0
local dropDelay = 800
local dropTimer = 0

local moveDir = 0          -- -1 left, +1 right, 0 none
local moveTimer = 0
local lockStart = nil
local lockResets = 0
local lowestY = 0

local pendingClears = nil  -- full row indices (1-based, ascending)
local clearAnimStart = nil

local gameOverStart = nil
local runStartMs = 0
local runEndMs = nil
local piecesPlaced = 0
local runMadeBest = false

local crankDropCharge = 0
local crankPulseUntil = 0
local ambientCrankEnergy = 0
local ambientCrankSpin = 0
local accelTiltX, accelTiltY = 0, 0

local sevenBagMenuItem = nil
local ghostMenuItem = nil

-- === Pieces ===
-- Spawn orientation (rotation state 0) inside a BOX x BOX grid, SRS style.
local tetrominos = {
    I = {{0,1},{1,1},{2,1},{3,1}},
    O = {{0,0},{1,0},{0,1},{1,1}},
    T = {{1,0},{0,1},{1,1},{2,1}},
    S = {{1,0},{2,0},{0,1},{1,1}},
    Z = {{0,0},{1,0},{1,1},{2,1}},
    J = {{0,0},{0,1},{1,1},{2,1}},
    L = {{2,0},{0,1},{1,1},{2,1}}
}
local tetrominoKeys = {"I","O","T","S","Z","J","L"}
local BOX = { I = 4, O = 2, T = 3, S = 3, Z = 3, J = 3, L = 3 }

-- ROT[key][r] = cells for rotation state r (0..3), rotated clockwise in the box
local ROT = {}
for key, cells in pairs(tetrominos) do
    local n = BOX[key]
    ROT[key] = { [0] = cells }
    for r = 1, 3 do
        local rotated = {}
        for i, c in ipairs(ROT[key][r - 1]) do
            rotated[i] = { n - 1 - c[2], c[1] }
        end
        ROT[key][r] = rotated
    end
end

-- SRS clockwise wall kicks, indexed by the starting rotation state.
-- Converted to screen coordinates (+y is down).
local KICKS_JLSTZ = {
    [0] = {{0,0},{-1,0},{-1,-1},{0,2},{-1,2}},
    [1] = {{0,0},{1,0},{1,1},{0,-2},{1,-2}},
    [2] = {{0,0},{1,0},{1,-1},{0,2},{1,2}},
    [3] = {{0,0},{-1,0},{-1,1},{0,-2},{-1,-2}},
}
local KICKS_I = {
    [0] = {{0,0},{-2,0},{1,0},{-2,1},{1,-2}},
    [1] = {{0,0},{-1,0},{2,0},{-1,-2},{2,1}},
    [2] = {{0,0},{2,0},{-1,0},{2,-1},{-1,2}},
    [3] = {{0,0},{1,0},{-2,0},{1,2},{-2,-1}},
}

-- Dither shade per piece for the "shaded" style: 0.0 = solid black, 1.0 = clear
local piecePattern = {
    I = 0.125, O = 0.0,   T = 0.5,
    S = 0.75,  Z = 0.25,  J = 0.875,
    L = 0.625
}

-- === Fonts ===
local titleFont = gfx.font.new("fonts/full-circle")
local hudFont = gfx.font.new("fonts/Supermini") or defaultFont
local mainFont = titleFont or hudFont or defaultFont

-- === SFX (synth, no assets) ===
local snd = playdate.sound
local sfx = {
    move   = snd.synth.new(snd.kWaveSquare),
    rotate = snd.synth.new(snd.kWaveTriangle),
    lock   = snd.synth.new(snd.kWaveSquare),
    clear  = snd.synth.new(snd.kWaveSine),
    level  = snd.synth.new(snd.kWaveSawtooth),
    drop   = snd.synth.new(snd.kWaveSquare),
}
sfx.move:setADSR(0,0.02,0,0.03);       sfx.move:setVolume(0.3)
sfx.rotate:setADSR(0,0.03,0,0.04);     sfx.rotate:setVolume(0.35)
sfx.lock:setADSR(0,0.02,0,0.05);       sfx.lock:setVolume(0.4)
sfx.clear:setADSR(0,0.06,0,0.12);      sfx.clear:setVolume(0.45)
sfx.level:setADSR(0,0.08,0,0.14);      sfx.level:setVolume(0.4)
sfx.drop:setADSR(0,0.02,0,0.06);       sfx.drop:setVolume(0.35)
local function SFX_move()   sfx.move:playNote(520) end
local function SFX_rotate() sfx.rotate:playNote(660) end
local function SFX_lock()   sfx.lock:playNote(340) end
local function SFX_clear(n) sfx.clear:playNote(680 + (n-1)*160) end
local function SFX_level()  sfx.level:playNote(860) end
local function SFX_drop()   sfx.drop:playNote(440) end

local function stopAllSfx()
    for _, syn in pairs(sfx) do syn:stop() end
end

-- === Persistence ===
local function saveData()
    playdate.datastore.write({
        bestScore = bestScore,
        SHOW_GHOST = SHOW_GHOST,
        USE_SEVEN_BAG = USE_SEVEN_BAG,
        BLOCK_STYLE = blockStyle,
    }, SAVE_FILE)
end

local function loadData()
    local data = playdate.datastore.read(SAVE_FILE)
    if not data then return end
    if type(data.bestScore) == "number" then bestScore = data.bestScore end
    if data.SHOW_GHOST ~= nil then SHOW_GHOST = data.SHOW_GHOST end
    if data.USE_SEVEN_BAG ~= nil then USE_SEVEN_BAG = data.USE_SEVEN_BAG end
    for _, s in ipairs(BLOCK_STYLES) do
        if data.BLOCK_STYLE == s then blockStyle = s end
    end
end

-- === Randomizer ===
local bag = {}

local function refillBag()
    bag = {"I","O","T","S","Z","J","L"}
    for i = #bag, 2, -1 do
        local j = math.random(i)
        bag[i], bag[j] = bag[j], bag[i]
    end
end

local function drawFromBag()
    if #bag == 0 then refillBag() end
    local key = bag[#bag]
    bag[#bag] = nil
    return key
end

-- === Block art (pre-rendered, cached per style/size/key) ===
local blockCache = {}

-- Fill the inner area of a hatched block with the piece's motif.
-- s = drawn size (block size minus the 1px gap), inner area is 1..s-2.
local function drawHatchMotif(key, s)
    gfx.setClipRect(1, 1, s - 2, s - 2)
    local function slash(step)      -- "/" lines, like the launcher art
        for c = -s, 2 * s, step do gfx.drawLine(c, s, c + s, 0) end
    end
    local function backslash(step)  -- "\" lines
        for c = -s, 2 * s, step do gfx.drawLine(c, 0, c + s, s) end
    end
    if key == "I" then
        slash(4)
    elseif key == "O" then
        slash(4); backslash(4)
    elseif key == "T" then
        slash(4)
        local d = math.max(1, s // 4)
        gfx.fillRect(2, 2, d, d)
    elseif key == "S" then
        backslash(4)
    elseif key == "Z" then
        slash(3)
    elseif key == "J" then
        backslash(3)
    else -- L
        for y = 2, s - 2, 3 do gfx.drawLine(1, y, s - 2, y) end
    end
    gfx.clearClipRect()
end

local function buildBlockImage(key, size, style, outlined)
    local s = size - 1
    local img = gfx.image.new(size, size, gfx.kColorClear)
    gfx.pushContext(img)
    if style == "hatched" then
        gfx.setColor(gfx.kColorWhite)
        gfx.fillRect(0, 0, s, s)
        gfx.setColor(gfx.kColorBlack)
        drawHatchMotif(key, s)
        gfx.drawRect(0, 0, s, s)
    else
        gfx.setColor(gfx.kColorBlack)
        gfx.setDitherPattern(piecePattern[key] or 0.0)
        gfx.fillRect(0, 0, s, s)
        gfx.setColor(gfx.kColorBlack)  -- resets the dither pattern
        if outlined then gfx.drawRect(0, 0, s, s) end
    end
    gfx.popContext()
    return img
end

local function getBlockImage(key, size, style, outlined)
    local id = style .. size .. key .. (outlined and "o" or "")
    local img = blockCache[id]
    if not img then
        img = buildBlockImage(key, size, style, outlined)
        blockCache[id] = img
    end
    return img
end

local function drawBlock(key, x, y, size, outlined)
    getBlockImage(key, size, blockStyle, outlined):draw(x, y)
end

-- === Menu ===
local function syncMenuChecks()
    if sevenBagMenuItem then sevenBagMenuItem:setValue(USE_SEVEN_BAG) end
    if ghostMenuItem then ghostMenuItem:setValue(SHOW_GHOST) end
end

local function setSevenBagEnabled(enabled)
    USE_SEVEN_BAG = enabled
    bag = {}
    syncMenuChecks()
    saveData()
end

local function setGhostEnabled(enabled)
    SHOW_GHOST = enabled
    syncMenuChecks()
    saveData()
end

local function cycleBlockStyle(dir)
    local idx = 1
    for i, s in ipairs(BLOCK_STYLES) do if s == blockStyle then idx = i end end
    idx = ((idx - 1 + dir) % #BLOCK_STYLES) + 1
    blockStyle = BLOCK_STYLES[idx]
    saveData()
end

local function enterTitle(now)
    state = "title"
    inputReadyAt = now + TITLE_INPUT_GRACE_MS
end

local function setupMenu()
    local m = playdate.getSystemMenu()
    m:removeAllMenuItems()
    sevenBagMenuItem = m:addCheckmarkMenuItem("7-bag", USE_SEVEN_BAG, setSevenBagEnabled)
    ghostMenuItem = m:addCheckmarkMenuItem("ghost", SHOW_GHOST, setGhostEnabled)
    m:addMenuItem("credits", function()
        if state == "credits" then return end
        -- An active run is kept and resumes when the credits are closed.
        creditsReturnState = (state == "game") and "game" or "title"
        state = "credits"
    end)
    syncMenuChecks()
end

-- Gravity table (milliseconds per row). Caps at last entry.
local DROP_DELAYS = {
    800, 720, 630, 550, 470, 400, 330, 270, 220, 180,  -- 0..9
    150, 130, 110, 100,  90,  80,  75,  70,  65,  60,  -- 10..19
     55,  50,  45,  42,  39,  36,  34,  32,  30,  28   -- 20..29
}
local function getDropDelayForLevel(lvl)
    return DROP_DELAYS[math.min(lvl + 1, #DROP_DELAYS)]
end

-- === Board / piece logic ===
local function resetBoard()
    for y = 1, ROWS do
        board[y] = {}
        for x = 1, COLS do board[y][x] = 0 end
    end
end

local function newPiece()
    local key
    if USE_SEVEN_BAG then key = drawFromBag()
    else key = tetrominoKeys[math.random(#tetrominoKeys)] end

    local minY = 999
    for _, c in ipairs(ROT[key][0]) do
        if c[2] < minY then minY = c[2] end
    end
    return { key = key, rot = 0, x = (COLS - BOX[key]) // 2, y = -minY }
end

local function cellsOf(piece, rot)
    return ROT[piece.key][rot or piece.rot]
end

local function isValidPosition(piece, dx, dy, rot)
    for _, c in ipairs(cellsOf(piece, rot)) do
        local x = piece.x + c[1] + dx
        local y = piece.y + c[2] + dy
        if x < 0 or x >= COLS or y >= ROWS then return false end
        if y >= 0 and board[y + 1][x + 1] ~= 0 then return false end
    end
    return true
end

local function getDropDistance(piece)
    local d = 0
    while isValidPosition(piece, 0, d + 1) do d += 1 end
    return d
end

local function addScore(points)
    score += points
    if score > bestScore then
        bestScore = score
        runMadeBest = true
    end
end

local function endRun(now)
    state = "gameover"
    gameOverStart = now
    runEndMs = now
    currentPiece = nil
    saveData()
end

local function spawnNext(now)
    currentPiece = nextPiece
    nextPiece = newPiece()
    lockStart = nil
    lockResets = 0
    lowestY = currentPiece.y
    dropTimer = now
    crankDropCharge = 0
    if not isValidPosition(currentPiece, 0, 0) then endRun(now) end
end

-- Writes the piece into the board. Returns false if any block is above the field.
local function lockPiece(piece)
    local inside = true
    for _, c in ipairs(cellsOf(piece)) do
        local px, py = piece.x + c[1], piece.y + c[2]
        if py < 0 then
            inside = false
        else
            board[py + 1][px + 1] = piece.key
        end
    end
    piecesPlaced += 1
    SFX_lock()
    return inside
end

local function findFullLines()
    local rows = {}
    for y = 1, ROWS do
        local full = true
        for x = 1, COLS do
            if board[y][x] == 0 then full = false; break end
        end
        if full then rows[#rows + 1] = y end
    end
    return rows
end

local function finalizeClear(now)
    -- Remove bottom-up so earlier removals don't shift the remaining indices,
    -- then add the same number of empty rows at the top.
    local cleared = #pendingClears
    for i = cleared, 1, -1 do
        table.remove(board, pendingClears[i])
    end
    for _ = 1, cleared do
        local row = {}
        for c = 1, COLS do row[c] = 0 end
        table.insert(board, 1, row)
    end
    pendingClears = nil
    clearAnimStart = nil

    local prevLevel = level
    local scoringTable = {40, 100, 300, 1200}
    addScore(scoringTable[cleared] * (prevLevel + 1))
    linesClearedTotal += cleared
    level = linesClearedTotal // 10
    dropDelay = getDropDelayForLevel(level)
    if level > prevLevel then SFX_level() end

    spawnNext(now)
end

local function lockAndAdvance(now)
    local inside = lockPiece(currentPiece)
    currentPiece = nil
    if not inside then endRun(now); return end
    local rows = findFullLines()
    if #rows > 0 then
        pendingClears = rows
        clearAnimStart = now
        SFX_clear(#rows)
    else
        spawnNext(now)
    end
end

-- A successful move or rotation restarts the lock timer (a limited number of times).
local function onPieceAdjusted(now)
    if lockStart and lockResets < MAX_LOCK_RESETS then
        lockStart = now
        lockResets += 1
    end
end

local function tryShift(dx, now)
    if isValidPosition(currentPiece, dx, 0) then
        currentPiece.x += dx
        SFX_move()
        onPieceAdjusted(now)
    end
end

local function tryRotate(now)
    local p = currentPiece
    if p.key == "O" then return end
    local from = p.rot
    local to = (from + 1) % 4
    local kicks = (p.key == "I") and KICKS_I[from] or KICKS_JLSTZ[from]
    for _, k in ipairs(kicks) do
        if isValidPosition(p, k[1], k[2], to) then
            p.x += k[1]
            p.y += k[2]
            p.rot = to
            SFX_rotate()
            onPieceAdjusted(now)
            return
        end
    end
end

local function hardDrop(now)
    local dist = getDropDistance(currentPiece)
    currentPiece.y += dist
    addScore(dist * HARD_DROP_POINTS_PER_CELL)
    SFX_drop()
    lockAndAdvance(now)
end

local function resetGame(now)
    resetBoard()
    bag = {}
    score = 0
    linesClearedTotal = 0
    level = 0
    dropDelay = getDropDelayForLevel(level)
    pendingClears = nil
    clearAnimStart = nil
    gameOverStart = nil
    runEndMs = nil
    runStartMs = now
    piecesPlaced = 0
    runMadeBest = false
    moveDir = 0
    crankPulseUntil = 0
    nextPiece = newPiece()
    spawnNext(now)
    state = "game"
end

-- Called after anything that froze the game (system menu, credits, sleep).
local function resumeTimers()
    local now = playdate.getCurrentTimeMilliseconds()
    dropTimer = now
    moveTimer = now + MOVE_INITIAL_DELAY
    if lockStart then lockStart = now end
    crankDropCharge = 0
    crankPulseUntil = 0
    playdate.getCrankChange() -- discard crank motion that happened meanwhile
end

-- === Drawing helpers ===
local scaledTextCache = {}

local function drawScaledTextCentered(text, cx, y, scale, font)
    local id = text .. "@" .. scale
    local image = scaledTextCache[id]
    if not image then
        local w = font:getTextWidth(text)
        local h = font:getHeight()
        image = gfx.image.new(w * scale, h * scale, gfx.kColorClear)
        local src = gfx.image.new(w, h, gfx.kColorClear)
        gfx.pushContext(src)
            gfx.setFont(font)
            gfx.drawText(text, 0, 0)
        gfx.popContext()
        gfx.pushContext(image)
            src:drawScaled(0, 0, scale)
        gfx.popContext()
        scaledTextCache[id] = image
    end
    image:draw(cx - image.width // 2, y)
end

local function drawTitleText(text, y)
    if titleFont then
        drawScaledTextCentered(text, SCREEN_W // 2, y, 2, titleFont)
    else
        gfx.drawTextAligned(text, SCREEN_W // 2, y + 8, kTextAlignment.center)
    end
end

local function drawMiniPiece(key, x, y, size, rot)
    for _, c in ipairs(ROT[key][rot or 0]) do
        drawBlock(key, x + c[1] * size, y + c[2] * size, size, true)
    end
end

local function drawSideWell(x, top, rows)
    local size = 8
    for y = 0, rows - 1 do
        for col = 0, 3 do
            if ((x + y * 7 + col * 11) % 5) < 2 then
                local key = tetrominoKeys[((y + col) % #tetrominoKeys) + 1]
                drawBlock(key, x + col * size, top + y * size, size, true)
            end
        end
    end
end

local function drawCrankIndicator(x, y, now)
    if playdate.isCrankDocked() then return end

    local active = now < crankPulseUntil
    local angle = playdate.getCrankPosition()
    if active then angle += (now // 18) % 360 end

    gfx.setColor(gfx.kColorBlack)
    gfx.setFont(mainFont)
    gfx.drawTextAligned("CRANK", x, y - 40, kTextAlignment.center)
    gfx.drawCircleAtPoint(x, y, 13)
    gfx.drawCircleAtPoint(x, y, 4)

    for i = 0, 11 do
        local tickAngle = math.rad(angle + i * 30)
        local outer = active and 21 or 19
        local inner = (i % 3 == 0) and 15 or 17
        gfx.drawLine(
            x + math.floor(math.cos(tickAngle) * inner + 0.5),
            y + math.floor(math.sin(tickAngle) * inner + 0.5),
            x + math.floor(math.cos(tickAngle) * outer + 0.5),
            y + math.floor(math.sin(tickAngle) * outer + 0.5))
    end

    local handAngle = math.rad(playdate.getCrankPosition() - 90)
    gfx.drawLine(x, y,
        x + math.floor(math.cos(handAngle) * 10 + 0.5),
        y + math.floor(math.sin(handAngle) * 10 + 0.5))
end

-- === Ambient background ===
-- Updated once per frame; crankDelta is this frame's crank motion that should energise it.
local function updateAmbience(crankDelta)
    local ax, ay = playdate.readAccelerometer()
    if ax and ay then
        accelTiltX = accelTiltX * 0.82 + ax * 0.18
        accelTiltY = accelTiltY * 0.82 + ay * 0.18
    end
    if crankDelta ~= 0 then
        ambientCrankEnergy = math.min(36, ambientCrankEnergy + math.abs(crankDelta) * 0.45)
        ambientCrankSpin = (ambientCrankSpin + crankDelta) % 360
    end
    ambientCrankEnergy *= 0.9
end

local function rectContains(rect, x, y)
    return x >= rect.x and x <= rect.x + rect.w and y >= rect.y and y <= rect.y + rect.h
end

local function drawAmbientBackground(blockedRects, now)
    local driftX = math.floor(accelTiltX * 18)
    local driftY = math.floor(accelTiltY * 18)
    local crankWave = math.floor(math.sin(math.rad(ambientCrankSpin)) * ambientCrankEnergy)
    local crankLift = math.floor(math.cos(math.rad(ambientCrankSpin)) * ambientCrankEnergy)
    local energy = math.floor(ambientCrankEnergy)

    gfx.setColor(gfx.kColorBlack)
    for i = 1, 56 do
        local x = (i * 43 + (now // 95) + driftX * ((i % 3) - 1) + crankWave * ((i % 4) - 1)) % SCREEN_W
        local y = (i * 29 + (now // 135) + driftY * (((i + 1) % 3) - 1) + crankLift * (((i + 2) % 4) - 1)) % SCREEN_H
        local blocked = false
        for r = 1, #blockedRects do
            if rectContains(blockedRects[r], x, y) then blocked = true; break end
        end

        if not blocked then
            local size = (i % 5 == 0) and 4 or 3
            local mode = (i + energy) % 7
            if mode == 0 then
                gfx.setDitherPattern(0.5)
                gfx.fillRect(x, y, size, size)
                gfx.setColor(gfx.kColorBlack)
            elseif mode == 1 then
                gfx.drawRect(x, y, size + 2, size + 2)
            elseif mode == 2 then
                gfx.drawLine(x, y, x + 6, y)
                gfx.drawLine(x + 3, y - 3, x + 3, y + 3)
            elseif mode == 3 then
                gfx.drawLine(x, y, x + 5, y + 5)
            elseif mode == 4 then
                gfx.drawLine(x, y + 3, x + 6, y + 3)
            else
                gfx.fillRect(x, y, 2, 2)
            end
        end
    end
end

-- === Screens ===
local function drawTitleScreen(now)
    gfx.clear(gfx.kColorWhite)
    drawAmbientBackground({
        { x = 58, y = 18, w = 284, h = 42 },
        { x = 120, y = 64, w = 160, h = 116 },
        { x = 94, y = 182, w = 212, h = 58 }
    }, now)

    drawSideWell(18, 34, 18)
    drawSideWell(350, 34, 18)

    gfx.setColor(gfx.kColorBlack)
    gfx.setFont(mainFont)
    drawTitleText("IAINTRIS", 22)

    -- Stage: shows the current block style
    gfx.drawRoundRect(135, 70, 130, 64, 4)
    drawMiniPiece("T", 145, 100, 12, 0)
    drawMiniPiece("I", 163, 78, 12, 1)
    drawMiniPiece("O", 225, 100, 12, 0)
    gfx.drawTextAligned("< " .. string.upper(blockStyle) .. " >", SCREEN_W // 2, 140, kTextAlignment.center)

    gfx.drawTextAligned("HIGH SCORE " .. bestScore, SCREEN_W // 2, 162, kTextAlignment.center)

    if (now // 420) % 2 == 0 then
        gfx.fillRoundRect(106, 186, 188, 22, 4)
        gfx.setImageDrawMode(gfx.kDrawModeFillWhite)
        gfx.drawTextAligned("PRESS A TO START", SCREEN_W // 2, 190, kTextAlignment.center)
        gfx.setImageDrawMode(gfx.kDrawModeCopy)
    else
        gfx.drawRoundRect(106, 186, 188, 22, 4)
        gfx.drawTextAligned("PRESS A TO START", SCREEN_W // 2, 190, kTextAlignment.center)
    end

    gfx.drawTextAligned("B: 7-BAG " .. (USE_SEVEN_BAG and "ON" or "OFF"), SCREEN_W // 2, 218, kTextAlignment.center)
end

local function drawCreditsScreen(now)
    gfx.clear(gfx.kColorWhite)
    drawAmbientBackground({
        { x = 64, y = 16, w = 272, h = 46 },
        { x = 70, y = 60, w = 260, h = 160 }
    }, now)

    drawSideWell(18, 34, 18)
    drawSideWell(350, 34, 18)

    gfx.setColor(gfx.kColorBlack)
    gfx.setFont(mainFont)
    drawTitleText("CREDITS", 20)

    local cx = SCREEN_W // 2
    local lines = {
        { "IAINTRIS", 18 },
        { "by Iain Bennett", 28 },
        { "Inspired by Tetris,", 16 },
        { "created by Alexey Pajitnov", 16 },
        { "in 1984.", 28 },
        { "Tetris is owned by", 16 },
        { "The Tetris Company.", 28 },
        { "An unofficial tribute for Playdate.", 0 },
    }
    local y = 66
    for _, l in ipairs(lines) do
        gfx.drawTextAligned(l[1], cx, y, kTextAlignment.center)
        y += l[2]
    end
end

local function drawGameOverScreen(now)
    gfx.clear(gfx.kColorWhite)
    drawAmbientBackground({
        { x = 56, y = 14, w = 288, h = 54 },
        { x = 76, y = 76, w = 248, h = 128 },
        { x = 120, y = 190, w = 160, h = 34 }
    }, now)

    local cx = SCREEN_W // 2
    drawSideWell(20, 34, 18)
    drawSideWell(348, 34, 18)

    gfx.setColor(gfx.kColorBlack)
    gfx.setFont(mainFont)
    drawTitleText("GAME OVER", 18)

    local endMs = runEndMs or now
    local secs = math.max(1, (endMs - runStartMs) // 1000)
    local lpm  = math.floor((linesClearedTotal * 60) / secs + 0.5)
    local ppm  = math.floor((piecesPlaced     * 60) / secs + 0.5)

    local rows = {
        {"SCORE", tostring(score)},
        {"HIGH SCORE", tostring(bestScore)},
        {"LEVEL", tostring(level)},
        {"LINES", linesClearedTotal .. "  " .. lpm .. " LPM"},
        {"PIECES", piecesPlaced .. "  " .. ppm .. " PPM"},
        {"TIME", secs .. "s"}
    }
    local y = 82
    for i = 1, #rows do
        gfx.drawText(rows[i][1], 96, y)
        gfx.drawTextAligned(rows[i][2], 304, y, kTextAlignment.right)
        y += 18
    end

    if runMadeBest then
        gfx.fillRoundRect(128, 196, 144, 20, 4)
        gfx.setImageDrawMode(gfx.kDrawModeFillWhite)
        gfx.drawTextAligned("NEW BEST", cx, 200, kTextAlignment.center)
        gfx.setImageDrawMode(gfx.kDrawModeCopy)
    end
end

-- HUD geometry (fixed, computed once)
local HUD = {}
do
    local labelH = mainFont:getHeight()
    HUD.margin = 10
    HUD.x = HUD.margin
    HUD.valueX = OFFSET_X - 12
    HUD.y = PLAYFIELD_TOP
    HUD.line = labelH + 2
    HUD.boxSize = CELL_SIZE * 4
    HUD.previewX = SCREEN_W - HUD.boxSize - (HUD.margin + 4)
    HUD.previewY = HUD.y + labelH + 4
    HUD.crankX = HUD.previewX + HUD.boxSize // 2
    HUD.crankY = HUD.previewY + HUD.boxSize + 52
    HUD.fieldW = COLS * CELL_SIZE
    HUD.fieldH = ROWS * CELL_SIZE
    HUD.fieldPanel = { x = OFFSET_X - 3, y = PLAYFIELD_TOP - 3, w = HUD.fieldW + 6, h = HUD.fieldH + 6 }
    HUD.hudPanel = { x = 0, y = HUD.y - 5, w = OFFSET_X - 12, h = HUD.line * 4 + 7 }
    HUD.nextPanel = {
        x = HUD.previewX - 6, y = HUD.y - 5,
        w = HUD.boxSize + 12, h = (HUD.previewY - HUD.y) + HUD.boxSize + 11
    }
    HUD.crankPanel = { x = HUD.crankX - 40, y = HUD.crankY - 44, w = 80, h = 68 }
    HUD.blocked = { HUD.fieldPanel, HUD.hudPanel, HUD.nextPanel, HUD.crankPanel }
end

local function drawBoard(now)
    gfx.clear(gfx.kColorWhite)
    drawAmbientBackground(HUD.blocked, now)

    -- Backplates
    gfx.setColor(gfx.kColorWhite)
    gfx.fillRect(HUD.hudPanel.x, HUD.hudPanel.y, HUD.hudPanel.w, HUD.hudPanel.h)
    gfx.fillRect(HUD.nextPanel.x, HUD.nextPanel.y, HUD.nextPanel.w, HUD.nextPanel.h)
    gfx.fillRect(OFFSET_X - 2, PLAYFIELD_TOP - 2, HUD.fieldW + 4, HUD.fieldH + 4)
    gfx.setColor(gfx.kColorBlack)

    -- HUD
    gfx.setFont(mainFont)
    local hudRows = {
        {"SCORE", score},
        {"LEVEL", level},
        {"LINES", linesClearedTotal},
        {"HIGH", bestScore}
    }
    for i = 1, #hudRows do
        local y = HUD.y + HUD.line * (i - 1)
        gfx.drawText(hudRows[i][1], HUD.x, y)
        gfx.drawTextAligned(tostring(hudRows[i][2]), HUD.valueX, y, kTextAlignment.right)
    end
    gfx.drawText("NEXT", HUD.previewX, HUD.y)

    -- Next piece, centred in the preview box
    if nextPiece then
        local cells = ROT[nextPiece.key][0]
        local minX, maxX, minY, maxY = 999, -999, 999, -999
        for _, c in ipairs(cells) do
            minX = math.min(minX, c[1]); maxX = math.max(maxX, c[1])
            minY = math.min(minY, c[2]); maxY = math.max(maxY, c[2])
        end
        local offX = (HUD.boxSize - (maxX - minX + 1) * CELL_SIZE) // 2 - minX * CELL_SIZE
        local offY = (HUD.boxSize - (maxY - minY + 1) * CELL_SIZE) // 2 - minY * CELL_SIZE
        for _, c in ipairs(cells) do
            drawBlock(nextPiece.key,
                HUD.previewX + offX + c[1] * CELL_SIZE,
                HUD.previewY + offY + c[2] * CELL_SIZE, CELL_SIZE, false)
        end
    end

    -- Placed blocks
    for y = 1, ROWS do
        local row = board[y]
        for x = 1, COLS do
            local cell = row[x]
            if cell ~= 0 then
                drawBlock(cell, OFFSET_X + (x - 1) * CELL_SIZE, PLAYFIELD_TOP + (y - 1) * CELL_SIZE, CELL_SIZE, false)
            end
        end
    end

    if currentPiece then
        local cells = cellsOf(currentPiece)
        -- Ghost (hidden when the piece is already grounded)
        if SHOW_GHOST then
            local dist = getDropDistance(currentPiece)
            if dist > 0 then
                gfx.setColor(gfx.kColorBlack)
                for _, c in ipairs(cells) do
                    gfx.drawRect(
                        OFFSET_X + (currentPiece.x + c[1]) * CELL_SIZE,
                        PLAYFIELD_TOP + (currentPiece.y + c[2] + dist) * CELL_SIZE,
                        CELL_SIZE - 1, CELL_SIZE - 1)
                end
            end
        end
        for _, c in ipairs(cells) do
            local py = currentPiece.y + c[2]
            if py >= 0 then
                drawBlock(currentPiece.key,
                    OFFSET_X + (currentPiece.x + c[1]) * CELL_SIZE,
                    PLAYFIELD_TOP + py * CELL_SIZE, CELL_SIZE, false)
            end
        end
    end

    drawCrankIndicator(HUD.crankX, HUD.crankY, now)

    -- Line-clear wipe
    if pendingClears and clearAnimStart then
        local elapsed = now - clearAnimStart
        local progress = math.min(1, elapsed / CLEAR_ANIM_MS)
        local center = (COLS + 1) / 2
        local opened = progress * ((COLS / 2) + 0.8)
        local tickPhase = elapsed // 55
        local s = CELL_SIZE - 1

        for _, row in ipairs(pendingClears) do
            local rowY = PLAYFIELD_TOP + (row - 1) * CELL_SIZE
            for x = 1, COLS do
                local cellX = OFFSET_X + (x - 1) * CELL_SIZE
                if math.abs(x - center) <= opened then
                    gfx.setColor(gfx.kColorWhite)
                    gfx.fillRect(cellX, rowY, s, s)
                    gfx.setColor(gfx.kColorBlack)
                    if ((x + tickPhase) % 2) == 0 then
                        gfx.drawLine(cellX + 1, rowY + s - 2, cellX + s - 2, rowY + 1)
                    else
                        gfx.drawLine(cellX + 1, rowY + 1, cellX + s - 2, rowY + s - 2)
                    end
                else
                    gfx.setColor(gfx.kColorWhite)
                    gfx.fillRect(cellX, rowY, s, s)
                    gfx.setColor(gfx.kColorBlack)
                    gfx.setDitherPattern(((x + tickPhase) % 2 == 0) and 0.25 or 0.75)
                    gfx.fillRect(cellX, rowY, s, s)
                    gfx.setColor(gfx.kColorBlack)
                end
            end
        end
    end

    -- Frames
    gfx.setColor(gfx.kColorBlack)
    gfx.drawRect(HUD.previewX - 2, HUD.previewY - 2, HUD.boxSize + 4, HUD.boxSize + 4)
    gfx.drawRect(OFFSET_X - 2, PLAYFIELD_TOP - 2, HUD.fieldW + 4, HUD.fieldH + 4)
end

-- Stats shown beside the system menu while paused (left 200px are visible).
local function buildMenuImage()
    local img = gfx.image.new(SCREEN_W, SCREEN_H, gfx.kColorWhite)
    gfx.pushContext(img)
        gfx.setColor(gfx.kColorBlack)
        gfx.setFont(mainFont)
        gfx.drawTextAligned("PAUSED", 100, 40, kTextAlignment.center)
        local rows = {
            {"SCORE", score}, {"LEVEL", level}, {"LINES", linesClearedTotal}, {"HIGH", bestScore}
        }
        local y = 80
        for _, r in ipairs(rows) do
            gfx.drawText(r[1], 24, y)
            gfx.drawTextAligned(tostring(r[2]), 176, y, kTextAlignment.right)
            y += 20
        end
        gfx.drawRect(14, 30, 172, 168)
    gfx.popContext()
    return img
end

-- === Per-state update ===
local function updateGame(now, crankDelta)
    -- Line-clear animation freezes play until it finishes
    if pendingClears then
        if now - clearAnimStart >= CLEAR_ANIM_MS then finalizeClear(now) end
        return
    end

    -- Crank: accelerated dropping
    local crankDrop = false
    local crankSpeed = math.abs(crankDelta)
    if crankSpeed >= CRANK_DROP_SENSITIVITY then
        crankDrop = true
        crankPulseUntil = now + 220
        crankDropCharge = math.min(crankDropCharge + crankSpeed, CRANK_DEGREES_PER_DROP * 4)
        while crankDropCharge >= CRANK_DEGREES_PER_DROP and isValidPosition(currentPiece, 0, 1) do
            currentPiece.y += 1
            crankDropCharge -= CRANK_DEGREES_PER_DROP
        end
        crankDropCharge = math.min(crankDropCharge, CRANK_DEGREES_PER_DROP - 1)
    elseif playdate.isCrankDocked() then
        crankDropCharge = 0
    end

    -- Left / Right with delayed auto-repeat
    if playdate.buttonJustPressed(playdate.kButtonLeft) then
        tryShift(-1, now); moveDir = -1; moveTimer = now + MOVE_INITIAL_DELAY
    elseif playdate.buttonJustPressed(playdate.kButtonRight) then
        tryShift(1, now); moveDir = 1; moveTimer = now + MOVE_INITIAL_DELAY
    end
    if playdate.buttonJustReleased(playdate.kButtonLeft) and moveDir == -1 then
        moveDir = playdate.buttonIsPressed(playdate.kButtonRight) and 1 or 0
        moveTimer = now + MOVE_INITIAL_DELAY
    end
    if playdate.buttonJustReleased(playdate.kButtonRight) and moveDir == 1 then
        moveDir = playdate.buttonIsPressed(playdate.kButtonLeft) and -1 or 0
        moveTimer = now + MOVE_INITIAL_DELAY
    end
    if moveDir ~= 0 and now >= moveTimer then
        tryShift(moveDir, now)
        moveTimer = now + MOVE_REPEAT_DELAY
    end

    -- Soft drop nudge
    if playdate.buttonJustPressed(playdate.kButtonDown) and isValidPosition(currentPiece, 0, 1) then
        currentPiece.y += 1
        dropTimer = now
    end

    -- Rotate
    if playdate.buttonJustPressed(playdate.kButtonA) then
        tryRotate(now)
    end

    -- Hard drop (ends this piece's frame)
    if playdate.buttonJustPressed(playdate.kButtonB) then
        hardDrop(now)
        return
    end

    -- Gravity
    local effectiveDelay = dropDelay
    if playdate.buttonIsPressed(playdate.kButtonDown) or crankDrop then
        effectiveDelay = math.max(MIN_SOFT_DELAY, math.floor(dropDelay * SOFT_DROP_FACTOR))
    end
    if now - dropTimer >= effectiveDelay then
        if isValidPosition(currentPiece, 0, 1) then currentPiece.y += 1 end
        dropTimer = now
    end

    -- Reaching a new lowest row earns the lock resets back
    if currentPiece.y > lowestY then
        lowestY = currentPiece.y
        lockResets = 0
    end

    -- Lock delay runs in real time, independent of gravity speed
    if isValidPosition(currentPiece, 0, 1) then
        lockStart = nil
    else
        lockStart = lockStart or now
        if now - lockStart >= LOCK_DELAY_MS then
            lockAndAdvance(now)
        end
    end
end

-- === Game loop ===
function playdate.update()
    local now = playdate.getCurrentTimeMilliseconds()
    local crankDelta = playdate.getCrankChange()
    if playdate.isCrankDocked() then crankDelta = 0 end

    if state == "credits" then
        updateAmbience(crankDelta)
        drawCreditsScreen(now)
        if playdate.buttonJustPressed(playdate.kButtonA) or playdate.buttonJustPressed(playdate.kButtonB) then
            if creditsReturnState == "game" then
                state = "game"
                resumeTimers()
            else
                enterTitle(now)
            end
        end
        return
    end

    if state == "title" then
        updateAmbience(crankDelta)
        drawTitleScreen(now)
        if now >= inputReadyAt then
            if playdate.buttonJustPressed(playdate.kButtonA) then
                resetGame(now)
            elseif playdate.buttonJustPressed(playdate.kButtonB) then
                setSevenBagEnabled(not USE_SEVEN_BAG)
            elseif playdate.buttonJustPressed(playdate.kButtonLeft) then
                cycleBlockStyle(-1)
            elseif playdate.buttonJustPressed(playdate.kButtonRight) then
                cycleBlockStyle(1)
            end
        end
        return
    end

    if state == "gameover" then
        updateAmbience(crankDelta)
        drawGameOverScreen(now)
        local elapsed = now - gameOverStart
        local skip = elapsed >= GAME_OVER_SKIP_MS and
            (playdate.buttonJustPressed(playdate.kButtonA) or playdate.buttonJustPressed(playdate.kButtonB))
        if skip or elapsed >= GAME_OVER_SCREEN_MS then
            enterTitle(now)
        end
        return
    end

    -- state == "game"
    updateGame(now, crankDelta)
    if state == "gameover" then
        drawGameOverScreen(now)
        return
    end
    -- Only crank motion that is actually dropping pieces stirs the background in play
    updateAmbience(math.abs(crankDelta) >= CRANK_DROP_SENSITIVITY and crankDelta or 0)
    drawBoard(now)
end

-- === Lifecycle ===
function playdate.gameWillPause()
    if state == "game" then
        playdate.setMenuImage(buildMenuImage())
    else
        playdate.setMenuImage(nil)
    end
    saveData()
end

function playdate.gameWillResume()
    resumeTimers()
end

function playdate.gameWillTerminate()
    if state == "gameover" and not runEndMs then
        runEndMs = playdate.getCurrentTimeMilliseconds()
    end
    saveData()
    stopAllSfx()
end

function playdate.deviceWillSleep()
    saveData()
    stopAllSfx()
end

function playdate.deviceDidWake()
    resumeTimers()
end

-- === Init ===
math.randomseed(playdate.getSecondsSinceEpoch())
playdate.startAccelerometer()
loadData()
setupMenu()
resetBoard()
enterTitle(playdate.getCurrentTimeMilliseconds())
