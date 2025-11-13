-- Grenade Helper V6 - v1.1b
-- Credits:
-- ShadyRetard - Grenade Helper base
-- Carter Poe & Agentsix1 - V6 API understanding
-- Ginette - Script optimization & AI reconstruction

--------------------------------
-- Constants & State
--------------------------------
local THROW_RADIUS          = 20
local DRAW_MARKER_DISTANCE  = 100
local GH_ACTION_COOLDOWN    = 30

local GRENADE_SAVE_FILE_NAME = "grenade_helper_data.dat"
local GRENADE_DATA_URL       = "https://raw.githubusercontent.com/Anybody4506/AMWRV6/refs/heads/main/Grenade%20Helper/grenade_helper_data.dat"
local SCRIPT_URL             = "https://raw.githubusercontent.com/Anybody4506/AMWRV6/refs/heads/main/Grenade%20Helper/Grenade%20Helper.lua"
local SCRIPT_NAME            = "Grenade Helper.lua"

-- Capability flags for safer calls
local HAS_HTTP           = type(http) == "table" and type(http.Get) == "function"
local HAS_FILE           = type(file) == "table"
local HAS_FILE_OPEN      = HAS_FILE and type(file.Open) == "function"
local HAS_FILE_WRITE     = HAS_FILE and type(file.Write) == "function"
local HAS_FILE_ENUMERATE = HAS_FILE and type(file.Enumerate) == "function"

local maps               = {}
local current_map_name   = nil
local last_action        = 0
local jumpthrow_stage    = 0
local jumpthrow_tick     = 0
local screen_w, screen_h = 0, 0

local checking_update    = false
local local_data_hash    = ""
local remote_data_hash   = ""
local local_script_hash  = ""
local remote_script_hash = ""
local update_window      = nil
local updates_found      = {}

-- Walkbot state
local walkbot_active        = false
local walkbot_target        = nil
local walkbot_target_nade   = nil
local walkbot_start_time    = 0
local WALKBOT_TIMEOUT       = 300
local WALKBOT_STOP_DISTANCE = 0.5

-- Movement buttons
local IN_FORWARD   = bit.lshift(1, 3)
local IN_BACK      = bit.lshift(1, 4)
local IN_MOVELEFT  = bit.lshift(1, 9)
local IN_MOVERIGHT = bit.lshift(1, 10)

--------------------------------
-- Notification System
--------------------------------
local notifications  = {}
local NOTIF_DURATION = 220

local function addNotification(text, r, g, b)
    table.insert(notifications, {
        text   = text,
        r      = r or 255,
        g      = g or 255,
        b      = b or 255,
        expire = globals.TickCount() + NOTIF_DURATION
    })
end

local function drawNotifications()
    local center_x = screen_w / 2
    local y_offset = screen_h * 0.8

    for i = #notifications, 1, -1 do
        local notif = notifications[i]

        if globals.TickCount() > notif.expire then
            table.remove(notifications, i)
        else
            local alpha = math.min(255, (notif.expire - globals.TickCount()) * 2)
            local tw, th = draw.GetTextSize(notif.text)

            draw.Color(0, 0, 0, alpha * 0.7)
            draw.FilledRect(
                center_x - tw / 2 - 10, y_offset - 5,
                center_x + tw / 2 + 10, y_offset + th + 5
            )

            draw.Color(notif.r, notif.g, notif.b, alpha)
            draw.TextShadow(center_x - tw / 2, y_offset, notif.text)

            y_offset = y_offset + th + 15
        end
    end
end

--------------------------------
-- Type definitions
--------------------------------
local POSITION_TYPES = {
    "stand", "jump", "run",
    "crouch", "jump + crouch", "run + jump"
}

local LAUNCH_TYPES = {
    "left", "right", "left + right"
}

local GRENADE_IDS = {
    [43] = "flashbang",
    [44] = "hegrenade",
    [45] = "smokegrenade",
    [46] = "molotovgrenade",
    [47] = "decoy",
    [48] = "molotovgrenade",
}

--------------------------------
-- Utility Functions
--------------------------------
local function clamp(x, a, b)
    return math.max(a, math.min(b, x))
end

local function canon_mapname(s)
    if not s or s == "" then return "" end
    s = tostring(s):lower()
    s = s:gsub("\\", "/"):gsub("^maps/", ""):gsub("%.bsp$", "")
         :gsub("%.vpk$", ""):gsub("%.zip$", ""):gsub("^.*/", "")
    return s
end

local function normalize_angles(pitch, yaw)
    pitch = clamp(pitch, -89, 89)
    yaw   = (yaw + 180) % 360 - 180
    return pitch, yaw
end

local function angles_to_forward(pitch, yaw)
    local rp, ry = math.rad(pitch), math.rad(yaw)
    local cp, sp = math.cos(rp), math.sin(rp)
    local cy, sy = math.cos(ry), math.sin(ry)
    return Vector3(cp * cy, cp * sy, -sp)
end

local function to_num2(angles)
    if not angles then return 0, 0 end

    local pitch, yaw = 0, 0

    if type(angles) == "userdata" then
        pitch = tonumber(angles.pitch) or 0
        yaw   = tonumber(angles.yaw)   or 0
    elseif type(angles) == "table" then
        pitch = tonumber(angles.pitch or angles.x or angles[1] or 0) or 0
        yaw   = tonumber(angles.yaw   or angles.y or angles[2] or 0) or 0
    end

    return normalize_angles(pitch, yaw)
end

local function get_origin_v3(ent)
    if not ent then return Vector3(0, 0, 0) end

    local origin = ent:GetAbsOrigin()
    if type(origin) == "userdata" then
        return origin
    elseif type(origin) == "table" then
        return Vector3(
            origin.x or origin[1] or 0,
            origin.y or origin[2] or 0,
            origin.z or origin[3] or 0
        )
    end

    return Vector3(0, 0, 0)
end

local function dist3v(a, b)
    if not a or not b then return 0 end

    local ax, ay, az
    local bx, by, bz

    if type(a) == "userdata" then
        ax, ay, az = a.x, a.y, a.z
    elseif type(a) == "table" then
        ax = a.x or a[1] or 0
        ay = a.y or a[2] or 0
        az = a.z or a[3] or 0
    else
        return 0
    end

    if type(b) == "userdata" then
        bx, by, bz = b.x, b.y, b.z
    elseif type(b) == "table" then
        bx = b.x or b[1] or 0
        by = b.y or b[2] or 0
        bz = b.z or b[3] or 0
    else
        return 0
    end

    local dx, dy, dz = ax - bx, ay - by, az - bz
    return math.sqrt(dx * dx + dy * dy + dz * dz)
end

local function get_velocity(me)
    if not me then return 0 end
    if not me.GetFieldVector then return 0 end

    local vel = me:GetFieldVector("m_vecAbsVelocity")
    if not vel then return 0 end

    return math.floor(math.min(10000, vel:Length2D() + 0.5))
end

local function simpleHash(str)
    if not str or str == "" then return 0 end
    local hash = 0
    for i = 1, #str do
        hash = (hash * 31 + string.byte(str, i)) % 2147483647
    end
    return hash
end

--------------------------------
-- Grenade Detection
--------------------------------
local function GetActiveGrenadeName()
    local me = entities.GetLocalPlayer()
    if not me then return nil end

    if me.IsAlive and not me:IsAlive() then
        return nil
    end

    local weapon_id = me.GetWeaponID and me:GetWeaponID() or nil
    return weapon_id and GRENADE_IDS[weapon_id] or nil
end

--------------------------------
-- Geometry
--------------------------------
local function GetThrowPositionV3(pos, pitch, yaw, z_offset)
    local fwd  = angles_to_forward(pitch, yaw)
    local base = Vector3(pos.x, pos.y, pos.z + z_offset)

    return Vector3(
        base.x + fwd.x * DRAW_MARKER_DISTANCE,
        base.y + fwd.y * DRAW_MARKER_DISTANCE,
        base.z + fwd.z * DRAW_MARKER_DISTANCE
    )
end

--------------------------------
-- Early data file check & download
--------------------------------
do
    if not HAS_FILE_OPEN then
        addNotification("[GH] file.Open not available, data file cannot be managed", 255, 100, 100)
    else
        local data_file_exists = false

        if HAS_FILE_ENUMERATE then
            file.Enumerate(function(filename)
                if filename == GRENADE_SAVE_FILE_NAME then
                    data_file_exists = true
                    addNotification("[GH] Data file found", 0, 255, 100)
                end
            end)
        else
            addNotification("[GH] file.Enumerate not available, skipping file scan", 255, 200, 0)
        end

        if not data_file_exists then
            addNotification("[GH] Data file not found, initializing...", 255, 200, 0)

            if HAS_HTTP then
                local ok, body_or_err = pcall(function()
                    return http.Get(GRENADE_DATA_URL)
                end)

                if ok then
                    local body = body_or_err
                    if body and body ~= "" and HAS_FILE_WRITE then
                        file.Write(GRENADE_SAVE_FILE_NAME, body)
                        addNotification("[GH] Data file downloaded successfully!", 0, 255, 100)
                    else
                        addNotification("[GH] Empty response or cannot write file, creating empty data file", 255, 200, 0)
                        local f = file.Open(GRENADE_SAVE_FILE_NAME, "a")
                        if f then f:Close() end
                    end
                else
                    addNotification("[GH] HTTP error while creating data file", 255, 100, 100)
                    local f = file.Open(GRENADE_SAVE_FILE_NAME, "a")
                    if f then f:Close() end
                end
            else
                addNotification("[GH] HTTP not available, creating empty data file", 255, 200, 0)
                local f = file.Open(GRENADE_SAVE_FILE_NAME, "a")
                if f then f:Close() end
            end
        end
    end
end

--------------------------------
-- Update System Functions
--------------------------------
local function downloadGrenadeData(callback)
    addNotification("[GH] Downloading grenade data...", 0, 200, 255)

    if not HAS_HTTP then
        addNotification("[GH] HTTP not available, cannot download data", 255, 100, 100)
        if callback then callback(false) end
        return
    end

    if not HAS_FILE_WRITE then
        addNotification("[GH] Cannot write data file", 255, 100, 100)
        if callback then callback(false) end
        return
    end

    local ok, err = pcall(function()
        http.Get(GRENADE_DATA_URL, function(body)
            if body and body ~= "" then
                file.Write(GRENADE_SAVE_FILE_NAME, body)
                local_data_hash = simpleHash(body)
                addNotification("[GH] Data downloaded!", 0, 255, 100)

                if loadData then
                    loadData()
                end

                if callback then
                    callback(true)
                end
            else
                addNotification("[GH] Data download failed (empty response)", 255, 100, 100)
                if callback then
                    callback(false)
                end
            end
        end)
    end)

    if not ok then
        addNotification("[GH] Data download failed (HTTP error)", 255, 100, 100)
        if callback then callback(false) end
    end
end

local function downloadScript(callback)
    addNotification("[GH] Downloading script...", 0, 200, 255)

    if not HAS_HTTP then
        addNotification("[GH] HTTP not available, cannot download script", 255, 100, 100)
        if callback then callback(false) end
        return
    end

    if not HAS_FILE_WRITE then
        addNotification("[GH] Cannot write script file", 255, 100, 100)
        if callback then callback(false) end
        return
    end

    local ok, err = pcall(function()
        http.Get(SCRIPT_URL, function(body)
            if body and body ~= "" then
                file.Write(SCRIPT_NAME, body)
                local_script_hash = simpleHash(body)
                addNotification("[GH] Script updated! Reload required", 255, 200, 0)

                if callback then
                    callback(true)
                end
            else
                addNotification("[GH] Script download failed (empty response)", 255, 100, 100)
                if callback then
                    callback(false)
                end
            end
        end)
    end)

    if not ok then
        addNotification("[GH] Script download failed (HTTP error)", 255, 100, 100)
        if callback then callback(false) end
    end
end

local function createUpdateWindow()
    if update_window then
        update_window:Remove()
        update_window = nil
    end

    update_window = gui.Window("gh_update_window", "Grenade Helper - Updates", 300, 200, 180, 360)
    if not update_window then
        addNotification("[GH] Failed to create update window", 255, 100, 100)
        return
    end

    local content_group = gui.Groupbox(update_window, "Update Status", 16, 16, 150, 0)
    gui.Text(content_group, "Update check complete!")

    for _, update in ipairs(updates_found) do
        gui.Text(content_group, " ")
        gui.Text(content_group, "--------------------------")
        gui.Text(content_group, " ")
        gui.Text(content_group, update.name)
        gui.Text(content_group, " ")
        gui.Text(content_group, "Status: " .. update.status)
        gui.Text(content_group, " ")

        if update.needs_update then
            if update.type == "data" then
                gui.Button(content_group, "Download Data", function()
                    downloadGrenadeData(function(success)
                        if success and update_window then
                            update.status       = "Downloaded!"
                            update.needs_update = false
                            update_window:Remove()
                            update_window = nil
                            createUpdateWindow()
                        end
                    end)
                end)
                gui.Text(content_group, "(Reload Required)")
            elseif update.type == "script" then
                gui.Button(content_group, "Download Script", function()
                    downloadScript(function(success)
                        if success and update_window then
                            update.status       = "Downloaded!"
                            update.needs_update = false
                            update_window:Remove()
                            update_window = nil
                            createUpdateWindow()
                        end
                    end)
                end)
                gui.Text(content_group, "(Reload Required)")
                gui.Text(content_group, " ")
            end
        end
    end

    gui.Text(content_group, "")
    gui.Text(content_group, "--------------------------")
    gui.Text(content_group, " ")

    gui.Button(content_group, "Close Window", function()
        if update_window then
            update_window:Remove()
            update_window = nil
        end
    end)
end

local function finishUpdateCheck()
    local has_updates = false

    for _, update in ipairs(updates_found) do
        if update.needs_update then
            has_updates = true
            break
        end
    end

    if has_updates then
        addNotification("[GH] Updates available!", 0, 255, 100)
    else
        addNotification("[GH] Everything is up to date!", 0, 255, 100)
    end

    createUpdateWindow()
end

local function checkForUpdates()
    if checking_update then
        addNotification("[GH] Already checking...", 255, 200, 0)
        return
    end

    if not HAS_HTTP then
        addNotification("[GH] HTTP disabled, cannot check updates", 255, 200, 0)
        return
    end

    checking_update = true
    updates_found   = {}

    addNotification("[GH] Checking for updates...", 0, 200, 255)

    local checks_remaining = 2

    local function check_done()
        checks_remaining = checks_remaining - 1
        if checks_remaining == 0 then
            checking_update = false
            finishUpdateCheck()
        end
    end

    -- Data check
    local ok1, err1 = pcall(function()
        http.Get(GRENADE_DATA_URL, function(body)
            if body and body ~= "" then
                remote_data_hash = simpleHash(body)

                if local_data_hash == "" and HAS_FILE_OPEN then
                    local f = file.Open(GRENADE_SAVE_FILE_NAME, "r")
                    if f then
                        local local_data = f:Read()
                        f:Close()
                        local_data_hash = simpleHash(local_data)
                    end
                end

                if remote_data_hash ~= local_data_hash then
                    table.insert(updates_found, {
                        name         = "Grenade Positions Data",
                        status       = "Update available",
                        type         = "data",
                        needs_update = true
                    })
                else
                    table.insert(updates_found, {
                        name         = "Grenade Positions Data",
                        status       = "Up to date",
                        type         = "data",
                        needs_update = false
                    })
                end
            else
                table.insert(updates_found, {
                    name         = "Grenade Positions Data",
                    status       = "Check failed",
                    type         = "data",
                    needs_update = false
                })
            end

            check_done()
        end)
    end)

    if not ok1 then
        table.insert(updates_found, {
            name         = "Grenade Positions Data",
            status       = "Check failed (HTTP error)",
            type         = "data",
            needs_update = false
        })
        addNotification("[GH] Data update check failed (HTTP error)", 255, 100, 100)
        check_done()
    end

    -- Script check
    local ok2, err2 = pcall(function()
        http.Get(SCRIPT_URL, function(body)
            if body and body ~= "" then
                remote_script_hash = simpleHash(body)

                if local_script_hash == "" and HAS_FILE_OPEN then
                    local f = file.Open(SCRIPT_NAME, "r")
                    if f then
                        local local_script = f:Read()
                        f:Close()
                        local_script_hash = simpleHash(local_script)
                    end
                end

                if remote_script_hash ~= local_script_hash then
                    table.insert(updates_found, {
                        name         = "Grenade Helper Script",
                        status       = "Update available",
                        type         = "script",
                        needs_update = true
                    })
                else
                    table.insert(updates_found, {
                        name         = "Grenade Helper Script",
                        status       = "Up to date",
                        type         = "script",
                        needs_update = false
                    })
                end
            else
                table.insert(updates_found, {
                    name         = "Grenade Helper Script",
                    status       = "Check failed",
                    type         = "script",
                    needs_update = false
                })
            end

            check_done()
        end)
    end)

    if not ok2 then
        table.insert(updates_found, {
            name         = "Grenade Helper Script",
            status       = "Check failed (HTTP error)",
            type         = "script",
            needs_update = false
        })
        addNotification("[GH] Script update check failed (HTTP error)", 255, 100, 100)
        check_done()
    end
end

--------------------------------
-- UI Configuration
--------------------------------
local visuals_ref = gui.Reference("VISUALS", "Local")
local GH_GB       = gui.Groupbox(visuals_ref, "Grenade Helper", 15, 0, 352, 0)

local GH_ENABLED        = gui.Checkbox(GH_GB, "gh.enabled", "Enable Grenade Helper", true)
local GH_NAME_EB        = gui.Editbox(GH_GB, "gh.name", "Throw Name")
local GH_POSITION_CB    = gui.Combobox(GH_GB, "gh.position", "Position Type", unpack(POSITION_TYPES))
local GH_LAUNCH_CB      = gui.Combobox(GH_GB, "gh.launch", "Launch Type", unpack(LAUNCH_TYPES))
local GH_ENABLE_KB      = gui.Checkbox(GH_GB, "gh.kb.enabled", "Enable Keybinds", true)
local GH_SAVE_KB        = gui.Keybox(GH_GB, "gh.kb.save", "Capture & Save", 97)
local GH_DEL_KB         = gui.Keybox(GH_GB, "gh.kb.del", "Delete Nearest", 98)
local GH_JUMPTHROW_KB   = gui.Keybox(GH_GB, "gh.kb.jumpthrow", "Jump Throw", 70)
local GH_WALKBOT_KB     = gui.Keybox(GH_GB, "gh.kb.walkbot", "Walk To Nearest", 18)
local GH_VISUALS_DISTANCE_SL = gui.Slider(GH_GB, "gh.visuals.distance", "Display Distance", 800, 1, 9999)

gui.Text(GH_GB, " ")
gui.Text(GH_GB, "Colors:")
gui.Text(GH_GB, " ")

local CP_TEXT_NAME       = gui.ColorPicker(GH_GB, "gh.color.name", "Throw Name", 255, 255, 0, 255)
local CP_TEXT_POS        = gui.ColorPicker(GH_GB, "gh.color.position", "Position Type", 150, 255, 150, 200)
local CP_TEXT_LAUNCH     = gui.ColorPicker(GH_GB, "gh.color.launch", "Launch Type", 255, 150, 150, 200)
local CP_LINE            = gui.ColorPicker(GH_GB, "gh.color.line", "Direction Line", 0, 255, 255, 220)
local CP_BOX             = gui.ColorPicker(GH_GB, "gh.color.box", "Box Color", 0, 0, 0, 255)
local CP_FINAL           = gui.ColorPicker(GH_GB, "gh.color.final", "Active Box", 0, 255, 100, 255)

gui.Button(GH_GB, "Check for Updates", function()
    checkForUpdates()
end)

--------------------------------
-- Data Persistence
--------------------------------
local function parseStringifiedTable(s)
    local new_map = {}

    if not s or s == "" then
        return new_map
    end

    for line in string.gmatch(s, "([^\n]*)\n?") do
        if line ~= "" then
            local p = {}

            for seg in string.gmatch(line, "([^,]*)") do
                if seg ~= "" then
                    p[#p + 1] = seg
                end
            end

            local key = canon_mapname(p[1])
            if key ~= "" and #p >= 10 then
                new_map[key] = new_map[key] or {}

                table.insert(new_map[key], {
                    name     = p[2],
                    position = p[3],
                    launch   = p[4],
                    nade     = p[5],
                    pos      = {
                        x = tonumber(p[6]) or 0,
                        y = tonumber(p[7]) or 0,
                        z = tonumber(p[8]) or 0
                    },
                    ax = tonumber(p[9])  or 0,
                    ay = tonumber(p[10]) or 0
                })
            end
        end
    end

    return new_map
end

local function convertTableToDataString(obj)
    local out = {}

    if not obj then
        return ""
    end

    for map_name, map in pairs(obj) do
        if type(map) == "table" then
            for _, t in ipairs(map) do
                out[#out + 1] = table.concat({
                    map_name,
                    t.name     or "",
                    t.position or "stand",
                    t.launch   or "left",
                    t.nade     or "auto",
                    tostring(t.pos and t.pos.x or 0),
                    tostring(t.pos and t.pos.y or 0),
                    tostring(t.pos and t.pos.z or 0),
                    tostring(t.ax or 0),
                    tostring(t.ay or 0)
                }, ",")
            end
        end
    end

    return (#out > 0) and (table.concat(out, "\n") .. "\n") or ""
end

function loadData()
    if not HAS_FILE_OPEN then
        addNotification("[GH] Cannot load data (file.Open unavailable)", 255, 100, 100)
        return
    end

    local ok, f_or_err = pcall(function()
        return file.Open(GRENADE_SAVE_FILE_NAME, "r")
    end)

    if not ok then
        addNotification("[GH] Error opening data file", 255, 100, 100)
        return
    end

    local f = f_or_err
    if not f then return end

    local ok_read, data_or_err = pcall(function()
        return f:Read()
    end)

    f:Close()

    if not ok_read then
        addNotification("[GH] Error reading data file", 255, 100, 100)
        return
    end

    local data = data_or_err
    if data and data ~= "" then
        maps            = parseStringifiedTable(data)
        local_data_hash = simpleHash(data)
        addNotification("[GH] Data file loaded", 0, 255, 100)
    end
end

local function saveData()
    if not HAS_FILE_WRITE then
        addNotification("[GH] Cannot save data (file.Write unavailable)", 255, 100, 100)
        return
    end

    local ok, err = pcall(function()
        file.Write(GRENADE_SAVE_FILE_NAME, convertTableToDataString(maps))
    end)

    if not ok then
        addNotification("[GH] Error writing data file", 255, 100, 100)
    else
        addNotification("[GH] Data saved", 0, 255, 100)
    end
end

--------------------------------
-- Throw Selection & Filtering
--------------------------------
local function getActiveThrows(map, me, nade_name, max_distance)
    local list, in_range = {}, {}

    if not map then
        return list, false
    end

    local mpos = get_origin_v3(me)

    for i = 1, #map do
        local t = map[i]

        local should_show = t.nade == nade_name or t.nade == "auto"
        if should_show then
            local tpos = Vector3(t.pos.x, t.pos.y, t.pos.z)
            local d    = dist3v(mpos, tpos)

            if d <= max_distance then
                t.distance = d
                if d < THROW_RADIUS then
                    in_range[#in_range + 1] = t
                else
                    list[#list + 1] = t
                end
            end
        end
    end

    return (#in_range > 0 and in_range or list), (#in_range > 0)
end

local function getClosestThrow(map, me, nade_name, max_distance)
    if not map or #map == 0 then
        return nil, math.huge
    end

    local mpos     = get_origin_v3(me)
    local best     = nil
    local bestDist = math.huge

    for i = 1, #map do
        local t = map[i]
        local should_consider = t.nade == nade_name or t.nade == "auto"

        if should_consider then
            local d = dist3v(mpos, Vector3(t.pos.x, t.pos.y, t.pos.z))
            if d < bestDist and d <= max_distance then
                best     = t
                bestDist = d
            end
        end
    end

    return best, bestDist
end

--------------------------------
-- Rendering
--------------------------------
local function showNadeThrows()
    local me = entities.GetLocalPlayer()
    if not me then return end

    local weapon_name = GetActiveGrenadeName()
    if not weapon_name then return end

    if not current_map_name or not maps[current_map_name] then
        return
    end

    local current_throws = maps[current_map_name]
    local max_distance   = GH_VISUALS_DISTANCE_SL:GetValue()

    local list, within = getActiveThrows(current_throws, me, weapon_name, max_distance)
    if not list then return end

    local nr, ng, nb, na       = CP_TEXT_NAME:GetValue()
    local pr, pg, pb, pa       = CP_TEXT_POS:GetValue()
    local lr, lg, lb, la       = CP_TEXT_LAUNCH:GetValue()
    local lnr, lng, lnb, lna   = CP_LINE:GetValue()
    local br, bg, bb, ba       = CP_BOX:GetValue()
    local fr, fg, fb, fa       = CP_FINAL:GetValue()

    for i = 1, #list do
        local t = list[i]
        if t.distance and t.distance > max_distance then
            goto continue
        end

        local pos          = Vector3(t.pos.x, t.pos.y, t.pos.z)
        local is_crouching = t.position:find("crouch") ~= nil
        local zoff         = is_crouching and 46 or 64

        local axn, ayn     = to_num2({ pitch = t.ax, yaw = t.ay })
        local fwd          = angles_to_forward(axn, ayn)
        local ahead        = Vector3(pos.x + fwd.x * 10, pos.y + fwd.y * 10, pos.z)
        local s1x, s1y     = client.WorldToScreen(ahead)

        if within then
            local target = GetThrowPositionV3(pos, axn, ayn, zoff)
            local dx, dy = client.WorldToScreen(target)

            if dx and dy then
                draw.Color(fr, fg, fb, fa)
                draw.OutlinedRect(dx - 8, dy - 8, dx + 8, dy + 8)

                draw.Color(lnr, lng, lnb, lna)
                draw.Line(dx, dy, screen_w / 2, screen_h / 2)

                if t.name then
                    local ntw, nth = draw.GetTextSize(t.name)
                    draw.Color(nr, ng, nb, na)
                    draw.TextShadow(dx - ntw / 2, dy - nth - 10, t.name)
                end

                local pos_text = "[" .. t.position .. "]"
                local ptw, pth = draw.GetTextSize(pos_text)
                draw.Color(pr, pg, pb, pa)
                draw.TextShadow(dx - ptw / 2, dy + 12, pos_text)

                local launch_text = "[" .. t.launch .. "]"
                local ltw, _ = draw.GetTextSize(launch_text)
                draw.Color(lr, lg, lb, la)
                draw.TextShadow(dx - ltw / 2, dy + 12 + pth + 2, launch_text)
            end
        end

        local cx, cy = client.WorldToScreen(pos)
        if not cx or not cy then
            goto continue
        end

        local half   = THROW_RADIUS / 2
        local ul     = Vector3(pos.x - half, pos.y - half, pos.z)
        local bl     = Vector3(pos.x - half, pos.y + half, pos.z)
        local ur     = Vector3(pos.x + half, pos.y - half, pos.z)
        local brpos  = Vector3(pos.x + half, pos.y + half, pos.z)

        local ulx, uly = client.WorldToScreen(ul)
        local blx, bly = client.WorldToScreen(bl)
        local urx, ury = client.WorldToScreen(ur)
        local brx, bry = client.WorldToScreen(brpos)

        local alpha = clamp((1 - (t.distance or 0) / max_distance) * 255, 50, 255)

        draw.Color(br, bg, bb, alpha)

        if ulx and uly and blx and bly and urx and ury and brx and bry then
            draw.Line(ulx, uly, blx, bly)
            draw.Line(blx, bly, brx, bry)
            draw.Line(brx, bry, urx, ury)
            draw.Line(urx, ury, ulx, uly)
        else
            draw.FilledRect(cx - 3, cy - 3, cx + 3, cy + 3)
        end

        if t.name then
            local tw, th = draw.GetTextSize(t.name)
            draw.Color(nr, ng, nb, alpha)
            draw.TextShadow(cx - tw / 2, cy - th - 4, t.name)
        end

        if s1x and s1y then
            draw.Color(lnr, lng, lnb, lna)
            draw.Line(cx, cy, s1x, s1y)
        end

        ::continue::
    end
end

--------------------------------
-- Walkbot System
--------------------------------
local function moveToPosition(cmd, me, target_pos, dist)
    if not cmd or not me or not target_pos then return end

    local origin   = get_origin_v3(me)
    local move_dir = Vector3(target_pos.x - origin.x, target_pos.y - origin.y, 0)

    if move_dir.x == 0 and move_dir.y == 0 then
        return
    end

    local dir_ang   = move_dir:Angles()
    local view_ang  = cmd:GetViewAngles()
    local yaw_diff  = dir_ang.y - view_ang.y

    while yaw_diff > 180 do yaw_diff = yaw_diff - 360 end
    while yaw_diff < -180 do yaw_diff = yaw_diff + 360 end

    local yaw_rad = math.rad(yaw_diff)

    cmd:SetForwardMove(math.cos(yaw_rad))
    cmd:SetSideMove(math.sin(yaw_rad))

    local buttons = bit.band(cmd:GetButtons() or 0,
        bit.bnot(bit.bor(IN_FORWARD, IN_BACK, IN_MOVELEFT, IN_MOVERIGHT)))

    local tick = globals.TickCount()

    if dist > 45 then
        buttons = bit.bor(buttons, IN_FORWARD, IN_MOVELEFT)
    else
        if (tick % 3) == 0 then
            buttons = bit.bor(buttons, IN_FORWARD, IN_MOVELEFT)
        else
            cmd:SetForwardMove(0)
            cmd:SetSideMove(0)
        end
    end

    cmd:SetButtons(buttons)
end

local function walkbotNavigate(cmd, me, target_pos)
    if not target_pos or not cmd or not me then return false end

    local my_pos = get_origin_v3(me)
    local dist   = dist3v(my_pos, target_pos)

    if dist < WALKBOT_STOP_DISTANCE then
        cmd:SetForwardMove(0)
        cmd:SetSideMove(0)
        addNotification("[GH] Arrived at position!", 0, 255, 100)
        return true
    end

    if globals.TickCount() - walkbot_start_time > WALKBOT_TIMEOUT then
        addNotification("[GH] Walkbot timeout - cancelled", 255, 100, 0)
        return true
    end

    moveToPosition(cmd, me, target_pos, dist)
    return false
end

local function startWalkbot(me)
    if not current_map_name or not maps[current_map_name] then
        addNotification("[GH] No throws on this map", 255, 100, 100)
        return
    end

    local weapon_name = GetActiveGrenadeName()
    if not weapon_name then
        addNotification("[GH] No grenade equipped", 255, 100, 0)
        return
    end

    local max_distance = GH_VISUALS_DISTANCE_SL:GetValue()
    local best, dist   = getClosestThrow(maps[current_map_name], me, weapon_name, max_distance)

    if not best then
        addNotification("[GH] No throws found in range", 255, 100, 100)
        return
    end

    walkbot_target      = Vector3(best.pos.x, best.pos.y, best.pos.z)
    walkbot_target_nade = weapon_name
    walkbot_active      = true
    walkbot_start_time  = globals.TickCount()

    addNotification("[GH] Walking to: " .. (best.name or "position"), 0, 255, 255)
end

--------------------------------
-- Actions
--------------------------------
local function doAdd(cmd)
    local me = entities.GetLocalPlayer()
    if not me or (me.IsAlive and not me:IsAlive()) then
        addNotification("[GH] Player not alive", 255, 100, 100)
        return
    end

    if get_velocity(me) > 0 then
        addNotification("[GH] Must be standing still", 255, 100, 0)
        return
    end

    if not current_map_name or current_map_name == "" then
        addNotification("[GH] No map loaded", 255, 100, 100)
        return
    end

    maps[current_map_name] = maps[current_map_name] or {}

    local name = tostring(GH_NAME_EB:GetValue() or "")
    name       = name:gsub("^%s+", ""):gsub("%s+$", "")

    if name == "" then
        addNotification("[GH] Name is empty", 255, 100, 100)
        return
    end

    local position = POSITION_TYPES[GH_POSITION_CB:GetValue() + 1] or "stand"
    local launch   = LAUNCH_TYPES[GH_LAUNCH_CB:GetValue() + 1]   or "left"

    local mpos     = get_origin_v3(me)
    local ax, ay   = 0, 0

    if cmd and cmd.GetViewAngles and cmd:GetViewAngles() then
        ax, ay = to_num2(cmd:GetViewAngles())
    end

    local nade = GetActiveGrenadeName() or "auto"

    table.insert(maps[current_map_name], {
        name     = name,
        position = position,
        launch   = launch,
        nade     = nade,
        pos      = { x = mpos.x, y = mpos.y, z = mpos.z },
        ax       = ax,
        ay       = ay
    })

    saveData()
end

local function doDel(me)
    if not current_map_name or not maps[current_map_name] then
        addNotification("[GH] No throws on this map", 255, 100, 100)
        return
    end

    local weapon_name = GetActiveGrenadeName() or "auto"
    local max_distance = GH_VISUALS_DISTANCE_SL:GetValue()

    local best = getClosestThrow(maps[current_map_name], me, weapon_name, max_distance)
    if not best then
        addNotification("[GH] No throws found", 255, 100, 100)
        return
    end

    local list = maps[current_map_name]
    for i = #list, 1, -1 do
        if list[i] == best then
            table.remove(list, i)
            saveData()
            addNotification("[GH] Deleted: " .. (best.name or "unnamed"), 255, 150, 0)
            return
        end
    end
end

--------------------------------
-- Event Handlers
--------------------------------
local function gameEventHandler(event)
    if not GH_ENABLED:GetValue() then return end
    if not event or not event.GetName then return end

    local event_name = event:GetName()

    if event_name == "round_start"
        or event_name == "round_end"
        or event_name == "player_death"
    then
        jumpthrow_stage     = 0
        walkbot_active      = false
        walkbot_target      = nil
        walkbot_target_nade = nil
    end
end

--------------------------------
-- Main Callbacks
--------------------------------
local function drawEventHandler()
    screen_w, screen_h = draw.GetScreenSize()

    if not GH_ENABLED:GetValue() then return end

    local active_map = engine.GetMapName and engine.GetMapName() or nil
    if not active_map or active_map == "" then return end

    local map_key = canon_mapname(active_map)
    if map_key == "" then return end

    if current_map_name ~= map_key then
        current_map_name = map_key
        loadData()
    end

    maps[current_map_name] = maps[current_map_name] or {}

    showNadeThrows()
    drawNotifications()

    if walkbot_active and walkbot_target then
        local me = entities.GetLocalPlayer()
        if me then
            local my_pos = get_origin_v3(me)
            local dist   = dist3v(my_pos, walkbot_target)

            draw.Color(0, 255, 255, 255)
            draw.TextShadow(10, screen_h - 50, "[GH] Walking to position...")
            draw.TextShadow(10, screen_h - 35, string.format("Distance: %.1f units", dist))
            draw.TextShadow(10, screen_h - 20, "(Press ALT again to cancel)")
        end
    end
end

local function moveEventHandler(cmd)
    if not GH_ENABLED:GetValue() then return end
    if not cmd then return end

    local me = entities.GetLocalPlayer()
    if not me or (me.IsAlive and not me:IsAlive()) then
        walkbot_active      = false
        walkbot_target      = nil
        walkbot_target_nade = nil
        return
    end

    if not current_map_name or not maps or not maps[current_map_name] then
        return
    end

    if last_action > globals.TickCount() then
        last_action = globals.TickCount()
    end

    if walkbot_active and walkbot_target then
        local current_nade = GetActiveGrenadeName()
        if current_nade ~= walkbot_target_nade then
            walkbot_active      = false
            walkbot_target      = nil
            walkbot_target_nade = nil
            addNotification("[GH] Walkbot cancelled - wrong grenade", 255, 150, 0)
        else
            local completed = walkbotNavigate(cmd, me, walkbot_target)
            if completed then
                walkbot_active      = false
                walkbot_target      = nil
                walkbot_target_nade = nil
            end
        end
    end

    if GH_JUMPTHROW_KB:GetValue() ~= 0 then
        if input.IsButtonPressed(GH_JUMPTHROW_KB:GetValue()) and jumpthrow_stage == 0 then
            jumpthrow_stage = 1
            jumpthrow_tick  = globals.TickCount()
        end

        if jumpthrow_stage > 0 then
            local tick_diff = globals.TickCount() - jumpthrow_tick

            if jumpthrow_stage == 1 then
                cmd:SetButtons(bit.bor(cmd:GetButtons(), 2))
                if tick_diff >= 1 then
                    jumpthrow_stage = 2
                end
            elseif jumpthrow_stage == 2 then
                cmd:SetButtons(bit.band(cmd:GetButtons(), bit.bnot(1)))
                cmd:SetButtons(bit.band(cmd:GetButtons(), bit.bnot(2048)))
                if tick_diff >= 2 then
                    jumpthrow_stage = 0
                end
            end
        end
    end

    if not GH_ENABLE_KB:GetValue() then return end

    local add_key     = GH_SAVE_KB:GetValue()
    local del_key     = GH_DEL_KB:GetValue()
    local walkbot_key = GH_WALKBOT_KB:GetValue()

    if add_key == 0 and del_key == 0 and walkbot_key == 0 then
        return
    end

    if add_key ~= 0
        and input.IsButtonDown(add_key)
        and globals.TickCount() - last_action > GH_ACTION_COOLDOWN
    then
        last_action = globals.TickCount()
        doAdd(cmd)
    end

    if del_key ~= 0
        and input.IsButtonDown(del_key)
        and globals.TickCount() - last_action > GH_ACTION_COOLDOWN
    then
        last_action = globals.TickCount()
        doDel(me)
    end

    if walkbot_key ~= 0
        and input.IsButtonDown(walkbot_key)
        and globals.TickCount() - last_action > GH_ACTION_COOLDOWN
    then
        last_action = globals.TickCount()

        if walkbot_active then
            walkbot_active      = false
            walkbot_target      = nil
            walkbot_target_nade = nil
            addNotification("[GH] Walkbot cancelled", 255, 150, 0)
        else
            startWalkbot(me)
        end
    end
end

--------------------------------
-- Initialization
--------------------------------
local function initializeData()
    if not HAS_FILE_OPEN then
        addNotification("[GH] Cannot load initial data (file.Open unavailable)", 255, 100, 100)
        return
    end

    -- Load grenade data
    local ok_file, f_or_err = pcall(function()
        return file.Open(GRENADE_SAVE_FILE_NAME, "r")
    end)

    if ok_file and f_or_err then
        local f = f_or_err
        local ok_read, data_or_err = pcall(function()
            return f:Read()
        end)
        f:Close()

        if ok_read then
            local data = data_or_err
            if data and data ~= "" then
                maps            = parseStringifiedTable(data)
                local_data_hash = simpleHash(data)
                addNotification("[GH] Initial data loaded", 0, 255, 100)
            end
        else
            addNotification("[GH] Error reading initial data file", 255, 100, 100)
        end
    elseif not ok_file then
        addNotification("[GH] Error opening initial data file", 255, 100, 100)
    end

    -- Load script hash (optional)
    if HAS_FILE_OPEN then
        local ok_script, sf_or_err = pcall(function()
            return file.Open(SCRIPT_NAME, "r")
        end)

        if ok_script and sf_or_err then
            local sf = sf_or_err
            local ok_sread, script_data_or_err = pcall(function()
                return sf:Read()
            end)
            sf:Close()

            if ok_sread then
                local script_data = script_data_or_err
                if script_data and script_data ~= "" then
                    local_script_hash = simpleHash(script_data)
                end
            else
                addNotification("[GH] Error reading script file", 255, 100, 100)
            end
        end
    end
end

initializeData()

client.AllowListener("round_start")
client.AllowListener("round_end")
client.AllowListener("player_death")

callbacks.Register("FireGameEvent", "GH_EVENT", gameEventHandler)
callbacks.Register("CreateMove",    "GH_MOVE",  moveEventHandler)
callbacks.Register("Draw",          "GH_DRAW",  drawEventHandler)

addNotification("[Grenade Helper V6] Loaded! (v1.1b)", 0, 255, 100)
addNotification("Numpad 1 = Save | Numpad 2 = Delete", 200, 200, 255)
addNotification("F = Jump Throw | ALT = Walk To Nearest", 200, 200, 255)
