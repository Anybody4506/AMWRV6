-- Grenade Helper V6
-- Credits:
--   ShadyRetard - Grenade Helper base
--   Carter Poe & Agentsix1 - V6 API understanding
--   Ginette - Script Fix & Reconstruction with AI

--------------------------------
-- Constants & State
--------------------------------
local THROW_RADIUS = 20
local DRAW_MARKER_DISTANCE = 100
local GH_ACTION_COOLDOWN = 30
local GRENADE_SAVE_FILE_NAME = "grenade_helper_data.dat"

local maps = {}
local current_map_name = nil
local last_action = globals.TickCount()
local jumpthrow_stage = 0
local jumpthrow_tick = 0
local screen_w, screen_h = 0, 0

-- Notification system
local notifications = {}
local NOTIF_DURATION = 180

--------------------------------
-- Type definitions
--------------------------------
local POSITION_TYPES = {"stand", "jump", "run", "crouch", "jump + crouch", "run + jump"}
local LAUNCH_TYPES = {"left", "right", "left + right"}

local GRENADE_IDS = {
    [43] = "flashbang",
    [44] = "hegrenade",
    [45] = "smokegrenade",
    [46] = "molotovgrenade",
    [47] = "decoy",
    [48] = "molotovgrenade",
}

--------------------------------
-- UI : VISUALS -> Local -> Groupbox
--------------------------------
local visuals_ref = gui.Reference("VISUALS", "Local")
local GH_GB = gui.Groupbox(visuals_ref, "Grenade Helper", 15, 0, 352, 0)

local GH_ENABLED = gui.Checkbox(GH_GB, "gh.enabled", "Enable Grenade Helper", true)
local GH_NAME_EB = gui.Editbox(GH_GB, "gh.name", "Throw Name")
local GH_POSITION_CB = gui.Combobox(GH_GB, "gh.position", "Position Type", unpack(POSITION_TYPES))
local GH_LAUNCH_CB = gui.Combobox(GH_GB, "gh.launch", "Launch Type", unpack(LAUNCH_TYPES))

local GH_ENABLE_KB = gui.Checkbox(GH_GB, "gh.kb.enabled", "Enable Keybinds", true)
local GH_SAVE_KB = gui.Keybox(GH_GB, "gh.kb.save", "Capture & Save", 97)
local GH_DEL_KB = gui.Keybox(GH_GB, "gh.kb.del", "Delete Nearest", 98)
local GH_JUMPTHROW_KB = gui.Keybox(GH_GB, "gh.kb.jumpthrow", "Jump Throw", 70)

local GH_VISUALS_DISTANCE_SL = gui.Slider(GH_GB, "gh.visuals.distance", "Display Distance", 800, 1, 9999)
local CP_TEXT_NAME = gui.ColorPicker(GH_GB, "gh.color.name", "Throw Name", 255, 255, 0, 255)
local CP_TEXT_POS = gui.ColorPicker(GH_GB, "gh.color.position", "Position Type", 150, 255, 150, 200)
local CP_TEXT_LAUNCH = gui.ColorPicker(GH_GB, "gh.color.launch", "Launch Type", 255, 150, 150, 200)
local CP_LINE = gui.ColorPicker(GH_GB, "gh.color.line", "Direction Line", 0, 255, 255, 220)
local CP_BOX = gui.ColorPicker(GH_GB, "gh.color.box", "Box Color", 0, 0, 0, 255)
local CP_FINAL = gui.ColorPicker(GH_GB, "gh.color.final", "Active Box", 0, 255, 100, 255)

-- Create file if doesn't exist
local init_file = file.Open(GRENADE_SAVE_FILE_NAME, "a")
if init_file then init_file:Close() end

--------------------------------
-- Notification System
--------------------------------
local function addNotification(text, r, g, b)
    table.insert(notifications, {
        text = text,
        r = r or 255,
        g = g or 255,
        b = b or 255,
        expire = globals.TickCount() + NOTIF_DURATION
    })
end

local function drawNotifications()
    local center_x = screen_w / 2
    local y_offset = screen_h * 0.7
    
    for i = #notifications, 1, -1 do
        local notif = notifications[i]
        if globals.TickCount() > notif.expire then
            table.remove(notifications, i)
        else
            local alpha = math.min(255, (notif.expire - globals.TickCount()) * 2)
            local tw, th = draw.GetTextSize(notif.text)
            
            draw.Color(0, 0, 0, alpha * 0.7)
            draw.FilledRect(center_x - tw/2 - 10, y_offset - 5, center_x + tw/2 + 10, y_offset + th + 5)
            
            draw.Color(notif.r, notif.g, notif.b, alpha)
            draw.Text(center_x - tw/2, y_offset, notif.text)
            
            y_offset = y_offset + th + 15
        end
    end
end

--------------------------------
-- Utils
--------------------------------
local function clamp(x, a, b)
    return math.max(a, math.min(b, x))
end

local function canon_mapname(s)
    if not s or s == "" then return "" end
    s = tostring(s):lower()
    s = s:gsub("\\","/"):gsub("^maps/",""):gsub("%.bsp$",""):gsub("%.vpk$",""):gsub("%.zip$",""):gsub("^.*/","")
    return s
end

local function normalize_angles(pitch, yaw)
    pitch = clamp(pitch, -89, 89)
    yaw = (yaw + 180) % 360 - 180
    return pitch, yaw
end

local function angles_to_forward(pitch, yaw)
    local rp, ry = math.rad(pitch), math.rad(yaw)
    local cp, sp = math.cos(rp), math.sin(rp)
    local cy, sy = math.cos(ry), math.sin(ry)
    return Vector3(cp*cy, cp*sy, -sp)
end

local function to_num2(angles)
    if not angles then return 0, 0 end
    local pitch, yaw = 0, 0
    
    if type(angles) == "userdata" then
        pitch, yaw = tonumber(angles.pitch) or 0, tonumber(angles.yaw) or 0
    elseif type(angles) == "table" then
        pitch = tonumber(angles.pitch or angles.x or angles[1] or 0) or 0
        yaw = tonumber(angles.yaw or angles.y or angles[2] or 0) or 0
    end
    
    return normalize_angles(pitch, yaw)
end

local function W2S(pos)
    if not pos then return nil, nil end
    
    if type(pos) == "userdata" then
        return client.WorldToScreen(pos)
    end
    
    if type(pos) == "table" then
        local v = Vector3(pos.x or pos[1] or 0, pos.y or pos[2] or 0, pos.z or pos[3] or 0)
        return client.WorldToScreen(v)
    end
    
    return nil, nil
end

local function get_origin_v3(ent)
    if not ent then return Vector3(0, 0, 0) end
    
    local origin = ent:GetAbsOrigin()
    if type(origin) == "userdata" then return origin end
    if type(origin) == "table" then
        return Vector3(origin.x or origin[1] or 0, origin.y or origin[2] or 0, origin.z or origin[3] or 0)
    end
    
    return Vector3(0, 0, 0)
end

local function dist3v(a, b)
    if not a or not b then return 0 end
    
    local ax, ay, az, bx, by, bz
    
    if type(a) == "userdata" then
        ax, ay, az = a.x, a.y, a.z
    elseif type(a) == "table" then
        ax, ay, az = a.x or a[1] or 0, a.y or a[2] or 0, a.z or a[3] or 0
    else
        return 0
    end
    
    if type(b) == "userdata" then
        bx, by, bz = b.x, b.y, b.z
    elseif type(b) == "table" then
        bx, by, bz = b.x or b[1] or 0, b.y or b[2] or 0, b.z or b[3] or 0
    else
        return 0
    end
    
    local dx, dy, dz = ax - bx, ay - by, az - bz
    return math.sqrt(dx*dx + dy*dy + dz*dz)
end

--------------------------------
-- Grenade Detection
--------------------------------
local function GetActiveGrenadeName()
    local me = entities.GetLocalPlayer()
    if not me or (me.IsAlive and not me:IsAlive()) then return nil end
    
    local id = me.GetWeaponID and me:GetWeaponID() or nil
    return id and GRENADE_IDS[id] or nil
end

--------------------------------
-- Geometry
--------------------------------
local function GetThrowPositionV3(pos, pitch, yaw, z_offset)
    local fwd = angles_to_forward(pitch, yaw)
    local base = Vector3(pos.x, pos.y, pos.z + z_offset)
    return Vector3(
        base.x + fwd.x * DRAW_MARKER_DISTANCE,
        base.y + fwd.y * DRAW_MARKER_DISTANCE,
        base.z + fwd.z * DRAW_MARKER_DISTANCE
    )
end

--------------------------------
-- Persistence
--------------------------------
local function parseStringifiedTable(s)
    local new_map = {}
    if not s or s == "" then return new_map end
    
    for line in string.gmatch(s, "([^\n]*)\n?") do
        if line ~= "" then
            local p = {}
            for seg in string.gmatch(line, "([^,]*)") do
                if seg ~= "" then p[#p + 1] = seg end
            end
            
            local key = canon_mapname(p[1])
            
            if key ~= "" and #p >= 10 then
                new_map[key] = new_map[key] or {}
                table.insert(new_map[key], {
                    name = p[2],
                    position = p[3],
                    launch = p[4],
                    nade = p[5],
                    pos = {
                        x = tonumber(p[6]) or 0,
                        y = tonumber(p[7]) or 0,
                        z = tonumber(p[8]) or 0
                    },
                    ax = tonumber(p[9]) or 0,
                    ay = tonumber(p[10]) or 0
                })
            end
        end
    end
    
    return new_map
end

local function convertTableToDataString(obj)
    local out = {}
    
    for map_name, map in pairs(obj or {}) do
        for _, t in ipairs(map) do
            out[#out + 1] = table.concat({
                map_name,
                t.name or "",
                t.position or "stand",
                t.launch or "left",
                t.nade or "auto",
                tostring(t.pos.x or 0),
                tostring(t.pos.y or 0),
                tostring(t.pos.z or 0),
                tostring(t.ax or 0),
                tostring(t.ay or 0)
            }, ",")
        end
    end
    
    return (#out > 0) and (table.concat(out, "\n") .. "\n") or ""
end

local function loadData()
    local f = file.Open(GRENADE_SAVE_FILE_NAME, "r")
    if not f then return end
    
    local data = f:Read()
    f:Close()
    
    if data and data ~= "" then
        maps = parseStringifiedTable(data)
    end
end

local function saveData()
    local f = file.Open(GRENADE_SAVE_FILE_NAME, "w")
    if not f then return end
    
    f:Write(convertTableToDataString(maps))
    f:Close()
end

--------------------------------
-- Selection & Rendering
--------------------------------
local function getActiveThrows(map, me, nade_name)
    local list, in_range = {}, {}
    if not map then return {}, false end
    
    local mpos = get_origin_v3(me)
    
    for i = 1, #map do
        local t = map[i]
        local should_show = t.nade == nade_name or t.nade == "auto"
        
        if should_show then
            local tpos = Vector3(t.pos.x, t.pos.y, t.pos.z)
            local d = dist3v(mpos, tpos)
            t.distance = d
            
            if d < THROW_RADIUS then
                in_range[#in_range + 1] = t
            else
                list[#list + 1] = t
            end
        end
    end
    
    return #in_range > 0 and in_range or list, #in_range > 0
end

local function getClosestThrow(map, me)
    if not map or #map == 0 then return nil, math.huge end
    
    local mpos = get_origin_v3(me)
    local best, bestDist = nil, math.huge
    
    for i = 1, #map do
        local t = map[i]
        local d = dist3v(mpos, Vector3(t.pos.x, t.pos.y, t.pos.z))
        if d < bestDist then
            best, bestDist = t, d
        end
    end
    
    return best, bestDist
end

local function drawText(x, y, text, r, g, b, a)
    draw.Color(0, 0, 0, a)
    for dx = -1, 1 do
        for dy = -1, 1 do
            if dx ~= 0 or dy ~= 0 then
                draw.Text(x + dx, y + dy, text)
            end
        end
    end
    draw.Color(r, g, b, a)
    draw.Text(x, y, text)
end

local function showNadeThrows()
    local me = entities.GetLocalPlayer()
    if not me then return end
    
    local weapon_name = GetActiveGrenadeName()
    if not weapon_name then return end
    
    local current_throws = maps[current_map_name]
    if not current_throws then return end
    
    local list, within = getActiveThrows(current_throws, me, weapon_name)
    if not list then return end
    
    local nr, ng, nb, na = CP_TEXT_NAME:GetValue()
    local pr, pg, pb, pa = CP_TEXT_POS:GetValue()
    local lr, lg, lb, la = CP_TEXT_LAUNCH:GetValue()
    local lnr, lng, lnb, lna = CP_LINE:GetValue()
    local br, bg, bb, ba = CP_BOX:GetValue()
    local fr, fg, fb, fa = CP_FINAL:GetValue()
    
    local max_distance = GH_VISUALS_DISTANCE_SL:GetValue()
    
    for i = 1, #list do
        local t = list[i]
        
        if t.distance and t.distance > max_distance then
            goto continue
        end
        
        local pos = Vector3(t.pos.x, t.pos.y, t.pos.z)
        local is_crouching = t.position:find("crouch") ~= nil
        local zoff = is_crouching and 46 or 64
        local axn, ayn = to_num2({pitch = t.ax, yaw = t.ay})
        local fwd = angles_to_forward(axn, ayn)
        
        local ahead = Vector3(pos.x + fwd.x * 10, pos.y + fwd.y * 10, pos.z)
        local s1x, s1y = W2S(ahead)
        
        if within then
            local target = GetThrowPositionV3(pos, axn, ayn, zoff)
            local dx, dy = W2S(target)
            
            if dx and dy then
                draw.Color(fr, fg, fb, fa)
                draw.OutlinedRect(dx - 8, dy - 8, dx + 8, dy + 8)
                draw.Color(lnr, lng, lnb, lna)
                draw.Line(dx, dy, screen_w/2, screen_h/2)
                
                local pos_text = "[" .. t.position .. "]"
                local ptw, pth = draw.GetTextSize(pos_text)
                drawText(dx - ptw/2, dy + 12, pos_text, pr, pg, pb, pa)
                
                local launch_text = "[" .. t.launch .. "]"
                local ltw, lth = draw.GetTextSize(launch_text)
                drawText(dx - ltw/2, dy + 12 + pth + 2, launch_text, lr, lg, lb, la)
            end
        end
        
        local cx, cy = W2S(pos)
        if not cx or not cy then goto continue end
        
        local half = THROW_RADIUS / 2
        local ul = Vector3(pos.x - half, pos.y - half, pos.z)
        local bl = Vector3(pos.x - half, pos.y + half, pos.z)
        local ur = Vector3(pos.x + half, pos.y - half, pos.z)
        local br = Vector3(pos.x + half, pos.y + half, pos.z)
        
        local ulx, uly = W2S(ul)
        local blx, bly = W2S(bl)
        local urx, ury = W2S(ur)
        local brx, bry = W2S(br)
        
        local alpha = max_distance > 0 and clamp((1 - t.distance / max_distance) * 255, 50, 255) or 255
        
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
            drawText(cx - tw/2, cy - th - 4, t.name, nr, ng, nb, alpha)
        end
        
        if s1x and s1y then
            draw.Color(lnr, lng, lnb, lna)
            draw.Line(cx, cy, s1x, s1y)
        end
        
        ::continue::
    end
end

--------------------------------
-- Actions
--------------------------------
local function doAdd(cmd)
    local me = entities.GetLocalPlayer()
    if not me or not me:IsAlive() then
        addNotification("[GH] Player not alive", 255, 100, 100)
        return
    end
    
    if not current_map_name or current_map_name == "" then
        addNotification("[GH] No map loaded", 255, 100, 100)
        return
    end
    
    maps[current_map_name] = maps[current_map_name] or {}
    
    local name = tostring(GH_NAME_EB:GetValue() or ""):gsub("^%s+",""):gsub("%s+$","")
    if name == "" then
        addNotification("[GH] Name is empty", 255, 100, 100)
        return
    end
    
    local position = POSITION_TYPES[GH_POSITION_CB:GetValue() + 1] or "stand"
    local launch = LAUNCH_TYPES[GH_LAUNCH_CB:GetValue() + 1] or "left"
    local mpos = get_origin_v3(me)
    
    local ax, ay = 0, 0
    if engine.GetViewAngles then
        ax, ay = to_num2(engine.GetViewAngles())
    elseif cmd and cmd.viewangles then
        ax, ay = to_num2(cmd.viewangles)
    end
    
    local nade = GetActiveGrenadeName() or "auto"
    
    local entry = {
        name = name,
        position = position,
        launch = launch,
        nade = nade,
        pos = {x = mpos.x, y = mpos.y, z = mpos.z},
        ax = ax,
        ay = ay
    }
    
    table.insert(maps[current_map_name], entry)
    saveData()
    
    addNotification("[GH] Saved: " .. name .. " [" .. position .. "] [" .. launch .. "]", 0, 255, 100)
end

local function doDel(me)
    if not current_map_name or not maps[current_map_name] then
        addNotification("[GH] No throws on this map", 255, 100, 100)
        return
    end
    
    local best = getClosestThrow(maps[current_map_name], me)
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
-- Event Handler
--------------------------------
local function gameEventHandler(event)
    if not GH_ENABLED:GetValue() then return end
    
    local event_name = event:GetName()
    
    if event_name == "round_start" then
        -- Reset jumpthrow on round start
        jumpthrow_stage = 0
    end
end

--------------------------------
-- Callbacks
--------------------------------
local function drawEventHandler()
    screen_w, screen_h = draw.GetScreenSize()
    
    if not GH_ENABLED:GetValue() then return end
    
    local active_map = engine.GetMapName()
    if not active_map or active_map == "" then return end
    
    if not maps then maps = {} end
    
    local map_key = canon_mapname(active_map)
    if map_key == "" then return end
    
    if current_map_name ~= map_key then
        current_map_name = map_key
        loadData()
    end
    
    if not maps[current_map_name] then
        maps[current_map_name] = {}
    end
    
    showNadeThrows()
    drawNotifications()
end

local function moveEventHandler(cmd)
    if not GH_ENABLED:GetValue() then return end
    
    local me = entities.GetLocalPlayer()
    if not me or not me:IsAlive() then return end
    
    -- Ensure map is loaded
    if not current_map_name or not maps or not maps[current_map_name] then
        return
    end
    
    -- Tick counter overflow protection
    if last_action and last_action > globals.TickCount() then
        last_action = globals.TickCount()
    end
    
    -- Jump throw
    if GH_JUMPTHROW_KB:GetValue() ~= 0 then
        if input.IsButtonPressed(GH_JUMPTHROW_KB:GetValue()) and jumpthrow_stage == 0 then
            jumpthrow_stage = 1
            jumpthrow_tick = globals.TickCount()
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
    
    local add_key = GH_SAVE_KB:GetValue()
    local del_key = GH_DEL_KB:GetValue()
    
    if add_key == 0 and del_key == 0 then return end
    
    if add_key ~= 0 and input.IsButtonDown(add_key) and globals.TickCount() - last_action > GH_ACTION_COOLDOWN then
        last_action = globals.TickCount()
        doAdd(cmd)
    end
    
    if del_key ~= 0 and input.IsButtonDown(del_key) and globals.TickCount() - last_action > GH_ACTION_COOLDOWN then
        last_action = globals.TickCount()
        doDel(me)
    end
end

-- Load initial data
loadData()

-- Register callbacks
callbacks.Register("FireGameEvent", "GH_EVENT", gameEventHandler)
callbacks.Register("CreateMove", "GH_MOVE", moveEventHandler)
callbacks.Register("Draw", "GH_DRAW", drawEventHandler)

print("========================================")
print("[Grenade Helper V6] Loaded!")
print("========================================")
print("Credits:")
print("  - ShadyRetard (Grenade Helper base)")
print("  - Carter Poe & Agentsix1 (V6 API)")
print("  - Ginette (Fix & Reconstruction with AI)")
print("========================================")
print("numpad 1 = Save | numpad 2 = Delete | F = Jumpthrow")
print("========================================")