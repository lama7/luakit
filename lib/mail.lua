
local imaplib = require("imap4")
local chrome = require("chrome")
local util = require("lousy.util")
local join = util.table.join

local mail = {}

local objects = {}
local mailo

local function entry()    return widget{type="entry"}    end
local function eventbox() return widget{type="eventbox"} end
local function hbox()     return widget{type="hbox"}     end
local function label()    return widget{type="label"}    end
local function notebook() return widget{type="notebook"} end
local function vbox()     return widget{type="vbox"}     end
local term       = globals.term   or "xterm"
local editor     = globals.editor or (os.getenv("EDITOR") or "vim")
local editor_cmd = string.format("%s -e %s", term, editor)


mail_page = "luakit://mail/"

function mail.__index(t,k)
    return mail[k]
end

function mail.__chk_result(self, r)
    if r:getTaggedResult() ~= 'OK' then
        error(r:getTaggedContents())
        return nil
    end
    return r
end

function mail.__logon(self)
    local r = self:__chk_result(self.imap:capability())
    self.capability = r:getUntaggedContent('CAPABILITY')[1]
    if not self.capability:find('IMAP4rev1') then
       self.imap:shutdown()
       return nil
    elseif self.account.ssl_opts.protocol == 'tlsv1' and
           self.capability:find('STARTTLS') then
       self:__chk_result(self.imap:starttls())
    end
    return self:__chk_result(self.imap:login(self.account.user, self.account.pw))
end

function mail.checkmail(self)
    -- send the imap STATUS command pipelined
    local result_str = "Checking for new mail on "..account.name.."\n"
    local r = self:__chk_result(self.imap:LIST('""', '*'))  -- list of all mailboxes
    local firsttag
    local lasttag
    self.imap:startPipeline()
    for i,v in ipairs(r:getUntaggedContent('LIST')) do
        if not v:find('%\Noselect') then
            local mb = v:match([[.* %"(.-)%"$]])
            lasttag = self.imap:STATUS(mb, 'UNSEEN')
            if i == 1 then firsttag = lasttag end
        end
    end
    self.imap:endPipeline()

    -- now read the responses, because we're using coroutines, we can't use
    -- the method as an iterator, but we CAN get the response function and then
    -- read the responses in a loop
    local responses = self.imap:readResponses(lasttag)
    while true do
        r = responses()
        if not r then break end
        local mbstat = r:getUntaggedContent('STATUS')[1] 
        local mb, newmail = mbstat:match([[^%"(.-)%"%s+%(UNSEEN (%d+)%)]])
        if newmail ~= '0' then
            result_str = result_str..string.format("\t%s:\t%u\n", mb, newmail)
        end
    end

    -- close the connection and return the results
    self.imap:shutdown()
    return result_str
end

function mail.getMailboxes(self)
--[[
    Builds a tree of mailboxes out of tables, like so:
        { 'foo' = 1,
          'bar' = 1,
          'baz' = { {true, '.' },
                    'blurdy-bloop' = 1,
                    'blah' = 1,
                    'fruit' = { { false, '.' },
                                'oranges' = 1,
                                'pears' = 1,
                              }
                  },
          'spam' = 1,
          'work' = { {false, '.'},
                     'todo' = 1,
                     'time' = 1,
                     'contacts' = 1,
                   }
          'INBOX' = 1
        }
    So, mailbox names are keys for fast lookup purposes.  For mailboxes with
    child mailboxes, the first entry is always a table with 'true' or 'false' to
    indicate weather it has messages in addition to children.  The second entry
    in the table is the hierarchy delimiter between mailbox name.

    The resulting tree is placed in 'mbtree'.
--]]
    function getmbnames(mb_name, mb_tbl, hd)
    -- store all selectable mailboxes as a key in a table for fast lookup
    -- if mailbox has sub-mailboxes, then store them with a table as the
    -- the value whose first entry is a table with 'true' if the top-level is
    -- selectable and 'false' if it isn't, followed by the hierarchy delimiter
         -- check if we're processing child mailboxes
        if hd then mb_name = mb_name..hd..'%' end
        local r = self:__chk_result(self.imap:LIST('""', mb_name))
        local mblist = r:getUntaggedContent('LIST')
        if mblist then
            for i,v in ipairs(mblist) do
                local fname = v:match([[.* %"(.-)%"$]])
                if hd then
                    local s, e = fname:find('%'..hd)
                    fname = fname:sub(e+1)
                end
                if not v:find('%\Noselect') then
                    if not mb_tbl[fname] then
                        mb_tbl[fname] = 1
                    end
                end
                if v:find('%\HasChildren') then
                    local h_delim = v:match([[%(.*%)%s%"(.)%"%s.*]])
                    if mb_tbl[fname] then
                        mb_tbl[fname] = { { true, h_delim }, }
                    else
                        mb_tbl[fname] = { { false, h_delim }, }
                    end
                end 
              end
        end
    end

    function buildmbtree(tbl, mb_hierarchy, hierarchy_delim)
        getmbnames(mb_hierarchy, tbl, hierarchy_delim)
        for mb, v in pairs(tbl) do
            if type(v) == 'table' and type(mb) == 'string' then
                buildmbtree(v, mb, v[1][2])
            end
        end
    end

    -- recursively build mb tree
    self.mbtree = self.mbtree or {}
    buildmbtree(self.mbtree, '%')
end

function mail.setWorkingMB(self, mb_name)
--[[
    Creates a __workingMB table if it doesn't already exist and then pushes
    mailbox names onto the table for use to keep track of navigating mailbox
    hierarchies.
--]]
    if not self.__workingMB then self.__workingMB = {} end

    if mb_name then
        table.insert(self.__workingMB, mb_name)
    elseif #self.__workingMB ~= 0 then
        table.remove(self.__workingMB)
    end
end

function mail.getWorkingMB(self)
--[[
    Returns the table for the current working mailbox as selected through
    the menu widget.  If self.mbtree does not exist, then it builds it and 
    returns the top-level tree.
--]]

    -- make sure we have a tree to work with
    if not self.mbtree then self:getMailboxes() end

    -- simplest case, no __workingMB: just return top level
    if not self.__workingMB then return self.mbtree end

    -- now, we need to go through the hierarchy as dictated by __workingMB
    -- note, in the following we assume each name in __workingMB corresponds to
    -- a valid entry point to child mailboxes
    local tree_ptr = self.mbtree
    for _, mb in ipairs(self.__workingMB) do
        tree_ptr = tree_ptr[mb]
    end
    return tree_ptr
end

function mail.workingMB2str(self)
--[[
    Turns __workingMB into a full IMAP mailbox name basically by concatenating
    all names in the table along with the appropriate hierarchy delimiters as
    defined in the mbtree table
--]]
    local mbstr = ''
    local tree_ptr = self.mbtree
    for _,mb in ipairs(self.__workingMB) do
        mbstr = mbstr..mb
        tree_ptr = tree_ptr[mb]
        -- grab hierarchy delimiter from table entry
        if type(tree_ptr) == 'table' then
            mbstr = mbstr..tree_ptr[1][2]
        end
    end
    -- did we end on a mb that's an entry to a lower hierarcy? 
    -- is it selectable?  if not, return nil, if so, be sure to strip the
    -- delimter
    if type(tree_ptr) == 'table' then
        if tree_ptr[1][1] == false then 
            return nil
        end
        mbstr = mbstr:sub(1,-2)
    end
    return mbstr
end

function mail.retrieveMsgSummaries(self)
--[[
    Retrieves a date, from and sender for all messages in the mailbox defined by
    __workingMB.  Puts them in a table called 'mail_summary'.
--]]
--    self.imap.threaded = true
    local mb = self:workingMB2str()
    if not mb then return end
    self.mail_summary= {}
    local r = self:__chk_result(self.imap:SELECT(mb))
    if not r then return end

    local mailcount = r:getUntaggedContent('EXISTS')[1]

    -- now retrieve the some minimal info for all the messages here
    local FETCH_SUMMARY = 'UID BODY\[HEADER\.FIELDS (DATE FROM SUBJECT)\]'
    r = self:__chk_result(self.imap:FETCH('1:'..mailcount, FETCH_SUMMARY))
    if r then
        for _, t in ipairs(r:getUntaggedContent('FETCH')) do
            local uid = t[1]:match("%(UID (%d+).*")
            local subject = util.escape(t[1]:match(".*Subject:%s*(.-)\r"))
            local from = util.escape(t[1]:match(".*From:%s*(.-)\r"))
            local date = t[1]:match(".*Date:%s*(.-)\r")
            table.insert(self.mail_summary, {date, from, subject, uid})
        end
    end
    return 1
end

function mail.retrieveMsg(self, uid)
--[[
    Current state, IMAP wise, we've selected a mailbox and already fetched some
    message summary info.  As for luakit, we're in "mailmessages" mode- not sure
    that's really relevant though.

    Basically, we've got to fetch the body of a message and return it somehow so
    the mode can display the message.
--]]
    FETCH_SUMMARY = "RFC822.TEXT"
    local msg = ''
    r = self:__chk_result(self.imap:UID('FETCH', uid, FETCH_SUMMARY))
    if r then
        msg = r:getUntaggedContent('FETCH')[1][1]
    else
        error("No message")
    end

   -- find text/html
--   self.currentmsg = msg:match("Content%-Type%: text/html.-(<.*>).*%-%-_Part.*")
--    self.currentmsg = msg
    self.currentmsg['html'] = msg:match("Content%-Type%: text/html.-(<.*>)")
    if self.currentmsg['html'] then return end
    if msg then
        self.currentmsg['plain'] = msg
        return
    end
    error("Can't display message... yet.")
end

function mail.destroy(self)
    self.imap:shutdown()
    self.account = nil
    self.mailboxes = nil
end

function mail.new(self, account_info)
    local o = {}
    setmetatable(o, self)

    o.account = account_info
    o.imap = imaplib.IMAP4:new(o.account.server, 
                               o.account.port,
                               o.account.ssl_opts)
    o.currentmsg = {}

    -- take care of the logging into the account
    if not o:__logon() then
        return nil
    end

    return o
end

function mail.edit(file)
    return luakit.spawn_sync(string.format("%s %q", editor_cmd, file))
end

function mail.select_recipients()
	ret,stdout,stderr = luakit.spawn_sync("sh -c \"echo 'user@example.com' | dmenu -p 'To:'\"")
	if string.len(stderr) > 0 then
		warn(stderr)
	end
	if ret ~= 0 then
		return nil
	end
	rcpt = trim5(stdout)
	warn ("debug. user choose rcpt: " .. rcpt)
	return rcpt
end

function trim5(s) -- see http://lua-users.org/wiki/StringTrim
	  return s:match'^%s*(.*%S)' or ''
end

--
--*************************************************************************** 
--
local function buildMailboxMenu()
    local rows = {{"Mailboxes", title = true}, }
    for mb, v in pairs(mailo:getWorkingMB()) do
      local row
      if type(v) == 'table' then
          if type(mb) == 'string' then
              -- first entry of table is another table with
              -- 'true' if mailbox is selectable or 'false' if not
              -- and a hierarchy delimiter
              if v[1][1] then
                  -- visual cue- + with no delimiter means mailbox
                  -- can contain mail and has child mailboxes
                  row = { " +"..mb }
              else
                  -- visual cue- + with delimiter means mailbox
                  -- has child mailboxes but no mail
                  -- NOTE: for now, regardless of the actual
                  -- delimiter used by the imap server, we'll
                  -- display a '/'
                  row = { " +"..mb..'/' }
              end
          end
      else
          row = { "  "..mb }
      end
      table.insert(rows, 2, row)
    end
    return rows
end

local function mbStrip(mb)
    if mb:sub(-1) == '/' then 
        mb = mb:sub(3,-2)
    else
        mb = mb:sub(3,-1)
    end

    return mb
end

new_mode("mail", 
         {
          leave = function(w)
                    mailo:setWorkingMB()
                    w.menu:hide() 
                  end,
          enter = function(w)
                    local rows = {{"Account", title = true},}
                    for name, account in pairs(accounts) do
                      table.insert(rows, 2, { "  "..name })
                    end
                    w.menu:build(rows)
                    w:notify("Use j/k to move, Enter to select", false)
                  end
         }
        )

new_mode("sendmail",
         {
          leave = function(w)
                    w.menu:hide()
                  end,
          enter = function(w)
                    local rows = {{"Account", title = true},}
                    for name, account in pairs(accounts) do
                      table.insert(rows, 2, { "  "..name })
                    end
                    w.menu:build(rows)
                    w:notify("Use j/k to move, Enter to select", false)
                  end
         }
        )

new_mode("mailbox", 
         {
          leave = function(w) 
                    mailo:setWorkingMB()
                    w.menu:hide() 
                  end,
          enter = function(w)
                    w.menu:build(buildMailboxMenu())
                    w:notify("Use j/k to move, Enter to select", false)
                  end
         }
        )

new_mode("mailmessages",
         {
          leave = function(w) 
                    mailo:setWorkingMB()
                    w.menu:hide()
                  end,
          enter = function(w)
                    local rows = {{ "Date", "Sender", "Subject", title = true }, }
                    for _, t in ipairs(mailo.mail_summary) do
                      table.insert(rows, 2, { t[1], t[2], t[3], uid=t[4] })
                    end
                    w.menu:build(rows)
                    w:notify("Use j/k to move, Enter to select", false)
                  end
         }
        )

chrome.add("mail/", 
           function(view, uri)
             if mailo.currentmsg['html'] then
                 view:load_string(mailo.currentmsg['html'], tostring(uri))
             elseif mailo.currentmsg['plain'] then
                 view:load_string('<pre>'..mailo.currentmsg['plain']..'<pre>',
                                  tostring(uri))
             end
           end
          )

local key = lousy.bind.key
add_binds("mail", join( {
                         key({}, 
                             "Return", 
                             function(w)
                               local row = w.menu:get()
                               local account = row[1]:sub(3)
                               mailo = objects[account]
                               if not mailo then
                                   mailo = mail:new(accounts[account])
                                   objects[account] = mailo
                               end
                               w:set_mode("mailbox")
                             end
                            ),
                        }, 
                        menu_binds
                      )
         )

add_binds("sendmail", join( {
                         key({},
                             "Return",
                             function(w)
                               local row = w.menu:get()
                               local account = row[1]:sub(3)
                               mailo = objects[account]
                               if not mailo then
                                   mailo = mail:new(accounts[account])
                                   objects[account] = mailo
                               end
			       rcpt = mail.select_recipients()
			       -- if user didn't enter any rcpt, or the program exited >0, abort
			       if not rcpt or string.len(rcpt) < 1 then
				       w:set_mode("command")
				       -- TODO: set status message: aborted
				end
				-- prepopulate mail with what we can figure out.
				fname = luakit.cache_dir .. "/compose_mail.TODO.randomstringhere"
				local f = assert(io.open(fname, "w"))
				f:write ("To: " .. rcpt .. "\n")
				f:write ("From: " .. mailo.account.sender.from .. "\n")
				f:write ("Subject: \n\n")
				f:close()
				-- open editor to edit/create a mail
				if mail.edit(fname) ~= 0 then
					error ("editor exited " .. ret .. ". Not sending any mail")
				else
					-- TODO: menu: are you sure you want to send this? yes/no/edit message
					info ("sending mail...")
					local fh = io.popen("cat " .. fname .. "| " .. mailo.account.sender.cmd .. " " .. rcpt)
					info ("sender output:")
					info(fh:read( "*a" ))
					fh:close()
					-- TODO copy to sent imap folder, if that folder exists. and if anything fails -> move to some retry-queue
				end
                             end
                            ),
                        },
                        menu_binds
                      )
         )

add_binds("mailbox", join( {
                            key({}, 
                                "Return", 
                                function(w)
                                  local row = w.menu:get()
                                  local mb = mbStrip(row[1])
                                  mailo:setWorkingMB(mb)
                                  if mailo:retrieveMsgSummaries(mb) then
                                      w:set_mode("mailmessages")
                                  else
                                      mailo:setWorkingMB()
                                  end
                                end
                               ),
                            key({},
                                "space",
                                function(w)
                                  local row = w.menu:get()
                                  local mb = row[1]
                                  -- we need to strip some of the visual stuff
                                  -- off the mb name
                                  -- set the parent mail box
                                  if mb:sub(2,2) ~= '+' then return end
                                  mb = mbStrip(mb)
                                  mailo:setWorkingMB(mb)
                                  w.menu:build(buildMailboxMenu())
                                end     
                               ),
                            key({},
                                "b",
                                function(w)
                                    mailo:setWorkingMB()
                                    w.menu:build(buildMailboxMenu())
                                end
                               ),
                           },
                           menu_binds
                          )
         )
 
add_binds("mailmessages", join( { key({}, 
                                      'b',
                                      function(w)
                                          mailo:setWorkingMB()
                                          w:set_mode("mailbox")
                                      end
                                     ),
                                  key({},
                                      "Return",
                                      function(w)
                                        local row = w.menu:get()
                                        mailo:retrieveMsg(row.uid)
                                        w:navigate(mail_page)
                                      end
                                     ),
                                 }, 
                                 menu_binds
                              )
         )

-- add to window methods
window.methods.mail = function(w)
                        if not accounts then
                            w:notify("No mail accounts setup.")
                        else
                            w:set_mode("mail")
                        end
                      end
window.methods.sendmail = function(w)
                        if not accounts then
                            w:notify("No mail accounts setup.")
                        else
                            w:set_mode("sendmail")
                        end
                      end

-- add the mail command
local cmd = lousy.bind.cmd
add_cmds({ cmd("mail", window.methods.mail), })
add_cmds({ cmd("sendmail", window.methods.sendmail), })
