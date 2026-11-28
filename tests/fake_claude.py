#!/usr/bin/env python3
"""A stand-in for `claude -p`, for tests: started as PW_CLAUDE, it talks to the MCP server the
command it was started by configured (pw mcp, with that server's environment), and calls its
tools as told by the JSON file FAKE_CLAUDE names:

  {"read":  {"<place>": {"object": "...", "quote": "..."} | {"why": "..."}},   a blind reader
   "edit":  {"<place>": "<new text>" | {"cannot": "why"}},                     an editing agent
   "find":  [["<tool>", {arguments}], ...],                                     a searching agent
   "log":   "<file>"}                                                           where each prompt is appended

It prints what `claude -p --output-format json` prints at the end of a session.
"""
import json
import os
import re
import subprocess
import sys


def main(argv):
    prompt = argv[argv.index("-p") + 1]
    cfg = json.load(open(argv[argv.index("--mcp-config") + 1]))["mcpServers"]["pw"]
    told = json.load(open(os.environ["FAKE_CLAUDE"]))
    if told.get("log"):
        with open(told["log"], "a") as fh:
            fh.write(json.dumps({"prompt": prompt, "env": cfg.get("env", {})}) + "\n")
    server = subprocess.Popen([cfg["command"], *cfg["args"]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                              env={**os.environ, **cfg.get("env", {})})
    n = 0

    def call(method, params):
        nonlocal n
        n += 1
        server.stdin.write(json.dumps({"jsonrpc": "2.0", "id": n, "method": method, "params": params}) + "\n")
        server.stdin.flush()
        return json.loads(server.stdout.readline())

    call("initialize", {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": "fake", "version": "0"}})
    tools = cfg.get("env", {}).get("PW_TOOLS", "read")
    if tools == "read":
        for h, place in re.findall(r"^=== h: (\S+)   place: (.+)$", prompt, re.M):
            said = told.get("read", {}).get(place)
            if said is None:
                continue
            if "why" in said:
                call("tools/call", {"name": "not_stated", "arguments": {"h": h, "place": place, "why": said["why"]}})
            else:
                call("tools/call", {"name": "read_place", "arguments": {"h": h, "place": place, **said}})
    elif tools == "edit":
        for i, at in re.findall(r"^=== id: (\d+)   (.+)$", prompt, re.M):
            said = told.get("edit", {}).get(at)
            if isinstance(said, dict):
                call("tools/call", {"name": "cannot", "arguments": {"id": int(i), "why": said["cannot"]}})
            elif said is not None:
                call("tools/call", {"name": "rewrite", "arguments": {"id": int(i), "text": said}})
    else:
        for name, args in told.get("find", []):
            call("tools/call", {"name": name, "arguments": args})
    server.stdin.close()
    server.wait()
    print(json.dumps({"type": "result", "subtype": "success", "is_error": False, "num_turns": 1, "total_cost_usd": 0.0, "result": "done"}))


if __name__ == "__main__":
    main(sys.argv[1:])
