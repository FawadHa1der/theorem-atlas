#!/usr/bin/env python3
"""
Dual-Stack (IPv6 ::1 + IPv4 127.0.0.1) Multi-Threaded Observatory Server on Port 4190.
Serves the unified Chrome & Safari 8-shard Observatory (`observatory/index.html`) with
concurrent chunk streaming and BrokenPipe suppression on speculative socket closes.
"""
import http.server
import mimetypes
import os
import socket
from pathlib import Path

OBS_DIR = Path(__file__).resolve().parent.parent
PORT = int(os.environ.get("PORT", "4190"))

mimetypes.add_type("application/javascript; charset=utf-8", ".js")
mimetypes.add_type("application/javascript; charset=utf-8", ".mjs")
mimetypes.add_type("text/css; charset=utf-8", ".css")
mimetypes.add_type("text/html; charset=utf-8", ".html")
mimetypes.add_type("application/json; charset=utf-8", ".json")


class ObservatoryHandler(http.server.SimpleHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(OBS_DIR), **kwargs)

    def end_headers(self):
        if "/chunks/" in self.path:
            self.send_header("Cache-Control", "public, max-age=3600")
        else:
            self.send_header("Cache-Control", "no-cache")
        self.send_header("Access-Control-Allow-Origin", "*")
        super().end_headers()

    def log_message(self, fmt, *args):
        if os.environ.get("QUIET_SERVER") != "1":
            super().log_message(fmt, *args)

    def copyfile(self, source, outputfile):
        try:
            super().copyfile(source, outputfile)
        except (BrokenPipeError, ConnectionResetError):
            pass


class DualStackThreadingHTTPServer(http.server.ThreadingHTTPServer):
    address_family = socket.AF_INET6
    allow_reuse_address = True

    def server_bind(self):
        try:
            self.socket.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 0)
        except Exception:
            pass
        super().server_bind()


def main():
    try:
        httpd = DualStackThreadingHTTPServer(("::", PORT), ObservatoryHandler)
        bind_desc = f"dual-stack IPv6 [::1]:{PORT} + IPv4 127.0.0.1:{PORT}"
    except OSError:
        http.server.ThreadingHTTPServer.allow_reuse_address = True
        httpd = http.server.ThreadingHTTPServer(("127.0.0.1", PORT), ObservatoryHandler)
        bind_desc = f"IPv4 127.0.0.1:{PORT}"

    print(f"Common Ground Observatory (V181 Unified Chrome & Safari) serving {OBS_DIR} on {bind_desc}")
    print(f"  • Unified Observatory: http://localhost:{PORT}/")
    print(f"  • Universe Sources:    http://localhost:{PORT}/universe/sources/")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down server.")
        httpd.server_close()


if __name__ == "__main__":
    main()
