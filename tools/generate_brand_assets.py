#!/usr/bin/env python3
import base64
import os
import re
import struct
import zlib


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "source")
TAGLINE = "An unofficial falling-block tribute"


def read_png_rgba(path):
    data = open(path, "rb").read()
    assert data[:8] == b"\x89PNG\r\n\x1a\n"
    pos = 8
    width = height = color_type = bit_depth = None
    raw = b""
    while pos < len(data):
        length = struct.unpack(">I", data[pos:pos + 4])[0]
        chunk_type = data[pos + 4:pos + 8]
        chunk = data[pos + 8:pos + 8 + length]
        pos += 12 + length
        if chunk_type == b"IHDR":
            width, height, bit_depth, color_type, _, _, _ = struct.unpack(">IIBBBBB", chunk)
        elif chunk_type == b"IDAT":
            raw += chunk
        elif chunk_type == b"IEND":
            break

    inflated = zlib.decompress(raw)
    channels = {0: 1, 2: 3, 4: 2, 6: 4}[color_type]
    bpp = channels
    stride = width * bpp
    rows = []
    prev = [0] * stride
    idx = 0
    for _ in range(height):
        filt = inflated[idx]
        idx += 1
        scan = list(inflated[idx:idx + stride])
        idx += stride
        out = [0] * stride
        for i, val in enumerate(scan):
            left = out[i - bpp] if i >= bpp else 0
            up = prev[i]
            up_left = prev[i - bpp] if i >= bpp else 0
            if filt == 0:
                recon = val
            elif filt == 1:
                recon = val + left
            elif filt == 2:
                recon = val + up
            elif filt == 3:
                recon = val + ((left + up) // 2)
            elif filt == 4:
                p = left + up - up_left
                pa, pb, pc = abs(p - left), abs(p - up), abs(p - up_left)
                pr = left if pa <= pb and pa <= pc else (up if pb <= pc else up_left)
                recon = val + pr
            else:
                raise ValueError(f"unsupported PNG filter {filt}")
            out[i] = recon & 0xff
        rows.append(out)
        prev = out

    pixels = []
    for row in rows:
        pix_row = []
        for x in range(width):
            off = x * channels
            if color_type == 6:
                r, g, b, a = row[off:off + 4]
            elif color_type == 2:
                r, g, b = row[off:off + 3]
                a = 255
            elif color_type == 4:
                r = g = b = row[off]
                a = row[off + 1]
            elif color_type == 0:
                r = g = b = row[off]
                a = 255
            else:
                raise ValueError(f"unsupported PNG color type {color_type}")
            pix_row.append((r, g, b, a))
        pixels.append(pix_row)
    return width, height, pixels


def write_png_1bit(path, width, height, pixels):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    scanlines = []
    row_bytes = (width + 7) // 8
    for y in range(height):
        row = bytearray([0])
        for byte_i in range(row_bytes):
            value = 0
            for bit in range(8):
                x = byte_i * 8 + bit
                white = 1 if x >= width or pixels[y][x] else 0
                value |= white << (7 - bit)
            row.append(value)
        scanlines.append(bytes(row))
    compressed = zlib.compress(b"".join(scanlines), 9)

    def chunk(kind, body):
        return struct.pack(">I", len(body)) + kind + body + struct.pack(">I", zlib.crc32(kind + body) & 0xffffffff)

    png = (
        b"\x89PNG\r\n\x1a\n"
        + chunk(b"IHDR", struct.pack(">IIBBBBB", width, height, 1, 0, 0, 0, 0))
        + chunk(b"IDAT", compressed)
        + chunk(b"IEND", b"")
    )
    open(path, "wb").write(png)


class Canvas:
    def __init__(self, w, h, white=True):
        self.w = w
        self.h = h
        self.px = [[white for _ in range(w)] for _ in range(h)]

    def set(self, x, y, white=False):
        if 0 <= x < self.w and 0 <= y < self.h:
            self.px[y][x] = white

    def rect(self, x, y, w, h, white=False, fill=True):
        if fill:
            for yy in range(y, y + h):
                for xx in range(x, x + w):
                    self.set(xx, yy, white)
        else:
            for xx in range(x, x + w):
                self.set(xx, y, white)
                self.set(xx, y + h - 1, white)
            for yy in range(y, y + h):
                self.set(x, yy, white)
                self.set(x + w - 1, yy, white)

    def line(self, x0, y0, x1, y1, white=False):
        dx = abs(x1 - x0)
        dy = -abs(y1 - y0)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx + dy
        while True:
            self.set(x0, y0, white)
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 >= dy:
                err += dy
                x0 += sx
            if e2 <= dx:
                err += dx
                y0 += sy

    def paste(self, other, x, y):
        for yy in range(other.h):
            for xx in range(other.w):
                self.set(x + xx, y + yy, other.px[yy][xx])


class Font:
    def __init__(self, fnt_path):
        text = open(fnt_path, "r").read()
        png_b64 = re.search(r"data=([A-Za-z0-9+/=]+)", text).group(1)
        tmp = os.path.join(ROOT, "tools", "_font_atlas.png")
        open(tmp, "wb").write(base64.b64decode(png_b64))
        self.atlas_w, self.atlas_h, rgba = read_png_rgba(tmp)
        os.remove(tmp)
        self.cell_w = int(re.search(r"^width=(\d+)", text, re.M).group(1))
        self.cell_h = int(re.search(r"^height=(\d+)", text, re.M).group(1))
        tracking = re.search(r"^tracking=(\d+)", text, re.M)
        self.tracking = int(tracking.group(1)) if tracking else 0
        self.cols = self.atlas_w // self.cell_w
        self.glyphs = {}
        after = text.split(f"height={self.cell_h}", 1)[1]
        for line in after.splitlines():
            line = line.strip()
            if not line or line.startswith("tracking="):
                continue
            if "\t" not in line:
                continue
            key, width = line.split("\t", 1)
            idx = len(self.glyphs)
            self.glyphs[key] = {
                "index": idx,
                "width": int(width),
            }
        self.bitmap = []
        for y in range(self.atlas_h):
            row = []
            for x in range(self.atlas_w):
                r, g, b, a = rgba[y][x]
                row.append(a > 64 and (r + g + b) < 600)
            self.bitmap.append(row)

    def measure(self, text, scale=1):
        total = 0
        for ch in text:
            key = "space" if ch == " " else ch
            glyph = self.glyphs.get(key)
            if glyph:
                total += glyph["width"] + self.tracking
        return max(0, total * scale)

    def draw(self, canvas, text, x, y, scale=1, white=False, align="left"):
        if align == "center":
            x -= self.measure(text, scale) // 2
        elif align == "right":
            x -= self.measure(text, scale)
        cursor = x
        for ch in text:
            key = "space" if ch == " " else ch
            glyph = self.glyphs.get(key)
            if not glyph:
                continue
            idx = glyph["index"]
            sx = (idx % self.cols) * self.cell_w
            sy = (idx // self.cols) * self.cell_h
            for gy in range(self.cell_h):
                for gx in range(glyph["width"]):
                    if self.bitmap[sy + gy][sx + gx]:
                        for yy in range(scale):
                            for xx in range(scale):
                                canvas.set(cursor + gx * scale + xx, y + gy * scale + yy, white)
            cursor += (glyph["width"] + self.tracking) * scale


TITLE = Font(os.path.join(SOURCE, "fonts", "full-circle.fnt"))
SMALL = Font(os.path.join(SOURCE, "fonts", "Supermini.fnt"))


PIECES = {
    "I": [(0, 1), (1, 1), (2, 1), (3, 1)],
    "O": [(0, 0), (1, 0), (0, 1), (1, 1)],
    "T": [(1, 0), (0, 1), (1, 1), (2, 1)],
    "S": [(1, 0), (2, 0), (0, 1), (1, 1)],
    "Z": [(0, 0), (1, 0), (1, 1), (2, 1)],
    "J": [(0, 0), (0, 1), (1, 1), (2, 1)],
    "L": [(2, 0), (0, 1), (1, 1), (2, 1)],
}


def block(c, x, y, size, phase=0):
    """Outlined block with "/" hatching. phase (0-3) slides the hatch one pixel
    per step, so consecutive phases animate as marching stripes."""
    c.rect(x, y, size, size, True, True)
    for k in range(-size, 2 * size, 4):
        off = k + (phase % 4)
        for t in range(size):
            px, py = off + t, size - 1 - t
            if 1 <= px <= size - 2 and 1 <= py <= size - 2:
                c.set(x + px, y + py, False)
    c.rect(x, y, size, size, False, False)


def piece(c, key, x, y, size, phase=0):
    for bx, by in PIECES[key]:
        block(c, x + bx * size, y + by * size, size, phase)


def ambient(c, count=70, exclude=()):
    for i in range(count):
        x = (i * 43 + 17) % c.w
        y = (i * 29 + 23) % c.h
        if any(x >= rx and x <= rx + rw and y >= ry and y <= ry + rh for rx, ry, rw, rh in exclude):
            continue
        mode = i % 5
        if mode == 0:
            c.rect(x, y, 3, 3, False, False)
        elif mode == 1:
            c.line(x, y, x + 7, y, False)
            c.line(x + 3, y - 3, x + 3, y + 3, False)
        elif mode == 2:
            c.rect(x, y, 2, 2, False, True)
        elif mode == 3:
            c.line(x, y, x + 5, y + 5, False)
        else:
            c.line(x, y + 3, x + 6, y + 3, False)


def title(c, text, y, scale):
    TITLE.draw(c, text, c.w // 2, y, scale, False, "center")


def draw_logo_scene(c, phase=0, compact=False):
    ambient(c, 90 if not compact else 38, exclude=[
        (50, 14, c.w - 100, 50),            # title
        (c.w // 2 - 78, 80, 156, 92),       # logo box
        (70, 176, c.w - 140, 22),           # tagline
    ])
    title(c, "IAINTRIS", 24 if not compact else 12, 2 if not compact else 1)
    if not compact:
        c.rect(c.w // 2 - 70, 88, 140, 76, False, False)
        piece(c, "S", c.w // 2 - 62, 102, 10, phase)
        piece(c, "T", c.w // 2 - 22, 102, 10, phase + 1)
        piece(c, "O", c.w // 2 + 30, 102, 10, phase)
        piece(c, "L", c.w // 2 - 62, 134, 10, phase + 1)
        piece(c, "I", c.w // 2 + 24, 132, 10, phase)
        SMALL.draw(c, TAGLINE, c.w // 2, 184, 1, False, "center")


def launcher_card(path, w, h, phase=0, pressed=False):
    c = Canvas(w, h, True)
    tag_w = SMALL.measure(TAGLINE)
    ambient(c, 70, exclude=[(52, 12, 246, 40), (94, 55, 162, 62), (w // 2 - tag_w // 2 - 12, 124, tag_w + 24, 24)])
    TITLE.draw(c, "IAINTRIS", w // 2, 20, 2, False, "center")
    c.rect(w // 2 - 58, 62, 116, 48, False, False)
    piece(c, "S", w // 2 - 44, 68, 8, phase)
    piece(c, "T", w // 2 - 12, 68, 8, phase + 1)
    piece(c, "O", w // 2 + 30, 68, 8, phase)
    piece(c, "L", w // 2 - 44, 90, 8, phase + 1)
    piece(c, "I", w // 2 + 20, 88, 8, phase)
    SMALL.draw(c, TAGLINE, w // 2, 132, 1, False, "center")
    if pressed:
        c.rect(0, 0, w, h, False, False)
        c.rect(3, 3, w - 6, h - 6, False, False)
    write_png_1bit(path, w, h, c.px)


def launch_image(path, w=400, h=240):
    c = Canvas(w, h, True)
    draw_logo_scene(c)
    write_png_1bit(path, w, h, c.px)


def icon(path, pressed=False, phase=0):
    c = Canvas(32, 32, True)
    c.rect(1, 1, 30, 30, False, False)
    block(c, 5, 17, 7, phase)
    block(c, 12, 17, 7, phase)
    block(c, 19, 17, 7, phase)
    block(c, 12, 10, 7, phase)
    TITLE.draw(c, "I", 6, 3, 1, False)
    TITLE.draw(c, "T", 18, 3, 1, False)
    if pressed:
        c.rect(0, 0, 32, 32, False, False)
        c.rect(2, 2, 28, 28, False, False)
    write_png_1bit(path, 32, 32, c.px)


def wrapping_pattern(path, w=400, h=240):
    """Tileable wrapping paper: staggered hatched tetrominoes on an 80x80 grid
    (400x240 is an exact multiple, so the pattern repeats cleanly)."""
    c = Canvas(w, h, True)
    keys = ["T", "S", "O", "L", "I", "Z", "J"]
    i = 0
    for gy in range(0, h, 80):
        for gx in range(0, w, 80):
            key = keys[i % len(keys)]
            i += 1
            ox = gx + (12 if (gy // 80) % 2 == 0 else 44)
            piece(c, key, ox, gy + 14, 8)
            # small accent in the opposite corner
            c.line(gx + 58, gy + 60, gx + 64, gy + 60, False)
            c.line(gx + 61, gy + 57, gx + 61, gy + 63, False)
            c.rect(gx + 20, gy + 62, 2, 2, False, True)
    write_png_1bit(path, w, h, c.px)


def catalog(path, w, h, mode):
    c = Canvas(w, h, True)
    compact = h <= 90 or w <= 185
    scale = 2 if h >= 150 and w >= 300 else 1
    margin = 26 if scale == 2 else 14
    exclude = [(margin - 8, 8, TITLE.measure("IAINTRIS", scale) + 16, 15 * scale + 18)]
    if not compact:
        exclude.append((w - 140, 20, 108, h - 40))            # piece board
        exclude.append((margin - 8, h - 38, 250, 24))         # tagline
    else:
        exclude.append((w - 80, h - 52, 76, 48))              # mini pieces
    ambient(c, 120 if not compact else 45, exclude=exclude)
    TITLE.draw(c, "IAINTRIS", margin, 18 if scale == 2 else 16, scale, False)
    if not compact:
        c.rect(w - 132, 28, 92, h - 56, False, False)
        for row in range(max(3, (h - 72) // 13)):
            for col in range(6):
                if (row * 4 + col) % 5 < 2:
                    block(c, w - 120 + col * 12, 42 + row * 12, 12)
        SMALL.draw(c, TAGLINE, margin, h - 30, 1, False)
    else:
        piece(c, "T", w - 70, h - 43, 9)
        piece(c, "O", w - 34, h - 34, 9)
    write_png_1bit(path, w, h, c.px)


def main():
    launcher = os.path.join(SOURCE, "assets", "launcher")
    os.makedirs(os.path.join(launcher, "card-highlighted"), exist_ok=True)
    os.makedirs(os.path.join(launcher, "icon-highlighted"), exist_ok=True)
    launcher_card(os.path.join(launcher, "card.png"), 350, 155)
    launcher_card(os.path.join(launcher, "card-pressed.png"), 350, 155, pressed=True)
    for i in range(1, 5):
        launcher_card(os.path.join(launcher, "card-highlighted", f"{i}.png"), 350, 155, phase=i - 1)
    open(os.path.join(launcher, "card-highlighted", "animation.txt"), "w").write("frames = 1, 2, 3, 4\n")
    icon(os.path.join(launcher, "icon.png"))
    icon(os.path.join(launcher, "icon-pressed.png"), pressed=True)
    for i in range(1, 5):
        icon(os.path.join(launcher, "icon-highlighted", f"{i}.png"), phase=i - 1)
    open(os.path.join(launcher, "icon-highlighted", "animation.txt"), "w").write("frames = 1, 2, 3, 4\n")
    launch_image(os.path.join(launcher, "launchImage.png"))
    launch_image(os.path.join(launcher, "launchImage-list.png"))
    wrapping_pattern(os.path.join(launcher, "wrapping-pattern.png"))

    catalog_dir = os.path.join(ROOT, "assets", "catalog")
    os.makedirs(catalog_dir, exist_ok=True)
    catalog(os.path.join(catalog_dir, "catalog-billboard-380x180.png"), 380, 180, "billboard")
    catalog(os.path.join(catalog_dir, "catalog-wide-380x90.png"), 380, 90, "wide")
    catalog(os.path.join(catalog_dir, "catalog-small-185x90.png"), 185, 90, "small")
    catalog(os.path.join(catalog_dir, "catalog-header-400x208.png"), 400, 208, "header")


if __name__ == "__main__":
    main()
