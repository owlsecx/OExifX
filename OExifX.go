// ============================================================
//
//	OExifX — Metadata Reader & Scrubber
//	Author  : khaled.s.haddad
//	Website : owlsec.org
//	Language: Go (stdlib only) — OWL suite
//
//	Reads the metadata people forget they publish — EXIF (IFD0 / Exif /
//	GPS / Interop / IFD1 thumbnail), XMP, IPTC, JPEG comments, PNG text
//	chunks, WebP / GIF metadata, PDF Info + XMP, and OOXML / ODF document
//	properties including track-change and comment authors — and grades
//	the privacy exposure: GPS fixes, device serial numbers, names, user
//	paths, emails, pre-edit thumbnails, editing history.
//
//	The scrubber removes metadata without re-encoding (JPEG, PNG, WebP,
//	GIF, OOXML, ODF), keeps colour profiles and orientation, and verifies
//	the result: image data byte-identical and pixels decode the same.
//	v1.1: MP4 / MOV / HEIC (ISO-BMFF) read + in-place scrub, OSINT
//	linking across files (shared serials, owners, documents, places) with
//	a capture timeline, a CI publishing policy gate, and metadata compare.
//	Files are only written when --scrub is given.
//
// ============================================================
package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"compress/zlib"
	"encoding/binary"
	"encoding/csv"
	"encoding/hex"
	"encoding/json"
	"encoding/xml"
	"errors"
	"flag"
	"fmt"
	"hash/crc32"
	"image"
	_ "image/gif"
	"image/jpeg"
	"image/png"
	"io"
	"io/fs"
	"math"
	"math/rand"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf16"
	"unicode/utf8"
)

// ---- OWL UI KIT (cyan "owl" house style) — stdlib only. Shared across the suite ----
// CYAN is the primary brand/frame colour; red is reserved for errors and
// CRITICAL/HIGH severities.
const (
	R   = "\033[91m"       // red     — errors / critical
	GRN = "\033[92m"       // green   — success / low
	YLW = "\033[93m"       // yellow  — prompts / warning text
	CY  = "\033[96m"       // cyan    — primary brand & frames
	W   = "\033[97m"       // white   — body text
	B   = "\033[1m"        // bold
	X   = "\033[0m"        // reset
	MG  = "\033[95m"       // magenta — suite name / accents
	DIM = "\033[2m"        // dim     — secondary text
	OR  = "\033[38;5;208m" // orange  — warning markers
	GY  = "\033[90m"       // gray    — muted
)

var noColor = os.Getenv("NO_COLOR") != "" || !isatty()

func isatty() bool { fi, _ := os.Stdout.Stat(); return (fi.Mode() & os.ModeCharDevice) != 0 }
func col(s string, c ...string) string {
	if noColor {
		return s
	}
	return strings.Join(c, "") + s + X
}
func clear()           { fmt.Print("\033[H\033[2J") }
func rule()            { fmt.Println(col(strings.Repeat("─", 66), CY)) }
func okMsg(s string)   { fmt.Println("  " + col("[✔] ", GRN+B) + col(s, W)) }
func errMsg(s string)  { fmt.Println("  " + col("[✘] ", R+B) + col(s, R)) }
func warnMsg(s string) { fmt.Println("  " + col("[!] ", OR+B) + col(s, YLW)) }
func info(s string)    { fmt.Println("  " + col("[*] ", CY) + col(s, DIM+W)) }
func kv(k, v string)   { fmt.Println("  " + col("│  ", CY) + col(pad(k+":", 16), DIM) + col(v, W)) }

const BANNER = `
 ██████╗ ███████╗██╗  ██╗██╗███████╗██╗  ██╗
██╔═══██╗██╔════╝╚██╗██╔╝██║██╔════╝╚██╗██╔╝
██║   ██║█████╗   ╚███╔╝ ██║█████╗   ╚███╔╝
██║   ██║██╔══╝   ██╔██╗ ██║██╔══╝   ██╔██╗
╚██████╔╝███████╗██╔╝ ██╗██║██║     ██╔╝ ██╗
 ╚═════╝ ╚══════╝╚═╝  ╚═╝╚═╝╚═╝     ╚═╝  ╚═╝
`

const APPNAME = "OExifX"
const SUITE = "Owl Forensics Suite"
const TAGLINE = "Metadata Reader & Scrubber"
const SUBLINE = "EXIF · GPS · Video/HEIC · Office · Scrub · OSINT Links · CI Policy · Compare"
const VERSION = "1.1"
const AUTHOR = "khaled.s.haddad"
const WEBSITE = "owlsec.org"

// banner prints the cyan ANSI-Shadow wordmark and the suite identity block.
func banner() {
	fmt.Println(col(BANNER, CY))
	fmt.Println("  " + col(SUITE+"  ", B+MG) + col("v"+VERSION, YLW))
	fmt.Println("  " + col(SUBLINE, W))
	fmt.Println()
	fmt.Println("  " + col("Developer : ", DIM) + col(AUTHOR, CY) +
		col("   |   Website : ", DIM) + col(WEBSITE, CY))
	rule()
	fmt.Println()
}

var stdin = bufio.NewReader(os.Stdin)

func prompt(label string) string {
	fmt.Print("  " + col("[»] ", YLW) + col(label+": ", W))
	s, _ := stdin.ReadString('\n')
	return strings.TrimSpace(s)
}
func pause() {
	fmt.Print(col("\n  [↩] Press Enter to continue...", YLW))
	stdin.ReadString('\n')
}

// sectionHeader prints a ⬡ heading between two cyan rules.
func sectionHeader(s string) {
	rule()
	fmt.Println("  " + col("⬡  "+s, B+CY))
	rule()
	fmt.Println()
}

func stripANSI(s string) string {
	var b strings.Builder
	esc := false
	for _, r := range s {
		if r == '\033' {
			esc = true
			continue
		}
		if esc {
			if r == 'm' {
				esc = false
			}
			continue
		}
		b.WriteRune(r)
	}
	return b.String()
}

func vlen(s string) int { return utf8.RuneCountInString(stripANSI(s)) }
func pad(s string, n int) string {
	if l := vlen(s); l < n {
		return s + strings.Repeat(" ", n-l)
	}
	return s
}

func trunc(s string, n int) string {
	r := []rune(s)
	if len(r) <= n {
		return s
	}
	return string(r[:n-1]) + "…"
}

// table prints aligned columns with a cyan frame.
func table(headers []string, rows [][]string) {
	w := make([]int, len(headers))
	for i, h := range headers {
		w[i] = vlen(h)
	}
	for _, r := range rows {
		for i, c := range r {
			if i < len(w) && vlen(c) > w[i] {
				w[i] = vlen(c)
			}
		}
	}
	var hb strings.Builder
	for i, h := range headers {
		hb.WriteString(col(pad(h, w[i]), CY+B))
		if i < len(headers)-1 {
			hb.WriteString(col(" │ ", CY))
		}
	}
	fmt.Println("  " + hb.String())
	seg := make([]string, len(w))
	for i := range w {
		seg[i] = strings.Repeat("─", w[i])
	}
	fmt.Println("  " + col(strings.Join(seg, "─┼─"), CY))
	for _, r := range rows {
		var rb strings.Builder
		for i := range headers {
			v := ""
			if i < len(r) {
				v = r[i]
			}
			rb.WriteString(pad(col(v, W), w[i]))
			if i < len(headers)-1 {
				rb.WriteString(col(" │ ", CY))
			}
		}
		fmt.Println("  " + rb.String())
	}
}

// ====================================================================
//  SEVERITY
// ====================================================================

const (
	SevCritical = "CRITICAL"
	SevHigh     = "HIGH"
	SevMedium   = "MEDIUM"
	SevLow      = "LOW"
	SevInfo     = "INFO"
)

var sevRank = map[string]int{SevCritical: 5, SevHigh: 4, SevMedium: 3, SevLow: 2, SevInfo: 1}
var sevOrder = []string{SevCritical, SevHigh, SevMedium, SevLow, SevInfo}

func sevColor(s string) string {
	switch s {
	case SevCritical:
		return col(s, R+B)
	case SevHigh:
		return col(s, R)
	case SevMedium:
		return col(s, OR)
	case SevLow:
		return col(s, YLW)
	}
	return col(s, DIM)
}

// ====================================================================
//  METADATA MODEL
// ====================================================================

// Tag is one metadata value with the container it came from.
type Tag struct {
	Group string `json:"group"` // IFD0 Exif GPS Interop IFD1 XMP IPTC JPEG PNG WebP GIF PDF Office
	ID    string `json:"id,omitempty"`
	Name  string `json:"name"`
	Value string `json:"value"`
}

type GPSFix struct {
	Lat  float64  `json:"lat"`
	Lon  float64  `json:"lon"`
	Alt  *float64 `json:"alt,omitempty"`
	Time string   `json:"time,omitempty"`
}

func (g GPSFix) String() string {
	ns, ew := "N", "E"
	if g.Lat < 0 {
		ns = "S"
	}
	if g.Lon < 0 {
		ew = "W"
	}
	s := fmt.Sprintf("%.6f°%s, %.6f°%s", math.Abs(g.Lat), ns, math.Abs(g.Lon), ew)
	if g.Alt != nil {
		s += fmt.Sprintf(", %.0f m", *g.Alt)
	}
	return s
}

func (g GPSFix) MapURL() string {
	return fmt.Sprintf("https://www.openstreetmap.org/?mlat=%.6f&mlon=%.6f#map=17/%.6f/%.6f", g.Lat, g.Lon, g.Lat, g.Lon)
}

type Meta struct {
	Path       string    `json:"path"`
	Format     string    `json:"format"`
	Size       int64     `json:"size"`
	Width      int       `json:"width,omitempty"`
	Height     int       `json:"height,omitempty"`
	Tags       []Tag     `json:"tags"`
	GPS        *GPSFix   `json:"gps,omitempty"`
	Blocks     []string  `json:"blocks"` // container structure: "APP1 Exif 4.1 KB"
	Warnings   []string  `json:"warnings,omitempty"`
	Findings   []Finding `json:"findings"`
	Scrubbable bool      `json:"scrubbable"`
	thumb      []byte
	nums       map[string][]float64 // numeric TIFF values by "Group:ID"
}

func (m *Meta) add(group, id, name, value string) {
	value = strings.TrimSpace(strings.Trim(value, "\x00"))
	if value == "" {
		return
	}
	m.Tags = append(m.Tags, Tag{group, id, name, value})
}

func (m *Meta) warn(f string, a ...any) { m.Warnings = append(m.Warnings, fmt.Sprintf(f, a...)) }

func (m *Meta) get(name string) string {
	for _, t := range m.Tags {
		if strings.EqualFold(t.Name, name) {
			return t.Value
		}
	}
	return ""
}

func humanBytes(n int) string {
	switch {
	case n >= 1<<20:
		return fmt.Sprintf("%.1f MB", float64(n)/(1<<20))
	case n >= 1<<10:
		return fmt.Sprintf("%.1f KB", float64(n)/(1<<10))
	}
	return fmt.Sprintf("%d B", n)
}

// ====================================================================
//  TIFF / EXIF
// ====================================================================

var tiffNames = map[string]map[uint16]string{
	"IFD0": {0x010E: "ImageDescription", 0x010F: "Make", 0x0110: "Model", 0x0112: "Orientation", 0x011A: "XResolution",
		0x011B: "YResolution", 0x0128: "ResolutionUnit", 0x0131: "Software", 0x0132: "DateTime", 0x013B: "Artist",
		0x013C: "HostComputer", 0x0100: "ImageWidth", 0x0101: "ImageLength", 0x0213: "YCbCrPositioning",
		0x8298: "Copyright", 0x8769: "ExifIFD", 0x8825: "GPSIFD", 0x9C9B: "XPTitle", 0x9C9C: "XPComment",
		0x9C9D: "XPAuthor", 0x9C9E: "XPKeywords", 0x9C9F: "XPSubject", 0xC62F: "CameraSerialNumber",
		0xC614: "UniqueCameraModel", 0x02BC: "ApplicationNotes", 0x83BB: "IPTC-NAA", 0x8773: "ICCProfile",
		0x4746: "Rating", 0xA480: "GDALMetadata"},
	"Exif": {0x829A: "ExposureTime", 0x829D: "FNumber", 0x8822: "ExposureProgram", 0x8827: "ISO", 0x9000: "ExifVersion",
		0x9003: "DateTimeOriginal", 0x9004: "DateTimeDigitized", 0x9010: "OffsetTime", 0x9011: "OffsetTimeOriginal",
		0x9012: "OffsetTimeDigitized", 0x9101: "ComponentsConfiguration", 0x9201: "ShutterSpeedValue",
		0x9202: "ApertureValue", 0x9204: "ExposureBiasValue", 0x9205: "MaxApertureValue", 0x9207: "MeteringMode",
		0x9209: "Flash", 0x920A: "FocalLength", 0x927C: "MakerNote", 0x9286: "UserComment", 0x9290: "SubSecTime",
		0x9291: "SubSecTimeOriginal", 0x9292: "SubSecTimeDigitized", 0xA000: "FlashpixVersion", 0xA001: "ColorSpace",
		0xA002: "PixelXDimension", 0xA003: "PixelYDimension", 0xA005: "InteropIFD", 0xA217: "SensingMethod",
		0xA401: "CustomRendered", 0xA402: "ExposureMode", 0xA403: "WhiteBalance", 0xA404: "DigitalZoomRatio",
		0xA405: "FocalLengthIn35mmFilm", 0xA406: "SceneCaptureType", 0xA420: "ImageUniqueID", 0xA430: "CameraOwnerName",
		0xA431: "BodySerialNumber", 0xA432: "LensSpecification", 0xA433: "LensMake", 0xA434: "LensModel",
		0xA435: "LensSerialNumber", 0x8830: "SensitivityType", 0x8832: "RecommendedExposureIndex"},
	"GPS": {0x0000: "GPSVersionID", 0x0001: "GPSLatitudeRef", 0x0002: "GPSLatitude", 0x0003: "GPSLongitudeRef",
		0x0004: "GPSLongitude", 0x0005: "GPSAltitudeRef", 0x0006: "GPSAltitude", 0x0007: "GPSTimeStamp",
		0x0008: "GPSSatellites", 0x000C: "GPSSpeedRef", 0x000D: "GPSSpeed", 0x0010: "GPSImgDirectionRef",
		0x0011: "GPSImgDirection", 0x0012: "GPSMapDatum", 0x001B: "GPSProcessingMethod", 0x001D: "GPSDateStamp",
		0x001F: "GPSHPositioningError"},
	"Interop": {0x0001: "InteropIndex", 0x0002: "InteropVersion"},
	"IFD1": {0x0103: "Compression", 0x0201: "ThumbnailOffset", 0x0202: "ThumbnailLength", 0x011A: "XResolution",
		0x011B: "YResolution", 0x0128: "ResolutionUnit"},
}

var typeSize = map[uint16]int{1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8, 11: 4, 12: 8, 13: 4}

type tiffReader struct {
	b       []byte
	bo      binary.ByteOrder
	m       *Meta
	seen    map[uint32]bool
	entries int
}

// parseTIFF walks IFD0 → Exif / GPS / Interop and IFD1 (thumbnail), with
// bounds checks, loop protection and an entry budget for hostile files.
func parseTIFF(b []byte, m *Meta) error {
	if len(b) < 8 {
		return errors.New("TIFF header truncated")
	}
	t := &tiffReader{b: b, m: m, seen: map[uint32]bool{}}
	switch string(b[:2]) {
	case "II":
		t.bo = binary.LittleEndian
	case "MM":
		t.bo = binary.BigEndian
	default:
		return errors.New("not a TIFF header")
	}
	if t.bo.Uint16(b[2:]) != 42 {
		return errors.New("bad TIFF magic")
	}
	next := t.readIFD(t.bo.Uint32(b[4:]), "IFD0")
	if next != 0 {
		t.readIFD(next, "IFD1")
	}
	return nil
}

func (t *tiffReader) readIFD(off uint32, group string) uint32 {
	if off == 0 || t.seen[off] || int(off)+2 > len(t.b) {
		if off != 0 && int(off)+2 > len(t.b) {
			t.m.warn("%s offset %d outside the TIFF block", group, off)
		}
		return 0
	}
	t.seen[off] = true
	n := int(t.bo.Uint16(t.b[off:]))
	if n > 1000 {
		t.m.warn("%s claims %d entries — truncated", group, n)
		n = 1000
	}
	p := int(off) + 2
	for i := 0; i < n; i++ {
		e := p + 12*i
		if e+12 > len(t.b) {
			t.m.warn("%s entry %d truncated", group, i)
			return 0
		}
		if t.entries++; t.entries > 5000 {
			t.m.warn("too many TIFF entries — stopped")
			return 0
		}
		tag, typ, cnt := t.bo.Uint16(t.b[e:]), t.bo.Uint16(t.b[e+2:]), t.bo.Uint32(t.b[e+4:])
		sz, ok := typeSize[typ]
		if !ok || cnt > 1<<24 {
			continue
		}
		total := sz * int(cnt)
		var data []byte
		if total <= 4 {
			data = t.b[e+8 : e+8+total]
		} else {
			vo := int(t.bo.Uint32(t.b[e+8:]))
			if vo < 0 || vo+total > len(t.b) {
				t.m.warn("%s tag 0x%04X points outside the block", group, tag)
				continue
			}
			data = t.b[vo : vo+total]
		}
		t.entry(group, tag, typ, int(cnt), data)
	}
	if e := p + 12*n; e+4 <= len(t.b) {
		return t.bo.Uint32(t.b[e:])
	}
	return 0
}

func (t *tiffReader) nums(typ uint16, cnt int, d []byte) []float64 {
	var out []float64
	for i := 0; i < cnt && i < 64; i++ {
		switch typ {
		case 1, 7:
			out = append(out, float64(d[i]))
		case 6:
			out = append(out, float64(int8(d[i])))
		case 3:
			out = append(out, float64(t.bo.Uint16(d[2*i:])))
		case 8:
			out = append(out, float64(int16(t.bo.Uint16(d[2*i:]))))
		case 4, 13:
			out = append(out, float64(t.bo.Uint32(d[4*i:])))
		case 9:
			out = append(out, float64(int32(t.bo.Uint32(d[4*i:]))))
		case 5, 10:
			n, den := t.bo.Uint32(d[8*i:]), t.bo.Uint32(d[8*i+4:])
			if den == 0 {
				out = append(out, 0)
				continue
			}
			if typ == 10 {
				out = append(out, float64(int32(n))/float64(int32(den)))
			} else {
				out = append(out, float64(n)/float64(den))
			}
		case 11:
			out = append(out, float64(math.Float32frombits(t.bo.Uint32(d[4*i:]))))
		case 12:
			out = append(out, math.Float64frombits(t.bo.Uint64(d[8*i:])))
		}
	}
	return out
}

func fmtNum(v float64) string {
	if v == math.Trunc(v) && math.Abs(v) < 1e15 {
		return strconv.FormatInt(int64(v), 10)
	}
	return strconv.FormatFloat(v, 'f', -1, 64)
}

func (t *tiffReader) entry(group string, tag, typ uint16, cnt int, d []byte) {
	id := fmt.Sprintf("0x%04X", tag)
	name := tiffNames[group][tag]
	if name == "" {
		name = tiffNames["IFD0"][tag] // IFD1 / odd writers reuse IFD0 tags
	}
	if name == "" {
		name = "Tag" + id
	}
	switch {
	case tag == 0x8769 && group == "IFD0":
		t.readIFD(t.bo.Uint32(d), "Exif")
		return
	case tag == 0x8825 && group == "IFD0":
		t.readIFD(t.bo.Uint32(d), "GPS")
		return
	case tag == 0xA005 && group == "Exif":
		t.readIFD(t.bo.Uint32(d), "Interop")
		return
	case group == "IFD1" && tag == 0x0201:
		t.m.nums["IFD1:thumboff"] = []float64{float64(t.bo.Uint32(d))}
	case group == "IFD1" && tag == 0x0202:
		t.m.nums["IFD1:thumblen"] = []float64{float64(t.bo.Uint32(d))}
	}
	if len(t.m.Tags) > 2000 {
		return
	}
	var v string
	switch {
	case typ == 2:
		v = strings.TrimRight(string(d), "\x00 ")
		if i := strings.IndexByte(v, 0); i >= 0 {
			v = v[:i]
		}
		v = strings.ToValidUTF8(v, "?")
	case tag >= 0x9C9B && tag <= 0x9C9F: // XP* tags: UTF-16LE in BYTE arrays
		v = utf16le(d)
	case tag == 0x927C:
		v = fmt.Sprintf("(%s vendor MakerNote, not decoded)", humanBytes(len(d)))
	case tag == 0x9286:
		v = userComment(d)
	case tag == 0x8773 || tag == 0x83BB || tag == 0x02BC:
		v = fmt.Sprintf("(%s block)", humanBytes(len(d)))
		if tag == 0x02BC {
			t.m.addXMP(d)
		}
		if tag == 0x83BB {
			parseIPTC(d, t.m)
		}
	case typ == 7 && (tag == 0x9000 || tag == 0xA000 || group == "Interop"):
		v = strings.TrimRight(string(d), "\x00")
	case typ == 7:
		if len(d) > 32 {
			v = fmt.Sprintf("(%s binary)", humanBytes(len(d)))
		} else {
			v = hex.EncodeToString(d)
		}
	default:
		ns := t.nums(typ, cnt, d)
		t.m.nums[group+":"+id] = ns
		var parts []string
		for i, x := range ns {
			if i == 16 {
				parts = append(parts, "…")
				break
			}
			parts = append(parts, fmtNum(x))
		}
		v = strings.Join(parts, " ")
	}
	t.m.add(group, id, name, v)
}

func utf16le(d []byte) string {
	var u []uint16
	for i := 0; i+1 < len(d); i += 2 {
		c := uint16(d[i]) | uint16(d[i+1])<<8
		if c == 0 {
			break
		}
		u = append(u, c)
	}
	return string(utf16.Decode(u))
}

func utf16be(d []byte) string {
	var u []uint16
	for i := 0; i+1 < len(d); i += 2 {
		u = append(u, uint16(d[i])<<8|uint16(d[i+1]))
	}
	return string(utf16.Decode(u))
}

func userComment(d []byte) string {
	if len(d) < 8 {
		return ""
	}
	code, body := string(bytes.TrimRight(d[:8], "\x00 ")), d[8:]
	switch code {
	case "UNICODE":
		if len(body) >= 2 && body[0] == 0 {
			return strings.TrimSpace(utf16be(body))
		}
		return strings.TrimSpace(utf16le(body))
	}
	return strings.TrimSpace(strings.ToValidUTF8(strings.Trim(string(body), "\x00 "), "?"))
}

// finishGPS converts the GPS IFD's degree/minute/second rationals.
func (m *Meta) finishGPS() {
	lat, lon := m.nums["GPS:0x0002"], m.nums["GPS:0x0004"]
	if len(lat) < 3 || len(lon) < 3 {
		return
	}
	dms := func(v []float64) float64 { return v[0] + v[1]/60 + v[2]/3600 }
	g := GPSFix{Lat: dms(lat), Lon: dms(lon)}
	for _, t := range m.Tags {
		switch {
		case t.Group == "GPS" && t.Name == "GPSLatitudeRef" && strings.HasPrefix(strings.ToUpper(t.Value), "S"):
			g.Lat = -g.Lat
		case t.Group == "GPS" && t.Name == "GPSLongitudeRef" && strings.HasPrefix(strings.ToUpper(t.Value), "W"):
			g.Lon = -g.Lon
		case t.Group == "GPS" && t.Name == "GPSDateStamp":
			g.Time = t.Value
		}
	}
	if g.Lat == 0 && g.Lon == 0 || math.Abs(g.Lat) > 90 || math.Abs(g.Lon) > 180 {
		return
	}
	if a := m.nums["GPS:0x0006"]; len(a) == 1 {
		alt := a[0]
		if r := m.nums["GPS:0x0005"]; len(r) == 1 && r[0] == 1 {
			alt = -alt
		}
		g.Alt = &alt
	}
	if ts := m.nums["GPS:0x0007"]; len(ts) == 3 {
		g.Time = strings.TrimSpace(g.Time + fmt.Sprintf(" %02.0f:%02.0f:%02.0f UTC", ts[0], ts[1], math.Floor(ts[2])))
	}
	m.GPS = &g
}

// ====================================================================
//  XMP + IPTC
// ====================================================================

var xmpPrefix = map[string]string{
	"http://purl.org/dc/elements/1.1/": "dc", "http://ns.adobe.com/xap/1.0/": "xmp",
	"http://ns.adobe.com/xap/1.0/mm/": "xmpMM", "http://ns.adobe.com/photoshop/1.0/": "photoshop",
	"http://ns.adobe.com/exif/1.0/": "exif", "http://ns.adobe.com/tiff/1.0/": "tiff",
	"http://iptc.org/std/Iptc4xmpCore/1.0/xmlns/": "Iptc4xmpCore", "http://ns.adobe.com/exif/1.0/aux/": "aux",
	"http://ns.adobe.com/xap/1.0/sType/ResourceEvent#": "stEvt", "http://ns.adobe.com/pdf/1.3/": "pdf",
	"http://ns.adobe.com/camera-raw-settings/1.0/": "crs", "http://ns.adobe.com/xap/1.0/rights/": "xmpRights",
	"http://ns.google.com/photos/1.0/panorama/": "GPano", "http://ns.adobe.com/xap/1.0/sType/ResourceRef#": "stRef",
	"http://ns.adobe.com/lightroom/1.0/": "lr", "http://ns.microsoft.com/photo/1.0/": "MicrosoftPhoto",
	"http://ns.adobe.com/exif/1.0/exifEX/": "exifEX", "http://www.w3.org/1999/02/22-rdf-syntax-ns#": "rdf",
	"adobe:ns:meta/": "x", "http://ns.adobe.com/xmp/1.0/DynamicMedia/": "xmpDM",
	"http://iptc.org/std/Iptc4xmpExt/2008-02-29/": "Iptc4xmpExt",
}

func xmpName(n xml.Name) string {
	p, ok := xmpPrefix[n.Space]
	if !ok {
		p = n.Space
		if i := strings.LastIndexAny(p, "/#"); i >= 0 && i < len(p)-1 {
			p = p[i+1:]
		}
	}
	if p == "" {
		return n.Local
	}
	return p + ":" + n.Local
}

// addXMP flattens an XMP packet into properties: attributes of rdf:Description
// and leaf element text (rdf:li values are attributed to their property).
func (m *Meta) addXMP(packet []byte) {
	if i := bytes.Index(packet, []byte("<x:xmpmeta")); i > 0 {
		packet = packet[i:]
	} else if i := bytes.Index(packet, []byte("<rdf:RDF")); i > 0 {
		packet = packet[i:]
	}
	if j := bytes.LastIndex(packet, []byte("</x:xmpmeta>")); j > 0 {
		packet = packet[:j+len("</x:xmpmeta>")]
	}
	dec := xml.NewDecoder(bytes.NewReader(packet))
	dec.Strict = false
	var stack []string
	history := 0
	count := 0
	for count < 3000 {
		tok, err := dec.Token()
		if err != nil {
			break
		}
		switch t := tok.(type) {
		case xml.StartElement:
			n := xmpName(t.Name)
			stack = append(stack, n)
			if n == "stEvt:action" { // one per editing event, as attribute or element
				history++
			}
			for _, a := range t.Attr {
				an := xmpName(a.Name)
				if strings.HasPrefix(an, "xmlns") || an == "rdf:about" || an == "rdf:parseType" || a.Name.Space == "xmlns" ||
					strings.HasPrefix(an, "x:") || an == "xml:lang" {
					continue
				}
				m.add("XMP", "", an, a.Value)
				count++
				if an == "stEvt:action" {
					history++
				}
			}
		case xml.EndElement:
			if len(stack) > 0 {
				stack = stack[:len(stack)-1]
			}
		case xml.CharData:
			v := strings.TrimSpace(string(t))
			if v == "" || len(stack) == 0 {
				continue
			}
			prop := ""
			for i := len(stack) - 1; i >= 0; i-- {
				if !strings.HasPrefix(stack[i], "rdf:") {
					prop = stack[i]
					break
				}
			}
			if prop != "" && !strings.HasPrefix(prop, "x:") {
				m.add("XMP", "", prop, v)
				count++
			}
		}
	}
	if history > 0 {
		m.add("XMP", "", "xmpMM:History", fmt.Sprintf("%d editing event(s)", history))
	}
}

var iptcNames = map[byte]string{5: "ObjectName", 25: "Keywords", 55: "DateCreated", 60: "TimeCreated", 80: "By-line",
	85: "By-lineTitle", 90: "City", 92: "Sub-location", 95: "Province-State", 101: "Country", 103: "OriginalTransmissionReference",
	105: "Headline", 110: "Credit", 115: "Source", 116: "CopyrightNotice", 118: "Contact", 120: "Caption-Abstract",
	122: "Writer-Editor", 62: "DigitalCreationDate", 65: "OriginatingProgram", 70: "ProgramVersion"}

func parseIPTC(d []byte, m *Meta) {
	for i := 0; i+5 <= len(d); {
		if d[i] != 0x1C {
			i++
			continue
		}
		rec, ds, n := d[i+1], d[i+2], int(binary.BigEndian.Uint16(d[i+3:]))
		if n&0x8000 != 0 || i+5+n > len(d) {
			break
		}
		if rec == 2 {
			name := iptcNames[ds]
			if name == "" {
				name = fmt.Sprintf("2:%d", ds)
			}
			if ds != 0 {
				m.add("IPTC", fmt.Sprintf("2:%d", ds), name, strings.ToValidUTF8(string(d[i+5:i+5+n]), "?"))
			}
		}
		i += 5 + n
	}
}

// parsePhotoshopIRB walks 8BIM resources (APP13) for IPTC (0x0404) and XMP.
func parsePhotoshopIRB(d []byte, m *Meta) {
	for i := 0; i+12 <= len(d); {
		if string(d[i:i+4]) != "8BIM" {
			break
		}
		id := binary.BigEndian.Uint16(d[i+4:])
		nl := int(d[i+6])
		p := i + 7 + nl
		if (nl+1)%2 == 1 {
			p++
		}
		if p+4 > len(d) {
			break
		}
		sz := int(binary.BigEndian.Uint32(d[p:]))
		p += 4
		if sz < 0 || p+sz > len(d) {
			break
		}
		switch id {
		case 0x0404:
			parseIPTC(d[p:p+sz], m)
		case 0x0424:
			m.addXMP(d[p : p+sz])
		}
		i = p + sz
		if sz%2 == 1 {
			i++
		}
	}
}

// ====================================================================
//  FORMAT PARSERS
// ====================================================================

func detectFormat(b []byte, name string) string {
	switch {
	case len(b) >= 3 && b[0] == 0xFF && b[1] == 0xD8 && b[2] == 0xFF:
		return "JPEG"
	case len(b) >= 8 && string(b[:8]) == "\x89PNG\r\n\x1a\n":
		return "PNG"
	case len(b) >= 12 && string(b[:4]) == "RIFF" && string(b[8:12]) == "WEBP":
		return "WebP"
	case len(b) >= 6 && (string(b[:6]) == "GIF87a" || string(b[:6]) == "GIF89a"):
		return "GIF"
	case len(b) >= 4 && (string(b[:4]) == "II*\x00" || string(b[:4]) == "MM\x00*"):
		return "TIFF"
	case len(b) >= 5 && string(b[:5]) == "%PDF-":
		return "PDF"
	case len(b) >= 12 && string(b[4:8]) == "ftyp":
		switch brand := string(b[8:12]); {
		case strings.Contains(brand, "hei") || brand == "mif1" || brand == "msf1" || brand == "avif" || brand == "hevc":
			return "HEIC"
		case brand == "qt  ":
			return "MOV"
		}
		return "MP4"
	case len(b) >= 8 && (string(b[4:8]) == "moov" || string(b[4:8]) == "wide" || string(b[4:8]) == "mdat" && strings.EqualFold(filepath.Ext(name), ".mov")):
		return "MOV"
	case len(b) >= 4 && string(b[:4]) == "PK\x03\x04":
		switch strings.ToLower(filepath.Ext(name)) {
		case ".docx", ".xlsx", ".pptx", ".docm", ".xlsm", ".pptm":
			return "OOXML"
		case ".odt", ".ods", ".odp", ".odg":
			return "ODF"
		}
		if bytes.Contains(b[:min(len(b), 4096)], []byte("[Content_Types].xml")) {
			return "OOXML"
		}
		if bytes.Contains(b[:min(len(b), 200)], []byte("mimetypeapplication/vnd.oasis")) {
			return "ODF"
		}
		return "ZIP"
	}
	return ""
}

var jpegMarkerName = map[byte]string{0xC0: "SOF0", 0xC1: "SOF1", 0xC2: "SOF2", 0xC4: "DHT", 0xDB: "DQT", 0xDD: "DRI",
	0xDA: "SOS", 0xFE: "COM", 0xE0: "APP0", 0xE1: "APP1", 0xE2: "APP2", 0xED: "APP13", 0xEE: "APP14"}

type jpegSeg struct {
	marker byte
	start  int // offset of the 0xFF
	end    int // offset after the segment (for SOS: end of file)
	data   []byte
}

// jpegSegments splits a JPEG up to and including SOS (the rest is image data).
func jpegSegments(b []byte) ([]jpegSeg, error) {
	var out []jpegSeg
	i := 2
	for i+4 <= len(b) {
		if b[i] != 0xFF {
			return out, fmt.Errorf("marker expected at offset %d", i)
		}
		mk := b[i+1]
		if mk == 0xFF { // fill byte
			i++
			continue
		}
		if mk == 0xD9 {
			out = append(out, jpegSeg{mk, i, i + 2, nil})
			return out, nil
		}
		if mk >= 0xD0 && mk <= 0xD7 || mk == 0x01 {
			i += 2
			continue
		}
		n := int(binary.BigEndian.Uint16(b[i+2:]))
		if n < 2 || i+2+n > len(b) {
			return out, fmt.Errorf("segment 0x%02X at %d overruns the file", mk, i)
		}
		s := jpegSeg{mk, i, i + 2 + n, b[i+4 : i+2+n]}
		if mk == 0xDA {
			s.end = len(b)
			out = append(out, s)
			return out, nil
		}
		out = append(out, s)
		i += 2 + n
	}
	return out, errors.New("no SOS marker — truncated JPEG")
}

func parseJPEG(b []byte, m *Meta) {
	segs, err := jpegSegments(b)
	if err != nil {
		m.warn("%v", err)
	}
	var extXMP bool
	for _, s := range segs {
		name := jpegMarkerName[s.marker]
		if name == "" {
			name = fmt.Sprintf("0x%02X", s.marker)
			if s.marker >= 0xE0 && s.marker <= 0xEF {
				name = fmt.Sprintf("APP%d", s.marker-0xE0)
			}
		}
		d := s.data
		label := name
		switch {
		case s.marker == 0xE1 && bytes.HasPrefix(d, []byte("Exif\x00")):
			label += " Exif"
			if len(d) > 6 {
				if err := parseTIFF(d[6:], m); err != nil {
					m.warn("Exif: %v", err)
				}
				if off, ok := m.nums["IFD1:thumboff"]; ok {
					if l, ok := m.nums["IFD1:thumblen"]; ok {
						o, n := int(off[0])+6, int(l[0])
						if o > 6 && n > 0 && o+n <= len(d) {
							m.thumb = d[o : o+n]
						}
					}
				}
			}
		case s.marker == 0xE1 && bytes.HasPrefix(d, []byte("http://ns.adobe.com/xap/1.0/\x00")):
			label += " XMP"
			m.addXMP(d[29:])
		case s.marker == 0xE1 && bytes.HasPrefix(d, []byte("http://ns.adobe.com/xmp/extension/\x00")):
			label += " XMP-extended"
			extXMP = true
		case s.marker == 0xED && bytes.HasPrefix(d, []byte("Photoshop 3.0\x00")):
			label += " Photoshop/IPTC"
			parsePhotoshopIRB(d[14:], m)
		case s.marker == 0xE2 && bytes.HasPrefix(d, []byte("ICC_PROFILE\x00")):
			label += " ICC"
			if len(d) > 14+48 {
				m.add("JPEG", "", "ICCProfile", iccDesc(d[14:]))
			}
		case s.marker == 0xE0 && bytes.HasPrefix(d, []byte("JFIF\x00")):
			label += " JFIF"
		case s.marker == 0xEE && bytes.HasPrefix(d, []byte("Adobe")):
			label += " Adobe"
		case s.marker == 0xFE:
			m.add("JPEG", "COM", "Comment", strings.ToValidUTF8(string(d), "?"))
		case s.marker >= 0xC0 && s.marker <= 0xCF && s.marker != 0xC4 && s.marker != 0xC8 && s.marker != 0xCC && len(d) >= 5:
			m.Height, m.Width = int(binary.BigEndian.Uint16(d[1:])), int(binary.BigEndian.Uint16(d[3:]))
		}
		if s.marker == 0xDA {
			m.Blocks = append(m.Blocks, fmt.Sprintf("SOS + image data %s", humanBytes(s.end-s.start)))
			continue
		}
		m.Blocks = append(m.Blocks, fmt.Sprintf("%s %s", label, humanBytes(len(d))))
	}
	if extXMP {
		m.add("XMP", "", "ExtendedXMP", "present (multi-segment)")
	}
	m.Scrubbable = err == nil
}

// iccDesc pulls the profile description ("sRGB IEC61966-2.1") if readable.
func iccDesc(p []byte) string {
	if len(p) < 132 {
		return fmt.Sprintf("%s profile", humanBytes(len(p)))
	}
	n := int(binary.BigEndian.Uint32(p[128:]))
	for i := 0; i < n && 132+12*i+12 <= len(p); i++ {
		e := 132 + 12*i
		if string(p[e:e+4]) == "desc" {
			o, l := int(binary.BigEndian.Uint32(p[e+4:])), int(binary.BigEndian.Uint32(p[e+8:]))
			if o+l <= len(p) && l > 12 {
				d := p[o : o+l]
				switch string(d[:4]) {
				case "desc":
					if sl := int(binary.BigEndian.Uint32(d[8:])); 12+sl <= len(d) {
						return strings.Trim(string(d[12:12+sl]), "\x00")
					}
				case "mluc":
					if len(d) >= 28 {
						so, sl := int(binary.BigEndian.Uint32(d[20:])), int(binary.BigEndian.Uint32(d[24:]))
						if so+sl <= len(d) {
							return utf16be(d[so : so+sl])
						}
					}
				}
			}
		}
	}
	return fmt.Sprintf("%s profile", humanBytes(len(p)))
}

func inflate(d []byte, limit int64) ([]byte, error) {
	r, err := zlib.NewReader(bytes.NewReader(d))
	if err != nil {
		return nil, err
	}
	defer r.Close()
	return io.ReadAll(io.LimitReader(r, limit))
}

type pngChunk struct {
	typ        string
	data       []byte
	start, end int
	crcOK      bool
}

func pngChunks(b []byte) ([]pngChunk, error) {
	var out []pngChunk
	for i := 8; i+12 <= len(b); {
		n := int(binary.BigEndian.Uint32(b[i:]))
		if n < 0 || i+12+n > len(b) {
			return out, fmt.Errorf("chunk at %d overruns the file", i)
		}
		typ := string(b[i+4 : i+8])
		c := pngChunk{typ, b[i+8 : i+8+n], i, i + 12 + n, crc32.ChecksumIEEE(b[i+4:i+8+n]) == binary.BigEndian.Uint32(b[i+8+n:])}
		out = append(out, c)
		i += 12 + n
		if typ == "IEND" {
			return out, nil
		}
	}
	return out, errors.New("no IEND chunk — truncated PNG")
}

func parsePNG(b []byte, m *Meta) {
	cs, err := pngChunks(b)
	if err != nil {
		m.warn("%v", err)
	}
	idat := 0
	for _, c := range cs {
		if !c.crcOK {
			m.warn("chunk %s has a bad CRC", c.typ)
		}
		switch c.typ {
		case "IHDR":
			if len(c.data) >= 8 {
				m.Width, m.Height = int(binary.BigEndian.Uint32(c.data)), int(binary.BigEndian.Uint32(c.data[4:]))
			}
		case "IDAT":
			idat += len(c.data)
			continue
		case "tEXt":
			k, v, _ := bytes.Cut(c.data, []byte{0})
			m.pngText(string(k), latin1(v))
		case "zTXt":
			k, rest, _ := bytes.Cut(c.data, []byte{0})
			if len(rest) > 1 {
				if v, err := inflate(rest[1:], 4<<20); err == nil {
					m.pngText(string(k), latin1(v))
				} else {
					m.warn("zTXt %s: %v", k, err)
				}
			}
		case "iTXt":
			k, rest, _ := bytes.Cut(c.data, []byte{0})
			if len(rest) >= 2 {
				comp := rest[0] == 1
				rest = rest[2:]
				_, rest, _ = bytes.Cut(rest, []byte{0}) // language
				_, rest, _ = bytes.Cut(rest, []byte{0}) // translated keyword
				v := rest
				if comp {
					if x, err := inflate(rest, 4<<20); err == nil {
						v = x
					}
				}
				m.pngText(string(k), string(v))
			}
		case "eXIf":
			if err := parseTIFF(c.data, m); err != nil {
				m.warn("eXIf: %v", err)
			}
		case "tIME":
			if len(c.data) == 7 {
				m.add("PNG", "tIME", "LastModified", fmt.Sprintf("%04d-%02d-%02d %02d:%02d:%02d UTC",
					binary.BigEndian.Uint16(c.data), c.data[2], c.data[3], c.data[4], c.data[5], c.data[6]))
			}
		case "iCCP":
			k, _, _ := bytes.Cut(c.data, []byte{0})
			m.add("PNG", "iCCP", "ICCProfile", latin1(k))
		}
		m.Blocks = append(m.Blocks, fmt.Sprintf("%s %s", c.typ, humanBytes(len(c.data))))
	}
	if idat > 0 {
		m.Blocks = append(m.Blocks, fmt.Sprintf("IDAT ×n %s", humanBytes(idat)))
	}
	m.Scrubbable = err == nil
}

func latin1(b []byte) string {
	if utf8.Valid(b) {
		return string(b)
	}
	r := make([]rune, len(b))
	for i, c := range b {
		r[i] = rune(c)
	}
	return string(r)
}

// pngText handles plain keywords, XMP and ImageMagick "Raw profile" hex blobs.
func (m *Meta) pngText(k, v string) {
	switch {
	case k == "XML:com.adobe.xmp":
		m.addXMP([]byte(v))
	case strings.HasPrefix(k, "Raw profile type "):
		// "\nexif\n    1234\n45786966..." — hex of an APP1 payload
		f := strings.Fields(v)
		if len(f) >= 3 {
			raw, err := hex.DecodeString(strings.Join(f[2:], ""))
			if err == nil {
				switch {
				case strings.HasSuffix(k, "exif") || strings.HasSuffix(k, "APP1"):
					if bytes.HasPrefix(raw, []byte("Exif\x00\x00")) {
						raw = raw[6:]
					}
					parseTIFF(raw, m)
				case strings.HasSuffix(k, "iptc"):
					parseIPTC(raw, m)
				case strings.HasSuffix(k, "xmp"):
					m.addXMP(raw)
				}
				return
			}
		}
		m.add("PNG", "text", k, v)
	default:
		m.add("PNG", "text", k, v)
	}
}

type riffChunk struct {
	id         string
	data       []byte
	start, end int
}

func webpChunks(b []byte) ([]riffChunk, error) {
	var out []riffChunk
	end := min(len(b), 8+int(binary.LittleEndian.Uint32(b[4:])))
	for i := 12; i+8 <= end; {
		n := int(binary.LittleEndian.Uint32(b[i+4:]))
		if n < 0 || i+8+n > end {
			return out, fmt.Errorf("chunk at %d overruns the file", i)
		}
		e := i + 8 + n + n%2
		out = append(out, riffChunk{string(b[i : i+4]), b[i+8 : i+8+n], i, min(e, end)})
		i = e
	}
	return out, nil
}

func parseWebP(b []byte, m *Meta) {
	cs, err := webpChunks(b)
	if err != nil {
		m.warn("%v", err)
	}
	for _, c := range cs {
		switch c.id {
		case "VP8X":
			if len(c.data) >= 10 {
				m.Width = 1 + int(c.data[4]) | int(c.data[5])<<8 | int(c.data[6])<<16
				m.Height = 1 + int(c.data[7]) | int(c.data[8])<<8 | int(c.data[9])<<16
			}
		case "EXIF":
			d := c.data
			if bytes.HasPrefix(d, []byte("Exif\x00\x00")) {
				d = d[6:]
			}
			if err := parseTIFF(d, m); err != nil {
				m.warn("EXIF: %v", err)
			}
		case "XMP ":
			m.addXMP(c.data)
		}
		m.Blocks = append(m.Blocks, fmt.Sprintf("%s %s", strings.TrimSpace(c.id), humanBytes(len(c.data))))
	}
	m.Scrubbable = err == nil
}

type gifBlock struct {
	start, end int
	kind       string // header | comment | xmp | app | gce | image | trailer
}

// gifBlocks walks a GIF into blocks (sub-block chains included).
func gifBlocks(b []byte) ([]gifBlock, error) {
	if len(b) < 13 {
		return nil, errors.New("GIF header truncated")
	}
	i := 13
	if b[10]&0x80 != 0 {
		i += 3 << (int(b[10]&7) + 1)
	}
	out := []gifBlock{{0, i, "header"}}
	skipSub := func(p int) (int, error) {
		for p < len(b) {
			n := int(b[p])
			p++
			if n == 0 {
				return p, nil
			}
			p += n
		}
		return p, errors.New("sub-block chain truncated")
	}
	for i < len(b) {
		s := i
		switch b[i] {
		case 0x3B:
			out = append(out, gifBlock{s, i + 1, "trailer"})
			return out, nil
		case 0x21:
			if i+2 > len(b) {
				return out, errors.New("extension truncated")
			}
			label := b[i+1]
			kind := "ext"
			switch label {
			case 0xFE:
				kind = "comment"
			case 0xF9:
				kind = "gce"
			case 0xFF:
				kind = "app"
				if i+14 <= len(b) && string(b[i+3:i+14]) == "XMP DataXMP" {
					kind = "xmp"
				}
			}
			p, err := skipSub(i + 2)
			if err != nil {
				return out, err
			}
			out = append(out, gifBlock{s, p, kind})
			i = p
		case 0x2C:
			if i+10 > len(b) {
				return out, errors.New("image descriptor truncated")
			}
			p := i + 10
			if b[i+9]&0x80 != 0 {
				p += 3 << (int(b[i+9]&7) + 1)
			}
			p++ // LZW minimum code size
			p, err := skipSub(p)
			if err != nil {
				return out, err
			}
			out = append(out, gifBlock{s, p, "image"})
			i = p
		default:
			return out, fmt.Errorf("unexpected byte 0x%02X at %d", b[i], i)
		}
	}
	return out, errors.New("no GIF trailer")
}

func gifSubData(b []byte) []byte {
	var out []byte
	for p := 0; p < len(b); {
		n := int(b[p])
		p++
		if n == 0 || p+n > len(b) {
			break
		}
		out = append(out, b[p:p+n]...)
		p += n
	}
	return out
}

func parseGIF(b []byte, m *Meta) {
	bs, err := gifBlocks(b)
	if err != nil {
		m.warn("%v", err)
	}
	m.Width, m.Height = int(binary.LittleEndian.Uint16(b[6:])), int(binary.LittleEndian.Uint16(b[8:]))
	frames := 0
	for _, x := range bs {
		switch x.kind {
		case "comment":
			m.add("GIF", "comment", "Comment", latin1(gifSubData(b[x.start+2:x.end])))
		case "xmp":
			seg := b[x.start:x.end]
			if i := bytes.Index(seg, []byte("<?xpacket begin")); i >= 0 {
				if j := bytes.Index(seg[i:], []byte("<?xpacket end")); j > 0 {
					m.addXMP(seg[i : i+j])
				}
			}
		case "image":
			frames++
			continue
		}
		if x.kind != "gce" {
			m.Blocks = append(m.Blocks, fmt.Sprintf("%s %s", x.kind, humanBytes(x.end-x.start)))
		}
	}
	m.Blocks = append(m.Blocks, fmt.Sprintf("%d image frame(s)", frames))
	m.Scrubbable = err == nil
}

// ---- PDF ----

var (
	rePDFKey    = regexp.MustCompile(`/(Title|Author|Subject|Keywords|Creator|Producer|CreationDate|ModDate|Company|SourceModified)\s*(\((?:\\.|[^\\)])*\)|<[0-9A-Fa-f\s]*>)`)
	rePDFStream = regexp.MustCompile(`(?s)<<(.{0,600}?)>>\s*stream\r?\n`)
)

func pdfString(s string) string {
	switch {
	case strings.HasPrefix(s, "<"):
		h := strings.Map(func(r rune) rune {
			if strings.ContainsRune("0123456789abcdefABCDEF", r) {
				return r
			}
			return -1
		}, s)
		if len(h)%2 == 1 {
			h += "0"
		}
		b, _ := hex.DecodeString(h)
		if bytes.HasPrefix(b, []byte{0xFE, 0xFF}) {
			return utf16be(b[2:])
		}
		return latin1(b)
	case strings.HasPrefix(s, "("):
		s = s[1 : len(s)-1]
		var out []byte
		for i := 0; i < len(s); i++ {
			c := s[i]
			if c != '\\' || i+1 >= len(s) {
				out = append(out, c)
				continue
			}
			i++
			switch s[i] {
			case 'n':
				out = append(out, '\n')
			case 'r':
				out = append(out, '\r')
			case 't':
				out = append(out, '\t')
			case '(', ')', '\\':
				out = append(out, s[i])
			case '\n':
			default:
				if s[i] >= '0' && s[i] <= '7' {
					j := i
					for j < len(s) && j < i+3 && s[j] >= '0' && s[j] <= '7' {
						j++
					}
					v, _ := strconv.ParseUint(s[i:j], 8, 8)
					out = append(out, byte(v))
					i = j - 1
				} else {
					out = append(out, s[i])
				}
			}
		}
		if bytes.HasPrefix(out, []byte{0xFE, 0xFF}) {
			return utf16be(out[2:])
		}
		return latin1(out)
	}
	return s
}

// pdfDate turns D:20240101120000+02'00' into 2024-01-01 12:00:00 +02:00.
func pdfDate(s string) string {
	s = strings.TrimPrefix(s, "D:")
	if len(s) < 14 {
		return s
	}
	out := fmt.Sprintf("%s-%s-%s %s:%s:%s", s[0:4], s[4:6], s[6:8], s[8:10], s[10:12], s[12:14])
	if tz := strings.ReplaceAll(s[14:], "'", ""); len(tz) >= 5 {
		out += " " + tz[:3] + ":" + tz[3:5]
	} else if tz == "Z" {
		out += " UTC"
	}
	return out
}

func parsePDF(b []byte, m *Meta) {
	texts := [][]byte{b}
	streams, inflated := 0, 0
	for _, loc := range rePDFStream.FindAllSubmatchIndex(b, -1) {
		streams++
		dict := string(b[loc[2]:loc[3]])
		if !strings.Contains(dict, "/FlateDecode") || !(strings.Contains(dict, "/ObjStm") || strings.Contains(dict, "/Metadata")) {
			continue
		}
		body := b[loc[1]:]
		if j := bytes.Index(body, []byte("endstream")); j > 0 {
			if d, err := inflate(body[:j], 16<<20); err == nil || len(d) > 0 {
				texts = append(texts, d)
				inflated++
			}
		}
		if inflated > 400 {
			break
		}
	}
	seen := map[string]bool{}
	for _, t := range texts {
		for _, mm := range rePDFKey.FindAllSubmatch(t, -1) {
			k := string(mm[1])
			if seen[k] {
				continue
			}
			v := pdfString(string(mm[2]))
			if strings.HasSuffix(k, "Date") || k == "SourceModified" {
				v = pdfDate(v)
			}
			if strings.TrimSpace(v) != "" {
				seen[k] = true
				m.add("PDF", "Info", k, v)
			}
		}
		for off := 0; ; {
			i := bytes.Index(t[off:], []byte("<x:xmpmeta"))
			if i < 0 {
				break
			}
			i += off
			j := bytes.Index(t[i:], []byte("</x:xmpmeta>"))
			if j < 0 {
				break
			}
			m.addXMP(t[i : i+j+12])
			off = i + j
		}
	}
	m.Blocks = append(m.Blocks, fmt.Sprintf("%d stream(s), %d metadata/object stream(s) inflated", streams, inflated))
	if c := bytes.Count(b, []byte("%%EOF")); c > 1 {
		m.add("PDF", "", "IncrementalUpdates", fmt.Sprintf("%d revisions (earlier versions remain inside the file)", c))
	}
}

// ---- OOXML / ODF ----

var (
	reXMLAuthor = regexp.MustCompile(`\b(?:w:author|author|w15:author)="([^"]+)"`)
	reXMLElem   = regexp.MustCompile(`(?s)<([A-Za-z0-9]+:)?(creator|lastModifiedBy|Company|Manager|Template|Application|AppVersion|TotalTime|Revision|revision|initial-creator|generator|editing-duration|editing-cycles|creation-date|created|modified|lastPrinted|HyperlinkBase|print-date|printed-by|title|subject|keywords|description|category)(?:\s[^>]*)?>([^<]*)</`)
	reAuthorEl  = regexp.MustCompile(`<author>([^<]+)</author>`)
	reCmtAuthor = regexp.MustCompile(`<p:cmAuthor[^>]*\bname="([^"]+)"`)
)

func xmlUnescape(s string) string {
	r := strings.NewReplacer("&amp;", "&", "&lt;", "<", "&gt;", ">", "&quot;", `"`, "&apos;", "'")
	return r.Replace(s)
}

func readZip(b []byte) (*zip.Reader, error) { return zip.NewReader(bytes.NewReader(b), int64(len(b))) }

func zipRead(f *zip.File, limit int64) []byte {
	rc, err := f.Open()
	if err != nil {
		return nil
	}
	defer rc.Close()
	d, _ := io.ReadAll(io.LimitReader(rc, limit))
	return d
}

// authorParts are document parts whose author attributes name real people.
func authorPart(n string) bool {
	return n == "word/document.xml" || n == "word/comments.xml" || n == "word/people.xml" ||
		strings.HasPrefix(n, "xl/comments") || strings.HasPrefix(n, "xl/threadedComments") ||
		n == "ppt/commentAuthors.xml" || n == "xl/persons/person.xml" || n == "word/commentsExtended.xml"
}

func parseOffice(b []byte, m *Meta) {
	zr, err := readZip(b)
	if err != nil {
		m.warn("zip: %v", err)
		return
	}
	authors := map[string]int{}
	for _, f := range zr.File {
		n := f.Name
		switch {
		case n == "docProps/core.xml" || n == "docProps/app.xml" || n == "meta.xml" || n == "docProps/custom.xml":
			d := zipRead(f, 4<<20)
			for _, mm := range reXMLElem.FindAllSubmatch(d, -1) {
				k := string(mm[2])
				m.add("Office", n, k, xmlUnescape(string(mm[3])))
			}
			if n == "docProps/custom.xml" {
				m.add("Office", n, "CustomProperties", fmt.Sprintf("%d propert(ies)", bytes.Count(d, []byte("<property "))))
			}
		case strings.HasPrefix(n, "docProps/thumbnail") || n == "Thumbnails/thumbnail.png":
			m.add("Office", n, "Thumbnail", humanBytes(int(f.UncompressedSize64)))
			m.thumb = zipRead(f, 8<<20)
		case authorPart(n):
			d := zipRead(f, 64<<20)
			for _, mm := range reXMLAuthor.FindAllSubmatch(d, -1) {
				authors[xmlUnescape(string(mm[1]))]++
			}
			for _, mm := range reAuthorEl.FindAllSubmatch(d, -1) {
				authors[xmlUnescape(string(mm[1]))]++
			}
			for _, mm := range reCmtAuthor.FindAllSubmatch(d, -1) {
				authors[xmlUnescape(string(mm[1]))]++
			}
		case n == "content.xml" && m.Format == "ODF":
			d := zipRead(f, 64<<20)
			for _, mm := range regexp.MustCompile(`<dc:creator>([^<]+)</dc:creator>`).FindAllSubmatch(d, -1) {
				authors[xmlUnescape(string(mm[1]))]++
			}
		}
	}
	var names []string
	for a, c := range authors {
		names = append(names, fmt.Sprintf("%s (%d)", a, c))
	}
	sort.Strings(names)
	if len(names) > 0 {
		m.add("Office", "revisions", "RevisionAndCommentAuthors", strings.Join(names, ", "))
	}
	m.Blocks = append(m.Blocks, fmt.Sprintf("%d zip entries", len(zr.File)))
	m.Scrubbable = true
}

// ====================================================================
//  ANALYSIS
// ====================================================================

func readMeta(path string, b []byte) *Meta {
	m := &Meta{Path: path, Format: detectFormat(b, path), Size: int64(len(b)), Tags: []Tag{}, Findings: []Finding{},
		Blocks: []string{}, nums: map[string][]float64{}}
	func() {
		defer func() {
			if r := recover(); r != nil {
				m.warn("parser stopped on malformed data: %v", r)
			}
		}()
		switch m.Format {
		case "JPEG":
			parseJPEG(b, m)
		case "PNG":
			parsePNG(b, m)
		case "WebP":
			parseWebP(b, m)
		case "GIF":
			parseGIF(b, m)
		case "TIFF":
			if err := parseTIFF(b, m); err != nil {
				m.warn("%v", err)
			}
			m.thumb = nil
		case "PDF":
			parsePDF(b, m)
		case "OOXML", "ODF":
			parseOffice(b, m)
		case "HEIC", "MP4", "MOV":
			parseBMFF(b, m)
		case "ZIP":
			m.warn("plain ZIP archive — not a document format OExifX reads")
		default:
			m.warn("unrecognised format")
		}
		m.finishGPS()
	}()
	if m.Width == 0 {
		if cfg, _, err := image.DecodeConfig(bytes.NewReader(b)); err == nil {
			m.Width, m.Height = cfg.Width, cfg.Height
		}
	}
	m.Findings = analyze(m)
	return m
}

// Finding is one privacy exposure.
type Finding struct {
	RuleID   string `json:"rule_id"`
	Severity string `json:"severity"`
	Title    string `json:"title"`
	Evidence string `json:"evidence"`
	Detail   string `json:"detail,omitempty"`
	Fix      string `json:"fix,omitempty"`
}

type ruleInfo struct{ ID, Sev, Title, Fix string }

var ruleCatalog = []ruleInfo{
	{"META-GPS", SevHigh, "GPS location embedded", "Scrub before sharing; disable location tagging in the camera app."},
	{"META-SERIAL", SevHigh, "Device serial number / unique ID", "Serials link every photo to one physical device — scrub them."},
	{"META-PATH", SevHigh, "Local file path with a user name", "Paths reveal user names and folder layout; scrub XMP history / templates."},
	{"META-THUMB-MISMATCH", SevHigh, "Embedded thumbnail differs from the image", "The thumbnail may still show what was cropped or edited out — scrub it."},
	{"META-PERSON", SevMedium, "Person name (author / owner / editor)", "Remove author fields unless attribution is intended."},
	{"META-REVISION-AUTHORS", SevMedium, "Track-change / comment authors", "Accept changes, delete comments and run document inspection, or scrub."},
	{"META-CONTACT", SevMedium, "E-mail address in metadata", "Remove contact details from metadata."},
	{"META-PLACE", SevMedium, "Place name (city / location fields)", "Location text is as revealing as GPS for many photos."},
	{"META-THUMB", SevMedium, "Embedded thumbnail / preview", "Previews can lag behind edits; scrub them with the rest."},
	{"META-HISTORY", SevMedium, "Editing history / document lineage", "XMP history and document IDs link copies to their originals."},
	{"META-PDF-REVISIONS", SevMedium, "PDF incremental updates", "Earlier versions are still inside the file — re-save / flatten the PDF."},
	{"META-DEVICE", SevLow, "Camera / device make and model", "Narrows down who could have taken the picture."},
	{"META-SOFTWARE", SevLow, "Software / tool fingerprint", "Tool and version strings help fingerprint the author's environment."},
	{"META-TIME", SevLow, "Capture time and timezone", "Timestamps (and UTC offsets) date the content and hint at location."},
	{"META-COMMENT", SevLow, "Free-text comment / description", "Check comments for internal notes before publishing."},
	{"META-COMPANY", SevLow, "Organisation / manager field", "Company and manager fields identify the organisation."},
	{"META-MAKERNOTE", SevLow, "Vendor MakerNote block", "Undecoded vendor data often holds more serials and settings — scrub it."},
}

var ruleByID = func() map[string]ruleInfo {
	m := map[string]ruleInfo{}
	for _, r := range ruleCatalog {
		m[r.ID] = r
	}
	return m
}()

func newFinding(id, ev, detail string) Finding {
	r := ruleByID[id]
	return Finding{RuleID: id, Severity: r.Sev, Title: r.Title, Evidence: ev, Detail: detail, Fix: r.Fix}
}

var (
	reUserPath = regexp.MustCompile(`(?i)(?:[A-Z]:\\(?:Users|Documents and Settings)\\[^\\/"<>|]+|/(?:Users|home)/[^/\s"<>]+|\\\\[A-Za-z0-9._-]+\\[^\\\s"<>]+)`)
	reEmail    = regexp.MustCompile(`[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}`)
)

var fileExts = set("png", "jpg", "jpeg", "gif", "svg", "webp", "tif", "tiff", "bmp", "ico", "psd", "pdf", "html", "js", "css", "json", "xml", "txt")

// tag name sets, compared case-insensitively against Tag.Name
var (
	serialTags  = set("BodySerialNumber", "LensSerialNumber", "CameraSerialNumber", "aux:SerialNumber", "aux:LensSerialNumber", "ImageUniqueID", "exifEX:BodySerialNumber", "exifEX:LensSerialNumber")
	personTags  = set("Artist", "XPAuthor", "CameraOwnerName", "Copyright", "By-line", "Writer-Editor", "Contact", "dc:creator", "dc:rights", "photoshop:AuthorsPosition", "photoshop:CaptionWriter", "xmpRights:Owner", "Author", "creator", "lastModifiedBy", "initial-creator", "printed-by", "aux:OwnerName", "exifEX:CameraOwnerName", "Iptc4xmpCore:CreatorContactInfo", "CopyrightNotice")
	placeTags   = set("City", "Sub-location", "Province-State", "Country", "photoshop:City", "photoshop:State", "photoshop:Country", "Iptc4xmpCore:Location", "Iptc4xmpExt:LocationShown", "Iptc4xmpExt:City")
	deviceTags  = set("Make", "Model", "LensMake", "LensModel", "UniqueCameraModel", "tiff:Make", "tiff:Model", "aux:Lens", "exifEX:LensModel", "HostComputer")
	softTags    = set("Software", "Encoder", "Creator", "Producer", "xmp:CreatorTool", "pdf:Producer", "Application", "AppVersion", "generator", "OriginatingProgram", "ProgramVersion", "Template")
	timeTags    = set("CreateDate", "ModifyDate", "DateTimeOriginal", "DateTimeDigitized", "DateTime", "OffsetTimeOriginal", "OffsetTime", "CreationDate", "ModDate", "xmp:CreateDate", "xmp:ModifyDate", "photoshop:DateCreated", "DateCreated", "created", "modified", "creation-date", "LastModified")
	commentTags = set("Title", "Information", "ImageDescription", "UserComment", "XPComment", "XPSubject", "XPTitle", "XPKeywords", "Comment", "Caption-Abstract", "dc:description", "Description", "Keywords", "description")
	historyTags = set("xmpMM:History", "xmpMM:DocumentID", "xmpMM:OriginalDocumentID", "xmpMM:InstanceID", "xmpMM:DerivedFrom", "stRef:documentID", "Revision", "revision", "editing-cycles", "TotalTime", "editing-duration", "photoshop:DocumentAncestors")
	companyTags = set("Company", "Manager", "HyperlinkBase")
)

func set(xs ...string) map[string]bool {
	m := map[string]bool{}
	for _, x := range xs {
		m[strings.ToLower(x)] = true
	}
	return m
}

func in(s map[string]bool, name string) bool { return s[strings.ToLower(name)] }

// analyze turns tags into privacy findings (one per rule, evidence merged).
func analyze(m *Meta) []Finding {
	type acc struct {
		ev   []string
		seen map[string]bool
	}
	got := map[string]*acc{}
	hit := func(id, ev string) {
		a := got[id]
		if a == nil {
			a = &acc{seen: map[string]bool{}}
			got[id] = a
		}
		if !a.seen[ev] {
			a.seen[ev] = true
			a.ev = append(a.ev, ev)
		}
	}
	placeholder := func(v string) bool {
		l := strings.ToLower(strings.TrimSpace(v))
		return l == "" || l == "unknown" || l == "none" || l == "-" || l == "0" || l == "pt0s" || strings.HasPrefix(l, "(")
	}
	for _, t := range m.Tags {
		v, n := t.Value, t.Name
		short := n + "=" + trunc(strings.ReplaceAll(v, "\n", " "), 60)
		switch {
		case in(serialTags, n) && !placeholder(v) && strings.Trim(v, "0 ") != "":
			hit("META-SERIAL", short)
		case in(personTags, n) && !placeholder(v):
			hit("META-PERSON", short)
		case n == "RevisionAndCommentAuthors":
			hit("META-REVISION-AUTHORS", trunc(v, 120))
		case in(placeTags, n) && !placeholder(v):
			hit("META-PLACE", short)
		case in(deviceTags, n) && !placeholder(v):
			hit("META-DEVICE", short)
		case in(softTags, n) && !placeholder(v):
			hit("META-SOFTWARE", short)
		case in(timeTags, n) && !placeholder(v) && !strings.HasPrefix(v, "0000"):
			hit("META-TIME", short)
		case in(commentTags, n) && !placeholder(v) && !isBoilerplate(v):
			hit("META-COMMENT", short)
		case in(historyTags, n) && !placeholder(v) && !(v == "1" && (strings.EqualFold(n, "revision") || n == "editing-cycles")):
			hit("META-HISTORY", short)
		case in(companyTags, n) && !placeholder(v):
			hit("META-COMPANY", short)
		case n == "MakerNote":
			hit("META-MAKERNOTE", v)
		case n == "IncrementalUpdates":
			hit("META-PDF-REVISIONS", v)
		}
		if p := reUserPath.FindString(v); p != "" {
			hit("META-PATH", n+": "+trunc(p, 70))
		}
		for _, e := range reEmail.FindAllString(v, 3) {
			// "icon@2x.png" is a file name, not an address
			if tld := strings.ToLower(e[strings.LastIndexByte(e, '.')+1:]); !fileExts[tld] {
				hit("META-CONTACT", n+": "+e)
				break
			}
		}
	}
	if m.GPS != nil {
		ev := m.GPS.String()
		if m.GPS.Time != "" {
			ev += " @ " + m.GPS.Time
		}
		hit("META-GPS", ev)
	}
	tiny := false // a 1×1 placeholder (what --scrub leaves in documents) is no preview
	if cfg, _, err := image.DecodeConfig(bytes.NewReader(m.thumb)); err == nil && cfg.Width <= 2 && cfg.Height <= 2 {
		tiny = true
	}
	if len(m.thumb) > 0 && !tiny {
		id, ev := "META-THUMB", humanBytes(len(m.thumb))+" preview"
		if cfg, _, err := image.DecodeConfig(bytes.NewReader(m.thumb)); err == nil && m.Width > 0 && m.Height > 0 && cfg.Height > 0 {
			ev = fmt.Sprintf("%dx%d preview of a %dx%d image", cfg.Width, cfg.Height, m.Width, m.Height)
			ra, rt := float64(m.Width)/float64(m.Height), float64(cfg.Width)/float64(cfg.Height)
			// a rotated thumbnail keeps the inverse ratio; anything else means the image was cropped
			if math.Abs(ra-rt)/ra > 0.04 && math.Abs(1/ra-rt)*ra > 0.04 && m.Format != "OOXML" && m.Format != "ODF" {
				id = "META-THUMB-MISMATCH"
				ev += fmt.Sprintf(" — aspect %.2f vs %.2f", rt, ra)
			}
		}
		hit(id, ev)
	}
	var out []Finding
	for _, r := range ruleCatalog {
		if a := got[r.ID]; a != nil {
			ev := strings.Join(a.ev, " · ")
			detail := ""
			if r.ID == "META-GPS" {
				detail = m.GPS.MapURL()
			}
			if len(a.ev) > 4 {
				ev = strings.Join(a.ev[:4], " · ") + fmt.Sprintf(" · +%d more", len(a.ev)-4)
			}
			out = append(out, newFinding(r.ID, ev, detail))
		}
	}
	if out == nil {
		out = []Finding{}
	}
	return out
}

// isBoilerplate filters descriptions cameras write by default.
func isBoilerplate(v string) bool {
	l := strings.ToLower(strings.TrimSpace(v))
	for _, b := range []string{"olympus digital camera", "sony dsc", "default", "screenshot", "digital camera", "created with gimp"} {
		if l == b {
			return true
		}
	}
	return len(strings.Trim(l, " ._-")) == 0
}

func exposure(fs []Finding) (int, string) {
	score := 100
	for _, f := range fs {
		score -= map[string]int{SevCritical: 40, SevHigh: 25, SevMedium: 10, SevLow: 3}[f.Severity]
	}
	score = max(score, 0)
	g := "F"
	switch {
	case score >= 97:
		g = "A+"
	case score >= 90:
		g = "A"
	case score >= 80:
		g = "B"
	case score >= 65:
		g = "C"
	case score >= 50:
		g = "D"
	}
	return score, g
}

func gradeColor(g string) string {
	switch g {
	case "A+", "A":
		return col(g, GRN+B)
	case "B":
		return col(g, CY+B)
	case "C":
		return col(g, YLW+B)
	case "D":
		return col(g, OR+B)
	}
	return col(g, R+B)
}

// ====================================================================
//  SCRUBBER
// ====================================================================

type scrubOpts struct {
	keepICC         bool
	keepOrientation bool
}

var sopt = scrubOpts{keepICC: true, keepOrientation: true}

type scrubResult struct {
	Out      []byte
	Removed  []string
	Kept     []string
	Verified string
	blanked  [][2]int // HEIF metadata item extents overwritten inside mdat
}

// minimalExif builds an APP1 Exif payload holding only Orientation.
func minimalExif(orient uint16) []byte {
	b := []byte("Exif\x00\x00II*\x00\x08\x00\x00\x00")
	b = append(b, 1, 0)                         // one entry
	b = append(b, 0x12, 0x01, 3, 0, 1, 0, 0, 0) // 0x0112 SHORT count 1
	b = append(b, byte(orient), byte(orient>>8), 0, 0)
	return append(b, 0, 0, 0, 0) // no next IFD
}

func scrubJPEG(b []byte, m *Meta) (scrubResult, error) {
	segs, err := jpegSegments(b)
	if err != nil {
		return scrubResult{}, err
	}
	var r scrubResult
	out := []byte{0xFF, 0xD8}
	orient := uint16(1)
	if o := m.nums["IFD0:0x0112"]; len(o) == 1 && o[0] >= 1 && o[0] <= 8 {
		orient = uint16(o[0])
	}
	wroteOrient := false
	for _, s := range segs {
		d, keep, what := s.data, true, ""
		switch {
		case s.marker == 0xE1:
			keep, what = false, "APP1 "+map[bool]string{true: "Exif", false: "XMP"}[bytes.HasPrefix(d, []byte("Exif"))]
		case s.marker == 0xED:
			keep, what = false, "APP13 Photoshop/IPTC"
		case s.marker == 0xFE:
			keep, what = false, "COM comment"
		case s.marker == 0xE2 && bytes.HasPrefix(d, []byte("ICC_PROFILE")):
			keep, what = sopt.keepICC, "APP2 ICC profile"
		case s.marker == 0xE0 || s.marker == 0xEE:
			keep, what = true, jpegMarkerName[s.marker]
		case s.marker > 0xE0 && s.marker <= 0xEF:
			keep, what = false, fmt.Sprintf("APP%d", s.marker-0xE0)
		}
		if !keep {
			r.Removed = append(r.Removed, fmt.Sprintf("%s (%s)", what, humanBytes(len(d))))
			continue
		}
		if what != "" {
			r.Kept = append(r.Kept, what)
		}
		// orientation goes right after APP0/JFIF (or first) so viewers still rotate
		if !wroteOrient && sopt.keepOrientation && orient != 1 && s.marker != 0xE0 {
			e := minimalExif(orient)
			out = append(out, 0xFF, 0xE1, byte((len(e)+2)>>8), byte(len(e)+2))
			out = append(out, e...)
			r.Kept = append(r.Kept, fmt.Sprintf("Orientation=%d (minimal Exif)", orient))
			wroteOrient = true
		}
		out = append(out, b[s.start:s.end]...)
	}
	r.Out = out
	return r, nil
}

func pngChunkBytes(typ string, data []byte) []byte {
	out := make([]byte, 8, 12+len(data))
	binary.BigEndian.PutUint32(out, uint32(len(data)))
	copy(out[4:], typ)
	out = append(out, data...)
	return binary.BigEndian.AppendUint32(out, crc32.ChecksumIEEE(out[4:]))
}

func scrubPNG(b []byte) (scrubResult, error) {
	cs, err := pngChunks(b)
	if err != nil {
		return scrubResult{}, err
	}
	var r scrubResult
	out := append([]byte(nil), b[:8]...)
	for _, c := range cs {
		switch c.typ {
		case "tEXt", "zTXt", "iTXt", "eXIf", "tIME":
			k := ""
			if c.typ != "eXIf" && c.typ != "tIME" {
				kk, _, _ := bytes.Cut(c.data, []byte{0})
				k = " " + latin1(kk)
			}
			r.Removed = append(r.Removed, fmt.Sprintf("%s%s (%s)", c.typ, k, humanBytes(len(c.data))))
			continue
		case "iCCP":
			if !sopt.keepICC {
				r.Removed = append(r.Removed, "iCCP colour profile")
				continue
			}
			r.Kept = append(r.Kept, "iCCP colour profile")
		}
		out = append(out, b[c.start:c.end]...)
	}
	r.Out = out
	return r, nil
}

func scrubWebP(b []byte) (scrubResult, error) {
	cs, err := webpChunks(b)
	if err != nil {
		return scrubResult{}, err
	}
	var r scrubResult
	out := append([]byte(nil), b[:12]...)
	vp8x := -1
	for _, c := range cs {
		switch c.id {
		case "EXIF", "XMP ":
			r.Removed = append(r.Removed, fmt.Sprintf("%s (%s)", strings.TrimSpace(c.id), humanBytes(len(c.data))))
			continue
		case "ICCP":
			if !sopt.keepICC {
				r.Removed = append(r.Removed, "ICCP colour profile")
				continue
			}
		case "VP8X":
			vp8x = len(out)
		}
		out = append(out, b[c.start:c.end]...)
	}
	if vp8x >= 0 {
		out[vp8x+8] &^= 0x08 | 0x04 // EXIF + XMP flags
		if !sopt.keepICC {
			out[vp8x+8] &^= 0x20
		}
	}
	binary.LittleEndian.PutUint32(out[4:], uint32(len(out)-8))
	r.Out = out
	return r, nil
}

func scrubGIF(b []byte) (scrubResult, error) {
	bs, err := gifBlocks(b)
	if err != nil {
		return scrubResult{}, err
	}
	var r scrubResult
	var out []byte
	for _, x := range bs {
		if x.kind == "comment" || x.kind == "xmp" {
			r.Removed = append(r.Removed, fmt.Sprintf("%s extension (%s)", x.kind, humanBytes(x.end-x.start)))
			continue
		}
		out = append(out, b[x.start:x.end]...)
	}
	r.Out = out
	return r, nil
}

var (
	reBlankElem = regexp.MustCompile(`(?s)(<(?:[A-Za-z0-9]+:)?(?:creator|lastModifiedBy|Company|Manager|Template|HyperlinkBase|initial-creator|printed-by)(?:\s[^>]*)?>)[^<]*(</)`)
	reAuthAttr  = regexp.MustCompile(`\b((?:w:|w15:)?author|w:initials|name)="[^"]*"`)
	reAuthorTxt = regexp.MustCompile(`<author>[^<]*</author>`)
	// numeric history fields cannot be emptied (schema): reset them
	resetElems = []struct {
		re  *regexp.Regexp
		val string
	}{
		{regexp.MustCompile(`(<(?:[A-Za-z0-9]+:)?(?:TotalTime)(?:\s[^>]*)?>)[^<]*(</)`), "0"},
		{regexp.MustCompile(`(<(?:[A-Za-z0-9]+:)?(?:revision|Revision|editing-cycles)(?:\s[^>]*)?>)[^<]*(</)`), "1"},
		{regexp.MustCompile(`(<(?:[A-Za-z0-9]+:)?(?:editing-duration)(?:\s[^>]*)?>)[^<]*(</)`), "PT0S"},
	}
)

// scrubOffice rewrites the zip: personal properties blanked and revision /
// comment authors renamed "Author" (what Word's Document Inspector does).
// Every other entry is copied byte for byte.
func scrubOffice(b []byte, format string) (scrubResult, error) {
	zr, err := readZip(b)
	if err != nil {
		return scrubResult{}, err
	}
	var r scrubResult
	var buf bytes.Buffer
	zw := zip.NewWriter(&buf)
	for _, f := range zr.File {
		n := f.Name
		var newData []byte
		switch {
		case n == "docProps/core.xml" || n == "docProps/app.xml" || n == "meta.xml":
			d := zipRead(f, 16<<20)
			nd := reBlankElem.ReplaceAll(d, []byte("${1}${2}"))
			for _, x := range resetElems {
				nd = x.re.ReplaceAll(nd, []byte("${1}"+x.val+"${2}"))
			}
			if !bytes.Equal(d, nd) {
				r.Removed = append(r.Removed, n+": personal properties")
			}
			newData = nd
		case strings.HasPrefix(n, "docProps/thumbnail") || n == "Thumbnails/thumbnail.png":
			// a 1×1 image of the same type: no relationship or content-type edits needed
			blank := image.NewGray(image.Rect(0, 0, 1, 1))
			switch strings.ToLower(filepath.Ext(n)) {
			case ".png":
				newData = encodePNG(blank)
			case ".jpg", ".jpeg":
				newData = encodeJPEG(blank)
			}
			if newData != nil {
				r.Removed = append(r.Removed, n+": page preview (replaced by a 1×1 image)")
			}
		case authorPart(n):
			d := zipRead(f, 256<<20)
			nd := reAuthAttr.ReplaceAllFunc(d, func(x []byte) []byte {
				k, _, _ := bytes.Cut(x, []byte("="))
				if string(k) == "name" && n != "ppt/commentAuthors.xml" && n != "word/people.xml" {
					return x
				}
				if bytes.HasSuffix(k, []byte("initials")) {
					return append(k, []byte(`="A"`)...)
				}
				return append(k, []byte(`="Author"`)...)
			})
			nd = reAuthorTxt.ReplaceAll(nd, []byte("<author>Author</author>"))
			if !bytes.Equal(d, nd) {
				r.Removed = append(r.Removed, n+": revision / comment authors")
				newData = nd
			}
		}
		if newData == nil {
			if err := zw.Copy(f); err != nil {
				return r, err
			}
			continue
		}
		h := f.FileHeader
		h.CompressedSize64, h.UncompressedSize64, h.CRC32 = 0, 0, 0
		w, err := zw.CreateHeader(&h)
		if err != nil {
			return r, err
		}
		if _, err := w.Write(newData); err != nil {
			return r, err
		}
	}
	if err := zw.Close(); err != nil {
		return r, err
	}
	r.Out = buf.Bytes()
	r.Kept = append(r.Kept, "document content, title / description, application name and dates")
	return r, nil
}

// scrub removes metadata from a supported file and verifies the result.
func scrub(b []byte, m *Meta) (scrubResult, error) {
	var r scrubResult
	var err error
	switch m.Format {
	case "JPEG":
		r, err = scrubJPEG(b, m)
	case "PNG":
		r, err = scrubPNG(b)
	case "WebP":
		r, err = scrubWebP(b)
	case "GIF":
		r, err = scrubGIF(b)
	case "OOXML", "ODF":
		r, err = scrubOffice(b, m.Format)
	case "MP4", "MOV", "HEIC":
		r, err = scrubBMFF(b, m)
	case "PDF":
		return r, errors.New("PDF scrubbing is not supported: metadata also lives in incremental updates and object streams — re-export the PDF or use qpdf/exiftool")
	case "TIFF":
		return r, errors.New("TIFF scrubbing is not supported: metadata shares IFDs with the image data")
	default:
		return r, fmt.Errorf("%s scrubbing is not supported", strings.ToLower(defaultStr(m.Format, "this format")))
	}
	if err != nil {
		return r, err
	}
	r.Verified, err = verifyScrub(b, r.Out, m.Format, r.blanked)
	return r, err
}

func defaultStr(s, d string) string {
	if s == "" {
		return d
	}
	return s
}

// verifyScrub proves nothing but metadata changed: image data bytes equal
// and decoded pixels equal (JPEG / PNG / GIF via the stdlib decoders).
func verifyScrub(orig, clean []byte, format string, blanked [][2]int) (string, error) {
	var parts []string
	switch format {
	case "JPEG":
		so, e1 := jpegSegments(orig)
		sc, e2 := jpegSegments(clean)
		if e1 != nil || e2 != nil || len(so) == 0 || len(sc) == 0 {
			return "", errors.New("verification: cannot re-read the cleaned JPEG")
		}
		a, b := so[len(so)-1], sc[len(sc)-1]
		if !bytes.Equal(orig[a.start:a.end], clean[b.start:b.end]) {
			return "", errors.New("verification: image data changed")
		}
		parts = append(parts, "scan data byte-identical")
	case "PNG":
		var ia, ib []byte
		co, _ := pngChunks(orig)
		cc, err := pngChunks(clean)
		if err != nil {
			return "", fmt.Errorf("verification: %v", err)
		}
		for _, c := range co {
			if c.typ == "IDAT" {
				ia = append(ia, c.data...)
			}
		}
		for _, c := range cc {
			if !c.crcOK {
				return "", errors.New("verification: bad CRC in output")
			}
			if c.typ == "IDAT" {
				ib = append(ib, c.data...)
			}
		}
		if !bytes.Equal(ia, ib) {
			return "", errors.New("verification: IDAT changed")
		}
		parts = append(parts, "IDAT byte-identical, CRCs valid")
	case "WebP":
		if _, err := webpChunks(clean); err != nil {
			return "", fmt.Errorf("verification: %v", err)
		}
		parts = append(parts, "RIFF structure valid")
	case "MP4", "MOV", "HEIC":
		v, err := verifyBMFF(orig, clean, blanked)
		if err != nil {
			return "", err
		}
		parts = append(parts, v)
	case "OOXML", "ODF":
		zr, err := readZip(clean)
		if err != nil {
			return "", fmt.Errorf("verification: %v", err)
		}
		for _, f := range zr.File {
			rc, err := f.Open()
			if err != nil {
				return "", fmt.Errorf("verification: %s: %v", f.Name, err)
			}
			_, err = io.Copy(io.Discard, rc)
			rc.Close()
			if err != nil {
				return "", fmt.Errorf("verification: %s: %v", f.Name, err)
			}
		}
		parts = append(parts, fmt.Sprintf("zip valid, %d entries readable", len(zr.File)))
	}
	if format == "JPEG" || format == "PNG" || format == "GIF" {
		ia, _, e1 := image.Decode(bytes.NewReader(orig))
		ib, _, e2 := image.Decode(bytes.NewReader(clean))
		switch {
		case e1 != nil:
			parts = append(parts, "pixels not compared (original does not decode in Go)")
		case e2 != nil:
			return "", fmt.Errorf("verification: cleaned file does not decode: %v", e2)
		case !samePixels(ia, ib):
			return "", errors.New("verification: decoded pixels differ")
		default:
			parts = append(parts, "decoded pixels identical")
		}
	}
	return strings.Join(parts, " · "), nil
}

func samePixels(a, b image.Image) bool {
	if a.Bounds() != b.Bounds() {
		return false
	}
	bd := a.Bounds()
	step := max(1, bd.Dx()*bd.Dy()/250000) // sample big images
	i := 0
	for y := bd.Min.Y; y < bd.Max.Y; y++ {
		for x := bd.Min.X; x < bd.Max.X; x++ {
			if i++; i%step != 0 {
				continue
			}
			r1, g1, b1, a1 := a.At(x, y).RGBA()
			r2, g2, b2, a2 := b.At(x, y).RGBA()
			if r1 != r2 || g1 != g2 || b1 != b2 || a1 != a2 {
				return false
			}
		}
	}
	return true
}

func cleanName(p string) string {
	ext := filepath.Ext(p)
	return strings.TrimSuffix(p, ext) + ".clean" + ext
}

// ====================================================================
//  ISO-BMFF: MP4 / MOV / M4A / 3GP / HEIC / AVIF
// ====================================================================

type bmffBox struct {
	typ        string
	start, end int // whole box
	body       int // payload start (after header / full-box fields handled by caller)
	path       string
}

// bmffContainers: boxes whose payload is a list of child boxes.
var bmffContainers = map[string]bool{"moov": true, "trak": true, "mdia": true, "minf": true, "stbl": true, "udta": true,
	"edts": true, "dinf": true, "mvex": true, "moof": true, "traf": true, "ilst": true, "iprp": true, "ipco": true,
	"meco": true, "tref": true, "sinf": true, "schi": true, "gmhd": true}

// walkBMFF visits every box (depth-first). meta is a FullBox in ISO files
// but a plain container in QuickTime; both layouts are detected.
func walkBMFF(b []byte, start, end int, path string, depth int, visit func(bx bmffBox) bool) error {
	for i := start; i+8 <= end; {
		size := int64(binary.BigEndian.Uint32(b[i:]))
		typ := latin1(b[i+4 : i+8]) // QuickTime "©xyz" atoms use byte 0xA9
		hdr := 8
		switch size {
		case 1:
			if i+16 > end {
				return fmt.Errorf("box %q at %d: large size truncated", typ, i)
			}
			size, hdr = int64(binary.BigEndian.Uint64(b[i+8:])), 16
		case 0:
			size = int64(end - i)
		}
		if size < int64(hdr) || int64(i)+size > int64(end) {
			return fmt.Errorf("box %q at %d overruns its parent", typ, i)
		}
		bx := bmffBox{typ: typ, start: i, end: i + int(size), body: i + hdr, path: path + "/" + typ}
		descend := visit(bx)
		if descend && depth < 16 {
			cs := bx.body
			switch {
			case typ == "meta":
				// FullBox (ISO / HEIF) when the 4 bytes after the header are version/flags = 0
				// and the next thing is a box ("hdlr" usually); QuickTime meta has no such field.
				if cs+12 <= bx.end && binary.BigEndian.Uint32(b[cs:]) == 0 && isFourCC(b[cs+8:cs+12]) {
					cs += 4
				}
				if err := walkBMFF(b, cs, bx.end, bx.path, depth+1, visit); err != nil {
					return err
				}
			case typ == "iinf" || typ == "iref" || typ == "dref":
				// FullBox + entry count, then boxes
				skip := 4 + 2
				if typ == "iinf" && cs+4 <= bx.end && b[cs] > 0 {
					skip = 4 + 4
				}
				if typ == "dref" {
					skip = 8
				}
				if cs+skip <= bx.end {
					walkBMFF(b, cs+skip, bx.end, bx.path, depth+1, visit)
				}
			case bmffContainers[typ] || strings.HasSuffix(path, "/ilst"): // ilst items hold 'data' boxes
				if err := walkBMFF(b, cs, bx.end, bx.path, depth+1, visit); err != nil {
					return err
				}
			}
		}
		i = bx.end
	}
	return nil
}

func isFourCC(b []byte) bool {
	for _, c := range b {
		if c < 0x20 || c > 0x7e {
			return false
		}
	}
	return len(b) == 4
}

// mac epoch: seconds since 1904-01-01
func macTime(secs uint64) string {
	if secs == 0 {
		return ""
	}
	t := time.Date(1904, 1, 1, 0, 0, 0, 0, time.UTC).Add(time.Duration(secs) * time.Second)
	if t.Year() < 1971 || t.Year() > 2100 {
		return ""
	}
	return t.Format("2006-01-02 15:04:05 UTC")
}

var qtTags = map[string]string{"©xyz": "GPSCoordinates", "©mak": "Make", "©mod": "Model", "©swr": "Software", "©day": "CreationDate",
	"©nam": "Title", "©ART": "Artist", "©cmt": "Comment", "©too": "Encoder", "©aut": "Author", "©cpy": "Copyright",
	"©des": "Description", "©inf": "Information", "©req": "Requirements", "©fmt": "Format", "©wrt": "Writer",
	"©enc": "EncodedBy", "©alb": "Album", "©gen": "Genre", "©dir": "Director", "©prd": "Producer", "©src": "Source"}

var appleKeys = map[string]string{
	"com.apple.quicktime.location.ISO6709": "GPSCoordinates", "com.apple.quicktime.make": "Make",
	"com.apple.quicktime.model": "Model", "com.apple.quicktime.software": "Software",
	"com.apple.quicktime.creationdate": "CreationDate", "com.apple.quicktime.location.accuracy.horizontal": "GPSHPositioningError",
	"com.apple.quicktime.author": "Author", "com.apple.quicktime.artist": "Artist", "com.apple.quicktime.comment": "Comment",
	"com.apple.quicktime.description": "Description", "com.apple.quicktime.title": "Title",
	"com.apple.quicktime.content.identifier": "ContentIdentifier", "com.android.version": "Software",
	"com.android.capture.fps": "CaptureFPS", "com.android.manufacturer": "Make", "com.android.model": "Model",
	// plain keys written by ffmpeg -movflags use_metadata_tags and others
	"make": "Make", "model": "Model", "artist": "Artist", "author": "Author", "comment": "Comment", "title": "Title",
	"encoder": "Encoder", "location": "GPSCoordinates", "location-eng": "GPSCoordinates", "description": "Description",
	"copyright": "Copyright", "creation_time": "CreationDate", "date": "CreationDate",
}

var reISO6709 = regexp.MustCompile(`^([+-]\d+(?:\.\d+)?)([+-]\d+(?:\.\d+)?)([+-]\d+(?:\.\d+)?)?`)

// iso6709 parses "+37.3317-122.0302+012.345/" (degrees, decimal form).
func iso6709(s string) *GPSFix {
	m := reISO6709.FindStringSubmatch(strings.TrimSpace(s))
	if m == nil {
		return nil
	}
	lat, _ := strconv.ParseFloat(m[1], 64)
	lon, _ := strconv.ParseFloat(m[2], 64)
	if math.Abs(lat) > 90 || math.Abs(lon) > 180 || lat == 0 && lon == 0 {
		return nil
	}
	g := &GPSFix{Lat: lat, Lon: lon}
	if m[3] != "" {
		a, _ := strconv.ParseFloat(m[3], 64)
		g.Alt = &a
	}
	return g
}

// dataValue decodes an ilst 'data' atom payload (type indicator + locale).
func dataValue(d []byte) string {
	if len(d) < 8 {
		return ""
	}
	typ := binary.BigEndian.Uint32(d) & 0xFFFFFF
	v := d[8:]
	switch typ {
	case 1, 4: // UTF-8
		return strings.ToValidUTF8(string(v), "?")
	case 2, 5: // UTF-16
		return utf16be(v)
	case 21, 22: // big-endian signed / unsigned int
		var n uint64
		for _, c := range v {
			n = n<<8 | uint64(c)
		}
		return strconv.FormatUint(n, 10)
	case 23:
		if len(v) == 4 {
			return fmtNum(float64(math.Float32frombits(binary.BigEndian.Uint32(v))))
		}
	case 13, 14:
		return fmt.Sprintf("(%s image)", humanBytes(len(v)))
	}
	return fmt.Sprintf("(%s binary)", humanBytes(len(v)))
}

var xmpUUID = []byte{0xBE, 0x7A, 0xCF, 0xCB, 0x97, 0xA9, 0x42, 0xE8, 0x9C, 0x71, 0x99, 0x94, 0x91, 0xE3, 0xAF, 0xAC}

// heifItem collects what iinf / iloc say about one item.
type heifItem struct {
	id      int
	typ     string // Exif | mime | hvc1 | …
	ctype   string // content type for mime items
	method  int    // 0 file offset, 1 idat
	extents [][2]int
}

func parseBMFF(b []byte, m *Meta) {
	if len(b) >= 12 && string(b[4:8]) == "ftyp" {
		brand := strings.TrimSpace(string(b[8:12]))
		m.add("BMFF", "ftyp", "MajorBrand", brand)
	}
	var keys []string // QuickTime mdta key table (1-based in ilst)
	items := map[int]*heifItem{}
	var idat []byte
	mdat := 0
	err := walkBMFF(b, 0, len(b), "", 0, func(bx bmffBox) bool {
		p := bx.body
		d := b[p:bx.end]
		switch bx.typ {
		case "mdat":
			mdat += bx.end - bx.start
			return false
		case "mvhd", "tkhd", "mdhd":
			if len(d) >= 12 && bx.typ == "mvhd" {
				var c, mo uint64
				if d[0] == 1 && len(d) >= 20 {
					c, mo = binary.BigEndian.Uint64(d[4:]), binary.BigEndian.Uint64(d[12:])
				} else {
					c, mo = uint64(binary.BigEndian.Uint32(d[4:])), uint64(binary.BigEndian.Uint32(d[8:]))
				}
				m.add("BMFF", "mvhd", "CreateDate", macTime(c))
				m.add("BMFF", "mvhd", "ModifyDate", macTime(mo))
			}
			if bx.typ == "tkhd" && len(d) >= 84 && m.Width == 0 {
				off := 76
				if d[0] == 1 {
					off = 88
				}
				if off+8 <= len(d) {
					w, h := binary.BigEndian.Uint32(d[off:])>>16, binary.BigEndian.Uint32(d[off+4:])>>16
					if w > 0 && h > 0 {
						m.Width, m.Height = int(w), int(h)
					}
				}
			}
		case "keys":
			if len(d) >= 8 {
				n := int(binary.BigEndian.Uint32(d[4:]))
				q := 8
				for k := 0; k < n && q+8 <= len(d); k++ {
					sz := int(binary.BigEndian.Uint32(d[q:]))
					if sz < 8 || q+sz > len(d) {
						break
					}
					keys = append(keys, string(d[q+8:q+sz]))
					q += sz
				}
			}
		case "data":
			parent := bx.path[:strings.LastIndex(bx.path, "/")]
			name := parent[strings.LastIndex(parent, "/")+1:]
			label := qtTags[name]
			if len(name) == 4 && label == "" {
				if idx := int(binary.BigEndian.Uint32([]byte(name))); idx >= 1 && idx <= len(keys) {
					k := keys[idx-1]
					label = appleKeys[k]
					if label == "" {
						label = k
					}
				} else {
					label = strings.TrimPrefix(name, "©")
				}
			}
			v := dataValue(d)
			m.add("QuickTime", name, label, v)
			if label == "GPSCoordinates" && m.GPS == nil {
				m.GPS = iso6709(v)
			}
		case "uuid":
			if len(d) >= 16 && bytes.Equal(d[:16], xmpUUID) {
				m.addXMP(d[16:])
			}
		case "XMP_":
			m.addXMP(d)
		case "infe":
			parseBMFFItems(bx, b, items)
		case "iloc":
			parseIloc(d, items)
		case "idat":
			idat = d
		case "ispe":
			if len(d) >= 12 && m.Width == 0 {
				m.Width, m.Height = int(binary.BigEndian.Uint32(d[4:])), int(binary.BigEndian.Uint32(d[8:]))
			}
		default:
			// classic QuickTime udta text atoms: ©xxx = len(2) lang(2) text
			if strings.HasPrefix(bx.typ, "©") && strings.Contains(bx.path, "/udta/") && !strings.Contains(bx.path, "/ilst/") && len(d) >= 4 {
				n := int(binary.BigEndian.Uint16(d))
				if 4+n <= len(d) && n > 0 && d[4] != 0 {
					v := strings.ToValidUTF8(string(d[4:4+n]), "?")
					label := qtTags[bx.typ]
					if label == "" {
						label = bx.typ
					}
					m.add("QuickTime", bx.typ, label, v)
					if label == "GPSCoordinates" && m.GPS == nil {
						m.GPS = iso6709(v)
					}
					return false
				}
			}
		}
		if bx.typ != "mdat" && bx.typ != "free" && bx.typ != "skip" && (bx.path == "/"+bx.typ || bx.typ == "udta" || bx.typ == "meta") {
			m.Blocks = append(m.Blocks, fmt.Sprintf("%s %s", strings.TrimPrefix(bx.path, "/"), humanBytes(bx.end-bx.start)))
		}
		return true
	})
	if err != nil {
		m.warn("%v", err)
	}
	if mdat > 0 {
		m.Blocks = append(m.Blocks, "mdat "+humanBytes(mdat))
	}
	// HEIF items: Exif and XMP
	for _, it := range items {
		data := itemData(b, idat, it)
		if data == nil {
			continue
		}
		switch {
		case it.typ == "Exif" && len(data) > 4:
			off := int(binary.BigEndian.Uint32(data))
			if 4+off < len(data) {
				t := data[4+off:]
				if bytes.HasPrefix(t, []byte("Exif\x00\x00")) {
					t = t[6:]
				}
				if err := parseTIFF(t, m); err != nil {
					m.warn("HEIF Exif: %v", err)
				}
			}
		case it.typ == "mime" && strings.Contains(it.ctype, "rdf+xml"):
			m.addXMP(data)
		}
	}
	m.Scrubbable = err == nil
}

// parseIloc reads ItemLocationBox versions 0–2.
func parseIloc(d []byte, items map[int]*heifItem) {
	if len(d) < 8 {
		return
	}
	ver := d[0]
	offSz, lenSz := int(d[4]>>4), int(d[4]&0xF)
	baseSz, idxSz := int(d[5]>>4), 0
	if ver == 1 || ver == 2 {
		idxSz = int(d[5] & 0xF)
	}
	q := 6
	rd := func(n int) (int, bool) {
		if n == 0 {
			return 0, true
		}
		if q+n > len(d) || n > 8 {
			return 0, false
		}
		var v uint64
		for _, c := range d[q : q+n] {
			v = v<<8 | uint64(c)
		}
		q += n
		return int(v), true
	}
	var count int
	var ok bool
	if ver < 2 {
		count, ok = rd(2)
	} else {
		count, ok = rd(4)
	}
	for i := 0; ok && i < count && i < 10000; i++ {
		var id, method, base, ext int
		if ver < 2 {
			id, ok = rd(2)
		} else {
			id, ok = rd(4)
		}
		if ver == 1 || ver == 2 {
			var cm int
			cm, ok = rd(2)
			method = cm & 0xF
		}
		rd(2) // data_reference_index
		base, _ = rd(baseSz)
		ext, ok = rd(2)
		it := items[id]
		if it == nil && ok { // iloc may precede iinf: merge by item id later
			it = &heifItem{id: id}
			items[id] = it
		}
		for e := 0; ok && e < ext; e++ {
			if idxSz > 0 {
				rd(idxSz)
			}
			o, ok1 := rd(offSz)
			l, ok2 := rd(lenSz)
			ok = ok1 && ok2
			if it != nil {
				it.method = method
				it.extents = append(it.extents, [2]int{base + o, l})
			}
		}
	}
}

func itemData(b, idat []byte, it *heifItem) []byte {
	src := b
	if it.method == 1 {
		src = idat
	} else if it.method != 0 {
		return nil
	}
	var out []byte
	for _, e := range it.extents {
		o, l := e[0], e[1]
		if l == 0 {
			l = len(src) - o
		}
		if o < 0 || l < 0 || o+l > len(src) || len(out)+l > 64<<20 {
			return nil
		}
		out = append(out, src[o:o+l]...)
	}
	return out
}

// scrubBMFF neutralises metadata in place so no box moves: chunk offsets
// (stco / co64) and HEIF item locations stay valid. udta / meta / XMP uuid
// boxes become 'free' boxes full of zeros, movie / track / media creation
// times are zeroed, and HEIF Exif / XMP items are overwritten with an empty
// TIFF / blank XMP of the same length.
func scrubBMFF(b []byte, m *Meta) (scrubResult, error) {
	out := append([]byte(nil), b...)
	var r scrubResult
	items := map[int]*heifItem{}
	var idatOff int
	isHEIF := false
	if len(b) >= 12 {
		switch string(b[8:12]) {
		case "heic", "heix", "mif1", "msf1", "avif", "heim", "heis", "hevc":
			isHEIF = true
		}
	}
	err := walkBMFF(b, 0, len(b), "", 0, func(bx bmffBox) bool {
		d := b[bx.body:bx.end]
		freeIt := func(what string) bool {
			copy(out[bx.start+4:bx.start+8], "free")
			for i := bx.body; i < bx.end; i++ {
				out[i] = 0
			}
			r.Removed = append(r.Removed, fmt.Sprintf("%s (%s)", what, humanBytes(bx.end-bx.start)))
			return false
		}
		switch {
		case bx.typ == "mdat":
			return false
		case bx.typ == "udta":
			return freeIt(strings.TrimPrefix(bx.path, "/") + " user data")
		case bx.typ == "meta" && !isHEIF:
			return freeIt(strings.TrimPrefix(bx.path, "/") + " metadata")
		case bx.typ == "uuid" && len(d) >= 16 && bytes.Equal(d[:16], xmpUUID):
			return freeIt("XMP uuid box")
		case bx.typ == "XMP_":
			return freeIt("XMP_ box")
		case bx.typ == "mvhd" || bx.typ == "tkhd" || bx.typ == "mdhd":
			if len(d) >= 12 {
				n := 8
				if d[0] == 1 {
					n = 16
				}
				if 4+n <= len(d) {
					for i := 0; i < n; i++ {
						out[bx.body+4+i] = 0
					}
					if bx.typ == "mvhd" {
						r.Removed = append(r.Removed, "creation / modification times (mvhd, tkhd, mdhd)")
					}
				}
			}
		case bx.typ == "infe" || bx.typ == "iloc":
			parseBMFFItems(bx, b, items)
		case bx.typ == "idat":
			idatOff = bx.body
		}
		return true
	})
	if err != nil {
		return r, err
	}
	for _, it := range items {
		if !(it.typ == "Exif" || it.typ == "mime" && strings.Contains(it.ctype, "rdf+xml")) {
			continue
		}
		base := 0
		if it.method == 1 {
			base = idatOff
		}
		for ei, e := range it.extents {
			o, l := base+e[0], e[1]
			if o < 0 || l <= 0 || o+l > len(out) {
				continue
			}
			r.blanked = append(r.blanked, [2]int{o, l})
			for i := o; i < o+l; i++ {
				out[i] = ' '
			}
			if it.typ == "mime" && ei == 0 {
				// a valid empty XMP packet, padded with spaces to the same length
				head := `<?xpacket begin="` + "\ufeff" + `" id="W5M0MpCehiHzreSzNTczkc9d"?><x:xmpmeta xmlns:x="adobe:ns:meta/"><rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"/></x:xmpmeta>`
				tail := `<?xpacket end="w"?>`
				if len(head)+len(tail) <= l {
					copy(out[o:], head)
					copy(out[o+l-len(tail):], tail)
				}
			}
			if it.typ == "Exif" && ei == 0 {
				// exif_tiff_header_offset = 0, then an empty little-endian TIFF
				empty := append([]byte{0, 0, 0, 0}, []byte("II*\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00")...)
				for i := 0; i < l; i++ {
					out[o+i] = 0
				}
				copy(out[o:], empty[:min(len(empty), l)])
			}
		}
		r.Removed = append(r.Removed, fmt.Sprintf("HEIF %s item #%d", it.typ, it.id))
	}
	r.Kept = append(r.Kept, "all boxes in place (renamed to 'free'), so media offsets stay valid")
	r.Out = out
	return r, nil
}

// parseBMFFItems feeds one infe / iloc box into the item table.
func parseBMFFItems(bx bmffBox, b []byte, items map[int]*heifItem) {
	d := b[bx.body:bx.end]
	if bx.typ == "iloc" {
		parseIloc(d, items)
		return
	}
	if len(d) >= 4 && d[0] >= 2 {
		q, id := 4, 0
		if d[0] == 2 && q+2 <= len(d) {
			id = int(binary.BigEndian.Uint16(d[q:]))
			q += 2
		} else if q+4 <= len(d) {
			id = int(binary.BigEndian.Uint32(d[q:]))
			q += 4
		}
		q += 2
		if q+4 <= len(d) {
			it := &heifItem{id: id, typ: string(d[q : q+4])}
			_, rest, _ := bytes.Cut(d[q+4:], []byte{0})
			ct, _, _ := bytes.Cut(rest, []byte{0})
			it.ctype = string(ct)
			if old := items[id]; old != nil {
				it.extents, it.method = old.extents, old.method
			}
			items[id] = it
		}
	}
}

// verifyBMFF: same size, same top-level box layout, byte-identical mdat.
// blanked are metadata item extents that may legitimately differ.
func verifyBMFF(orig, clean []byte, blanked [][2]int) (string, error) {
	if len(blanked) > 0 && len(orig) == len(clean) {
		o := append([]byte(nil), orig...)
		for _, x := range blanked {
			copy(o[x[0]:x[0]+x[1]], clean[x[0]:x[0]+x[1]])
		}
		orig = o
	}
	top := func(b []byte) ([][3]int, error) {
		var out [][3]int
		err := walkBMFF(b, 0, len(b), "", 0, func(bx bmffBox) bool {
			mdat := 0
			if bx.typ == "mdat" {
				mdat = 1
			}
			out = append(out, [3]int{bx.start, bx.end, mdat})
			return false
		})
		return out, err
	}
	ta, err := top(orig)
	if err != nil {
		return "", err
	}
	tb, err := top(clean)
	if err != nil {
		return "", fmt.Errorf("verification: %v", err)
	}
	if len(orig) != len(clean) || len(ta) != len(tb) {
		return "", errors.New("verification: container layout changed")
	}
	n := 0
	for i := range ta {
		if ta[i] != tb[i] {
			return "", errors.New("verification: container layout changed")
		}
		if ta[i][2] == 1 {
			n++
			if !bytes.Equal(orig[ta[i][0]:ta[i][1]], clean[ta[i][0]:ta[i][1]]) {
				return "", errors.New("verification: media data changed")
			}
		}
	}
	extra := ""
	if len(blanked) > 0 {
		extra = fmt.Sprintf(" outside %d blanked metadata item(s)", len(blanked))
	}
	return fmt.Sprintf("size and box layout unchanged, %d mdat payload(s) byte-identical%s", n, extra), nil
}

// ====================================================================
//  OSINT: link files by shared identifiers + capture timeline
// ====================================================================

type linkGroup struct {
	Kind  string   `json:"kind"` // serial | owner | document | email | user | device | place
	Value string   `json:"value"`
	Files []string `json:"files"`
	Weak  bool     `json:"weak,omitempty"` // common values (a phone model) link weakly
}

type timelineEntry struct {
	Time   string  `json:"time"`
	File   string  `json:"file"`
	Device string  `json:"device,omitempty"`
	GPS    *GPSFix `json:"gps,omitempty"`
	Place  string  `json:"place,omitempty"`
}

var reUserName = regexp.MustCompile(`(?i)(?:\\Users\\|/Users/|/home/)([^\\/\s"<>]+)`)

func normTime(v string) string {
	v = strings.TrimSpace(v)
	if len(v) >= 19 && v[4] == ':' && v[7] == ':' { // EXIF 2024:01:31 10:00:00
		v = v[:4] + "-" + v[5:7] + "-" + v[8:10] + v[10:19]
	}
	v = strings.Replace(v, "T", " ", 1)
	if len(v) >= 19 {
		return v[:19]
	}
	return v
}

func haversine(a, b GPSFix) float64 {
	const R = 6371000.0
	la1, la2 := a.Lat*math.Pi/180, b.Lat*math.Pi/180
	dla, dlo := la2-la1, (b.Lon-a.Lon)*math.Pi/180
	h := math.Sin(dla/2)*math.Sin(dla/2) + math.Cos(la1)*math.Cos(la2)*math.Sin(dlo/2)*math.Sin(dlo/2)
	return 2 * R * math.Asin(math.Sqrt(h))
}

// linkFiles groups files that share an identifying value and orders all
// timestamped files into a timeline. GPS fixes within 250 m form a place.
func linkFiles(ms []*Meta) ([]linkGroup, []timelineEntry) {
	idx := map[string]map[string]bool{}
	display := map[string]string{}
	add := func(kind, val, file string) {
		val = strings.TrimSpace(val)
		if val == "" || len(val) < 3 {
			return
		}
		k := kind + "\x00" + strings.ToLower(val)
		if idx[k] == nil {
			idx[k] = map[string]bool{}
			display[k] = val // first spelling seen
		}
		idx[k][file] = true
	}
	var tl []timelineEntry
	for _, m := range ms {
		var when, device string
		for _, t := range m.Tags {
			v, n := t.Value, t.Name
			switch {
			case in(serialTags, n) && !strings.HasPrefix(v, "("):
				add("serial", n+"="+v, m.Path)
			case in(personTags, n) && n != "Copyright" && n != "dc:rights" && n != "CopyrightNotice":
				add("owner", v, m.Path)
			case n == "xmpMM:OriginalDocumentID" || n == "xmpMM:DocumentID" || n == "stRef:documentID" || n == "ContentIdentifier":
				add("document", v, m.Path)
			case n == "Make" || n == "Model":
				device = strings.TrimSpace(device + " " + v)
			case n == "Company":
				add("organisation", v, m.Path)
			}
			for _, e := range reEmail.FindAllString(v, 3) {
				if tld := strings.ToLower(e[strings.LastIndexByte(e, '.')+1:]); !fileExts[tld] {
					add("email", strings.ToLower(e), m.Path)
				}
			}
			for _, u := range reUserName.FindAllStringSubmatch(v, 3) {
				add("user", u[1], m.Path)
			}
			if when == "" && (n == "DateTimeOriginal" || n == "CreationDate" || n == "xmp:CreateDate" || n == "CreateDate" || n == "created" || n == "photoshop:DateCreated") {
				when = normTime(v)
			}
		}
		if device != "" {
			add("device", device, m.Path)
		}
		if when != "" || m.GPS != nil {
			tl = append(tl, timelineEntry{Time: when, File: m.Path, Device: device, GPS: m.GPS})
		}
	}
	// places: greedy clusters of GPS fixes within 250 m
	type place struct {
		c     GPSFix
		files []string
	}
	var places []*place
	for i := range tl {
		g := tl[i].GPS
		if g == nil {
			continue
		}
		var hit *place
		for _, p := range places {
			if haversine(p.c, *g) <= 250 {
				hit = p
				break
			}
		}
		if hit == nil {
			hit = &place{c: *g}
			places = append(places, hit)
		}
		hit.files = append(hit.files, tl[i].File)
		tl[i].Place = fmt.Sprintf("P%d", indexOf(places, hit)+1)
	}
	var groups []linkGroup
	for i, p := range places {
		if len(p.files) >= 2 {
			groups = append(groups, linkGroup{Kind: "place", Value: fmt.Sprintf("P%d ≈ %.5f, %.5f (250 m)", i+1, p.c.Lat, p.c.Lon), Files: p.files})
		}
	}
	for k, files := range idx {
		if len(files) < 2 {
			continue
		}
		kind, val, _ := strings.Cut(k, "\x00")
		_ = val
		var fs []string
		for f := range files {
			fs = append(fs, f)
		}
		sort.Strings(fs)
		g := linkGroup{Kind: kind, Value: display[k], Files: fs, Weak: kind == "device" || kind == "organisation"}
		if g.Value == "" {
			g.Value = originalValue(ms, kind, val)
		}
		groups = append(groups, g)
	}
	rank := map[string]int{"serial": 0, "document": 1, "email": 2, "owner": 3, "user": 4, "place": 5, "organisation": 6, "device": 7}
	sort.SliceStable(groups, func(i, j int) bool {
		if rank[groups[i].Kind] != rank[groups[j].Kind] {
			return rank[groups[i].Kind] < rank[groups[j].Kind]
		}
		return len(groups[i].Files) > len(groups[j].Files)
	})
	sort.SliceStable(tl, func(i, j int) bool {
		if (tl[i].Time == "") != (tl[j].Time == "") {
			return tl[j].Time == ""
		}
		return tl[i].Time < tl[j].Time
	})
	return groups, tl
}

func indexOf[T comparable](xs []T, x T) int {
	for i, v := range xs {
		if v == x {
			return i
		}
	}
	return -1
}

// originalValue recovers the original spelling of a lower-cased key.
func originalValue(ms []*Meta, kind, low string) string {
	if kind == "device" || kind == "email" || kind == "user" {
		return low
	}
	for _, m := range ms {
		for _, t := range m.Tags {
			if strings.EqualFold(strings.TrimSpace(t.Value), low) || strings.EqualFold(t.Name+"="+strings.TrimSpace(t.Value), low) {
				if kind == "serial" {
					return t.Name + "=" + t.Value
				}
				return t.Value
			}
		}
	}
	return low
}

func printLinks(groups []linkGroup, tl []timelineEntry, n int) {
	sectionHeader(fmt.Sprintf("Links between %d file(s)", n))
	if len(groups) == 0 {
		okMsg("No shared identifiers — nothing ties these files together.")
	}
	for _, g := range groups {
		strength := col("strong", R+B)
		if g.Weak {
			strength = col("weak", DIM)
		}
		fmt.Println("  " + col(pad(strings.ToUpper(g.Kind), 13), CY+B) + strength + "  " + col(trunc(g.Value, 70), W) + col(fmt.Sprintf("  (%d files)", len(g.Files)), DIM))
		for i, f := range g.Files {
			if i == 6 {
				fmt.Println("      " + col(fmt.Sprintf("… %d more", len(g.Files)-6), DIM))
				break
			}
			fmt.Println("      " + col("• "+f, GY))
		}
	}
	if len(tl) > 0 {
		fmt.Println()
		sectionHeader("Capture timeline")
		var rows [][]string
		for _, t := range tl {
			gps := ""
			if t.GPS != nil {
				gps = fmt.Sprintf("%.5f, %.5f %s", t.GPS.Lat, t.GPS.Lon, t.Place)
			}
			rows = append(rows, []string{defaultStr(t.Time, "—"), trunc(t.File, 40), trunc(t.Device, 24), gps})
		}
		table([]string{"TIME", "FILE", "DEVICE", "GPS"}, rows)
	}
}

// ====================================================================
//  POLICY (CI gate)
// ====================================================================

type policyRule struct {
	action string // deny | warn | allow
	rule   string // META-… or *
}

type policy struct {
	rules       []policyRule
	maxSev      string
	allowValues map[string]*regexp.Regexp // tag → allowed value pattern
	source      string
}

const defaultPolicyText = `# OExifX default publishing policy
deny META-GPS
deny META-SERIAL
deny META-PATH
deny META-THUMB-MISMATCH
deny META-CONTACT
deny META-REVISION-AUTHORS
warn META-PERSON
warn META-PLACE
warn META-HISTORY
warn META-THUMB
allow META-SOFTWARE
allow META-TIME
allow META-DEVICE
max-severity MEDIUM
`

func parsePolicy(text, source string) (*policy, error) {
	p := &policy{maxSev: SevCritical, allowValues: map[string]*regexp.Regexp{}, source: source}
	for n, ln := range strings.Split(text, "\n") {
		if i := strings.Index(ln, "#"); i >= 0 {
			ln = ln[:i]
		}
		f := strings.Fields(ln)
		if len(f) == 0 {
			continue
		}
		bad := func(msg string) error { return fmt.Errorf("%s line %d: %s", source, n+1, msg) }
		switch strings.ToLower(f[0]) {
		case "deny", "warn", "allow":
			if len(f) != 2 {
				return nil, bad(f[0] + " needs one rule id (META-… or *)")
			}
			r := strings.ToUpper(f[1])
			if _, ok := ruleByID[r]; !ok && r != "*" {
				return nil, bad("unknown rule " + f[1])
			}
			p.rules = append(p.rules, policyRule{strings.ToLower(f[0]), r})
		case "max-severity":
			if len(f) != 2 || sevRank[strings.ToUpper(f[1])] == 0 {
				return nil, bad("max-severity needs INFO|LOW|MEDIUM|HIGH|CRITICAL")
			}
			p.maxSev = strings.ToUpper(f[1])
		case "allow-value":
			k, v, ok := strings.Cut(strings.TrimSpace(strings.TrimPrefix(strings.TrimSpace(ln), f[0])), "=")
			if !ok {
				return nil, bad("allow-value needs TAG=REGEX")
			}
			re, err := regexp.Compile(strings.TrimSpace(v))
			if err != nil {
				return nil, bad(err.Error())
			}
			p.allowValues[strings.ToLower(strings.TrimSpace(k))] = re
		default:
			return nil, bad("unknown directive " + f[0])
		}
	}
	return p, nil
}

func loadPolicy(arg string) (*policy, error) {
	if arg == "default" {
		return parsePolicy(defaultPolicyText, "default policy")
	}
	data, err := os.ReadFile(arg)
	if err != nil {
		return nil, err
	}
	return parsePolicy(string(data), arg)
}

type violation struct {
	File, Rule, Level, Message string
}

// action returns the last matching rule's action (later lines win).
func (p *policy) action(rule string) string {
	a := ""
	for _, r := range p.rules {
		if r.rule == rule || r.rule == "*" {
			a = r.action
		}
	}
	return a
}

// evaluate a file: denied rules and anything above max-severity fail;
// "warn" rules are reported but do not fail. allow-value exempts findings
// whose evidence only consists of allowed TAG=value pairs.
func (p *policy) evaluate(m *Meta) []violation {
	var out []violation
	for _, f := range m.Findings {
		if p.exempt(m, f) {
			continue
		}
		act := p.action(f.RuleID)
		switch {
		case act == "allow":
		case act == "deny":
			out = append(out, violation{m.Path, f.RuleID, "error", f.Title + ": " + f.Evidence})
		case act == "warn":
			out = append(out, violation{m.Path, f.RuleID, "warning", f.Title + ": " + f.Evidence})
		case sevRank[f.Severity] > sevRank[p.maxSev]:
			out = append(out, violation{m.Path, f.RuleID, "error", fmt.Sprintf("%s (%s > max-severity %s): %s", f.Title, f.Severity, p.maxSev, f.Evidence)})
		}
	}
	return out
}

func (p *policy) exempt(m *Meta, f Finding) bool {
	if len(p.allowValues) == 0 {
		return false
	}
	any := false
	for _, t := range m.Tags {
		short := t.Name + "=" + trunc(strings.ReplaceAll(t.Value, "\n", " "), 60)
		if !strings.Contains(f.Evidence, short) {
			continue
		}
		any = true
		re := p.allowValues[strings.ToLower(t.Name)]
		if re == nil || !re.MatchString(t.Value) {
			return false
		}
	}
	return any
}

func printViolations(vs []violation, files int, format string) {
	switch format {
	case "github":
		for _, v := range vs {
			fmt.Printf("::%s file=%s,title=%s::%s\n", v.Level, v.File, v.Rule, strings.ReplaceAll(v.Message, "\n", " "))
		}
		return
	case "plain":
		for _, v := range vs {
			fmt.Printf("%s: %s: %s: %s\n", v.File, v.Level, v.Rule, v.Message)
		}
		return
	}
	errs := 0
	for _, v := range vs {
		if v.Level == "error" {
			errs++
		}
	}
	if errs == 0 {
		okMsg(fmt.Sprintf("POLICY PASS — %d file(s), %d warning(s)", files, len(vs)))
	} else {
		errMsg(fmt.Sprintf("POLICY FAIL — %d violation(s), %d warning(s) in %d file(s)", errs, len(vs)-errs, files))
	}
	var rows [][]string
	for _, v := range vs {
		lv := col("WARN", YLW)
		if v.Level == "error" {
			lv = col("FAIL", R+B)
		}
		rows = append(rows, []string{lv, trunc(v.File, 36), v.Rule, trunc(v.Message, 60)})
	}
	if len(rows) > 0 {
		fmt.Println()
		table([]string{"", "FILE", "RULE", "WHY"}, rows)
	}
}

// ====================================================================
//  COMPARE two files' metadata
// ====================================================================

type metaChange struct {
	Key, Kind, Old, New string
}

func compareMeta(a, b *Meta) ([]metaChange, []string, []string) {
	key := func(t Tag) string { return t.Group + ":" + t.Name }
	ma, mb := map[string][]string{}, map[string][]string{}
	for _, t := range a.Tags {
		ma[key(t)] = append(ma[key(t)], t.Value)
	}
	for _, t := range b.Tags {
		mb[key(t)] = append(mb[key(t)], t.Value)
	}
	keys := map[string]bool{}
	for k := range ma {
		keys[k] = true
	}
	for k := range mb {
		keys[k] = true
	}
	var ks []string
	for k := range keys {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	var out []metaChange
	for _, k := range ks {
		va, vb := strings.Join(ma[k], " | "), strings.Join(mb[k], " | ")
		switch {
		case ma[k] == nil:
			out = append(out, metaChange{k, "added", "", vb})
		case mb[k] == nil:
			out = append(out, metaChange{k, "removed", va, ""})
		case va != vb:
			out = append(out, metaChange{k, "changed", va, vb})
		}
	}
	fa, fb := map[string]bool{}, map[string]bool{}
	for _, f := range a.Findings {
		fa[f.RuleID] = true
	}
	for _, f := range b.Findings {
		fb[f.RuleID] = true
	}
	var gone, added []string
	for _, r := range ruleCatalog {
		switch {
		case fa[r.ID] && !fb[r.ID]:
			gone = append(gone, r.ID)
		case fb[r.ID] && !fa[r.ID]:
			added = append(added, r.ID)
		}
	}
	return out, gone, added
}

func printCompare(a, b *Meta, cs []metaChange, gone, added []string) {
	_, ga := exposure(a.Findings)
	_, gb := exposure(b.Findings)
	kv("A", fmt.Sprintf("%s · %s · %d tags · grade %s", a.Path, a.Format, len(a.Tags), gradeColor(ga)))
	kv("B", fmt.Sprintf("%s · %s · %d tags · grade %s", b.Path, b.Format, len(b.Tags), gradeColor(gb)))
	c := map[string]int{}
	for _, x := range cs {
		c[x.Kind]++
	}
	kv("Tags", fmt.Sprintf("%s · %s · %s", col(fmt.Sprintf("removed %d", c["removed"]), R), col(fmt.Sprintf("added %d", c["added"]), GRN), col(fmt.Sprintf("changed %d", c["changed"]), YLW)))
	if len(gone) > 0 {
		kv("Exposures gone", col(strings.Join(gone, ", "), GRN))
	}
	if len(added) > 0 {
		kv("New exposures", col(strings.Join(added, ", "), R+B))
	}
	fmt.Println()
	if len(cs) == 0 {
		okMsg("Metadata is identical.")
		return
	}
	var rows [][]string
	for _, x := range cs {
		mark := map[string]string{"added": col("+", GRN+B), "removed": col("-", R+B), "changed": col("~", YLW+B)}[x.Kind]
		rows = append(rows, []string{mark, trunc(x.Key, 34), trunc(strings.ReplaceAll(x.Old, "\n", " "), 34), trunc(strings.ReplaceAll(x.New, "\n", " "), 34)})
	}
	table([]string{"", "TAG", "A", "B"}, rows)
}

// ====================================================================
//  BATCH + OUTPUT
// ====================================================================

var mediaExt = set(".jpg", ".jpeg", ".jpe", ".png", ".webp", ".gif", ".tif", ".tiff", ".pdf", ".docx", ".xlsx", ".pptx",
	".docm", ".xlsm", ".pptm", ".odt", ".ods", ".odp", ".odg", ".heic", ".heif", ".dng", ".avif",
	".mp4", ".m4v", ".mov", ".m4a", ".3gp", ".qt")

func collect(paths []string) ([]string, []string) {
	var files, warns []string
	for _, p := range paths {
		fi, err := os.Stat(p)
		if err != nil {
			warns = append(warns, err.Error())
			continue
		}
		if !fi.IsDir() {
			files = append(files, p)
			continue
		}
		filepath.WalkDir(p, func(q string, d fs.DirEntry, err error) error {
			if err != nil {
				warns = append(warns, err.Error())
				return nil
			}
			if d.IsDir() && q != p && strings.HasPrefix(d.Name(), ".") {
				return filepath.SkipDir
			}
			if d.Type().IsRegular() && in(mediaExt, filepath.Ext(q)) && !strings.Contains(filepath.Base(q), ".clean.") {
				files = append(files, q)
			}
			return nil
		})
	}
	return files, warns
}

const maxFile = 2 << 30 // videos are read whole; 2 GB cap

func loadMeta(p string) (*Meta, []byte, error) {
	fi, err := os.Stat(p)
	if err != nil {
		return nil, nil, err
	}
	if fi.Size() > maxFile {
		return nil, nil, fmt.Errorf("%s: larger than %s — skipped", p, humanBytes(maxFile))
	}
	b, err := os.ReadFile(p)
	if err != nil {
		return nil, nil, err
	}
	return readMeta(p, b), b, nil
}

func worst(fs []Finding) string {
	w := ""
	for _, f := range fs {
		if sevRank[f.Severity] > sevRank[w] {
			w = f.Severity
		}
	}
	return w
}

var showAll bool

func printMeta(m *Meta) {
	score, g := exposure(m.Findings)
	kv("File", m.Path)
	dim := ""
	if m.Width > 0 {
		dim = fmt.Sprintf(" · %d×%d", m.Width, m.Height)
	}
	kv("Format", fmt.Sprintf("%s · %s%s", defaultStr(m.Format, "unknown"), humanBytes(int(m.Size)), dim))
	kv("Tags", strconv.Itoa(len(m.Tags)))
	kv("Exposure", gradeColor(g)+col(fmt.Sprintf("  (privacy score %d/100)", score), DIM))
	if m.GPS != nil {
		kv("GPS", col(m.GPS.String(), R+B))
		kv("Map", m.GPS.MapURL())
	}
	if len(m.Blocks) > 0 {
		kv("Structure", trunc(strings.Join(m.Blocks, " · "), 110))
	}
	for _, w := range m.Warnings {
		warnMsg(w)
	}
	fmt.Println()
	if len(m.Findings) == 0 {
		okMsg("No privacy-relevant metadata found.")
	} else {
		var rows [][]string
		for _, f := range m.Findings {
			rows = append(rows, []string{sevColor(f.Severity), f.RuleID, trunc(f.Evidence, 70)})
		}
		table([]string{"SEV", "RULE", "EVIDENCE"}, rows)
	}
	if showAll && len(m.Tags) > 0 {
		fmt.Println()
		var rows [][]string
		for _, t := range m.Tags {
			rows = append(rows, []string{t.Group, trunc(t.Name, 30), trunc(strings.ReplaceAll(t.Value, "\n", "⏎"), 70)})
		}
		table([]string{"GROUP", "TAG", "VALUE"}, rows)
	} else if len(m.Tags) > 0 {
		info(fmt.Sprintf("%d tag(s) — show them all with --all", len(m.Tags)))
	}
}

func printBatch(ms []*Meta) {
	var rows [][]string
	counts := map[string]int{}
	gps := 0
	for _, m := range ms {
		w := worst(m.Findings)
		counts[defaultStr(w, "clean")]++
		if m.GPS != nil {
			gps++
		}
		var ids []string
		for _, f := range m.Findings {
			if sevRank[f.Severity] >= sevRank[SevMedium] {
				ids = append(ids, strings.TrimPrefix(f.RuleID, "META-"))
			}
		}
		_, g := exposure(m.Findings)
		rows = append(rows, []string{gradeColor(g), trunc(m.Path, 48), defaultStr(m.Format, "?"), strconv.Itoa(len(m.Tags)), trunc(strings.Join(ids, ","), 44)})
	}
	table([]string{"GRADE", "FILE", "FORMAT", "TAGS", "EXPOSURES (MEDIUM+)"}, rows)
	fmt.Println()
	kv("Files", strconv.Itoa(len(ms)))
	kv("With GPS", strconv.Itoa(gps))
	var cs []string
	for _, s := range append(sevOrder, "clean") {
		if counts[s] > 0 {
			cs = append(cs, fmt.Sprintf("%s %d", s, counts[s]))
		}
	}
	kv("Worst finding", strings.Join(cs, " · "))
}

type reportDoc struct {
	Tool      string  `json:"tool"`
	Version   string  `json:"version"`
	Generated string  `json:"generated"`
	Files     []*Meta `json:"files"`
}

func render(ms []*Meta, format string) (string, error) {
	switch strings.ToLower(format) {
	case "json":
		b, _ := json.MarshalIndent(reportDoc{APPNAME, VERSION, time.Now().UTC().Format(time.RFC3339), ms}, "", "  ")
		return string(b) + "\n", nil
	case "csv":
		var buf bytes.Buffer
		w := csv.NewWriter(&buf)
		w.Write([]string{"file", "format", "severity", "rule_id", "title", "evidence", "detail"})
		for _, m := range ms {
			for _, f := range m.Findings {
				w.Write([]string{m.Path, m.Format, f.Severity, f.RuleID, f.Title, f.Evidence, f.Detail})
			}
		}
		w.Flush()
		return buf.String(), nil
	case "md", "markdown":
		var b strings.Builder
		fmt.Fprintf(&b, "# %s report\n\n", APPNAME)
		for _, m := range ms {
			_, g := exposure(m.Findings)
			fmt.Fprintf(&b, "## `%s`\n\n- Format: %s · %d tag(s) · grade **%s**\n", m.Path, m.Format, len(m.Tags), g)
			if m.GPS != nil {
				fmt.Fprintf(&b, "- GPS: %s ([map](%s))\n", m.GPS, m.GPS.MapURL())
			}
			b.WriteString("\n| Severity | Rule | Evidence |\n|---|---|---|\n")
			for _, f := range m.Findings {
				fmt.Fprintf(&b, "| %s | %s | %s |\n", f.Severity, f.RuleID, strings.ReplaceAll(f.Evidence, "|", `\|`))
			}
			b.WriteString("\n")
		}
		return b.String(), nil
	case "", "txt", "text":
		var b strings.Builder
		fmt.Fprintf(&b, "%s v%s — %s\n", APPNAME, VERSION, TAGLINE)
		for _, m := range ms {
			_, g := exposure(m.Findings)
			fmt.Fprintf(&b, "\n%s\n  format %s · %d tags · grade %s\n", m.Path, m.Format, len(m.Tags), g)
			if m.GPS != nil {
				fmt.Fprintf(&b, "  GPS %s  %s\n", m.GPS, m.GPS.MapURL())
			}
			for _, f := range m.Findings {
				fmt.Fprintf(&b, "  [%s] %s: %s\n", f.Severity, f.RuleID, f.Evidence)
			}
			if showAll {
				for _, t := range m.Tags {
					fmt.Fprintf(&b, "    %-8s %-32s %s\n", t.Group, t.Name, strings.ReplaceAll(t.Value, "\n", " "))
				}
			}
		}
		return b.String(), nil
	}
	return "", fmt.Errorf("unknown format %q (txt|md|json|csv)", format)
}

// geoJSON maps every GPS fix as a FeatureCollection (open in any GIS / geojson.io).
func geoJSON(ms []*Meta) string {
	type feat struct {
		Type     string         `json:"type"`
		Geometry map[string]any `json:"geometry"`
		Props    map[string]any `json:"properties"`
	}
	fc := struct {
		Type     string `json:"type"`
		Features []feat `json:"features"`
	}{"FeatureCollection", []feat{}}
	for _, m := range ms {
		if m.GPS == nil {
			continue
		}
		coords := []float64{m.GPS.Lon, m.GPS.Lat}
		if m.GPS.Alt != nil {
			coords = append(coords, *m.GPS.Alt)
		}
		fc.Features = append(fc.Features, feat{"Feature", map[string]any{"type": "Point", "coordinates": coords},
			map[string]any{"file": m.Path, "time": m.GPS.Time, "device": strings.TrimSpace(m.get("Make") + " " + m.get("Model"))}})
	}
	b, _ := json.MarshalIndent(fc, "", "  ")
	return string(b) + "\n"
}

func writeOut(content, path string) error {
	if path == "" || path == "-" {
		fmt.Print(content)
		return nil
	}
	return os.WriteFile(path, []byte(content), 0o644)
}

// scrubFile writes a cleaned copy (or replaces the file with --in-place)
// and re-reads it to show what is left.
func scrubFile(p, outPath string, inPlace bool) (*Meta, scrubResult, error) {
	m, b, err := loadMeta(p)
	if err != nil {
		return nil, scrubResult{}, err
	}
	r, err := scrub(b, m)
	if err != nil {
		return m, r, err
	}
	switch {
	case inPlace:
		outPath = p
	case outPath == "":
		outPath = cleanName(p)
	}
	mode := os.FileMode(0o644)
	if fi, err := os.Stat(p); err == nil {
		mode = fi.Mode().Perm()
	}
	tmp := outPath + ".oexifx-tmp"
	if err := os.WriteFile(tmp, r.Out, mode); err != nil {
		return m, r, err
	}
	if err := os.Rename(tmp, outPath); err != nil {
		os.Remove(tmp)
		return m, r, err
	}
	after := readMeta(outPath, r.Out)
	return after, r, nil
}

func printScrub(src string, after *Meta, r scrubResult, out string) {
	okMsg(fmt.Sprintf("%s → %s", src, out))
	for _, x := range r.Removed {
		fmt.Println("     " + col("− "+x, R))
	}
	for _, x := range r.Kept {
		fmt.Println("     " + col("= kept "+x, DIM))
	}
	if r.Verified != "" {
		fmt.Println("     " + col("✔ "+r.Verified, GRN))
	}
	if after != nil {
		if len(after.Findings) == 0 {
			fmt.Println("     " + col("✔ re-scan: no privacy-relevant metadata left", GRN))
		} else {
			var ids []string
			for _, f := range after.Findings {
				ids = append(ids, f.RuleID)
			}
			fmt.Println("     " + col("! re-scan still finds: "+strings.Join(ids, ", "), YLW))
		}
	}
}

// ====================================================================
//  DEMO + SELF-TEST (synthetic files built with real structures)
// ====================================================================

// tiffBuilder writes a little-endian or big-endian TIFF with IFD0, Exif
// and GPS sub-IFDs and an optional IFD1 thumbnail.
type tiffEntry struct {
	tag, typ uint16
	cnt      uint32
	data     []byte
}

func buildTIFF(bo binary.ByteOrder, ifd0, exif, gps []tiffEntry, thumb []byte) []byte {
	hdr := []byte("II*\x00")
	if bo == binary.BigEndian {
		hdr = []byte("MM\x00*")
	}
	var buf bytes.Buffer
	buf.Write(hdr)
	buf.Write(make([]byte, 4))
	sizeOf := func(es []tiffEntry) int { return 2 + 12*len(es) + 4 }
	// layout: IFD0, Exif, GPS, IFD1, then data
	if exif != nil {
		ifd0 = append(ifd0, tiffEntry{0x8769, 4, 1, nil})
	}
	if gps != nil {
		ifd0 = append(ifd0, tiffEntry{0x8825, 4, 1, nil})
	}
	var ifd1 []tiffEntry
	if thumb != nil {
		ifd1 = []tiffEntry{{0x0103, 3, 1, u16(bo, 6)}, {0x0201, 4, 1, nil}, {0x0202, 4, 1, u32(bo, uint32(len(thumb)))}}
	}
	sort.Slice(ifd0, func(i, j int) bool { return ifd0[i].tag < ifd0[j].tag })
	p0 := 8
	pe := p0 + sizeOf(ifd0)
	pg := pe
	if exif != nil {
		pg += sizeOf(exif)
	}
	p1 := pg
	if gps != nil {
		p1 += sizeOf(gps)
	}
	dataPos := p1
	if ifd1 != nil {
		dataPos += sizeOf(ifd1)
	}
	var data bytes.Buffer
	put := func(es []tiffEntry, next int) []byte {
		var o bytes.Buffer
		binary.Write(&o, bo, uint16(len(es)))
		for _, e := range es {
			if e.typ == 2 {
				e.cnt = uint32(len(e.data))
			}
			binary.Write(&o, bo, e.tag)
			binary.Write(&o, bo, e.typ)
			binary.Write(&o, bo, e.cnt)
			d := e.data
			switch e.tag {
			case 0x8769:
				d = u32(bo, uint32(pe))
			case 0x8825:
				d = u32(bo, uint32(pg))
			case 0x0201:
				d = u32(bo, uint32(dataPos+data.Len()))
				data.Write(thumb)
			}
			if len(d) <= 4 {
				o.Write(append(append([]byte(nil), d...), make([]byte, 4-len(d))...))
			} else {
				binary.Write(&o, bo, uint32(dataPos+data.Len()))
				data.Write(d)
				if data.Len()%2 == 1 {
					data.WriteByte(0)
				}
			}
		}
		binary.Write(&o, bo, uint32(next))
		return o.Bytes()
	}
	next0 := 0
	if ifd1 != nil {
		next0 = p1
	}
	buf.Write(put(ifd0, next0))
	if exif != nil {
		buf.Write(put(exif, 0))
	}
	if gps != nil {
		buf.Write(put(gps, 0))
	}
	if ifd1 != nil {
		buf.Write(put(ifd1, 0))
	}
	buf.Write(data.Bytes())
	out := buf.Bytes()
	bo.PutUint32(out[4:], uint32(p0))
	return out
}

func u16(bo binary.ByteOrder, v uint16) []byte { b := make([]byte, 2); bo.PutUint16(b, v); return b }
func u32(bo binary.ByteOrder, v uint32) []byte { b := make([]byte, 4); bo.PutUint32(b, v); return b }
func ascii(s string) []byte                    { return append([]byte(s), 0) }
func rats(bo binary.ByteOrder, vs ...[2]uint32) []byte {
	var o []byte
	for _, v := range vs {
		o = append(o, u32(bo, v[0])...)
		o = append(o, u32(bo, v[1])...)
	}
	return o
}

// demoJPEG builds a real, decodable JPEG with Exif (GPS: Eiffel Tower),
// a serial number, XMP with a user path, IPTC city and a cropped thumbnail.
func demoJPEG(bo binary.ByteOrder) []byte {
	img := image.NewRGBA(image.Rect(0, 0, 64, 48))
	for y := 0; y < 48; y++ {
		for x := 0; x < 64; x++ {
			img.Pix[(y*64+x)*4], img.Pix[(y*64+x)*4+1], img.Pix[(y*64+x)*4+2], img.Pix[(y*64+x)*4+3] = uint8(x*4), uint8(y*5), 120, 255
		}
	}
	main := encodeJPEG(img)
	thumb := encodeJPEG(image.NewRGBA(image.Rect(0, 0, 16, 16))) // square: the original before a crop
	ifd0 := []tiffEntry{
		{0x010F, 2, 8, ascii("OWLCam")}, {0x0110, 2, 9, ascii("Hoot X1")}, {0x0112, 3, 1, u16(bo, 6)},
		{0x0131, 2, 13, ascii("PhotoTool 3")}, {0x013B, 2, 10, ascii("Jane Roe")},
	}
	exif := []tiffEntry{
		{0x9003, 2, 20, ascii("2026:10:30 09:41:00")}, {0x9011, 2, 7, ascii("+01:00")},
		{0xA431, 2, 11, ascii("SN-4471902")},
	}
	gps := []tiffEntry{
		{0x0001, 2, 2, ascii("N")}, {0x0002, 5, 3, rats(bo, [2]uint32{48, 1}, [2]uint32{51, 1}, [2]uint32{2976, 100})},
		{0x0003, 2, 2, ascii("E")}, {0x0004, 5, 3, rats(bo, [2]uint32{2, 1}, [2]uint32{17, 1}, [2]uint32{4020, 100})},
		{0x0005, 1, 1, []byte{0}}, {0x0006, 5, 1, rats(bo, [2]uint32{330, 1})},
	}
	tiff := buildTIFF(bo, ifd0, exif, gps, thumb)
	xmpPkt := `<?xpacket begin="" id="W5M0MpCehiHzreSzNTczkc9d"?><x:xmpmeta xmlns:x="adobe:ns:meta/"><rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">` +
		`<rdf:Description xmlns:xmp="http://ns.adobe.com/xap/1.0/" xmlns:xmpMM="http://ns.adobe.com/xap/1.0/mm/" xmlns:dc="http://purl.org/dc/elements/1.1/" xmp:CreatorTool="PhotoTool 3" xmpMM:DocumentID="xmp.did:4f1a">` +
		`<dc:creator><rdf:Seq><rdf:li>Jane Roe</rdf:li></rdf:Seq></dc:creator><xmpMM:History><rdf:Seq><rdf:li xmlns:stEvt="http://ns.adobe.com/xap/1.0/sType/ResourceEvent#" stEvt:action="saved" stEvt:instanceID="xmp.iid:1"/>` +
		`<rdf:li xmlns:stEvt="http://ns.adobe.com/xap/1.0/sType/ResourceEvent#" stEvt:action="derived" stEvt:parameters="from C:\Users\jroe\Desktop\IMG_0042.CR2"/></rdf:Seq></xmpMM:History>` +
		`</rdf:Description></rdf:RDF></x:xmpmeta><?xpacket end="w"?>`
	iptc := []byte{0x1C, 2, 90, 0, 5}
	iptc = append(iptc, "Paris"...)
	irb := append([]byte("Photoshop 3.0\x008BIM\x04\x04\x00\x00"), u32(binary.BigEndian, uint32(len(iptc)))...)
	irb = append(irb, iptc...)
	if len(iptc)%2 == 1 {
		irb = append(irb, 0)
	}
	seg := func(mk byte, d []byte) []byte {
		return append([]byte{0xFF, mk, byte((len(d) + 2) >> 8), byte(len(d) + 2)}, d...)
	}
	out := []byte{0xFF, 0xD8}
	out = append(out, seg(0xE1, append([]byte("Exif\x00\x00"), tiff...))...)
	out = append(out, seg(0xE1, append([]byte("http://ns.adobe.com/xap/1.0/\x00"), xmpPkt...))...)
	out = append(out, seg(0xED, irb)...)
	out = append(out, seg(0xFE, []byte("internal draft — do not publish"))...)
	return append(out, main[2:]...) // main JPEG without its SOI
}

func encodeJPEG(img image.Image) []byte {
	var b bytes.Buffer
	jpeg.Encode(&b, img, &jpeg.Options{Quality: 90})
	return b.Bytes()
}

func encodePNG(img image.Image) []byte {
	var b bytes.Buffer
	png.Encode(&b, img)
	return b.Bytes()
}

func demoPNG() []byte {
	img := image.NewNRGBA(image.Rect(0, 0, 8, 8))
	for i := range img.Pix {
		img.Pix[i] = uint8(i * 7)
	}
	raw := encodePNG(img)
	cs, _ := pngChunks(raw)
	out := append([]byte(nil), raw[:8]...)
	for _, c := range cs {
		out = append(out, raw[c.start:c.end]...)
		if c.typ == "IHDR" {
			out = append(out, pngChunkBytes("tEXt", []byte("Author\x00Jane Roe"))...)
			var z bytes.Buffer
			zw := zlib.NewWriter(&z)
			zw.Write([]byte("saved from /home/jroe/projects/secret-launch/mock.png"))
			zw.Close()
			out = append(out, pngChunkBytes("iTXt", append([]byte("Comment\x00\x01\x00en\x00\x00"), z.Bytes()...))...)
			out = append(out, pngChunkBytes("tIME", []byte{0x07, 0xEA, 10, 30, 9, 41, 0})...)
		}
	}
	return out
}

func demoDOCX() []byte {
	var buf bytes.Buffer
	zw := zip.NewWriter(&buf)
	add := func(n, s string) { w, _ := zw.Create(n); w.Write([]byte(s)) }
	add("[Content_Types].xml", `<?xml version="1.0"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"/>`)
	add("docProps/core.xml", `<?xml version="1.0"?><cp:coreProperties xmlns:cp="x" xmlns:dc="y"><dc:creator>Jane Roe</dc:creator><cp:lastModifiedBy>j.roe@example.com</cp:lastModifiedBy><cp:revision>14</cp:revision><dcterms:created>2026-10-01T08:00:00Z</dcterms:created></cp:coreProperties>`)
	add("docProps/app.xml", `<?xml version="1.0"?><Properties><Template>C:\Users\jroe\AppData\Roaming\Microsoft\Templates\Normal.dotm</Template><Company>Acme Corp</Company><Application>Microsoft Office Word</Application><TotalTime>412</TotalTime></Properties>`)
	add("word/document.xml", `<w:document><w:body><w:p><w:ins w:id="1" w:author="Legal Reviewer" w:date="2026-10-02T10:00:00Z"><w:r><w:t>new clause</w:t></w:r></w:ins></w:p></w:body></w:document>`)
	add("word/comments.xml", `<w:comments><w:comment w:id="0" w:author="John Smith" w:initials="JS"><w:p><w:r><w:t>remove before sending</w:t></w:r></w:p></w:comment></w:comments>`)
	zw.Close()
	return buf.Bytes()
}

func runDemo() []*Meta {
	var ms []*Meta
	for _, x := range []struct {
		name string
		data []byte
	}{{"demo-photo.jpg", demoJPEG(binary.LittleEndian)}, {"demo-mockup.png", demoPNG()}, {"demo-contract.docx", demoDOCX()}} {
		ms = append(ms, readMeta(x.name, x.data))
	}
	return ms
}

func runSelfTest() int {
	var rows [][]string
	fail, total := 0, 0
	check := func(name, expect, got string, ok bool) {
		total++
		res := col("PASS", GRN+B)
		if !ok {
			res = col("FAIL", R+B)
			fail++
		}
		rows = append(rows, []string{trunc(name, 36), trunc(expect, 26), trunc(got, 30), res})
	}
	has := func(m *Meta, id string) bool {
		for _, f := range m.Findings {
			if f.RuleID == id {
				return true
			}
		}
		return false
	}
	for _, bo := range []binary.ByteOrder{binary.LittleEndian, binary.BigEndian} {
		b := demoJPEG(bo)
		m := readMeta("t.jpg", b)
		lat, lon := 0.0, 0.0
		if m.GPS != nil {
			lat, lon = m.GPS.Lat, m.GPS.Lon
		}
		tag := "II"
		if bo == binary.BigEndian {
			tag = "MM"
		}
		check("JPEG/"+tag+": GPS decoded (Eiffel Tower)", "48.858267, 2.294500", fmt.Sprintf("%.6f, %.6f", lat, lon),
			math.Abs(lat-48.858267) < 1e-5 && math.Abs(lon-2.2945) < 1e-5 && m.GPS.Alt != nil && *m.GPS.Alt == 330)
		check("JPEG/"+tag+": serial, person, path, place", "4 rules", fmt.Sprint(has(m, "META-SERIAL"), has(m, "META-PERSON"), has(m, "META-PATH"), has(m, "META-PLACE")),
			has(m, "META-SERIAL") && has(m, "META-PERSON") && has(m, "META-PATH") && has(m, "META-PLACE"))
	}
	b := demoJPEG(binary.LittleEndian)
	m := readMeta("t.jpg", b)
	check("XMP history (2 events) + comment + crop", "HISTORY COMMENT MISMATCH", fmt.Sprint(m.get("xmpMM:History"), has(m, "META-COMMENT"), has(m, "META-THUMB-MISMATCH")),
		m.get("xmpMM:History") == "2 editing event(s)" && has(m, "META-COMMENT") && has(m, "META-THUMB-MISMATCH"))
	r, err := scrub(b, m)
	after := readMeta("c.jpg", r.Out)
	check("JPEG scrub: nothing left, pixels same", "0 findings", fmt.Sprint(len(after.Findings), err), err == nil && len(after.Findings) == 0 &&
		strings.Contains(r.Verified, "pixels identical"))
	o := after.nums["IFD0:0x0112"]
	check("JPEG scrub keeps orientation", "Orientation=6", fmt.Sprint(o), len(o) == 1 && o[0] == 6)

	p := demoPNG()
	pm := readMeta("t.png", p)
	check("PNG tEXt + compressed iTXt + tIME", "PERSON PATH TIME", fmt.Sprint(has(pm, "META-PERSON"), has(pm, "META-PATH"), has(pm, "META-TIME")),
		has(pm, "META-PERSON") && has(pm, "META-PATH") && has(pm, "META-TIME"))
	pr, err := scrub(p, pm)
	pa := readMeta("c.png", pr.Out)
	check("PNG scrub: CRCs valid, IDAT same", "0 findings", fmt.Sprint(len(pa.Findings), err), err == nil && len(pa.Findings) == 0 && len(pa.Warnings) == 0)

	d := demoDOCX()
	dm := readMeta("t.docx", d)
	check("DOCX: creator, email, template path, authors", "4 rules", fmt.Sprint(has(dm, "META-PERSON"), has(dm, "META-CONTACT"), has(dm, "META-PATH"), has(dm, "META-REVISION-AUTHORS")),
		has(dm, "META-PERSON") && has(dm, "META-CONTACT") && has(dm, "META-PATH") && has(dm, "META-REVISION-AUTHORS") && has(dm, "META-COMPANY"))
	dr, err := scrub(d, dm)
	da := readMeta("c.docx", dr.Out)
	leftover := ""
	for _, f := range da.Findings {
		if sevRank[f.Severity] >= sevRank[SevMedium] && f.RuleID != "META-REVISION-AUTHORS" {
			leftover += f.RuleID + " "
		}
	}
	check("DOCX scrub: people + company gone", "only generic 'Author'", leftover+da.get("RevisionAndCommentAuthors"),
		err == nil && leftover == "" && !strings.Contains(da.get("RevisionAndCommentAuthors"), "Smith") && strings.Contains(dr.Verified, "zip valid"))

	// WebP: VP8X + EXIF + XMP → scrub flags + RIFF size
	tiff := buildTIFF(binary.LittleEndian, []tiffEntry{{0x013B, 2, 4, ascii("Bob")}}, nil, nil, nil)
	wp := []byte("RIFF\x00\x00\x00\x00WEBP")
	ch := func(id string, d []byte) []byte {
		c := append([]byte(id), u32(binary.LittleEndian, uint32(len(d)))...)
		c = append(c, d...)
		if len(d)%2 == 1 {
			c = append(c, 0)
		}
		return c
	}
	wp = append(wp, ch("VP8X", []byte{0x0C, 0, 0, 0, 7, 0, 0, 7, 0, 0})...)
	wp = append(wp, ch("VP8L", []byte{0x2F, 7, 0xC0, 0xF7, 0, 0, 0})...)
	wp = append(wp, ch("EXIF", tiff)...)
	wp = append(wp, ch("XMP ", []byte(`<x:xmpmeta xmlns:x="adobe:ns:meta/"><rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"><rdf:Description xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:creator>Bob</dc:creator></rdf:Description></rdf:RDF></x:xmpmeta>`))...)
	binary.LittleEndian.PutUint32(wp[4:], uint32(len(wp)-8))
	wm := readMeta("t.webp", wp)
	wr, err := scrub(wp, wm)
	wa := readMeta("c.webp", wr.Out)
	check("WebP EXIF+XMP scrub, flags + size", "flags 0x00, 0 tags", fmt.Sprintf("0x%02X %d", wr.Out[20], len(wa.Tags)),
		err == nil && has(wm, "META-PERSON") && len(wa.Tags) == 0 && wr.Out[20] == 0 && int(binary.LittleEndian.Uint32(wr.Out[4:])) == len(wr.Out)-8)

	// PDF Info dict (literal + UTF-16 hex) + incremental update
	pdf := []byte("%PDF-1.4\n1 0 obj\n<< /Author (Jane \\(J.\\) Roe) /Producer <FEFF004F0057004C> /CreationDate (D:20261030094100+01'00') >>\nendobj\ntrailer\n<< /Info 1 0 R >>\n%%EOF\n2 0 obj\n<<>>\nendobj\n%%EOF\n")
	fm := readMeta("t.pdf", pdf)
	check("PDF Info strings + revisions", "Jane (J.) Roe · OWL", fm.get("Author")+" · "+fm.get("Producer"),
		fm.get("Author") == "Jane (J.) Roe" && fm.get("Producer") == "OWL" && has(fm, "META-PDF-REVISIONS") && strings.HasPrefix(fm.get("CreationDate"), "2026-10-30 09:41:00 +01:00"))
	_, err = scrub(pdf, fm)
	check("PDF scrub refused with a reason", "error", fmt.Sprint(err != nil), err != nil)

	// robustness: random corruption must never panic or hang
	rng := rand.New(rand.NewSource(3))
	crashes := 0
	for i := 0; i < 400; i++ {
		src := [][]byte{b, p, d, wp, pdf}[i%5]
		c := append([]byte(nil), src...)
		for k := 0; k < 1+rng.Intn(12); k++ {
			c[rng.Intn(len(c))] = byte(rng.Intn(256))
		}
		if rng.Intn(4) == 0 {
			c = c[:rng.Intn(len(c))+1]
		}
		func() {
			defer func() {
				if recover() != nil {
					crashes++
				}
			}()
			mm := readMeta("fuzz", c)
			if mm.Scrubbable {
				scrub(c, mm)
			}
		}()
	}
	check("400 corrupted files: no crash", "0 panics", strconv.Itoa(crashes), crashes == 0)
	selfTestExtras(check, has)

	table([]string{"CASE", "EXPECT", "GOT", "RESULT"}, rows)
	fmt.Println()
	if fail == 0 {
		okMsg(fmt.Sprintf("self-test: %d/%d passed", total, total))
	} else {
		errMsg(fmt.Sprintf("self-test: %d/%d FAILED", fail, total))
	}
	return fail
}

// box builds one ISO-BMFF box.
func box(typ string, parts ...[]byte) []byte {
	var body []byte
	for _, p := range parts {
		body = append(body, p...)
	}
	out := binary.BigEndian.AppendUint32(nil, uint32(8+len(body)))
	out = append(out, []byte(typ)...)
	return append(out, body...)
}

// demoMOV: an iPhone-style QuickTime file with udta ©xyz / ©mak and a
// meta/keys/ilst model entry; mdat holds stand-in media bytes.
func demoMOV() []byte {
	qt := func(typ, v string) []byte {
		return box(typ, binary.BigEndian.AppendUint16(nil, uint16(len(v))), []byte{0x15, 0xC7}, []byte(v))
	}
	data := func(v string) []byte { return box("data", []byte{0, 0, 0, 1, 0, 0, 0, 0}, []byte(v)) }
	mvhd := box("mvhd", []byte{0, 0, 0, 0}, binary.BigEndian.AppendUint32(nil, 3_844_663_260), binary.BigEndian.AppendUint32(nil, 3_844_663_260), make([]byte, 88))
	key := "com.apple.quicktime.model"
	keys := box("keys", []byte{0, 0, 0, 0}, binary.BigEndian.AppendUint32(nil, 1), binary.BigEndian.AppendUint32(nil, uint32(8+len(key))), []byte("mdta"), []byte(key))
	ilst := box("ilst", box(string([]byte{0, 0, 0, 1}), data("iPhone 15 Pro")))
	meta := box("meta", box("hdlr", make([]byte, 8), []byte("mdta"), make([]byte, 13)), keys, ilst)
	udta := box("udta", qt("\xa9xyz", "+48.8583+002.2945+035.000/"), qt("\xa9mak", "Apple"))
	moov := box("moov", mvhd, udta, meta)
	media := make([]byte, 4096)
	for i := range media {
		media[i] = byte(i * 31)
	}
	return append(append(box("ftyp", []byte("qt  \x00\x00\x00\x00qt  ")), moov...), box("mdat", media)...)
}

// demoHEIC: ftyp + meta(iinf with an Exif item, iloc pointing into mdat).
func demoHEIC() []byte {
	tiff := buildTIFF(binary.BigEndian, []tiffEntry{{0x010F, 2, 0, ascii("Apple")}, {0x013B, 2, 0, ascii("Jane Roe")}}, nil,
		[]tiffEntry{{0x0001, 2, 0, ascii("N")}, {0x0002, 5, 3, rats(binary.BigEndian, [2]uint32{48, 1}, [2]uint32{51, 1}, [2]uint32{2976, 100})},
			{0x0003, 2, 0, ascii("E")}, {0x0004, 5, 3, rats(binary.BigEndian, [2]uint32{2, 1}, [2]uint32{17, 1}, [2]uint32{4020, 100})}}, nil)
	exif := append([]byte{0, 0, 0, 6}, append([]byte("Exif\x00\x00"), tiff...)...)
	infe := box("infe", []byte{2, 0, 0, 0}, []byte{0, 1, 0, 0}, []byte("Exif"), []byte{0})
	iinf := box("iinf", []byte{0, 0, 0, 0}, []byte{0, 1}, infe)
	build := func(off int) []byte {
		// version 0, offset/length 4 bytes, no base offset: count, id, data_ref, extents, offset, length
		iloc := box("iloc", []byte{0, 0, 0, 0}, []byte{0x44, 0x00}, []byte{0, 1}, []byte{0, 1}, []byte{0, 0},
			[]byte{0, 1}, binary.BigEndian.AppendUint32(nil, uint32(off)), binary.BigEndian.AppendUint32(nil, uint32(len(exif))))
		meta := box("meta", []byte{0, 0, 0, 0}, box("hdlr", make([]byte, 8), []byte("pict"), make([]byte, 13)), iloc, iinf)
		return append(box("ftyp", []byte("heic\x00\x00\x00\x00mif1heic")), meta...)
	}
	head := build(0)
	pixels := bytes.Repeat([]byte{0xAB, 0xCD}, 512)
	off := len(head) + 8 + len(pixels)
	head = build(off)
	return append(head, box("mdat", pixels, exif)...)
}

// selfTestExtras covers video / HEIC, OSINT links, policies and compare.
func selfTestExtras(check func(name, expect, got string, ok bool), has func(*Meta, string) bool) {
	mov := demoMOV()
	m := readMeta("t.mov", mov)
	model := m.get("Model")
	check("MOV: ©xyz GPS, ©mak, keys/ilst model", "48.8583,2.2945 iPhone 15 Pro", fmt.Sprint(m.GPS, model),
		m.Format == "MOV" && m.GPS != nil && m.GPS.Lat == 48.8583 && model == "iPhone 15 Pro" && m.get("Make") == "Apple" &&
			strings.HasPrefix(m.get("CreateDate"), "2025-"))
	r, err := scrub(mov, m)
	after := readMeta("c.mov", r.Out)
	check("MOV scrub: same size, mdat intact, clean", "0 findings", fmt.Sprint(len(after.Findings), err),
		err == nil && len(r.Out) == len(mov) && len(after.Findings) == 0 && strings.Contains(r.Verified, "byte-identical"))
	h := demoHEIC()
	hm := readMeta("t.heic", h)
	check("HEIC: Exif item via iloc → GPS + person", "GPS PERSON", fmt.Sprint(hm.GPS, has(hm, "META-PERSON"), hm.Warnings),
		hm.Format == "HEIC" && hm.GPS != nil && math.Abs(hm.GPS.Lat-48.858267) < 1e-5 && has(hm, "META-PERSON"))
	hr, err := scrub(h, hm)
	ha := readMeta("c.heic", hr.Out)
	check("HEIC scrub: item blanked in place", "0 findings", fmt.Sprint(len(ha.Findings), err), err == nil && len(ha.Findings) == 0 && len(hr.Out) == len(h))

	// OSINT links: two photos share a body serial, two were taken ~40 m apart
	mk := func(path, serial string, lat float64, when string) *Meta {
		x := &Meta{Path: path, nums: map[string][]float64{}}
		x.add("Exif", "", "BodySerialNumber", serial)
		x.add("Exif", "", "DateTimeOriginal", when)
		x.add("IFD0", "", "Model", "X100V")
		x.GPS = &GPSFix{Lat: lat, Lon: 2.2945}
		return x
	}
	groups, tl := linkFiles([]*Meta{mk("a.jpg", "SN-1", 48.8583, "2026:10:30 09:00:00"), mk("b.jpg", "SN-1", 48.8586, "2026:10:30 10:00:00"),
		mk("c.jpg", "SN-9", 40.7, "2026:10:29 08:00:00")})
	kinds := map[string]int{}
	for _, g := range groups {
		kinds[g.Kind] = len(g.Files)
	}
	check("link: shared serial + place cluster", "serial 2, place 2, device 3", fmt.Sprint(kinds),
		kinds["serial"] == 2 && kinds["place"] == 2 && kinds["device"] == 3 && len(tl) == 3 && tl[0].File == "c.jpg")

	// policy: the demo photo fails the default policy; allow-value exempts an approved name
	demo := readMeta("demo.jpg", demoJPEG(binary.LittleEndian))
	p, _ := loadPolicy("default")
	vs := p.evaluate(demo)
	failGPS := false
	for _, v := range vs {
		if v.Rule == "META-GPS" && v.Level == "error" {
			failGPS = true
		}
	}
	check("policy default: GPS photo fails", "META-GPS error", fmt.Sprint(len(vs)), failGPS)
	p2, err := parsePolicy("deny META-PERSON\nallow-value Artist=^Jane Roe$\nallow-value dc:creator=^Jane Roe$\n", "t")
	vs2 := p2.evaluate(demo)
	check("policy allow-value exempts approved author", "0 violations", fmt.Sprint(len(vs2), err), err == nil && len(vs2) == 0)
	_, err = parsePolicy("deny META-NOPE\n", "t")
	check("policy rejects unknown rules", "error", fmt.Sprint(err != nil), err != nil)

	// compare original vs scrubbed
	sr, _ := scrub(demoJPEG(binary.LittleEndian), demo)
	cs, gone, added := compareMeta(demo, readMeta("clean.jpg", sr.Out))
	check("compare: scrub removed GPS / serial", "GPS, SERIAL gone", fmt.Sprint(len(cs), gone),
		len(cs) > 10 && slicesHas(gone, "META-GPS") && slicesHas(gone, "META-SERIAL") && len(added) == 0)
}

func slicesHas(xs []string, s string) bool {
	for _, x := range xs {
		if x == s {
			return true
		}
	}
	return false
}

// ====================================================================
//  INTERACTIVE TUI
// ====================================================================

var lastMetas []*Meta

type tuiAction struct {
	name, desc string
	fn         func()
}

var tuiActions []tuiAction

func init() {
	tuiActions = []tuiAction{
		{"Inspect a file", "findings · GPS · structure", uiInspect},
		{"Show every tag", "full EXIF / XMP / IPTC / doc dump", uiAllTags},
		{"Inspect a folder", "batch exposure summary", uiFolder},
		{"Scrub a file", "clean copy, verified, nothing re-encoded", uiScrub},
		{"Scrub a folder", "clean copies of every supported file", uiScrubFolder},
		{"GPS map export", "GeoJSON of every geotagged file", uiGeo},
		{"Link files (OSINT)", "shared serials · owners · places · timeline", uiLink},
		{"Policy check (CI)", "would these files pass publishing rules?", uiPolicy},
		{"Compare two files", "metadata added / removed / changed", uiCompare},
		{"Extract thumbnail", "save the embedded preview", uiThumb},
		{"Rule catalog", "what each exposure means", uiCatalog},
		{"Export last result", "txt · md · json · csv", uiExport},
		{"Run demo", "photo · mockup · contract (synthetic)", uiDemo},
		{"Self-test", "parsers · scrubbers · fuzzing", func() { sectionHeader("Self-Test"); runSelfTest() }},
	}
}

func mainMenu() {
	for {
		clear()
		banner()
		fmt.Println("  " + col("⬡  Main Menu", B+CY))
		fmt.Println()
		for i, a := range tuiActions {
			fmt.Println("  " + col(pad(fmt.Sprintf("[%d]", i+1), 4), CY+B) + "  " +
				col(pad(a.name, 26), W) + col("─ "+a.desc, DIM))
		}
		fmt.Println()
		fmt.Println("  " + col(pad("[H]", 4), YLW+B) + "  " + col(pad("Help & Usage", 26), W) + col("─ How to use, every option, CLI flags & examples", DIM))
		fmt.Println("  " + col(pad("[0]", 4), R+B) + "  " + col(pad("Exit", 26), W) + col("─ Quit "+APPNAME, DIM))
		fmt.Println()
		rule()
		c := strings.TrimLeft(prompt("Select option"), "0")
		if c == "" {
			clear()
			okMsg("Goodbye.")
			return
		}
		if strings.EqualFold(c, "h") || strings.EqualFold(c, "help") || c == "?" {
			tuiHelp()
			continue
		}
		n, err := strconv.Atoi(c)
		if err != nil || n < 1 || n > len(tuiActions) {
			errMsg("Unknown option")
			pause()
			continue
		}
		clear()
		banner()
		tuiActions[n-1].fn()
		pause()
	}
}

func uiInspectWith(all bool) {
	p := prompt("file path")
	if p == "" {
		return
	}
	m, _, err := loadMeta(p)
	if err != nil {
		errMsg(err.Error())
		return
	}
	lastMetas = []*Meta{m}
	saved := showAll
	showAll = all
	fmt.Println()
	printMeta(m)
	showAll = saved
}

func uiInspect() { sectionHeader("Inspect a File"); uiInspectWith(false) }
func uiAllTags() { sectionHeader("Every Tag"); uiInspectWith(true) }

func uiFolder() {
	sectionHeader("Inspect a Folder")
	p := prompt("folder (blank = .)")
	if p == "" {
		p = "."
	}
	files, warns := collect([]string{p})
	var ms []*Meta
	for _, f := range files {
		m, _, err := loadMeta(f)
		if err != nil {
			warns = append(warns, err.Error())
			continue
		}
		ms = append(ms, m)
	}
	for _, w := range warns {
		warnMsg(w)
	}
	if len(ms) == 0 {
		warnMsg("no supported files found")
		return
	}
	lastMetas = ms
	printBatch(ms)
}

func uiScrub() {
	sectionHeader("Scrub a File")
	p := prompt("file path")
	if p == "" {
		return
	}
	out := prompt(fmt.Sprintf("output (blank = %s)", cleanName(p)))
	after, r, err := scrubFile(p, out, false)
	if err != nil {
		errMsg(err.Error())
		return
	}
	if out == "" {
		out = cleanName(p)
	}
	fmt.Println()
	printScrub(p, after, r, out)
}

func uiScrubFolder() {
	sectionHeader("Scrub a Folder")
	p := prompt("folder")
	if p == "" {
		return
	}
	files, _ := collect([]string{p})
	info(fmt.Sprintf("%d supported file(s); cleaned copies are written next to them as *.clean.*", len(files)))
	if !strings.HasPrefix(strings.ToLower(prompt("continue? [y/N]")), "y") {
		return
	}
	ok, skipped := 0, 0
	for _, f := range files {
		after, r, err := scrubFile(f, "", false)
		if err != nil {
			skipped++
			warnMsg(f + ": " + err.Error())
			continue
		}
		ok++
		printScrub(f, after, r, cleanName(f))
	}
	okMsg(fmt.Sprintf("%d cleaned, %d skipped", ok, skipped))
}

func uiGeo() {
	sectionHeader("GPS Map Export")
	p := prompt("file or folder (blank = last result)")
	ms := lastMetas
	if p != "" {
		files, _ := collect([]string{p})
		ms = nil
		for _, f := range files {
			if m, _, err := loadMeta(f); err == nil {
				ms = append(ms, m)
			}
		}
	}
	n := 0
	for _, m := range ms {
		if m.GPS != nil {
			n++
			fmt.Println("  " + col("•", R) + " " + col(m.Path, W) + col("  "+m.GPS.String(), DIM))
		}
	}
	if n == 0 {
		okMsg("no geotagged files")
		return
	}
	out := prompt("GeoJSON file (blank = oexifx-gps.geojson)")
	if out == "" {
		out = "oexifx-gps.geojson"
	}
	if err := writeOut(geoJSON(ms), out); err != nil {
		errMsg(err.Error())
		return
	}
	okMsg(fmt.Sprintf("%d point(s) → %s (open at geojson.io or in QGIS)", n, out))
}

func uiLink() {
	sectionHeader("Link Files (OSINT)")
	p := prompt("folder or files")
	files, _ := collect(strings.Fields(p))
	var ms []*Meta
	for _, f := range files {
		if m, _, err := loadMeta(f); err == nil {
			ms = append(ms, m)
		}
	}
	if len(ms) < 2 {
		warnMsg("need at least two supported files")
		return
	}
	lastMetas = ms
	groups, tl := linkFiles(ms)
	printLinks(groups, tl, len(ms))
}

func uiPolicy() {
	sectionHeader("Policy Check")
	pf := prompt("policy file (blank = built-in default)")
	if pf == "" {
		pf = "default"
	}
	p, err := loadPolicy(pf)
	if err != nil {
		errMsg(err.Error())
		return
	}
	files, _ := collect(strings.Fields(prompt("files / folder to check")))
	var vs []violation
	for _, f := range files {
		vs = append(vs, p.evaluate(readMetaPath(f))...)
	}
	fmt.Println()
	printViolations(vs, len(files), "")
	if pf == "default" {
		fmt.Println()
		info("built-in rules: deny GPS / serials / user paths / thumbnail mismatch / emails / revision authors")
	}
}

func uiCompare() {
	sectionHeader("Compare Two Files")
	ma, _, err := loadMeta(prompt("file A"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	mb, _, err := loadMeta(prompt("file B"))
	if err != nil {
		errMsg(err.Error())
		return
	}
	fmt.Println()
	cs, gone, added := compareMeta(ma, mb)
	printCompare(ma, mb, cs, gone, added)
}

func uiThumb() {
	sectionHeader("Extract Thumbnail")
	p := prompt("file path")
	m, _, err := loadMeta(p)
	if err != nil {
		errMsg(err.Error())
		return
	}
	if len(m.thumb) == 0 {
		warnMsg("no embedded thumbnail")
		return
	}
	ext := ".jpg"
	if bytes.HasPrefix(m.thumb, []byte("\x89PNG")) {
		ext = ".png"
	}
	out := strings.TrimSuffix(p, filepath.Ext(p)) + ".thumb" + ext
	if err := os.WriteFile(out, m.thumb, 0o644); err != nil {
		errMsg(err.Error())
		return
	}
	okMsg(fmt.Sprintf("thumbnail (%s) → %s", humanBytes(len(m.thumb)), out))
}

func uiCatalog() {
	sectionHeader("Rule Catalog")
	var rows [][]string
	for _, r := range ruleCatalog {
		rows = append(rows, []string{r.ID, sevColor(r.Sev), r.Title})
	}
	table([]string{"RULE", "SEV", "TITLE"}, rows)
	fmt.Println()
	info("Reads: JPEG · PNG · WebP · GIF · TIFF · HEIC · MP4/MOV · PDF · DOCX/XLSX/PPTX · ODT/ODS/ODP")
	info("Scrubs: JPEG · PNG · WebP · GIF · HEIC · MP4/MOV · OOXML · ODF (PDF / TIFF: read-only)")
}

func uiExport() {
	sectionHeader("Export Last Result")
	if len(lastMetas) == 0 {
		warnMsg("inspect something first")
		return
	}
	f := prompt("format [txt|md|json|csv]")
	out := prompt("output file (blank = stdout)")
	s, err := render(lastMetas, f)
	if err != nil {
		errMsg(err.Error())
		return
	}
	if err := writeOut(s, out); err != nil {
		errMsg(err.Error())
	} else if out != "" {
		okMsg("wrote " + out)
	}
}

func uiDemo() {
	sectionHeader("Demo — synthetic photo, mockup and contract")
	ms := runDemo()
	lastMetas = ms
	for i, m := range ms {
		if i > 0 {
			fmt.Println()
			rule()
		}
		printMeta(m)
	}
	fmt.Println()
	info("try: OExifX --scrub on a copy of your own photo, then inspect the .clean file")
}

// ====================================================================
//  CLI
// ====================================================================

func usage() {
	banner()
	fmt.Print(`USAGE:
  OExifX [flags] PATH ...      files or folders (folders are walked)
  With no PATH the interactive TUI starts.

READ (JPEG PNG WebP GIF TIFF HEIC · MP4 MOV · PDF · DOCX XLSX PPTX ODT …):
  --all               List every tag, not just the privacy findings
  --min-sev SEV       Hide findings below SEV (INFO|LOW|MEDIUM|HIGH|CRITICAL)
  --geojson FILE      Write every GPS fix as GeoJSON
  --extract-thumb     Save embedded thumbnails as NAME.thumb.jpg

SCRUB (JPEG · PNG · WebP · GIF · HEIC · MP4/MOV · DOCX/XLSX/PPTX · ODT/ODS/ODP):
  --scrub             Write a cleaned copy NAME.clean.EXT (verified, no re-encode)
  --out FILE          Output path (single input only)
  --in-place          Replace the original (atomic rename)
  --strip-icc         Also remove colour profiles (kept by default)
  --no-orientation    Do not keep the Orientation tag in JPEGs

OSINT / CI / COMPARE:
  --link              Link files by shared serials, owners, document IDs, emails,
                      user names and places (≤ 250 m), plus a capture timeline
  --policy FILE       Publishing gate: deny / warn / allow rules, max-severity,
                      allow-value TAG=REGEX ("--policy default" = built-in rules);
                      --format github prints ::error annotations, plain for logs
  --compare A B       What changed in the metadata between two files

OUTPUT:
  --format FMT        txt | md | json | csv   (default: coloured report)
  --output FILE       Write the report to FILE
  --demo              Synthetic photo, mockup and contract
  --selftest          Parser / scrubber / fuzz regression suite
  --no-color          Disable colours
  --version           Print version

EXIT CODES:
  0 nothing HIGH or above · 1 error · 3 HIGH exposure (GPS, serials, user paths …)

EXAMPLES:
  OExifX IMG_0042.jpg
  OExifX --all report.docx
  OExifX ~/Pictures --geojson where.geojson
  OExifX --scrub photo.jpg && OExifX photo.clean.jpg
  OExifX --scrub --in-place ./to-publish/
  OExifX --link ~/case/photos --format json --output links.json
  OExifX --policy default --format github ./site/static/
  OExifX --compare original.jpg original.clean.jpg
  OExifX clip.mov            # MP4 / MOV / HEIC: GPS, device, dates; --scrub keeps offsets valid
`)
}

// parseInterleaved lets flags appear before or after positional paths.
func parseInterleaved(fs *flag.FlagSet, args []string) ([]string, error) {
	var pos []string
	for {
		if err := fs.Parse(args); err != nil {
			return nil, err
		}
		args = fs.Args()
		if len(args) == 0 {
			return pos, nil
		}
		pos = append(pos, args[0])
		args = args[1:]
	}
}

func main() { os.Exit(run()) }

func failMsg(err error) int { errMsg(err.Error()); return 1 }

func readMetaPath(p string) *Meta {
	m, _, err := loadMeta(p)
	if err != nil {
		return &Meta{Path: p}
	}
	return m
}

func run() int {
	fs := flag.NewFlagSet(APPNAME, flag.ContinueOnError)
	fs.Usage = usage
	all := fs.Bool("all", false, "")
	minSev := fs.String("min-sev", "INFO", "")
	geo := fs.String("geojson", "", "")
	thumbs := fs.Bool("extract-thumb", false, "")
	doScrub := fs.Bool("scrub", false, "")
	out := fs.String("out", "", "")
	inPlace := fs.Bool("in-place", false, "")
	stripICC := fs.Bool("strip-icc", false, "")
	noOrient := fs.Bool("no-orientation", false, "")
	format := fs.String("format", "", "")
	output := fs.String("output", "", "")
	demo := fs.Bool("demo", false, "")
	self := fs.Bool("selftest", false, "")
	nocol := fs.Bool("no-color", false, "")
	ver := fs.Bool("version", false, "")
	link := fs.Bool("link", false, "")
	pol := fs.String("policy", "", "")
	compare := fs.Bool("compare", false, "")
	paths, err := parseInterleaved(fs, os.Args[1:])
	if err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return 0
		}
		return 1
	}
	if *nocol {
		noColor = true
	}
	showAll = *all
	sopt = scrubOpts{keepICC: !*stripICC, keepOrientation: !*noOrient}
	ms := strings.ToUpper(*minSev)
	if _, ok := sevRank[ms]; !ok {
		errMsg("unknown --min-sev " + *minSev)
		return 1
	}
	switch {
	case *ver:
		fmt.Printf("%s v%s — %s\n", APPNAME, VERSION, TAGLINE)
		return 0
	case *self:
		if runSelfTest() != 0 {
			return 1
		}
		return 0
	case *demo:
		banner()
		sectionHeader("Demo — synthetic photo, mockup and contract")
		for i, m := range runDemo() {
			if i > 0 {
				fmt.Println()
				rule()
			}
			printMeta(m)
		}
		return 0
	case len(paths) == 0:
		mainMenu()
		return 0
	}
	if *compare {
		if len(paths) != 2 {
			errMsg("--compare needs two files")
			return 1
		}
		ma, _, err := loadMeta(paths[0])
		if err != nil {
			return failMsg(err)
		}
		mb, _, err := loadMeta(paths[1])
		if err != nil {
			return failMsg(err)
		}
		cs, gone, added := compareMeta(ma, mb)
		if *format == "json" {
			b, _ := json.MarshalIndent(map[string]any{"a": ma.Path, "b": mb.Path, "changes": cs, "exposures_gone": gone, "exposures_new": added}, "", "  ")
			writeOut(string(b)+"\n", *output)
		} else {
			banner()
			sectionHeader("Metadata Compare")
			printCompare(ma, mb, cs, gone, added)
		}
		if len(cs) > 0 {
			return 3
		}
		return 0
	}
	files, warns := collect(paths)
	if *out != "" && len(files) != 1 {
		errMsg("--out needs exactly one input file")
		return 1
	}
	if *doScrub {
		if *format == "" {
			banner()
			sectionHeader("Scrub")
		}
		bad := 0
		for _, f := range files {
			after, r, err := scrubFile(f, *out, *inPlace)
			if err != nil {
				bad++
				if *format == "" {
					warnMsg(f + ": " + err.Error())
				} else {
					fmt.Fprintln(os.Stderr, f+": "+err.Error())
				}
				continue
			}
			dst := *out
			if *inPlace {
				dst = f
			} else if dst == "" {
				dst = cleanName(f)
			}
			if *format == "" {
				printScrub(f, after, r, dst)
			} else {
				fmt.Fprintf(os.Stderr, "scrubbed %s → %s (%d block(s) removed; %s)\n", f, dst, len(r.Removed), r.Verified)
			}
		}
		if bad > 0 {
			return 1
		}
		return 0
	}
	var metas []*Meta
	for _, f := range files {
		m, _, err := loadMeta(f)
		if err != nil {
			warns = append(warns, err.Error())
			continue
		}
		var keep []Finding
		for _, x := range m.Findings {
			if sevRank[x.Severity] >= sevRank[ms] {
				keep = append(keep, x)
			}
		}
		if keep == nil {
			keep = []Finding{}
		}
		m.Findings = keep
		metas = append(metas, m)
		if *thumbs && len(m.thumb) > 0 {
			t := strings.TrimSuffix(f, filepath.Ext(f)) + ".thumb.jpg"
			if bytes.HasPrefix(m.thumb, []byte("\x89PNG")) {
				t = strings.TrimSuffix(t, ".jpg") + ".png"
			}
			if err := os.WriteFile(t, m.thumb, 0o644); err == nil {
				warns = append(warns, "thumbnail saved: "+t)
			}
		}
	}
	if *pol != "" {
		p, err := loadPolicy(*pol)
		if err != nil {
			return failMsg(err)
		}
		var vs []violation
		for _, m := range metas {
			// policies judge the full findings, not the --min-sev view
			full := readMetaPath(m.Path)
			vs = append(vs, p.evaluate(full)...)
		}
		f := *format
		if f == "" {
			banner()
			sectionHeader("Publishing Policy — " + p.source)
		}
		printViolations(vs, len(metas), f)
		for _, v := range vs {
			if v.Level == "error" {
				return 3
			}
		}
		return 0
	}
	if *link {
		groups, tl := linkFiles(metas)
		if *format == "json" {
			b, _ := json.MarshalIndent(map[string]any{"files": len(metas), "links": groups, "timeline": tl}, "", "  ")
			writeOut(string(b)+"\n", *output)
		} else {
			banner()
			printLinks(groups, tl, len(metas))
		}
		strong := 0
		for _, g := range groups {
			if !g.Weak {
				strong++
			}
		}
		if strong > 0 {
			return 3
		}
		return 0
	}
	if *geo != "" {
		if err := writeOut(geoJSON(metas), *geo); err != nil {
			errMsg(err.Error())
			return 1
		}
	}
	if *format == "" && *output == "" {
		banner()
		switch len(metas) {
		case 0:
		case 1:
			sectionHeader("Metadata Report")
			printMeta(metas[0])
		default:
			sectionHeader(fmt.Sprintf("Metadata Report — %d files", len(metas)))
			printBatch(metas)
		}
		for _, w := range warns {
			warnMsg(w)
		}
	} else {
		s, err := render(metas, *format)
		if err != nil {
			errMsg(err.Error())
			return 1
		}
		if err := writeOut(s, *output); err != nil {
			errMsg(err.Error())
			return 1
		}
		for _, w := range warns {
			fmt.Fprintln(os.Stderr, "warning: "+w)
		}
	}
	if len(metas) == 0 {
		return 1
	}
	for _, m := range metas {
		if sevRank[worst(m.Findings)] >= sevRank[SevHigh] {
			return 3
		}
	}
	return 0
}

// ---------------------------------------------------------------------------
// Help & Usage  (interactive menu [H])
// Page 1: in-app guide (what the tool does, every menu option, tips).
// Page 2: the full command-line reference (same text as --help).
// ---------------------------------------------------------------------------

type owlHelpItem struct{ key, text string }

func owlHelpWrap(s string, width int) []string {
	var out []string
	for _, para := range strings.Split(s, "\n") {
		words := strings.Fields(para)
		if len(words) == 0 {
			out = append(out, "")
			continue
		}
		cur := ""
		for _, w := range words {
			if cur != "" && len([]rune(cur))+1+len([]rune(w)) > width {
				out = append(out, cur)
				cur = w
			} else if cur == "" {
				cur = w
			} else {
				cur += " " + w
			}
		}
		out = append(out, cur)
	}
	return out
}

func owlHelpTitle(t string) {
	fmt.Println()
	fmt.Println("  " + col("▸ "+t, B+CY))
}

func owlHelpPara(lines []string) {
	for _, l := range lines {
		for _, w := range owlHelpWrap(l, 60) {
			fmt.Println("    " + col(w, W))
		}
	}
}

func owlHelpRows(items []owlHelpItem) {
	kw := 0
	for _, it := range items {
		if n := len([]rune(it.key)); n > kw {
			kw = n
		}
	}
	for _, it := range items {
		k := "[" + it.key + "]" + strings.Repeat(" ", kw-len([]rune(it.key)))
		for i, w := range owlHelpWrap(it.text, 56-kw) {
			if i == 0 {
				fmt.Println("    " + col(k, YLW+B) + "  " + col(w, W))
			} else {
				fmt.Println("    " + strings.Repeat(" ", kw+2) + "  " + col(w, W))
			}
		}
	}
}

func owlHelpRule() { fmt.Println(col(strings.Repeat("─", 66), CY)) }

func tuiHelp() {
	clear()
	banner()
	owlHelpRule()
	fmt.Println("  " + col("⬡  Help & Usage — "+APPNAME, B+CY))
	owlHelpRule()
	owlHelpTitle("WHAT IT DOES")
	owlHelpPara(owlHelpAbout)
	owlHelpTitle("HOW TO USE THE MENU")
	owlHelpPara(owlHelpFlow)
	owlHelpTitle("MENU OPTIONS")
	owlHelpRows(owlHelpMenu)
	owlHelpTitle("TIPS")
	owlHelpRows(owlHelpTips)
	fmt.Println()
	owlHelpRule()
	fmt.Println("  " + col("Next page: command-line flags & copy-paste examples", DIM))
	pause()
	clear()
	owlHelpCLI()
	fmt.Println()
	fmt.Println("  " + col("Tip: the same reference is printed by  "+APPNAME+" --help", DIM))
	pause()
}

var owlHelpAbout = []string{
	"OExifX reads and removes hidden metadata from photos, videos and documents: JPEG, PNG, WebP, GIF, TIFF, HEIC, MP4 / MOV, PDF, Office (DOCX / XLSX / PPTX) and OpenDocument files. It reports what could expose you: GPS location, camera and phone serial numbers, owner and author names, software, edit history, dates and embedded thumbnails (which may still show the uncropped picture).",
	"Scrubbing writes a clean copy without re-encoding the image or video, so quality is unchanged, and then re-reads the copy to verify that the metadata is really gone. For investigations, it can link many files together (same camera serial, same owner, nearby places) and build a timeline.",
}

var owlHelpFlow = []string{
	"Type the number of an option and press Enter. To check a single file use [1]; to clean it use [4]. [6] and [12] can reuse the last result. [H] opens this help, [0] or a blank line quits.",
	"Originals are never changed from this menu. Clean copies are saved as NAME.clean.EXT next to the original.",
}

var owlHelpMenu = []owlHelpItem{
	{"1", "Inspect a file: enter a path. Shows privacy findings by severity, GPS position with a map link, and the file structure."},
	{"2", "Show every tag: the same, but lists every EXIF / XMP / IPTC / document property found."},
	{"3", "Inspect a folder: enter a folder (blank = current). Gives an exposure summary for every supported file."},
	{"4", "Scrub a file: enter a path and an output name (blank = NAME.clean.EXT). Shows what was removed and confirms the copy is clean."},
	{"5", "Scrub a folder: enter a folder. It shows how many files will be cleaned and asks y/N, then writes a .clean copy of each."},
	{"6", "GPS map export: enter a file or folder (blank = last result) and a GeoJSON file name (blank = oexifx-gps.geojson). Open it in QGIS, geojson.io or Google Earth."},
	{"7", "Link files (OSINT): enter a folder or files. Groups files that share a camera serial, owner, document ID, e-mail, user name or place (within 250 m) and prints a capture timeline."},
	{"8", "Policy check (CI): enter a policy file (blank = built-in default rules) and the files to check. Shows pass or fail per file."},
	{"9", "Compare two files: enter file A and file B (e.g. original and clean copy). Shows metadata added, removed or changed."},
	{"10", "Extract thumbnail: enter a path. Saves the embedded preview as NAME.thumb.jpg (or .png)."},
	{"11", "Rule catalog: what each exposure means and why it matters."},
	{"12", "Export last result: choose txt, md, json or csv and an output file (blank = print to screen)."},
	{"13", "Run demo: a synthetic photo, design mock-up and contract full of metadata."},
	{"14", "Self-test: parsers, scrubbers and fuzzing checks."},
}

var owlHelpTips = []owlHelpItem{
	{"*", "Most social networks strip metadata, but e-mail, chat apps that send \"files\", cloud links and websites usually do not. Scrub before sharing."},
	{"*", "Colour profiles (ICC) are kept by default so colours stay correct. Use --strip-icc on the command line to remove them too."},
	{"*", "--in-place replaces the original (atomic). Keep a backup if you may need the metadata later."},
}

func owlHelpCLI() { usage() }
