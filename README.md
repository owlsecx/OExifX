# 🦉 OExifX

<p align="center">
  <img src="https://img.shields.io/badge/Platform-Linux-0a0c10?style=flat-square"/>
  <img src="https://img.shields.io/badge/Category-Forensics%20/%20DFIR-blue?style=flat-square"/>
  <img src="https://img.shields.io/badge/License-MIT-green?style=flat-square"/>
  <img src="https://img.shields.io/badge/Part%20of-OwlSec%20Toolkit-7b5ea7?style=flat-square"/>
  <img src="https://img.shields.io/badge/Version-1.0-cyan?style=flat-square"/>
</p>

> **OExifX** — Metadata reader & scrubber (EXIF, GPS, XMP, PDF, Office) ║

---

> ⚠️ **AUTHORISED USE ONLY** — Use only on systems you own or have explicit written permission to test. Unauthorised use is illegal.

---

## 📌 Overview

OExifX — Metadata reader & scrubber (EXIF, GPS, XMP, PDF, Office). Metadata Reader & Scrubber Reads the metadata people forget they publish — EXIF (IFD0 / Exif / GPS / Interop / IFD1 thumbnail), XMP, IPTC, JPEG comments, PNG text chunks, WebP / GIF metadata, PDF Info + XMP, and OOXML / ODF document properties including track-change and comment authors — and grades the privacy exposure: GPS fixes, device serial numbers, names, user paths, emails, pre-edit thumbnails, editing history. The scrubber removes metadata without re-encoding (JPEG, PNG, WebP, GIF, OOXML, ODF), keeps colour profiles and orientation, and verifies the result: image data byte-identical and pixels decode the same.

---

## ✨ Features

- Read metadata from images and documents (EXIF, GPS, XMP, PDF, Office)
- Scrub sensitive location and author fields before sharing
- Batch and single-file workflows with clear before/after views
- Highlight high-risk tags commonly used in OSINT leaks
- Offline stdlib-friendly processing pipeline
- Export inventories of remaining metadata

---

## ⚙️ Requirements

- **Linux**
- **Go 1.21+** (stdlib only; `CGO_ENABLED=0`)

---

## 🚀 Usage

```bash
go build -ldflags="-s -w" -o OExifX OExifX.go
./OExifX --help
./OExifX --input photo.jpg
./OExifX --input photo.jpg --scrub --output clean.jpg
./OExifX --path ./album --format json
```

---

## 📦 Part of OwlSec Toolkit

This tool is part of the **OwlSec** suite — a collection of 300+ security and privacy tools.

🔗 [owlsec.org](https://owlsec.org)

---

## ©️ License

MIT License — © Khaled S. Haddad
