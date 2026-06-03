#!/usr/bin/env bash
# Download and extract the latest AFP release into the corpus directory.
# No-op if the corpus is already present (e.g. restored from cache).
set -euo pipefail

DEST="${1:-corpus}"
URL="${AFP_URL:-https://isa-afp.org/release/afp-current.tar.gz}"

mkdir -p "$DEST"
if find "$DEST" -name '*.thy' -print -quit 2>/dev/null | grep -q .; then
  echo "Corpus already present in '$DEST' ($(find "$DEST" -name '*.thy' | wc -l) .thy files) - skipping download."
  exit 0
fi

echo "Downloading $URL ..."
tmp="$(mktemp --suffix=.tar.gz)"
curl -fsSL "$URL" -o "$tmp"

echo "Extracting ..."
tar -xzf "$tmp" -C "$DEST"
rm -f "$tmp"

# Record the release name: the extracted top-level directory (e.g. afp-2026-06-01).
version="$(find "$DEST" -maxdepth 1 -mindepth 1 -type d -name 'afp-*' -printf '%f\n' | head -1 || true)"
[ -n "$version" ] && echo "$version" > "$DEST/AFP_VERSION"

echo "Extracted $(find "$DEST" -name '*.thy' | wc -l) .thy files (${version:-unknown})."
