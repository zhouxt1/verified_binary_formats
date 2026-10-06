#!/usr/bin/env bash
# Regenerate the checked-in syntax tables (src/gen/) from the transcribed
# syntax tables (syn/), with vsync.
set -euo pipefail
cd "$(dirname "$0")/.."
cargo build --release -q -p vsync
for c in h264 h265; do
    ./target/release/vsync "vh26x-tool/syn/$c.syn" "vh26x-tool/src/gen/$c.rs" > /dev/null
done
