#!/usr/bin/env bash
set -euo pipefail
cargo test sorted_language --lib
cargo bench --bench sorted_language_scaling
