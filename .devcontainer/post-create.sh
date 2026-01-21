#!/bin/bash
set -e

echo "=== Starting post-create setup ==="

# --- Independent tasks (run in parallel) ---

# System packages (completely independent)
(
    echo "[apt] Installing system packages..."
    sudo apt-get update && sudo apt-get install -y linux-perf
    echo "[apt] Done"
) &
APT_PID=$!

# Rustup nightly (uses /usr/local/rustup, independent of cargo dirs)
(
    echo "[rustup] Installing nightly toolchain..."
    rustup toolchain install nightly
    echo "[rustup] Done"
) &
RUSTUP_PID=$!

# --- Sequential cargo tasks (depend on volume permissions) ---

echo "[chown] Fixing volume permissions..."
sudo chown -R vscode:vscode /usr/local/cargo "${containerWorkspaceFolder:-/workspaces/parpl}/target"
echo "[chown] Done"

echo "[cargo] Installing sccache..."
cargo binstall --no-confirm sccache

echo "[cargo] Installing cargo-fuzz and flamegraph..."
cargo install cargo-fuzz flamegraph

# --- Wait for parallel tasks ---

echo "[wait] Waiting for background tasks..."
wait $APT_PID
wait $RUSTUP_PID

echo "=== Post-create setup complete ==="
