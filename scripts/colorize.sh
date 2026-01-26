#!/bin/bash
# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright (C) 2026 Noah Sedlik
#
# Color output filter
#
RED='\033[0;31m'
ORANGE='\033[0;33m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

while IFS= read -r line; do
    # Color errors in red
    if echo "$line" | grep -qi "error\|failed\|fatal"; then
        echo -e "${RED}${line}${NC}"
    # Color warnings in orange
    elif echo "$line" | grep -qi "warning\|warn"; then
        echo -e "${ORANGE}${line}${NC}"
    # Color success messages in green
    elif echo "$line" | grep -qi "success\|passed\|complete"; then
        echo -e "${GREEN}${line}${NC}"
    # Color info in cyan
    elif echo "$line" | grep -qi "info\|note"; then
        echo -e "${CYAN}${line}${NC}"
    else
        echo "$line"
    fi
done
