#!/bin/bash

mkdir -p boards/9x9 boards/12x12 boards/16x16 boards/25x25

python3 board_generator.py boards/9x9/b 50 3 3 30
python3 board_generator.py boards/12x12/b 50 3 4 60
python3 board_generator.py boards/16x16/b 50 4 4 110
python3 board_generator.py boards/25x25/b 20 5 5 200

echo "Boards generated."
