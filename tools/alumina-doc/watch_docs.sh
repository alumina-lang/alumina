#!/bin/bash

if ! command -v inotifywait &> /dev/null; then
    echo "inotifywait could not be found (inotify-utils)"
    exit 1
fi

serve() {
    cd $BUILD_DIR/html
    python3 -m http.server
}

serve &

while true; do
    while ! make -q docs; do
        make docs || break
    done
    inotifywait --exclude '^(\./)?(target/|build/)' -qre close_write .;
done
