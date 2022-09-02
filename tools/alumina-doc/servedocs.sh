#!/bin/bash

serve() {
    cd $BUILD_DIR/html
    python3 -m http.server
}

serve &

while true; do
    while ! make -q docs; do
        make docs;
    done
    inotifywait --exclude '^(\./)?(target/|build/)' -qre close_write .;
done
