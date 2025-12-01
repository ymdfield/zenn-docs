#!/bin/sh
docker run --rm -v $PWD:/workspace -p 8000:8000 --name zenn zenn npx zenn preview
