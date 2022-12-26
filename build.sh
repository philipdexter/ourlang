#!/usr/bin/env sh

set -ex

docker build . -t dexter22
docker run --rm dexter22
