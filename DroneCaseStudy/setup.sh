#!/bin/bash


mkdir -p Licensing
chmod -R 757 "$PWD/Licensing"

echo ""
echo "Loading Docker Image"
echo ""
docker load < keymaerax.tar.gz

echo ""
echo "Creating Docker Container"
echo ""
docker create -it -v "$PWD/Licensing:/root.WolframEngine/Licensing" -w /root -p 8090:8090 --name kyx keymaerax
echo "Starting container for Mathematica license activation"
docker start kyx
echo ""
echo "If you want to re-initialize the container but keep an earlier Wolfram Engine license: abort Wolfram Engine activation with Ctrl-d and comment out line 9 of setup.sh"
echo ""
docker exec -it kyx wolframscript "-activate"
docker commit kyx keymaerax:latest

docker stop kyx