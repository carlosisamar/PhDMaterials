#!/bin/bash
# The script can be invoked with -l and -m options

# -m MAC_ADDRESS specifies the MAC address
# If not specified, the script will try to guess a default address

# run example
# setup.sh -m MAC_ADDRESS

set -e

while getopts "l:m:u:" flag; do
    case $flag in
        m) macaddr=${OPTARG};;
        u) user=${OPTARG};;
    esac
done

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    # *)          machine="UNKNOWN:${unameOut}"
esac
echo "Running on $machine"
case "$machine" in
  Linux)  ethif=eth0;;
  Mac)    ethif=en0;;
esac

if [ -z "$macaddr" ]
then
  macaddr="$(ifconfig $ethif | grep -o -E '([[:xdigit:]]{1,2}:){5}[[:xdigit:]]{1,2}')"
  if [ -z "$macaddr" ]
  then
    echo "Failed to detect \$macaddr for setup. Provide MAC address with -m."
    exit 1
  fi
fi

# Set up licensing for WolframEngine
# The folder for Licensing is given lax permissions so that WolframEngine's activation process inside Docker can write to it
mkdir -p Licensing
chmod -R 757 "$PWD/Licensing"

echo "Removing previous docker image"
docker rm -f kyx
echo "Building docker image"
docker build -t keymaerax .
docker create --mac-address $macaddr -it -v "$PWD/Licensing:/root.WolframEngine/Licensing" -w /root -p 8090:8090 --name kyx keymaerax bash
echo "Starting container for initialization process"
docker start kyx
# initialize .keymaerax directory with Z3
docker exec -it kyx bash -c 'java -da -jar keymaerax.jar -launch -setup'
# add and modify configuration
docker cp ./keymaerax.math.conf kyx:/root/keymaerax.conf
docker exec -it kyx bash -c 'rm .keymaerax/keymaerax.conf;cp keymaerax.conf .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_LINK_NAME = /usr/local/Wolfram/WolframEngine/14.1/Executables/MathKernel" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_JLINK_LIB_DIR = /usr/local/Wolfram/WolframEngine/14.1/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "WOLFRAMENGINE_TCPIP = false" >> .keymaerax/keymaerax.conf'
docker exec -it kyx bash -c 'echo "IS_DOCKER = true" >> .keymaerax/keymaerax.conf'
docker exec -it kyx sed -i "s/QE_TOOL = z3/QE_TOOL = wolframengine/g" .keymaerax/keymaerax.conf
docker inspect -f '{{ .NetworkSettings.IPAddress }}' kyx > dockerip.txt
docker exec -it kyx sed -i "s/HOST = 127.0.0.1/HOST = $(<dockerip.txt)/g" .keymaerax/keymaerax.conf

docker commit kyx keymaerax:latest
docker stop kyx
# docker save keymaerax:latest | gzip > keymaerax.tar.gz

# mv keymaerax.tar.gz ../