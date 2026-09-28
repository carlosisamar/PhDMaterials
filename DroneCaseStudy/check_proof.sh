#!/bin/bash

echo "
*******************************************************************************
Checking proof in KeYmaera X.
*******************************************************************************
"

set -e

while getopts "u:" flag; do
    case $flag in
        u) user=${OPTARG};;
    esac
done

if [ -z "$user" ]
then
  user="$(whoami)"
  if [ -z "$user" ]
  then
    echo "Failed to detect \$user for licenses. Provide username with -u."
    exit 1
  fi
fi

docker start kyx
docker exec kyx bash -c 'java -jar keymaerax.jar -prove Drone_Example_Proof.kyx'

docker exec kyx bash -c 'java -jar keymaerax.jar -prove Drone_Noisy_Example_Proof.kyx'

echo "
*******************************************************************************
Finished checking proof in KeYmaeara X.
*******************************************************************************
"

docker stop kyx
