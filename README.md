# PhD Materials

This repository contains the reproducibility package of my PhD. thesis.

## Chapter 3

The reproducibility package for Chapter 3 is hosted [here](https://figshare.com/articles/dataset/Artifact_for_Safe_Temperature_Regulation_Formally_Verified_and_Real-World_Validated/28869218).
This package includes the Incubator formal model and proof and the data for the experiments.

## Chapter 4

The Drone and Noisy Drone formal models and proofs are located in the `DroneCaseStudy` folder. 
The contents of that folder are as follows:

| File/Folder Name                                | Description                                                          |
| ----------------------------------------------- | -------------------------------------------------------------------- |
| `DockerBuild`                                   | Contains the required script and sources to create the Docker image. |
| &nbsp;&nbsp;&nbsp;&nbsp;`DockerBuild/build.sh`  | Script to create the Docker image to run the proof.                  |
| &nbsp;&nbsp;&nbsp;&nbsp;`DockerBuild/Drone_Example_Proof.kyx` | File containing the model and proof tactic of the Drone without noise to be verified.           |
| &nbsp;&nbsp;&nbsp;&nbsp;`DockerBuild/Drone_Noisy_Example_Proof.kyx` | File containing the model and proof tactic of the drone with noise to be verified.           |
| &nbsp;&nbsp;&nbsp;&nbsp;/Other files             | Files needed to create the docker image.                                        |
| `setup.sh`                                      | Script to mount the image and activate the Wolfram license.          |
| `check_proof.sh`                                | Script to check all the proofs using KeYmaera X.                     |


### Setup and Checking the Proofs

In order to run the scripts, Docker needs to be installed on your machine and working correctly, see [docs.docker.com/get-docker/](https://docs.docker.com/get-docker/). KeYmaera X requires Wolfram Engine for QE. The Wolfram Engine license can be obtained for free and you will be prompted during the setup to login with your account. We present two options to check the correctness of our proof.


1. Go to the folder `Proof/DockerBuild/` and run `./build.sh`. This script creates the docker image `keymaerax.tar.gz` and a container called `kyx` with all necessary components to run KeYmaera X and check the proof.
2. Go to the folder `Proof/` and run `./setup.sh`. This script mounts the docker image `keymaerax.tar.gz` in a container called `kyx` with all necessary components to run KeYmaera X and check the proof.
3. Log in with a Wolfram ID when prompted
4. Once the setup is complete run `./check_proof.sh`. This script calls KeYmaera X with our proof in order to check it. It usually takes around 5-10 minutes, but may take up to 20-30 minutes depending on the machine.
5. You should see the output:
```
PROVED Drone Example: tactic=<undefined>,tacticsize=18,budget=0[s],duration=9971[ms],qe=876[ms],rcf=0,steps=6075

...

PROVED Drone Noisy Example: tactic=<undefined>,tacticsize=18,budget=0[s],duration=128169[ms],qe=114628[ms],rcf=0,steps=8107

*******************************************************************************
Finished checking proof in KeYmaeara X.
*******************************************************************************

```

## Chapter 5.

The dLCHP shallow embedding is contained in the `dlchpShallowEmbedding` folder and all the required libraries to verify it are located in the `libraries` folder.
To inspect and run the Isabelle files, download [Isabelle2025](https://isabelle.in.tum.de/website-Isabelle2025/index.html) and launch Isabelle from the main directory with the command 
```
PATH/isabelle jedit -d . -l dlCHP_Toolkit
```
Usually `PATH` is in the directory `INSTALLATION_PATH/Isabelle2025/bin/isabel`

Note: `Isabelle2025-1` and `Isabelle2025-2` will not work due to dependency changes affecting AFP libraries.
