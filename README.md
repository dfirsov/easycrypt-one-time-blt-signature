# Verified Security of BLT Signature Scheme 

This repository contains the EasyCrypt code associated with the paper "A. Buldas, D. Firsov, R. Laanoja, A. Truu. [Verified Security of BLT Signature Scheme ](https://eprint.iacr.org/2020/028.pdf)".

## Contents

- [BLT_ReadOnly_Hashed/](BLT_ReadOnly_Hashed) - adversary has read-only access to hashed repository. 
- [BLT_ReadWrite_Hashed/](BLT_ReadWrite_Hashed) - adversary has read/write access to hashed repository.
- [BLT_ReadWrite_Hashed_Set/](BLT_ReadWrite_Hashed_Set) - adversary has read/write access to repository containing sets of hashed entries.
- [BLT_ReadWrite_Plain/](BLT_ReadWrite_Plain) - adversary has read/write access to the plain repository.
- [BLT_ReadWrite_Hashed_MT/](BLT_ReadWrite_Hashed_MT) - adversary has read/write access to the repository containing roots of Merkle Trees.

## Setup
* For this project we used the version of EasyCrypt (1.0) theorem prover with GIT hash: r2022.04-48-gc8d3d6c1.
* EasyCrypt was configured with support from the following SMT solvers: Why3@1.5.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.1.
* To check the development run:

      $> cd DEVELOPMENT_FOLDER
      $> bash checkall

* If you want to typecheck this code in Emacs then you must update your load path. Make sure your `~/.emacs` file contains the following load paths:

      '(easycrypt-load-path
       (quote
        ( "DEVELOPMENT_PATH/BLT_ReadOnly_Hashed" 
          "DEVELOPMENT_PATH/BLT_ReadWrite_Hashed"
          "DEVELOPMENT_PATH/BLT_ReadWrite_Hashed_MT"
          "DEVELOPMENT_PATH/BLT_ReadWrite_Hashed_Set"
          "DEVELOPMENT_PATH/BLT_ReadWrite_Plain")))






