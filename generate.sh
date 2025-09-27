#!/bin/bash

# download most up-to-date syntax file
wget -L https://raw.github.com/VNNLIB/VNNLIB-Standard/main/syntax.cf

# generate BNFC Agda parser
bnfc -d --agda syntax.cf -o src # add the -m flag to generate the make file as well

# delete the duplicated syntax file
rm syntax.cf