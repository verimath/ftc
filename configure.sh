#!/bin/sh

coq_makefile -R ./src/tactics Tactics -R ./src/algebra Algebra -R ./src/ftc FTC -R ./src/reals Reals -f Make -o Makefile
