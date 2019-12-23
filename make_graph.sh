#!/bin/bash
#TODO: remove redundancy of "-R ~~" with Makefile
coqdep -dumpgraph graph.dot \
  -R lib compcert.lib -R common compcert.common -R x86 compcert.x86 -R backend compcert.backend -R cfrontend compcert.cfrontend \
  -R driver compcert.driver -R flocq compcert.flocq -R exportclight compcert.exportclight -R cparser compcert.cparser \
  -R x86_64 compcert.x86_64 \
  **

dot -Tpng graph.dot > graph.png
