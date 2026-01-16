#!/bin/sh
./autogen.sh
./configure
make -j6 | tee build.log

# make check
# make install

# aldor -g loop

# cd test
# create aldorconf.as
# ...
