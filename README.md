# VST Array Programs

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/palmskog/vst-array-progs/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/palmskog/vst-array-progs/actions?query=workflow%3ACI




Several C programs for manipulating and searching arrays, verified
using the VST framework in Coq.

## Meta

- Author(s):
  - Karl Palmskog
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.11 or later
- Additional dependencies:
  - [CompCert](http://compcert.inria.fr) 3.7
  - [VST](https://vst.cs.princeton.edu) 2.6
- Coq namespace: `VSTArrayProgs`
- Related publication(s): none

## Building and installation instructions

To build and install, do:

``` shell
git clone https://github.com/palmskog/vst-array-progs.git
cd vst-array-progs
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

## Documentation

More similar programs can be found in the [VST repository](https://github.com/PrincetonUniversity/VST/tree/master/progs).
