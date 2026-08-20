# Licensing note for engine-check/

`harness.cpp` and `stubs.cpp` include VCMI headers and link against VCMI's
battle classes (https://github.com/vcmi/vcmi, GPL-2.0-or-later per its
`license.txt`). To keep distribution unambiguous, everything in this
directory is licensed **GPL-2.0-or-later**, matching VCMI.

The rest of the artifact (see ../LICENSE) does not link against VCMI: the
Python model cites VCMI source locations as *documentation* and reimplements
the arithmetic independently — that is the whole point of the cross-check.
