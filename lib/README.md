Pre-compiled Libraries
=======================

This directory contains the nanopass framework in a single pre-compiled binary
that can be used with the Chez Scheme (the full compiler) or Petite Chez Scheme
(the interpreter).  These binaries follow Chez Scheme's naming convention of
using the library name (`nanopass`) with the standard compiled file extension
(`so`) for the file.

Right now this is compiled for Chez Scheme 8.4 on the 32-bit and 64-bit
Intel/AMD platforms for Linux and Mac OS X.  (I can compile this for other
operating systems, though I'll need to install those somewhere in order to do
the compilation.)

Directory Structure
====================

```
lib/                # the main library directory
  csv8.4/           # compiled libraries for Chez Scheme 8.4
    i3le/           # 32-bit Linux library
    ti3le/          # Threaded 32-bit Linux library
    a6le/           # 64-bit Linux library
    ta6le/          # Threaded 64-bit Linux library
    i3osx/          # 32-bit Mac OS X library
    ti3osx/         # Threaded 32-bit Mac OS X library
    a6osx/          # 64-bit Mac OS X library
    ta6osx/         # Threaded 64-bit Mac OS X library
```

These directories correspond to the machine types used by Chez Scheme
(accessible through the procedure `machine-type`).

Usage
======

To use the binary nanopass library, determine which directory you need, based
on which version of petite you have installed (if you are not sure start petite
and run `(machine-type)` at the REPL, this should correspond to one of the
listed subdirectories in the Directory Structure section---You can determine
the version of Chez Scheme you are using by running the `(scheme-version)`
command).

Once you have determined what version you are using you can start petite with
an extended library directories statement.  Then you should be able to start
using the nanopass library by importing the nanopass library with
 `(import (nanopass))`

```
petite --libdirs .:<NANOPASS_HOME>/lib/csv8.4/<machine-type>
Petite Chez Scheme Version 8.4
Copyright (c) 1985-2011 Cadence Research Systems

> (import (nanopass))
```

For instance, if you are using the 64-bit Mac OS X (single-threaded) this
command would look like:

```
petite --libdirs .:<NANOPASS_HOME>/lib/csv8.4/i3osx
Petite Chez Scheme Version 8.4
Copyright (c) 1985-2011 Cadence Research Systems

> (import (nanopass))
```

You can also add the directory from the REPL as follows (assuming
nanopass-framework is a subdirectory of your home directory):

```
petite

> (library-directories
    (cons
      (format
         "~~/nanopass-framework/lib/csv8.4/~s"
        (machine-type))
    (library-directories)))
> (import (nanopass))
```

Note: This technique will not work within an R6RS library or program, you'll
need to use the `--libdirs` command line flag as in the first example.
