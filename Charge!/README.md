Charge!
=======

Charge! is a framework for embedding logics inside of Coq.

Dependencies
------------

Charge! depends on the following projects.

 - Containers
 - ExtLib
 - MirrorCore

All of these should be accessible when building Coq files. If these libraries
are installed with your Coq distribution then everything should work.

*Local Installation*

If you do not wish to install any of the libraries for any reason, you can
write the include lines in the ```_CoqPath``` file which will be included when
constructing the ```_CoqProject``` file. For example, for a local installation
of MirrorCore, include the following in the ```_CoqPath``` file:

```
-Q ../relative/path/to/mirror-core/theories MirrorCore
-I ../relative/path/to/mirror-core/src
```

In Coq 8.5 all paths inside this file should be written with ```-Q``` since
Coq uses ```-Q``` to include ```user-contrib``` which is where packages are
installed.

For convenience, we recommend making symbolic links in this directory or the
parent directory.

*NOTE*: The ```_CoqPath``` file should *not* be checked in. It should contain
user-specific configuration only. When Charge! is installed via opam,
```_CoqPath``` will be empty and all dependencies will be installed.

Building
--------

Once you have configured the dependencies, you can simply run ```make```
to build everything.

Adding Files
------------

If you add a file to this project, you *must* record its existance in the
```_CoqConfig``` file.