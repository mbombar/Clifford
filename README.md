This repository contains the work that was developped during my undergraduate internship in INRIA Sophia-Antipolis, under the supervision of Cyril Cohen.

How to install the repository ?
-----------------------------

1. Install a newer version of Coq.

It is necessary to install a recent version of Coq (>= v8.4), and a newer version of OCamL (using opam for instance for more information see the opam repository : https://github.com/ocaml/opam).

If it is not already done : 
```
$ opam init
$ opam install coq
```

To accelerate the installation, it is possible to parallelize jobs :
```
$ opam install coq -j $NBRE
```
```
$ eval ̀ opam config env`
```

2. Install mathematical-components.

   First, clone the repository from GitHub
```
$ git clone https://github.com/math-comp/math-comp.git
$ cd math-comp/mathcomp
$ make (optional : -j $NBRE)
$ make install 
```

3. Install CoqEAL.

```
$ git clone https://github.com/CoqEAL/CoqEAL.git
$ cd CoqEAL
```

This repository is not really up-to-date and it is necessary to change branch :

```
$ git checkout test_ring
$ cd theory
$ make
$ make install
```

4. Final Step : 

```
$ git clone https://github.com/mbombar/Clifford.git
$ cd Clifford/Clifford
$ make
$ make install
```