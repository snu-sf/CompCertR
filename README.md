# CompCertR
This is the refactored version of [CompCert 3.5](https://github.com/AbsInt/CompCert/tree/v3.5) in the style of open simulations.

Main differences include:  

1) Proving "guarantee" conditions of each translations.  
In the context of open simulations, CompCert only "rely" on it (by external call axioms) but does not "guarantee" it.  
To address this gap, we needed to prove "guarantee" conditions for each per-pass proofs.  
We needed to prove additional properties for injection passes only.  

2) Changing "Callstate" of each language to carry function pointer, instead of function definition.  
External module's function definition may not be visible in the local module, but it should be able to call it with function pointer.  

3) Relaxing each translation's simulation relation so that first stack (`main`, in CompCert) may have called with arguments.  
This change affects only three passes, and except for the Stackingproof the change is very small.  

4) Generalizing "step" relation to respect "symbol environment".  

Note that, in spite of these technical modifications, mathematical meaning of the semantics is unchanged.  
- For source languages, see `/cfrontend/ClightBigstep.v` and `/cfrontend/Cstrategy.v` which proves the small-step variant and big-step variant of the semantics are equivalent. We modified small-step variant but it is still equivalent to (unmodified) big-step semantics.
- For target language (`/x86/Asm.v`), we didn't modify the semantics at all.

## Installation Instructions
Our development is tested with Coq 8.9.1. CompCertR only supports x86_64 architecture.

1) Follow _2-2 Prerequisites_ in [standard CompCert build process](http://compcert.inria.fr/man/manual002.html) to install prerequisites.  
- Install [opam](https://opam.ocaml.org/) **>= [2.0.0](https://opam.ocaml.org/blog/opam-2-0-0/)**.
- Install required dependencies. <pre>
opam switch 4.09.0               # Use OCaml version 4.09.0
eval \`opam env\`
opam install coq=8.10.1           # Use Coq version 8.10.1
opam install menhir=<b>20190924</b>     # Use Menhir version 20190924
</pre>

2) Install [Paco coq library](https://github.com/snu-sf/paco) via opam. (version 4.0.0)
   `opam repo add coq-released https://coq.inria.fr/opam/released; opam install coq-paco`  
   
3) Configure and Build.  
  `./configure` with proper architecture.  
  `make -j[N]` 
