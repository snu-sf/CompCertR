# CompCertR
This is the refactored version of [CompCert 3.5](https://github.com/AbsInt/CompCert/tree/v3.5) in the style of open simulations.

Main differences include:  

(i) Proving "guarantee" conditions of each translations.  
In the context of open simulations, CompCert only "rely" on it (by external call axioms) but does not "guarantee" it.  
To address this gap, we needed to prove "guarantee" conditions for each per-pass proofs.  
We needed to prove additional properties for injection passes only.  

(ii) Changing "Callstate" of each language to carry function pointer, instead of function definition.  
External module's function definition may not be visible in the local module, but it should be able to call it with function pointer.  

(iii) Relax each translation's simulation relation so that first stack (`main`, in CompCert) may have called with arguments.  
This change affects only three passes, and except for the Stackingproof the change is very small.  

(iv) Changing "step" relation to respect "symbol environment".  

## Installation Instructions
Our development is tested with Coq 8.9.1, linux. We only support x86_64 architecture.

(i) Follow **2-2 Prerequisites** in [standard CompCert build process](http://compcert.inria.fr/man/manual002.html) to install required dependencies.  

(ii) Install [Paco coq library](https://github.com/snu-sf/paco) via opam.  
   `opam repo add coq-released https://coq.inria.fr/opam/released; opam install coq-paco`  
   
(iii) Configure and Build.  
  `./configure` with proper architecture.  
  `make -j[N]` 
