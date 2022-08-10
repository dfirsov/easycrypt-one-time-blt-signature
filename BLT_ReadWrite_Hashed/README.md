
Repository
==========

At each moment `t`, repository contains a pair of hashes which represents the binding of a
message and a tag: 

```
  R.get(t : int) : (hash * hash) option 
```

More specifically, the valid signature of message `m` at time `t` must contain an entry 
```R.get(t) = Some (H(tag sk t || m), H(tag sk t))```.

Adversary can read and write to the repository, but can not interfere:

```
  R.put(x : hash * hash) := {
    t := t + 1;
    R.r[t] = x;
    return t;
  }
```


Assumptions
===========

- Forward-security
- Tag-and-Hash unpredictability
- Tag Phantom-freeness 


Sketch of the proof of EUF
=========================

Assume that `A` makes a forgery.

1. Oracle not used:  Tag-system is unsafe.

2. Oracle used at time `t` and signature is forged for time `t'`.

   2.1. `t < t'`: Tag-system is unsafe.

   2.2. `t > t'`: T&H unpred. assumption.

   2.3. `t = t'`: Adversary found a collision `H(tagk sk t || m) = H(tag sk t || m')` where `m` is part of a forgery and `m'` is used in the oracle request.

        

