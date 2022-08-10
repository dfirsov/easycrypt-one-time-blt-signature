
Repository
==========

At each moment `t`, repository contains set of hashes.

```
  R.get(t : int) : (hash fset) option 
```
More specifically, the valid signature of message `m` at time `t` must contain an entry `R.get(t) = Some hs` so that 

```{ h(tag sk t || m), h(tag sk t) } ⊆ hs```.

Adversary `A` can react on repository writes, by adding new entries: 

```
  R.put(x : hash fset) := {
    t := t + 1;
    y := A.react(x);
    R.r[t] = y ∪ x;
    return t;
  }
```


Assumptions
===========

- Tag-and-Hash non-malleability
- Tag-and-Hash unpredictability (optional)
- Tag-system phantom-freeness 


Sketch of the proof of EUF
=========================

Assume that `A` makes a forgery.

1. Oracle not used: Tag-system is unsafe.

2. Oracle used at time `t` and signature is forged for time `t'`.

   2.1. `t < t'`: Tag-system is unsafe.

   2.2. `t > t'`: Use Tag-&-Hash unpredictability assumption and construct adversaires `A₁` and `A₂`.
        
        A₁: Run A with no oracles provided. Uniformly choose an entry
        from repository from the interval [1..t].
  
        A₂: Run A with tagging oracle.

   Clearly, with probability `1/t` `A₁` will choose correct entry (same as
   `A` would choose with full info). The rest follows.

   2.3. `t = t'`: Let the signature be forged for message `m`; in this
   case one of the entries at `R.r[t]` must contain

       h(tg || m), h(tg)

   which the adversary produced from knowledge of

       h(tg || m'), h(tg) 

   So, `A` for Tag-&-Hash non-malleability can be constructed by sending an oracle two
   requests `m'` and `EMPTY`. After this adversary `A` will generate 
   `y = h(tg || m')`.

