
Repository
==========

At each moment `t`, repository contains set of hashes which represent the roots of Merkle Trees.

```
  R.get(t : int) : (hash fset) option 
```
More specifically, the valid signature of message `m` at time `t` must contain an entry `R.get(t) = Some hs` so that 
there exists a hash-chain `c` so that `leaf c = h(tag sk t || m) || h(tag sk t)` and `root c ⊆ hs`.

Adversary has full control over the repository (can even sabbotage it)

```
  R.put(x : hash fset) := {
    t := t + 1;
    y := A.react(x);
    R.r[t] = y;
    return t;
  }
```


Assumptions
===========

- Tag-and-Hash chain-non-malleability
- Tag-and-Hash chain-unpredictability
- Tag-system phantom-freeness


Sketch of the proof of EUF
=========================

Assume that `A` makes a forgery.

1. Oracle not used:  Tag-system is unsafe.

2. Oracle used at time `t` and signature is forged for time `t'`.

   2.1. `t < t'`: Tag-system is unsafe.

   2.2. `t > t'`: Use S&H chain-unpred. and construct adversaires `A₁` and `A₂` as follows
        
        A₁: Run `A` with no oracles provided. Uniformly choose an entry
        from repository from the interval [1..t].
  
        A₂: Run A with tagging oracle.

   Clearly, with probability `1/t` adversary `A₁` will choose the correct entry (same as
   `A` would choose with full info). The rest follows.

   2.3. `t = t'`: Use S&H chain-non-mall. and construct adversaries= `A₁`, `A₂`, and `A₃` out of `A`.

        A₁: Since t = t' then A₁ is simply A with no oracles provided.

        A₂: A was able to create a valid entry into the repository
            from seeing values h( h(m) || tag sk t ) || h(tag sk
            t). Therefore A₂ can be constructed out of A by providing
            him a "sign-and-hash" oracle [h(tag sk t || ∙ )] which
            creates Log.

        A₃: A with full information (~oracle tag sk ∙).

   Clearly, if `A` succeeded in BLT forgery then `A₁`, `A₂`, and `A₃` will win
   in  S&H chain-non-mall. game.

