 
require import Int Bool SmtMap Distr FSet.

abstract theory RepoType.

type d. (* type of entries *)
type o. (* type of entries *)
type r. (* receipt *)

module type TS = {
  proc init(seed : int) : unit
  proc clock() : int
  proc put(x : o) : r
  proc getE(t : int) : d option
  proc get() : (int, d) fmap
}.


end RepoType.


abstract theory Repo.

type d.
op tdistr : int distr.

module TsU = {

  var r : (int, d) fmap  (* "timestamped" values *)
  var t : int            (* current time *)
  var i : int            (* initial time *)
  
  proc init(seed : int) = {
    i <-  seed;  
    t <- i;
    r <-  empty<:int, d>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d) = {
     t <- t + 1;
     r <- r.[t <- x];
     return t;
  }

  proc getE(t : int) = {
    return r.[t];
  }  

  proc get() = {
    return TsU.r;
  }  
}.



module Ts  = {

  var r : (int, d) fmap
  var t : int 
  
  proc init(seed : int) = {
    t <- 0;  
    r <- empty<:int, d>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d) = {
     t <- t + 1;
     r <- r.[t <- x];
     return t;
  }

  proc getE(t : int) = {
    return r.[t];
  }  

  proc get() = {
    return r;
  }  
}.

end Repo.



abstract theory RepoSet.

type d.
op tdistr : int distr.

clone export Repo as R with type d      <- d fset,
                            op   tdistr <- tdistr.
                      


module type BLT_Adv_Set = {
  proc react(ri : d fset) : d fset
}.


module TsU_Set (A : BLT_Adv_Set) = {
  
  proc init(seed : int) = {
    TsU.init(seed);
  }

  proc clock() = {
    var t;
    t <@ TsU.clock();
    return t;
  }  

  proc put(x : d fset) = {
    var t, r;
    r <@ A.react(x);
    t <@ TsU.put(r);
    return t;
  }

  proc getE(t : int) = {
    var r;
    r <@ TsU.getE(t);
    return r;
  }  

  proc get() = {
    return TsU.r;
  }    

}.

module TsU_1  = {

  var r : (int, d fset) fmap  
  var t : int            
  var i : int            
  
  proc init(seed : int) = {
    i <- seed;  
    t <- i;
    r <-  empty<:int, d fset>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d fset) = {
     t <- t + 1;
     r <- r.[t <- x];
     return t;
  }

  proc getE(t : int) = {
    return r.[t];
  }  

  proc get() = {
    return r;
  }  
}.


module TsU_Set_1 (A : BLT_Adv_Set)  = {
  
  proc init(seed : int) = {
    TsU_1.init(seed);
  }

  proc clock() = {
      var t;
      t <@ TsU_1.clock();
      return t;
  }  

  proc put(x : d fset) = {
    var t, r;
    r <@ A.react(x);
    t <@ TsU_1.put(r);
    return t;
  }

  proc getE(t : int) = {
      var r;
      r <@ TsU_1.getE(t);
      return r;
  }  

  proc get() = {
    return TsU_1.r;
  }    

}.


end RepoSet.

