 
require import Int Bool SmtMap Distr.


abstract theory Repo.

type Time = int.
type d.

module type TS = {
  proc init() : unit
  proc clock() : Time
  proc put(x : d) : Time
  proc getE(t : Time) : d option
  proc get() : (Time, d) fmap
}.

op tdistr : Time distr.
axiom d_ll : is_lossless tdistr.
axiom tdistr_pos t : t \in tdistr => 0 <= t.


module TsU : TS  = {

  var r : (Time, d) fmap  (* "timestamped" values *)
  var t : Time            (* current time *)
  var i : Time            (* initial time *)
  
  proc init() = {
    i <$ tdistr;  
    t <-  i;
    r  <-  empty<:Time, d>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d) = {
     t <- t + 1;
     r <- r.[t <- x];
     return t;
  }

  proc getE(t : Time) = {
    return r.[t];
  }  

  proc get() = {
    return TsU.r;
  }  
}.



module Ts : TS = {

  var r : (Time, d) fmap
  var t : Time 
  
  proc init() = {
    t <- 0;  
    r <- empty<:Time, d>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d) = {
     t <- t + 1;
     r <- r.[t <- x];
     return t;
  }

  proc getE(t : Time) = {
    return r.[t];
  }  

  proc get() = {
    return r;
  }  
}.


module Ts1 : TS = {

  var r : (Time, d) fmap
  var t : Time 
  
  proc init() = {
    t <- 0;  
    r <- empty<:Time, d>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : d) = {
    if(t = 0){
      t <- t + 1;
      r <- r.[t <- x];
    }
    return t;
  }

  proc getE(t : Time) = {
    return r.[t];
  }

  
  proc get() = {
    return r;
  }  

}.


end Repo.

