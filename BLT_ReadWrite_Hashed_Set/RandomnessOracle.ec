

require import DInterval.

module type ROracle = {

  proc init() : int
  proc rndStr() : int
  
}.

module RO : ROracle = {

  var t : int
  proc init() = {
    t <$ dinter 0 100;
    return t;
  }

  proc rndStr() = {
    return t;
  }
 
}.
