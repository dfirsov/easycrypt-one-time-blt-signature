pragma Goals : printall.

require import Int Real Distr SmtMap FSet.

require import BLT_Instance.
require import SHGame.
require import RandomnessOracle.

theory Case3_A2_Theory.

module Tag_Wrap_2 : Tag_Oracle = {
   var usedFlag : bool
   var usedTag  : tag

  proc init(pk : pkey, sk : skey) : unit = {
    usedFlag <-  false;
    usedTag  <-  deftag;
  }

  proc createTag(t : int) : tag = {

    return usedTag;
  }

  proc verifyTag(s : tag) : bool = {
    return true;
  }

  proc askedTag() : tag = {
    return usedTag;
  }
   
}.

module TsU_2 : TS = {

  var r : (int, hash_output fset) fmap  (* "timestamped" values *)
  var t : int            (* current time *)
  var i : int            (* initial time *)
  
  proc init(seed : int) = {
    i <- seed;  
    t <- i;
    r <-  empty<:int, hash_output fset>;
  }

  proc clock() = {
    return t;
  }  

  proc put(x : hash_output fset) = {
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


module TsU_Set_2 (A : BLT_Adv_Set) : TS = {
  
  proc init(seed : int) = {
    TsU_2.init(seed);
  }

  proc clock() = {
      var t;
      t <@ TsU_2.clock();
      return t;
  }  

  proc put(x : hash_output fset) = {
    var t, r;
    r <@ A.react(x);
    t <@ TsU_2.put(x `|` r);
    return t;
  }

  proc getE(t : int) = {
      var r;
      r <@ TsU_2.getE(t);
      return r;
  }  

  proc get() = {
    return TsU_2.r;
  }    

}.


module BLT_Dummy_Repo (SH_O : SH_OracleT) (Tag_O : Tag_Oracle) (Ts_O : TS)  = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  var used : bool
  var usedTime : int
  var qs : message option
  
  proc init() : unit = {

    used <- false;
    usedTime <- 0;
    qs <- None;
  }

  proc sign(m : message) : tag = {
    var t : int;
    var h1v : hash_output;
    var h2v : hash_output;

    if(!used){
      t <@ Ts_O.clock();
      usedTime <- t + 1;
      qs <- Some m;
      h1v <@ SH_O.h(HM.H m, usedTime);
      h2v <@ SH_O.h(EMPTY, usedTime);

      Ts_O.put(fset1 h1v `|` fset1 h2v);

    }
    used <- true;


     return deftag;
  }

  proc verify(m : message, s : tag) : bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc fresh(m : message) : bool = {
    return true;
  }

  proc put(ri : hash_output fset) : unit = {
    Ts_O.put(ri);
  }

  proc get() : (int , hash_output fset) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.




module Case3_Adv2(A : BLT_Adv, A2 : BLT_Adv_Set, RO : ROracle, SH_O : SH_OracleT) = {
    

  module TsU_Set_2 = TsU_Set_2(A2)
  module BLT_Dummy_Repo = BLT_Dummy_Repo(SH_O, Tag_Wrap_2, TsU_Set_2)

  module A = A(BLT_Dummy_Repo)
  proc main(pk:pkey) = {

    var m : message;
    var tg : tag;
    var it : int;

    it <@ RO.rndStr();
    Tag_Wrap_2.init(pk, witness);
    TsU_Set_2.init(initialTime it);
    BLT_Dummy_Repo.init();

    (m,tg) <@ A.forge(pk, it);

    return (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]);
  }
  
}.


section. 


declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame, -BLT_Dummy_Repo, -TsU_2, -Tag_Wrap_2, -SH_Oracle, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -BLTGame, -BLT_Dummy_Repo, -TsU_2, -Tag_Wrap_2, -SH_Oracle, -RO}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.

axiom A2_ll : islossless A2.react.


op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> hash_output fset.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.

axiom computableAdvs &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2), Tag_Wrap,A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t ] = 1%r.

local lemma a2 &m pkk skk :(pkk, skk) \in keys 
 => Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m : 
     ogetf TsU.r.[toTime BLT_Wrap.qt] = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs) = message_setX pkk RO.t ] = 1%r.
proof. move => h.

have : Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t ] <= Pr [ BLTGameD(TsU_Set(A2), Tag_Wrap,A).main(pkk, skk) @ &m : 
     ogetf TsU.r.[toTime BLT_Wrap.qt] = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs) = message_setX pkk RO.t ].
rewrite Pr[mu_sub]. auto. auto.

have : Pr[BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m :
   toTime BLT_Wrap.qt = timeX pkk RO.t /\
   ogetf TsU.r.[toTime BLT_Wrap.qt] = hash_setX pkk RO.t /\
   BLT_Wrap.used = boolX pkk RO.t /\
   fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t /\
   (ogetff BLT_Wrap.qs) = message_setX pkk RO.t /\
   BLTGameD.m = messageX pkk RO.t ] = 1%r. 
apply (computableAdvs &m pkk skk h).
move => z.

smt.
qed.




local lemma repoExtractor' :
  equiv [ A(BLT_Dummy_Repo(SH_Oracle, Tag_Wrap_2, TsU_Set_2(A2))).forge 
          ~ A(BLT_Wrap(Tag_Wrap, TsU_Set(A2))).forge 
   : ={rs, glob A, pk, glob A2, glob RO} /\ TsU.t{2} = TsU_2.t{1} /\ TsU.r{2} = TsU_2.r{1} /\ BLT_Wrap.qs{2} = None 
     /\ SH_Oracle.sk{1} = Tag_Wrap.sk{2}  
     /\ !BLT_Wrap.used{2}
     /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
     /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2}
     /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys
     /\ toTime BLT_Wrap.qt{2} <= TsU.t{2}
     /\ toTime BLT_Wrap.qt{2} = BLT_Dummy_Repo.usedTime{1}
     /\ BLT_Wrap.qt{2} = deftag
     /\ SH_Oracle.logT{1} = fset0
     /\ SH_Oracle.logM{1} = fset0
     /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
     /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
    ==> BLT_Dummy_Repo.usedTime{1} = toTime BLT_Wrap.qt{2}  
     /\ TsU.r.[toTime BLT_Wrap.qt]{2} = TsU_2.r.[BLT_Dummy_Repo.usedTime]{1}
     /\ SH_Oracle.logT{1} \subset (fset1 BLT_Dummy_Repo.usedTime{1})
     /\ SH_Oracle.logT{1} = (if BLT_Dummy_Repo.used{1} then (fset1 BLT_Dummy_Repo.usedTime{1}) else fset0)
     /\ SH_Oracle.logM{1} \subset (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1}))
     /\ SH_Oracle.logM{1} = (if BLT_Dummy_Repo.used{1} then (fset1 EMPTY  `|` (ogetff BLT_Dummy_Repo.qs{1}) ) else fset0)
     /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
     /\ ={RO.t}
     /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
    ].

proof. proc*. 

call (_: BLT_Wrap.used,  
     ={glob A2} 
  /\ (toTime BLT_Wrap.qt{2} = BLT_Dummy_Repo.usedTime{1})                                        (* not used  *)
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2} 
  /\ TsU_2.t{1} = TsU.t{2} 
  /\ TsU.r{2} = TsU_2.r{1}
  /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys 
  /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2}
  /\ Tag_Wrap.sk{2} = SH_Oracle.sk{1}
  /\ (toTime BLT_Wrap.qt{2} = BLT_Dummy_Repo.usedTime{1})
  /\ (!BLT_Wrap.used{2} => BLT_Wrap.qt{2} = deftag /\ SH_Oracle.logT{1} = fset0 /\ SH_Oracle.logM{1} = fset0)
  /\ SH_Oracle.logT{1} \subset (fset1 BLT_Dummy_Repo.usedTime{1}) 
  /\ SH_Oracle.logT{1} = fset0
  /\ SH_Oracle.logM{1} \subset (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1})) 
  /\ SH_Oracle.logM{1} = fset0
  /\ ={RO.t}
  /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
  , 
     (toTime BLT_Wrap.qt{2} = BLT_Dummy_Repo.usedTime{1})                                         (* used *)
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2} 
  /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2} 
  /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys 
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
  /\ TsU.r.[toTime BLT_Wrap.qt]{2} = TsU_2.r.[BLT_Dummy_Repo.usedTime]{1}
  /\ toTime BLT_Wrap.qt{2} <= TsU.t{2}
  /\ toTime BLT_Wrap.qt{2} <= TsU_2.t{1}
  /\ SH_Oracle.logT{1} \subset (fset1 BLT_Dummy_Repo.usedTime{1}) 
  /\ SH_Oracle.logT{1} = (if BLT_Dummy_Repo.used{1} then (fset1 BLT_Dummy_Repo.usedTime{1}) else fset0)
     /\ SH_Oracle.logM{1} = (if BLT_Dummy_Repo.used{1} then ( fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1}) ) else fset0)
  /\ SH_Oracle.logM{1} \subset (fset1 EMPTY `|`  (ogetff BLT_Dummy_Repo.qs{1}))
  /\ ={RO.t}
  /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
  ). 
apply A_ll.

proc. inline*. if. auto. wp.
call (_: true). simplify.

wp. skip. progress. smt. smt. smt. smt. 

have : toTime BLT_Wrap.qt{2} = 0. smt.
move => hhh.

smt.  smt. smt. rewrite /ogetff. smt. rewrite /ogetff. smt. smt. smt. smt. smt. smt. smt. smt. smt. smt.
  
wp. skip. progress.

move => &2 u. proc.
inline*. if. wp. call (_:true). apply A2_ll. wp. skip. smt.
wp. skip. smt.

move => &1. proc.
inline*. if. wp. call (_:true). apply A2_ll. wp. skip. smt.
wp. skip. smt.

proc. inline*. wp.
call (_:true). wp.
skip. progress. smt. smt. smt. smt. smt. 

move => &2 a. proc.
inline*.  wp. call (_:true). apply A2_ll. wp. skip. progress. smt. smt.

move => &1. proc.
inline*. wp. call (_:true). apply A2_ll. wp. skip. progress. smt. smt.

proc. inline*. wp.
skip. progress. smt. smt. smt. smt. smt. 

move => &2 u. proc.
inline*.  wp.  skip. progress.

move => &1. proc.
inline*. wp. skip. smt.
 
skip. progress. 
smt.  smt. smt. smt. smt. smt. smt. smt.  smt. smt. smt. smt. smt.  smt.
qed.





local lemma repoExtractor pkk skk : (pkk, skk) \in keys => 
  equiv [ Case3_Adv2(A, A2, RO, SH_Oracle).main ~ BLTGameD(TsU_Set(A2), Tag_Wrap,A).main 
  : ={glob A, glob A2, glob RO} /\ (pkk, skk) = (pk{2}, sk{2}) /\ pk{1} = pk{2} /\ SH_Oracle.logM{1} = fset0 /\ SH_Oracle.logT{1} = fset0 /\ SH_Oracle.sk{1} = sk{2} ==>

        BLT_Dummy_Repo.usedTime{1} = toTime BLT_Wrap.qt{2}  
     /\ TsU.r.[toTime BLT_Wrap.qt]{2} = TsU_2.r.[BLT_Dummy_Repo.usedTime]{1}
     /\ SH_Oracle.logT{1} \subset (fset1 BLT_Dummy_Repo.usedTime{1})
     /\ SH_Oracle.logT{1} = (if BLT_Dummy_Repo.used{1} then (fset1 BLT_Dummy_Repo.usedTime{1}) else fset0)
     /\ SH_Oracle.logM{1} = (if BLT_Dummy_Repo.used{1} then (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1}) ) else fset0)
     /\ SH_Oracle.logM{1} \subset (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1}))
  /\ ={RO.t}
  /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
  /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
  /\ res{1} = (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]){1} 
    ].
proof. move => pr. proc. inline*.
wp. call repoExtractor'. wp.  skip. progress. smt.  smt.  qed.



local lemma a2' &m pkk skk :  (pkk, skk) \in keys => SH_Oracle.sk{m} = skk /\ SH_Oracle.logT{m} = fset0 /\ SH_Oracle.logM{m} = fset0   =>
  Pr [ Case3_Adv2(A,A2, RO, SH_Oracle).main(pkk) @ &m : 
     (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]) = hash_setX pkk RO.t
  /\  BLT_Dummy_Repo.used = boolX pkk RO.t
  /\ SH_Oracle.logT = (if BLT_Dummy_Repo.used then (fset1 BLT_Dummy_Repo.usedTime) else fset0)
  /\ SH_Oracle.logM = (if BLT_Dummy_Repo.used then (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs) ) else fset0)
  /\ (fset1 (BLT_Dummy_Repo.usedTime)) = time_setX pkk RO.t
  /\ ( (ogetff BLT_Dummy_Repo.qs)) = message_setX pkk RO.t
  /\ res = hash_setX pkk RO.t
  ]
 = Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m : 
     (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t 
  /\ (fset1 (toTime BLT_Wrap.qt)) = time_setX pkk RO.t
  /\ ( (ogetff BLT_Wrap.qs)) = message_setX pkk RO.t ].
proof.   move => pr1 pr2.
byequiv (_ : ={glob A, glob A2, glob RO, glob TsU} /\ (pkk, skk) = (pk{2}, sk{2}) /\ pk{1} = pk{2} /\ SH_Oracle.logM{1} = fset0 /\ SH_Oracle.logT{1} = fset0 /\ ( SH_Oracle.sk{1}) = ( sk{2})   ==>  
         BLT_Dummy_Repo.usedTime{1} = toTime BLT_Wrap.qt{2}  
     /\ SH_Oracle.logT{1} = (if BLT_Dummy_Repo.used{1} then (fset1 BLT_Dummy_Repo.usedTime{1}) else fset0)
     /\ SH_Oracle.logM{1} = (if BLT_Dummy_Repo.used{1} then (fset1 EMPTY `|`(ogetff BLT_Dummy_Repo.qs{1}) ) else fset0)
     /\ TsU.r.[toTime BLT_Wrap.qt]{2} = TsU_2.r.[BLT_Dummy_Repo.usedTime]{1}
     /\ SH_Oracle.logT{1} \subset (fset1 BLT_Dummy_Repo.usedTime{1})
    /\ BLT_Dummy_Repo.used{1} = BLT_Wrap.used{2}
     /\ SH_Oracle.logM{1} \subset (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs{1})) /\ ={RO.t}
     /\ BLT_Dummy_Repo.qs{1} = BLT_Wrap.qs{2}
    /\ res{1} = (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]){1}
   ).

conseq (repoExtractor  pkk skk pr1). smt.
progress. smt. progress. smt.  smt.    smt.
qed.


local lemma a2'' &m pkk skk :  (pkk, skk) \in keys => SH_Oracle.sk{m} = skk /\ SH_Oracle.logT{m} = fset0 /\ SH_Oracle.logM{m} = fset0  =>
  Pr [ Case3_Adv2(A,A2, RO, SH_Oracle).main(pkk) @ &m : 

     (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]) = hash_setX pkk RO.t
  /\  BLT_Dummy_Repo.used = boolX pkk RO.t
  /\ SH_Oracle.logT = (if BLT_Dummy_Repo.used then (fset1 BLT_Dummy_Repo.usedTime) else fset0)
  /\ SH_Oracle.logM = (if BLT_Dummy_Repo.used then (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs) ) else fset0)
  /\ (fset1 (BLT_Dummy_Repo.usedTime)) = time_setX pkk RO.t
  /\ ( (ogetff BLT_Dummy_Repo.qs)) = message_setX pkk RO.t 
  /\ res = hash_setX pkk RO.t

 ]
 = 1%r. 
proof.  move => pr pr2.
rewrite - (a2 &m pkk skk pr).
apply (a2' &m pkk skk pr pr2).
qed.
   
lemma a2_premise pkk skk  : phoare [ Case3_Adv2(A,A2, RO, SH_Oracle).main : (pkk, skk) \in keys  /\ pk = pkk /\ SH_Oracle.sk = skk /\ SH_Oracle.logT = fset0 /\ SH_Oracle.logM = fset0   ==> 
     (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]) = hash_setX pkk RO.t
  /\ BLT_Dummy_Repo.used = boolX pkk RO.t
  /\ SH_Oracle.logT = (if BLT_Dummy_Repo.used then (fset1 BLT_Dummy_Repo.usedTime) else fset0)
  /\ SH_Oracle.logM = (if BLT_Dummy_Repo.used then (fset1 EMPTY `|` (ogetff BLT_Dummy_Repo.qs) ) else fset0)
  /\ (fset1 (BLT_Dummy_Repo.usedTime)) = time_setX pkk RO.t
  /\ ( (ogetff BLT_Dummy_Repo.qs)) = message_setX pkk RO.t
  /\ res = hash_setX pkk RO.t
   ] = 1%r.
proof.  bypr. move => &m0 pr1.  
elim pr1.  move => q1 q2. 

elim q2. move => z1 z2.
rewrite z1.
apply (a2'' &m0 pkk skk q1 z2 ).
qed.



end section.

end Case3_A2_Theory.
