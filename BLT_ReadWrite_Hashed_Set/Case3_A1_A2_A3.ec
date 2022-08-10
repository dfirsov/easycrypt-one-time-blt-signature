pragma Goals:printall.

require import Int Real Distr SmtMap FSet DInterval.

require import BLT_Instance SHGame  RandomnessOracle.
require Case3_A1 Case3_A2 Case3_A3.


theory A1_A2_A3_Theory.

op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> hash_output fset.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.


clone export Case3_A1.Case3_A1_Theory as A1T with op timeX <- timeX,       
                                         op hash_setX      <- hash_setX,   
                                         op time_setX      <- time_setX,   
                                         op message_setX   <- message_setX,
                                         op messageX       <- messageX,    
                                         op boolX          <- boolX.       

clone export Case3_A2.Case3_A2_Theory as A2T with op timeX <- timeX,       
                                         op hash_setX      <- hash_setX,   
                                         op time_setX      <- time_setX,   
                                         op message_setX   <- message_setX,
                                         op messageX       <- messageX,    
                                         op boolX          <- boolX.       

clone export Case3_A3.Case3_A3_Theory as A3T with op timeX <- timeX,       
                                         op hash_setX      <- hash_setX,   
                                         op time_setX      <- time_setX,   
                                         op message_setX   <- message_setX,
                                         op messageX       <- messageX,    
                                         op boolX          <- boolX.       


section. 

module SHGame1(RO : ROracle, A2 : SH_Adv2, A3 : SH_Adv3) = {

  module A2 = A2(RO, SH_Oracle)  
  module A3 = A3(RO, Tag_Wrap)

  var pk : pkey
  var sk : skey

  proc main() = {

    var t : int;
    var y : hash_output fset;
    var m : message;
    var rs : int;

    rs <@ RO.init();
    (pk, sk) <$ keys;

    SH_Oracle.init(pk, sk);
    y <@ A2.main(pk);


    Tag_Wrap.init(pk, sk);  
    m <@ A3.main(pk);  


    return (SH_Oracle.logT \subset (fset1 (timeX pk rs))) 
        /\ if Tag_Wrap.usedFlag then (toTime Tag_Wrap.usedTag) = timeX pk rs else true
        /\ !(m \in SH_Oracle.logM)
        /\ HMT.H(m, tag sk (timeX pk rs)) \in y;    
  }

}.

module SHGame2(RO : ROracle, A3 : SH_Adv3) = {


  module A3 = A3(RO, Tag_Wrap)

  var pk : pkey
  var sk : skey
  proc main() = {
    var t : int;
    var y : hash_output fset;
    var m : message;
    var rs : int;
    
    rs <@ RO.init();
    (pk, sk) <$ keys;

    Tag_Wrap.init(pk, sk);  
    m <@ A3.main(pk);  


    
    return ((if boolX pk rs then time_setX pk rs else fset0) \subset (fset1 (timeX pk rs))) 
        /\ if Tag_Wrap.usedFlag then (toTime Tag_Wrap.usedTag) = timeX pk rs else true
        /\ !(m \in (if boolX pk rs then fset1 EMPTY `|` message_setX pk rs else fset0) )
        /\ HMT.H(m,tag sk (timeX pk rs)) \in hash_setX pk rs;
    
  }

}.


module SHGame3(RO : ROracle, A3 : SH_Adv3) = {

  module A3 = A3(RO, Tag_Wrap)

  var pk : pkey
  var sk : skey

  proc main() = {

    var t : int;
    var y : hash_output fset;
    var m : message;
    var rs : int;

    rs <@ RO.init();    
    (pk, sk) <$ keys;

    Tag_Wrap.init(pk, sk);  
    m <@ A3.main(pk);  

    
    return ((fset1 (toTime BLT_Wrap.qt)) \subset (fset1 (toTime BLT_Wrap.qt))) 
      /\ if boolX pk rs then timeX pk rs = timeX pk rs else true
        /\ !(m \in (if boolX pk rs then fset1 EMPTY `|` ((ogetff BLT_Wrap.qs)) else fset0) )
        /\ HMT.H(m,tag sk (toTime BLT_Wrap.qt)) \in (ogetf TsU.r.[toTime BLT_Wrap.qt]);
    
  }

}.



declare module A <: BLT_Adv{-Tag_Wrap_1, -BLT_Wrap, -TsU, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -TsU_2,  -Tag_Wrap_2, -SH_Oracle, -SHGame,  -SHGame1, -SHGame2, -SHGame3, -RO, -Case3_Adv3, -BLTGameD, -BLT_Dummy_Repo}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap_1, -BLT_Wrap, -TsU, -A, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -TsU_2,  -Tag_Wrap_2,  -SH_Oracle, -SHGame,  -SHGame1, -SHGame2, -SHGame3, -RO, -Case3_Adv3, -BLTGameD, -BLT_Dummy_Repo}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.
axiom A2_ll : islossless A2.react.



axiom computableAdvs_A &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t) ] = 1%r.

axiom computableAdvs_A' &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t ] = 1%r.



  
local lemma a1_premise pkk skk : phoare [ Case3_Adv1(A,A2, RO).main  :(pkk, skk) \in keys /\ pk = pkk ==> res = timeX pkk RO.t ] = 1%r.
proof. apply (A1T.a1_premise A A2 (* A_ll A2_ll computableAdvs_A' *) pkk skk).
qed.


local lemma a2_premise pkk skk  : phoare [ Case3_Adv2(A,A2, RO, SH_Oracle).main : (pkk, skk) \in keys /\ pk = pkk /\ SH_Oracle.sk = skk /\ SH_Oracle.logT = fset0 /\ SH_Oracle.logM = fset0   ==> 
     (ogetf TsU_2.r.[BLT_Dummy_Repo.usedTime]) = hash_setX pkk RO.t
  /\ BLT_Dummy_Repo.used = boolX pkk RO.t
  /\ SH_Oracle.logT = (if BLT_Dummy_Repo.used then (fset1 BLT_Dummy_Repo.usedTime) else fset0)
  /\ SH_Oracle.logM = (if BLT_Dummy_Repo.used then (fset1 EMPTY `|` ogetff BLT_Dummy_Repo.qs)  else fset0)
  /\ (fset1 (BLT_Dummy_Repo.usedTime)) = time_setX pkk RO.t
  /\ ( (ogetff BLT_Dummy_Repo.qs)) = message_setX pkk RO.t
  /\ res = hash_setX pkk RO.t
   ] = 1%r.
proof.  apply (A2T.a2_premise A A2 (* A_ll A2_ll computableAdvs_A' *) pkk skk). qed.


local lemma a3_premise  pkk skk :    
  phoare [ Case3_Adv3(A,A2, RO, Tag_Wrap).main : 
  (pkk, skk) \in keys /\
  pk = pkk /\ Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
 /\ Tag_Wrap.pk = pkk ==>
  
  toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t 
  /\ Tag_Wrap.usedFlag = boolX pkk RO.t 
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ res = HM.H (messageX pkk RO.t)
  /\ BLT_Wrap.qt = Tag_Wrap.usedTag     
  ]
 = 1%r.
apply (A3T.a3_premise A A2 (* A_ll A2_ll computableAdvs_A *) pkk skk). qed.   


local lemma ig1 : equiv [ SHGame(RO, Case3_Adv1(A,A2), Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main ~ SHGame1(RO,  Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main :
  ={glob RO, glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle}
     ==> 
  ={res} ].
proof. proc. 

seq 2 2 : (rs{2} = rs{1} /\ rs{1} = RO.t{1}  /\  SHGame.pk{1} = SHGame1.pk{2} /\ SHGame.sk{1} = SHGame1.sk{2} /\ ={RO.t,  glob TsU,  glob SH_Oracle, glob BLT_Wrap}  /\  (SHGame.pk{1}, SHGame.sk{1}) \in keys ).

wp. inline*. wp. rnd. wp. rnd. skip. progress. smt. 


seq 1 0 : (rs{2} = rs{1} /\ rs{1} = RO.t{1} /\ SHGame.t{1} = timeX SHGame.pk{1} RO.t{1} /\  SHGame.pk{1} = SHGame1.pk{2} /\ SHGame.sk{1} = SHGame1.sk{2} /\ ={RO.t, glob TsU,    glob SH_Oracle, glob BLT_Wrap} /\ (SHGame.pk{1}, SHGame.sk{1}) \in keys). 


exists* RO.t{1}, SHGame.pk{1}, SHGame.sk{1}.
elim*. move => ttt pk_L pk_R.

call {1} (a1_premise pk_L  pk_R). skip. progress. 

exists* RO.t{1}, SHGame.pk{1}, SHGame.sk{1}.
elim*. move => ttt pk_L sk_L.

call {1} (a3_premise pk_L sk_L). 
call {2} (a3_premise pk_L sk_L). 

inline Tag_Wrap.init. wp.

call {1} (a2_premise pk_L sk_L). 
call {2} (a2_premise pk_L sk_L). 

inline*. wp. 


skip. progress. smt.

qed.



local lemma ig2 : equiv [ SHGame1(RO, Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main ~ SHGame2(RO, Case3_Adv3(A,A2)).main :
  ={glob RO, glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle} ==>  ={res} ].
proof. proc. 

  seq 2 2 : (SHGame1.pk{1} = SHGame2.pk{2} /\ SHGame1.sk{1} = SHGame2.sk{2}  /\ RO.t{2} = rs{2} 
  /\ ={rs, glob RO,glob Tag_Wrap, glob TsU, glob BLT_Wrap} /\ (SHGame1.pk{1}, SHGame1.sk{1}) \in keys ).
wp. inline*. wp. rnd. wp. rnd. skip. progress. smt. 

  seq 2 0 : (y{1} = hash_setX SHGame1.pk{1} rs{1} /\   SH_Oracle.logT{1} = (if BLT_Dummy_Repo.used then time_setX SHGame1.pk{1} RO.t else fset0){1} /\  SH_Oracle.logM{1} = (if BLT_Dummy_Repo.used then fset1 EMPTY `|` message_setX  SHGame1.pk{1} RO.t else fset0){1} /\  BLT_Dummy_Repo.used{1} = boolX SHGame1.pk{1} rs{1}   /\  SHGame1.pk{1} = SHGame2.pk{2} /\ SHGame1.sk{1} = SHGame2.sk{2}  /\ RO.t{2} = rs{2}
  /\ ={rs, glob RO,glob Tag_Wrap, glob TsU, glob BLT_Wrap} /\ (SHGame1.pk{1}, SHGame1.sk{1}) \in keys ).


exists* RO.t{1}, SHGame1.pk{1}, SHGame1.sk{1}.
elim*. move => ttt pk_L sk_L.

call {1} (a2_premise pk_L sk_L).  


inline*.  wp.    skip. progress. smt. smt.  

exists* RO.t{1}, SHGame1.pk{1}, SHGame1.sk{1}.
elim*. move => ttt pk_L sk_L.
call {1} (a3_premise pk_L sk_L). 
call {2} (a3_premise pk_L sk_L). 

inline*. wp. skip. progress.  smt. 

qed.


local lemma ig3 : equiv [ SHGame2(RO, Case3_Adv3(A,A2)).main ~ SHGame3(RO, Case3_Adv3(A,A2)).main :
  ={glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle} ==>  ={res} ].

proof. proc.

seq 3 3 : (rs{2} = rs{1} /\ rs{1} = RO.t{1}  /\  SHGame2.pk{1} = SHGame3.pk{2} /\ SHGame2.sk{1} = SHGame3.sk{2} /\ ={glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle, glob RO} /\ Tag_Wrap.usedTag{2} = deftag /\  Tag_Wrap.usedFlag{2} = false /\ 
  (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) = (SHGame3.pk{2},SHGame3.sk{2}) /\  (SHGame2.pk{1}, SHGame2.sk{1}) \in keys ) .

inline*. wp. rnd. wp. rnd. skip. progress. smt.

exists* RO.t{1}, SHGame2.pk{1}, SHGame2.sk{1}.
elim*. move => ttt pk_L sk_L.

call {1} (a3_premise pk_L sk_L). 
call {2} (a3_premise pk_L sk_L). 

skip. progress. smt. 

qed.


local lemma os  (z : message option) : z <> None => exists q, z = Some q.
proof. case z. smt. smt. qed.


local lemma ig4 : equiv [ SHGame3(RO, Case3_Adv3(A,A2)).main ~ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main :
  ={glob A2, glob A, glob Tag_Wrap, glob TsU, glob BLT_Wrap} 
     ==> 
  ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)){2} /\ toTime BLTGame.tg{2} = toTime BLT_Wrap.qt{2} /\ HM.H (oget BLT_Wrap.qs{2}) <> (HM.H BLTGame.m{2})  => res{1}  ].
proof. proc.
inline*. wp. call (_: ={glob TsU, glob BLT_Wrap, glob Tag_Wrap, glob A2}). 
proc. if. auto. inline*. wp. call (_:true). wp. skip. progress.  wp. skip. progress.
proc. inline*. wp. call (_:true). wp. skip. progress. 
proc. inline*. wp.  skip. progress.
wp. rnd.   wp. rnd. progress.  wp.  skip.
progress.
smt.
case (boolX pkskL.`1 tL).
move => h.
case (qs_R = None).
move => hh. smt. (* relies on the fact that HM.H m <> EMPTY *)
move => qq.
have :  exists z, qs_R = Some z.  apply (os qs_R qq).
elim.
move => zz zzz. smt. timeout 20. smt.
qed.


local lemma igmain : equiv [ SHGame(RO, Case3_Adv1(A,A2), Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main ~ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main :
  ={glob A, glob A2, glob Tag_Wrap, glob TsU, glob BLT_Wrap} 
     ==> 
  (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg{2} = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m)){2} => res{1}  ].
proof.
symmetry.

transitivity SHGame1(RO,  Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main 
  (={glob Tag_Wrap, glob TsU, glob BLT_Wrap}  ==> (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m)){1}  => res{2}) 
  (={glob RO, glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle} ==> ={res}). smt.
progress.

transitivity SHGame2(RO, Case3_Adv3(A,A2)).main 
  (={glob Tag_Wrap, glob TsU, glob BLT_Wrap}  ==> (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m)){1} => res{2}) 
  (={glob RO, glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle} ==> ={res}). smt.
progress.

transitivity SHGame3(RO,   Case3_Adv3(A,A2)).main 
  (={glob A, glob A2, glob Tag_Wrap, glob TsU, glob BLT_Wrap}  ==> (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m)){1} => res{2}) 
  (={glob RO, glob BLT_Dummy_Repo, glob TsU_2, glob Tag_Wrap, glob TsU, glob BLT_Wrap, glob SH_Oracle} ==> ={res}). smt.
progress. 

symmetry. conseq ig4. progress. auto. 

symmetry. conseq ig3. progress. auto. 

symmetry. conseq ig2. progress. auto. 

symmetry. conseq ig1. progress. auto. 

qed.



lemma case3 &m :  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m) ] <= Pr [ SHGame(RO, Case3_Adv1(A,A2), Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main() @ &m : res ] .
proof. 
byequiv (_ : ={glob A, glob A2, glob Tag_Wrap, glob TsU, glob BLT_Wrap}  ==> (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m)){1} => res{2}).
symmetry. conseq igmain. progress. progress. progress. 
qed.

end section.

end A1_A2_A3_Theory.
