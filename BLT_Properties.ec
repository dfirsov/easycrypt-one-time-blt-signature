pragma Goals:printall.

require import AllCore.
require  BLT.

clone import BLT.BLT_Scheme_Theory.



(* 
One-time correctnes + Stateless property => Many-time correctness.

Note that BLT_Scheme is one-time signature scheme which means that
method "BLT_Scheme.sign" to be used only once, however
"BLT_Scheme.verify" can be used any number of times hence we need to
make sure that entire scheme is stateless.

*)

module BLT_Scheme_Correctness = {

   module BLT = BLT_Scheme(Tag_Wrap, TsU)

   proc main(m : message) = {
      var t, r;

      Tag_Wrap.init();
      TsU.init();

      t <@ BLT.sign(m);
      r <@ BLT.verify(m, t);
     
      return r;  
  }

}.

(* BLT Scheme is one-time correct *)
lemma blt_correct : phoare [ BLT_Scheme_Correctness.main : true ==> res ] = 1%r.
proof. proc. inline*. wp. rnd predT. wp. rnd predT. skip. progress;smt. qed.


(* BLT Scheme is stateless *)
lemma blt_stateless (Tag_O <: Tag_Oracle) (Ts_O <: TS) : 
           (forall state,
              hoare [BLT_Scheme(Tag_O, Ts_O).sign: (glob BLT_Scheme) = state
                        ==> (glob BLT_Scheme) = state]) /\
           (forall state,
               hoare [BLT_Scheme(Tag_O, Ts_O).verify: (glob BLT_Scheme) = state
                        ==> (glob BLT_Scheme) = state]).
proof. split. 
move => state. proc. inline*. call (_:true). wp. call (_:true). call (_:true). skip. auto. 
move => state. proc. inline*. call (_:true). call (_:true). wp. skip. auto. 
qed.

