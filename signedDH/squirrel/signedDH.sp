(*
 * Protocol:	  Signed Diffie-Hellman
 * Modeler: 	  Charlie Jacomme
 * Date:        April 2025
 *
 * Status: 	    Finished
 * 
 * attacker:    active
 * sessions:    unbounded ∞ 
 * agents:      unbounded ∞ 
 * compromises: long-term keys (LTK)
 * primitives:  ROM, signatures, diffie-hellman
 * properties:  auth, forward secrecy
 * difficulty:  medium
 *

Verifies in under a second.

Example adapted from: D. Baelde, A. Koutsos, and J. Lallemand, “A
higher-order indistinguishability logic for cryptographic reasoning,”
in 2023 38th annual ACM/IEEE symposium on logic in computer science
(LICS), 2023, pp. 1–13, https://hal.inria.fr/hal-03981949.
*) 


(*
=====================
Function Definitions
=====================
*)

(* a public communication channel over the network.*)
channel c.


(*------------------------------------------------------------------*)
(* Gdh group *)
type G
type Z [large]

(* Squirrel directly has a builtin interface to declared such a group. *)
gdh gen, (^), ( ** ) where group:G exponents:Z.


(*------------------------------------------------------------------*)
abstract Z_e : Z.
abstract inv_Z : Z -> Z
abstract dlog : G -> Z
abstract ofG : G -> message.
abstract toG : message -> G.


(* signature *)
signature SIGsign,SIGverify,pk.

axiom [any] SIGsign_ax (x,y,k : message) : x = y => SIGverify(x, SIGsign(y,k), pk(k)).

abstract error : G.

(* Hash *)

(* We model the ROM has a PRF with a magical secret key, and we give an oracle access to the attacker. *)
hash Hash.
(* magical secret key. *)
name kHash : message.

(* In Squirrel, random values are represented as "names", that can be indexed. 
   Instead of sampling x_sk in the i-th Session of the Client, it will directly use the value `x_sk i`.
   This is equivalent to assuming that all secret values were precomputed at the begining of the universe. 
   (eager sampling)
*)

(* long term signing keys *)
name s_sk : index -> message.

(* ephemerals for Client  *)
name x_sk : index -> Z.
(* ephemerals for Server  *)
name y_sk : index * index  -> Z.

(*
=====================
Protocol model
=====================
*)

process Client (i:index) =
  (* we receive some server public key *)
  in(c, s_pk);

  (* we compute our ephemeral *)
  let x_sk = x_sk i in
  let x_pk = gen^x_sk in

  C1:out(c, ofG(x_pk));

  in(c, mA);
  let y_pk = toG(fst(mA)) in
  let sig = snd(mA) in
  if SIGverify(< ofG(x_pk), ofG(y_pk)>, sig, s_pk) then
    let gCS = y_pk^x_sk  in
    let kC = Hash( ofG(gCS), kHash) in
    C2: null.


process Server (S:index, j:index) =
  in(c, x_pk');

  let x_pk = toG(x_pk') in

  let y_sk = y_sk(S, j) in
  let y_pk = gen^y_sk in

  let sig = SIGsign(< ofG(x_pk), ofG(y_pk)>, s_sk S) in  
  let gSC = x_pk^y_sk in
  let kS = Hash(ofG( gSC ), kHash) in
  S1:out(c, <ofG(y_pk), sig>).

process kdforacle (i:index) =
   in(c,x); O : 
   out(c, Hash(x,kHash)).

process corrupt (S:index) =
  out(c, s_sk S).

process protocol = (
   (!_i Client(i))
   | 
   (!_S !_k Server(S,k))
   |
   (!_S corrupt(S)) 
   | 
  (!_O kdforacle(O))
).

system default = protocol.

(*------------------------------------------------------------------*)
include Core.

abstract Some : message -> message.
abstract None : message.
abstract oget : message -> message.
include DHLib.


(*
=====================
Security queries
=====================
*)

(* We can write lemma that talk about possible execution traces. *)

(*------------------------------------------------------------------*)
(* Agreement of Client holds whenever S has not been corrupted before A's execution *)
lemma [default] authentication (S,i:index):
   (* a client session terminated *)
   happens(C2(i)) =>
   (* which received the key of the honest S *) 
   input@C1(i) = pk(s_sk S) &&
   (* and this S was not corrupted before *)
   not (corrupt(S) < C2(i)) =>

   (* then, the SIGverify in C2 is equivalent to a matching of keys with some server session k. *)
   (cond@C2(i) <=>
    exists (k:index),
      (* there exists an execution of the server in the past. *)
      S1(S,k) < C2(i) && 
      (* and all the value match. *)
      gCS i@C2(i) =  gen ^ (y_sk (S, k) ** x_sk i) &&
      toG(fst (input@C2(i))) = gen ^ y_sk (S,k) &&
      toG(input@S1(S,k)) = gen ^ x_sk i &&

      (* to prove the equivalence between the SIGverify and our
      formula, as we only have eufcma and not sufcma, we also need
      this final bit. *)
      SIGverify(<ofG (gen ^ x_sk(i)), ofG (gen ^ y_sk(S,k))>, 
                snd (input@C2(i)), 
                pk(s_sk S))).
Proof.
  intro HC2 [Hon NoCor].
  (* we prove both sides of the equivalence. *)
  split. 
   
  - intro Cond.
  (* we replace the received key by its honest value in Cond.*)
    rewrite /cond Hon in Cond. 
    euf Cond.
    + (* case 1: B corrupted *)
      auto.


    +   (* case 2: the signature comes from the server *)
      intro [k [Ord Eq]].
      exists k; simpl.

     (* we extract from Eq that `y_pk i@C2(i)` is equal to `y_pk1 S k@S1(S, k))` *)
     have Eq2 :  y_pk i@C2(i) = y_pk1 S k@S1(S, k).
      by apply f_apply snd in Eq; simpl.   
    apply f_apply fst in Eq; simpl.         
      
     (* rewrite macros and use Eq2 to conclude. *)
     by rewrite /gCS Eq2 /y_pk1 /y_sk1 /x_sk1 /=.
    
  (* other direction. *)
  - intro [j [H1 [H2 H3 H4 H5]]].  
    auto.
Qed.



(*------------------------------------------------------------------*)
(* We prove the weak forward secrecy of the shared DH of the client. *)
lemma [default] gCS_secret (i:index, t:timestamp):
  (* at any point in time *)
  happens(t) =>

  (* if some client session happened *)
  happens(C2(i)) =>
  (* and its SIGverify was true *)
  cond@C2(i) =>  
  (* and this session is exuting for an honest server S not corrupted before that *)
  (exists S:index,  (input@C1(i) = pk(s_sk S) &&
                     not ((corrupt(S)) < C2(i)))) 
  =>
  (* then the attacker cannot provide as input at time t the derived shared DH. *)
  input@t = ofG(gCS i@C2(i)) =>
  false.
Proof.
  intro Ht HC2 C [S [Hon NoCor]] T.

  (* we replace the received key by its honest value in C.*)
  rewrite /cond Hon in C.
  euf C.
  (* case 1: corrupted server *)
  + auto. (* direct contradictions with the hypothesis NoCor *)
  
  (* case 2: the signature comes from the server *)
  +  intro [k [Ord Eq]].
     clear C.
     (* we extract from Eq that `y_pk i@C2(i)` is equal to `y_pk1 S k@S1(S, k))` *)
     apply f_apply snd in Eq; simpl.      
     rewrite /gCS Eq /y_pk1 /y_sk1 /x_sk1 in T.
     apply f_apply toG in T; simpl.
     gdh T, gen.
Qed.




(* Squirrel enables through the `frame@t` value to talk about all the
values sent over the network in all possible executions.  We can model
real-or-random of some key `key` by asking to prove something of the
form `frame@t, diff(key, nfresh)`, where `diff` enables to specify the
two side of the indistinguishability, and where `nfresh` is a fresh
random value.  *)

(*------------------------------------------------------------------*)
name nfresh : message.

(* Strong forward secrecy of Client's key as long as the server was not corrupted. *)
global lemma [set:default/left; equiv:default/left, default/left]
  kC_strong_forward_secrecy (t, t0 : timestamp[const], i:index[const]) :
   (* for any two points t and t0 in the trace, with t before t0 *)
  [t <= t0] ->
  (* if t is point where a client accepted. *)
  [t = C2(i)] ->
  (* and if this client tried to contact an honest server not corrupted before this point. *)
  [exists S:index,  (input@C1(i) = pk(s_sk S) &&
                     not ((corrupt(S)) < t)) ] ->
  equiv(
    (* if we give the full frame up to t0 to an attacker *)
    frame@t0, 
    (* as long as C2 i accepted successfully. *)
    if cond@t then 
       (* then the derived key is indistinguishable from the secret. *)
      diff(kC i@t, nfresh)).
Proof.
  intro Hhap Heq [S [Hon NoCor]]. 
  rewrite /kC.
  (* prf allows to replace Hash... by a new fresh name, if the hash is never computed anywhere else in the frame@t0. *)
  prf 1 => /=. 
   (* The attacker may try to get the key kC from the ROM, we prove
   its impossible by using the previous gCS_secret lemma, as the
   attacker then needs to give gCS to the ROM. *) 
   { 
   intro Cond.
   rewrite Heq in *.  
   intro j H1 H2.  

   (* We simplify H1 into its consequence. *)
   have ? : O(j) <= t0.  
    case H1; 1,2: auto. by have _ := depends_C1_C2 i.
   clear H1.     

   rewrite eq_sym in H2. 

   apply gCS_secret in H2; 1,2,3: auto.  exists S; auto.
   auto.
  }.
 
  (* PRF application succeeded. *)
  (* we break the if then else into pieces. *)
  fa 1.

  (* remains to prove that the freshly introduced n_PRF name is
  indistinguishable from our own nfresh, direct with the corresponding
  tactic. *)
  by fresh 2.
Qed.




(*------------------------------------------------------------------*)
(* We prove the weak forward secrecy of the shared DH of the server. *)
lemma [default] gSC_secret (S,k:index, t:timestamp):
  (* at any point in time *)
  happens(t) =>

  (* if some server session happened *)
  happens(S1(S,k)) => 
  (* and this session received an honest DH Client share *)
  (exists i:index,  (C1(i) < S1(S,k) && input@S1(S,k) = output@(C1 i) ))
  =>
  (* then the attacker cannot provide as input at time t the derived shared DH. *)
  input@t = ofG(gSC S k@S1(S,k)) =>
  false.
Proof.
  intro Ht HS1 [C [Hon NoCor]] T.

  rewrite /gSC /x_pk1 NoCor /output /x_pk /= in T.

  apply f_apply toG in T; simpl.
  gdh T, gen.
Qed.


(* Strong forward secrecy of Server's key that received honest DH Client share *)
global lemma [set:default/left; equiv:default/left, default/left]
  kS_strong_forward_secrecy (t, t0 : timestamp[const], S,k:index[const]) :
   (* for any two points t and t0 in the trace, with t before t0 *)
  [t <= t0] ->
  (* if t is point where a server derived key. *)
  [t = S1(S,k)] ->
  (* and if this server got an honest DH Client share *)
  [exists i:index,  (C1(i) < S1(S,k) && input@S1(S,k) = output@(C1 i) )]
  ->
  equiv(
    (* if we give the full frame up to t0 to an attacker *)
    frame@t0, 
       (* then the derived key is indistinguishable from the secret. *)
      diff(kS S k@t, nfresh)).
Proof.
  intro Hhap Heq [i [Hon NoCor]]. 
  rewrite /kS.
  prf 1 => /=. 
   (* The attacker may try to get the key kC from the ROM, we prove
   its impossible by using the previous gCS_secret lemma, as the
   attacker then needs to give gCS to the ROM. *) 
   { 
   intro j H1 H2.
   rewrite Heq in *.  
  

   (* We simplify H1 into its consequence. *)
   have ? : O(j) <= t0.  
    case H1; 1,2: auto. 
   clear H1.     

   rewrite eq_sym in H2. 

   apply gSC_secret in H2; 1,2: auto.  exists i; auto.
   auto.
  }.
 
  by fresh 1.
Qed.
