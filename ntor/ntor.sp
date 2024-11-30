(* Novel file *)


(* <!> Full WIP <!> *)


include WeakSecrecy.

channel pub.

type id.

(* Elliptic Curve Diffie-Hellman *)

type G
type E [large]

gdh g, (^), ( ** ) where group:G exponents:E.


 
abstract Gtomess : G -> message.

(* Hash functions *)


abstract t_mac : message.
abstract t_key : message.
abstract t_verify  : message.


hash H.

(* Data formatter *)

abstract PROTOID:string.
abstract Server:string.

abstract concat1 : G * G * id * G * G * G * string -> message.
abstract deconcat1 :  message -> G * G * id * G * G * G * string .

abstract concat2 : message * id * G * G * G *  string *  string -> message.
abstract deconcat2 :  message -> message * id * G * G * G *  string *  string.

axiom [any] dec1 (a,b,c,d,e,f,g:_): deconcat1(concat1(a,b,c,d,e,f,g)) = (a,b,c,d,e,f,g).
axiom [any] dec2 (a,b,c,d,e,f,g:_): deconcat2(concat2(a,b,c,d,e,f,g)) = (a,b,c,d,e,f,g).

abstract CREATE : id * G * G -> message.
abstract parseCREATE : message -> id * G * G.
abstract CREATED : G * message -> message.
abstract parseCREATED : message -> G * message.

abstract parseID : message  -> id.

process client(romkey:message, i:index, ID: id, B:G)  =
    new x : E;
    let X = g^x in
    C1 : out(pub, CREATE( ID, B, X));
    in(pub, mess);
    let Y2 = parseCREATED(mess)#1 in
    let AUTH = parseCREATED(mess)#2 in
    let secret_input =  concat1( Y2^x, B^x, ID, B, X, Y2, PROTOID) in
    let KEY_SEED = H(<secret_input, t_key>, romkey) in
    let verify = H(<secret_input, t_verify>, romkey) in
    let auth_input = concat2( verify, ID, B, Y2, X, PROTOID, Server) in
    if H(<auth_input, t_mac>,romkey) = AUTH then
       C2 : out(pub, zero).

process serveur(romkey:message, j:index, ID: id, b:E, B:G) =

    in(pub, mess);
    if parseCREATE(mess)#1 = ID && parseCREATE(mess)#2 = B then
    let X2 = parseCREATE(mess)#3 in
    new y:E;
    let Y = g^y in
    
    let secret_input =  concat1( X2^y, X2^b, ID, B, X2, Y, PROTOID) in
    let KEY_SEED = H( <secret_input, t_key>,romkey) in
    let verify = H( <secret_input, t_verify>,romkey) in
    let auth_input = concat2( verify, ID, B, Y, X2, PROTOID, Server) in
    S : out(pub, CREATED( Y, H(<auth_input, t_mac>, romkey) )).

system  new romkey :message;
        (
	!_u
        
	in(pub, mID);
        let ID = parseID(mID) in
	new b : E;
	let B = g^b in
	out(pub, Gtomess(B));
       (
	!_i client(romkey,i, ID,B)
	|
	!_j serveur(romkey, j, ID,b,B)
        |
        !_h in(pub,x); out(pub,H(x,romkey))
)
        ).

axiom diff_t : t_mac <> t_verify.


lemma perfect_cond (u,i:index): 
 happens(C2(u,i)) => (cond@C2(u,i) <=> (exists j:index, S(u,j) < C2(u,i) && X2 u j@S(u,j) = X u i@C2(u,i) && Y u j@S(u,j) = Y2 u i@C2(u,i))  ).
Proof.     
intro Hap.
split.
intro C.
rewrite /cond in C.
euf C; try by have := diff_t.

intro [u0 j [H Eq]].
rewrite /auth_input /auth_input1 in Eq.

 (* injectivity axiom on concat2, and inj of B u0 = B u *)
admit.

intro [u0 j [H Eq]].

rewrite /auth_input /verify  /input in Eq.


have U :  deconcat2(fst(att( frame@pred (A1(u0, j)))))#1 = H (<secret_input u i@C2(u, i),t_verify>, romkey) .
{ rewrite -Eq.
simpl.
rewrite dec2. auto.  }.

euf U.

  (* inj G^x *)
  admit.
  admit.

   (* found exists. *)
   admit.

 by have := diff_t.
 
  intro [u1 h [Hyp GG]].
  rewrite /secret_input /B in GG.

have U' : deconcat1(fst(input@A1(u1,h)))#2 = g^(b u ** x (u,i)).
rewrite -GG. simpl. rewrite dec1. simpl.  (* gdh comm *) admit.


gdh U', g.
  depends A(u), C2(u,i) => //.
  intro Neg. 
have m := mutex_C3_C2 u i. auto.
 auto. auto.
 intro Neg.


cycle 1 .
intro [j [Ord A B]].
rewrite /* in *.
rewrite -B.
auto.

lemma weak_sec (tau:timestamp,u,i,j:index, f : message -> G [adv]) :
happens(tau) => f(frame@tau) <> g^( y(u,i) ** x(u, j) ).
Proof.
intro H eq.
gdh eq, g.

global lemma [set:default/left; equiv:default/left, default/left] weak_sec (tau:timestamp,u,i,j:index) :

[happens(tau)] ->  $( (frame@tau)  *> (g^( y(u,i) ** x(u, j) ))).
Proof.

intro Hap.
rewrite /( *>).
intro f.
intro Neq.


 gdh Neq, G.

lemma auth (u, i:index) :
happens(C2(u, i)) && cond@C2(u, i) => exists j:index, S(u,j) < .


