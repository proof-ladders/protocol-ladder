require import AllCore List Distr.

type output.

op [lossless full uniform] dout : output distr.

op f : output -> (output * output).

(* 

    PRG 2

*)
module type PRG2 = {
  proc query(s : output) : output * output
}.

module PRG2r : PRG2 = {
  proc query(s : output) = {
    return f s;
  }
}.

module PRG2i : PRG2 = {
  proc query(s : output) = {
    var x,y;
    
    x <$ dout;
    y <$ dout;
    return (x,y);
  }
}.

module type Dist2 = {
  proc distinguish(v : output * output) : bool
}.

module IND_2 (F : PRG2) (D : Dist2) = {
  proc game() : bool = {
    var b; 
    var s;
    var x,y;
    
    s <$ dout;

    (x,y) <@ F.query(s);

    b <@ D.distinguish(x,y);
    return b;
  }
}.

(* 

    PRG 3 

*)
module type PRG3 = {
  proc query(s : output) : output * output * output
}.

module PRG3r : PRG3 = {
  proc query(s : output) = {
    var a,b1,b2,c;

    (a, b1) <- f s;
    (b2, c) <- f b1;
    return (a,b2,c);
  }
}.

module PRG3h : PRG3 = {
  proc query(s : output) = {
    var a,b,c;

    a <$ dout;
    (b,c) <- f s;
    return (a,b,c);
  }
}.

module PRG3i : PRG3 = {
  proc query(s : output) = {
    var a,b,c;
    
    a <$ dout;
    b <$ dout;
    c <$ dout;
    return (a,b,c);
  }
}.

module type Dist3 = {
  proc distinguish(v : output * output * output) : bool
}.

module IND_3 (G : PRG3) (D : Dist3) = {
  proc game() : bool = {
    var b; 
    var s;
    var x,y,z;
    
    s <$ dout;

    (x,y,z) <@ G.query(s);

    b <@ D.distinguish(x,y,z);
    return b;
  }
}.

(* 

Equivalent games 

*)
module D2_embed_rh (Drhyb : Dist3) : Dist2 = {
  (* Embed D2 at the first use of G in real D3 *)
  proc distinguish(a : output, b1 : output) : bool = {
    var b : bool; 
    var b2,c : output;
    
    (b2, c) <- f b1;
    b <@ Drhyb.distinguish(a,b2,c);

    return b;
  }
}.

module D2_embed_hi (Drhyb : Dist3) : Dist2 = {
  (* Embed D2 at the second use of G in hybrid D3 *)
  proc distinguish(b1 : output, c : output) : bool = {
    var b : bool; 
    var a : output;
    
    a <$ dout;
    b <@ Drhyb.distinguish(a,b1,c);

    return b;
  }
}.

(* 

    Proofs

*)
section PROOFS.
  declare module D3 <: Dist3.

  local lemma eq_D3r_D2r &m : 
      Pr[IND_3(PRG3r, D3).game() @ &m : res]
      =
      Pr[IND_2(PRG2r, D2_embed_rh(D3)).game() @ &m : res].
  proof.
    byequiv (_ : ={glob D3} ==> ={res}); trivial.
    proc.
    inline *.
    wp.
    call (_ : true).
    auto.
  qed.

  local lemma eq_D3h_D2i &m :
      Pr[IND_3(PRG3h, D3).game() @ &m : res]
      =
      Pr[IND_2(PRG2i, D2_embed_rh(D3)).game() @ &m : res].
  proof.
    byequiv (_ : ={glob D3} ==> ={res}); trivial.
    proc.
    inline *.
    wp.
    swap {2} 3 1.
    call (_ : true).
    auto.
  qed.

  local lemma eq_D3h_D2r &m :
      Pr[IND_3(PRG3h, D3).game() @ &m : res]
      =
      Pr[IND_2(PRG2r, D2_embed_hi(D3)).game() @ &m : res].
  proof.
    byequiv (_ : ={glob D3} ==> ={res}); trivial.
    proc.
    inline *.
    wp.
    call (_ : true).
    auto.
  qed.

  local lemma eq_D3i_D2i &m :
      Pr[IND_3(PRG3i, D3).game() @ &m : res]
      =
      Pr[IND_2(PRG2i, D2_embed_hi(D3)).game() @ &m : res].
  proof.
    byequiv (_ : ={glob D3} ==> ={res}); trivial.
    proc.
    inline *.
    swap {2} 8 -5.
    wp.
    call (_ : true).
    auto.
  qed.
  

  local lemma adv_D3rh_is_D2 &m : 
      `|Pr[IND_3(PRG3r, D3).game() @ &m : res] -
      Pr[IND_3(PRG3h, D3).game() @ &m : res]|
      =
      `|Pr[IND_2(PRG2r, D2_embed_rh(D3)).game() @ &m : res] -
      Pr[IND_2(PRG2i, D2_embed_rh(D3)).game() @ &m : res] |.
  proof.
    rewrite eq_D3r_D2r.
    rewrite eq_D3h_D2i.
    reflexivity.
  qed.

  local lemma adv_D3hi_is_D2 &m : 
      `| Pr[IND_3(PRG3h, D3).game() @ &m : res] -
      Pr[IND_3(PRG3i, D3).game() @ &m : res] |
      =
      `| Pr[IND_2(PRG2r, D2_embed_hi(D3)).game() @ &m : res] -
      Pr[IND_2(PRG2i, D2_embed_hi(D3)).game() @ &m : res] |.
  proof.
    rewrite eq_D3h_D2r.
    rewrite eq_D3i_D2i.
    reflexivity.
  qed.
  
  lemma D3_adv_2D2 &m : 
      `|Pr[IND_3(PRG3r, D3).game() @ &m : res] -
      Pr[IND_3(PRG3h, D3).game() @ &m : res]|
      +
      `| Pr[IND_3(PRG3h, D3).game() @ &m : res] -
      Pr[IND_3(PRG3i, D3).game() @ &m : res] |
      =
      2%r *
      `| Pr[IND_2(PRG2i, D2_embed_hi(D3)).game() @ &m : res] -
      Pr[IND_2(PRG2r, D2_embed_hi(D3)).game() @ &m : res] |.
  proof.
    rewrite adv_D3hi_is_D2.
    rewrite adv_D3rh_is_D2.
  admitted.
