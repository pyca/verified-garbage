module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: MGF1 in constant time

`mgfXor lay hs` is constant time in two runs with the same frame, regions,
`src` and `dst` (`MQ`) and the same selector of MGF1's hash function `G`,
whatever the bytes they hold (`mgf_ct`). In each round (`round_ct`) the
pieces between the calls are checked by the taint analysis from the frame's
public slots (`RW.words`), each call is of `G` in both runs (`two_callD`),
with the same arguments; the rounds are as many as `dstLen` and `hLen` say,
by correctness (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs round xorOut nextCtr initArgs updSrcArgs updCtrArgs finArgs mgfXor ldSel)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-- MGF1's public data: the frame, the working space, the other two writable
regions, and `src` and `dst` in the working space. -/
structure MQ where
  F : Addr
  S : Addr
  ws : List Region
  src : Nat
  srcLen : Nat
  dst : Nat
  dstLen : Nat

/-- The frame's words MGF1 reads, with the counter `c` and `hLen = D`. -/
def mw (D : Nat) (q : MQ) (c k : Nat) : BitVec 64 :=
  if k = 14 then q.S else if k = 15 then off q.S q.src else if k = 16 then BitVec.ofNat 64 q.srcLen
  else if k = 17 then off q.S q.dst else if k = 18 then BitVec.ofNat 64 q.dstLen
  else if k = 19 then BitVec.ofNat 64 c else if k = 43 then BitVec.ofNat 64 D else BitVec.ofNat 64 (c * D)

/-- A point of the round with counter `c`, for the hash function of
`hLen = D` that the selector `kG` names. -/
structure RW (n D kG : Nat) (q : MQ) (c : Nat) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  lt : c * D < q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    W 19 = BitVec.ofNat 64 c ∧ W 20 = BitVec.ofNat 64 (c * D) ∧ W 38 = BitVec.ofNat 64 kG ∧
    W 43 = BitVec.ofNat 64 D

theorem RW.words {n D kG : Nat} {q : MQ} {c : Nat} {t : State} (h : RW n D kG q c t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ [14, 15, 16, 17, 18, 19, 20, 43], word t.mem q.F (8 * k) = mw D q c k := by
  obtain ⟨V, W, R, A, h19, h20, -, h43⟩ := h.rep
  refine ⟨h.fv, fun k hk => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (slot_eq sScr 14 rfl _ _).symm.trans h.L.slot
  · rw [R.fr 15 (by decide), A.hsrc]; rfl
  · rw [R.fr 16 (by decide), A.hsl]; rfl
  · rw [R.fr 17 (by decide), A.hdst]; rfl
  · rw [R.fr 18 (by decide), A.hdl]; rfl
  · rw [R.fr 19 (by decide), h19]; rfl
  · rw [R.fr 20 (by decide), h20]; rfl
  · rw [R.fr 43 (by decide), h43]; rfl

/-- The selector, in its slot. -/
theorem RW.sel {n D kG : Nat} {q : MQ} {c : Nat} {t : State} (h : RW n D kG q c t) :
    FrV n q.F q.ws t ∧ Lay t q.F q.S ∧ t.mem.readW (off q.F sSelG) 64 = BitVec.ofNat 64 kG := by
  obtain ⟨V, W, R, -, -, -, h38, -⟩ := h.rep
  exact ⟨h.fv, h.L, by rw [R.rd (d := sSelG) 38 rfl (by decide), h38]⟩

theorem RW.congr {n D kG : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D kG q c t)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : RW n D kG q c t' :=
  ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), h.fit, h.lt, by rw [hm]; exact h.rep⟩

/-- Of a state but for `rax` and the flags. -/
theorem RW.of_mod {n D kG : Nat} {q : MQ} {c : Nat} {t t₀ : State} (h : RW n D kG q c t₀) (hm : t.mem = t₀.mem)
    (hwr : t.wr = t₀.wr) (g : ∀ r, r ≠ .rax → t.gpr r = t₀.gpr r) : RW n D kG q c t :=
  h.congr (g .rsp (by decide)) hwr hm

/-- After a piece that keeps the regions, with the slots as they were. -/
theorem RW.after {n D kG : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW n D kG q c t) (L' : Lay t' q.F q.S)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : MArgs W q.S q.src q.srcLen q.dst q.dstLen) (h19 : W 19 = BitVec.ofNat 64 c)
    (h20 : W 20 = BitVec.ofNat 64 (c * D)) (h38 : W 38 = BitVec.ofNat 64 kG) (h43 : W 43 = BitVec.ofNat 64 D) :
    RW n D kG q c t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', h.fit, h.lt, V, W, R, A, h19, h20, h38, h43⟩

variable {G : Stream} (hG : StreamOK G) (n : Nat) {hs : List (Nat × Stream)} {kG : Nat}

/-! ## The points of a round -/

abbrev P0 (a : MQ × Nat) (t : State) : Prop := RW n G.D kG a.1 a.2 t

abbrev P1 (a : MQ × Nat) (t : State) : Prop := RW n G.D kG a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt

abbrev P3 (a : MQ × Nat) (t : State) : Prop :=
  RW n G.D kG a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
    t.gpr .rdx = off a.1.S a.1.src ∧ t.gpr .rcx = BitVec.ofNat 64 a.1.srcLen ∧ t.gpr .r8 = off a.1.S oW

abbrev P5 (a : MQ × Nat) (t : State) : Prop :=
  RW n G.D kG a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 a.1.srcLen ∧
    t.gpr .rdx = off a.1.S oCtr ∧ t.gpr .rcx = BitVec.ofNat 64 4 ∧ t.gpr .r8 = off a.1.S oW

abbrev P7 (a : MQ × Nat) (t : State) : Prop :=
  RW n G.D kG a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 (a.1.srcLen + 4) ∧
    t.gpr .rdx = off a.1.S oDig ∧ t.gpr .rcx = off a.1.S oW

theorem mod_P1 {a : MQ × Nat} {t : State} (h : Mod (P1 (G := G) n (kG := kG)) a t) : P1 (G := G) n (kG := kG) a t :=
  let ⟨_, ⟨p, hdi⟩, hm, _, hwr, g⟩ := h
  ⟨p.of_mod hm hwr g, (g _ (by decide)).trans hdi⟩

theorem mod_P3 {a : MQ × Nat} {t : State} (h : Mod (P3 (G := G) n (kG := kG)) a t) : P3 (G := G) n (kG := kG) a t :=
  let ⟨_, ⟨p, hdi, hsi, hdx, hcx, h8⟩, hm, _, hwr, g⟩ := h
  ⟨p.of_mod hm hwr g, (g _ (by decide)).trans hdi, (g _ (by decide)).trans hsi, (g _ (by decide)).trans hdx,
    (g _ (by decide)).trans hcx, (g _ (by decide)).trans h8⟩

theorem mod_P5 {a : MQ × Nat} {t : State} (h : Mod (P5 (G := G) n (kG := kG)) a t) : P5 (G := G) n (kG := kG) a t :=
  let ⟨_, ⟨p, hdi, hsi, hdx, hcx, h8⟩, hm, _, hwr, g⟩ := h
  ⟨p.of_mod hm hwr g, (g _ (by decide)).trans hdi, (g _ (by decide)).trans hsi, (g _ (by decide)).trans hdx,
    (g _ (by decide)).trans hcx, (g _ (by decide)).trans h8⟩

theorem mod_P7 {a : MQ × Nat} {t : State} (h : Mod (P7 (G := G) n (kG := kG)) a t) : P7 (G := G) n (kG := kG) a t :=
  let ⟨_, ⟨p, hdi, hsi, hdx, hcx⟩, hm, _, hwr, g⟩ := h
  ⟨p.of_mod hm hwr g, (g _ (by decide)).trans hdi, (g _ (by decide)).trans hsi, (g _ (by decide)).trans hdx,
    (g _ (by decide)).trans hcx⟩

theorem ks_lt : ∀ k ∈ [14, 15, 16, 17, 18, 19, 20, 43], k < nW := by decide

/-- The words of `RW`, for any of its slots. -/
theorem RW.sub {m D kG : Nat} {q : MQ} {c : Nat} {t : State} (h : RW m D kG q c t) {ks : List Nat}
    (hks : ∀ k ∈ ks, k ∈ [14, 15, 16, 17, 18, 19, 20, 43]) :
    FrV m q.F q.ws t ∧ ∀ k ∈ ks, word t.mem q.F (8 * k) = mw D q c k :=
  ⟨h.words.1, fun k hk => h.words.2 k (hks k hk)⟩

include hG in
theorem round_ct (hd : Keys hs) (hk : (kG, G) ∈ hs) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (P0 (G := G) n (kG := kG))) (round lay hs) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have ldT : ∃ hc, (taint.check (frT [] [] n) (.block (ldSel sSelG)) hc).isSome = true := by
    rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine RelCT.seq (two_pieceF (Ψ := P1 (G := G) n (kG := kG)) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw G.D a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => WP.mono (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
      fun t' ⟨hdi, hm, k⟩ => ⟨h.congr (k.gpr (by decide)) k.2.2 hm, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := P0 (G := G) n (kG := kG))
    (two_callD hd hk (f := fun H => .call H.initN H.initC) (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a t h => h.1.sel) (by decide) ldT
      (two_map id (fun a t h => mod_P1 n h) (two_init hG (fun a => a.1.F) (fun a => a.1.S) fun a t h => ⟨h.1.L, h.2⟩)))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.1.rep
    exact WP.mono (initD_ok hG hs hd hk h.1.L R rfl (by decide) h38 h.2) fun t' ⟨L', _, wr', _, R', _⟩ =>
      h.1.after L' wr' R' A h19 h20 h38 h43
  -- `update` with `src`.
  refine RelCT.seq (two_pieceF (Ψ := P3 (G := G) n (kG := kG)) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw G.D a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
    exact WP.mono (updSrc_ok h.L R A) fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.2 hm, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0 (G := G) n (kG := kG))
    (two_callD hd hk (f := fun H => .call H.updN H.updC) (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a t h => h.1.sel) (by decide) ldT
      (two_map id (fun a t h => mod_P3 n h) (two_upd hG (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.src)
        (fun a => a.1.srcLen) (fun _ => BitVec.ofNat 64 0) fun a t h => by
          have := h.1.fit.fs
          exact ⟨h.1.L, by omega, by omega, by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.1.rep
    have := h.1.fit.fs
    exact WP.mono (updD_ok hG hs hd hk h.1.L R rfl (by decide) h38 (a := a.1.src) (len := a.1.srcLen) (by omega)
      (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', _, wr', _, R', _⟩ =>
      h.1.after L' wr' R' A h19 h20 h38 h43
  -- The counter, and `update` with it.
  refine RelCT.seq (two_pieceF (Ψ := P5 (G := G) n (kG := kG)) [] [14] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw G.D a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.rep
    have := h.lt
    have := h.fit.dstB
    have hc : a.2 ≤ a.2 * G.D := Nat.le_mul_of_pos_right _ hzD
    exact WP.mono (updCtr_ok h.L R A.hsl h19 (by omega)) fun t' ⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩ =>
      ⟨h.after L' k.2.2 R' A h19 h20 h38 h43, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0 (G := G) n (kG := kG))
    (two_callD hd hk (f := fun H => .call H.updN H.updC) (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a t h => h.1.sel) (by decide) ldT
      (two_map id (fun a t h => mod_P5 n h) (two_upd hG (fun a => a.1.F) (fun a => a.1.S) (fun _ => oCtr)
        (fun _ => 4) (fun a => BitVec.ofNat 64 a.1.srcLen) fun a t h =>
          ⟨h.1.L, by omega, by omega, by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.1.rep
    exact WP.mono (updD_ok hG hs hd hk h.1.L R rfl (by decide) h38 (a := oCtr) (len := 4) (by omega) (by omega)
      (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', _, wr', _, R', _⟩ =>
      h.1.after L' wr' R' A h19 h20 h38 h43
  -- `finalize`.
  refine RelCT.seq (two_pieceF (Ψ := P7 (G := G) n (kG := kG)) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw G.D a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
    exact WP.mono (finA_ok h.L R A.hsl) fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ =>
      ⟨h.congr (k.gpr (by decide)) k.2.2 hm, hdi, hsi, hdx, hcx⟩
  refine RelCT.seq (two_post (Ψ := P0 (G := G) n (kG := kG))
    (two_callD hd hk (f := fun H => .call H.finN H.finC) (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws)
      (fun a t h => h.1.sel) (by decide) ldT
      (two_map id (fun a t h => mod_P7 n h) (two_fin hG (fun a => a.1.F) (fun a => a.1.S) (fun _ => oDig)
        (fun a => BitVec.ofNat 64 (a.1.srcLen + 4)) fun a t h =>
          ⟨h.1.L, by omega, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.1.rep
    exact WP.mono (finD_ok hG hs hd hk h.1.L R rfl (by decide) h38 (o := oDig) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ => h.1.after L' wr' R' A h19 h20 h38 h43
  -- Into `dst`, and the next counter.
  refine RelCT.seq (two_pieceF (Ψ := P0 (G := G) n (kG := kG)) [] [14, 17, 18, 20, 43] (fun a => a.1.F)
    (fun a => a.1.ws) (fun a => mw G.D a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h38, h43⟩ := h.rep
    have := h.fit.fd
    exact WP.mono (xorOut_ok h.L R (dst := a.1.dst) (dstLen := a.1.dstLen) (done := a.2 * G.D) (by omega) hzD
      (by omega) A.hdst A.hdl h20 h43 h.lt) fun t' ⟨L', k, R'⟩ => h.after L' k.2.2 R' A h19 h20 h38 h43
  exact two_taintF [] [] (fun a => a.1.F) (fun a => a.1.ws) (fun a => mw G.D a.1 a.2)
    (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)

/-! ## MGF1 -/

/-- Where MGF1 starts: in the frame, with its slots set, for the hash
function of `hLen = D` that the selector `kG` names. -/
structure ME (D kG : Nat) (q : MQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧ W 38 = BitVec.ofNat 64 kG ∧
    W 43 = BitVec.ofNat 64 D

/-- Before the round with counter `j`. -/
def ML (Gs : Spec.Mgf1.Hash) (q : MQ) (j : Nat) (t : State) : Prop :=
  FrV n q.F q.ws t ∧ MFit q.src q.srcLen q.dst q.dstLen ∧ ∃ u₀ V W, MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    W 38 = BitVec.ofNat 64 kG ∧ W 43 = BitVec.ofNat 64 G.D ∧
    MgfI u₀ q.F q.S V W (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen G.D j t

/-- The number of rounds. -/
def nR (D : Nat) (q : MQ) : Nat := (q.dstLen + D - 1) / D

theorem lt_nR {D : Nat} (hD : 0 < D) (q : MQ) (j : Nat) : j < nR D q ↔ j * D < q.dstLen := by
  unfold nR
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega

include hG in
theorem ML.rw {Gs : Spec.Mgf1.Hash} {q : MQ} {j : Nat} {t : State} (h : ML (G := G) n (kG := kG) Gs q j t)
    (hj : j < nR G.D q) : RW n G.D kG q j t := by
  obtain ⟨fv, fit, u₀, V, W, A, h38, h43, I⟩ := h
  obtain ⟨V', W', R', h19, h20, hW, -⟩ := I.rep
  exact ⟨fv, I.L, fit, (lt_nR (sizes hG).2.2.2.2 q j).mp hj, V', W', R',
    A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega) (by omega) (by omega), h19, h20,
    (hW 38 (by decide) (by decide) (by decide)).trans h38, (hW 43 (by decide) (by decide) (by decide)).trans h43⟩

include hG in
/-- `dst ⊕= MGF1(src, dstLen)` in two runs with the same `MQ` and the
selector of `G`. -/
theorem mgf_ct (hd : Keys hs) (hk : (kG, G) ∈ hs) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x)
    (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (ME n G.D kG)) (mgfXor lay hs) fun _ _ => True := by
  have hD := (sizes hG).2.2.2.2
  unfold mgfXor
  refine RelCT.seq (two_pieceF (Ψ := fun q t => 0 < nR G.D q ∧ ML (G := G) n (kG := kG) Gs q 0 t) [] [] MQ.F
    MQ.ws (fun _ _ => 0) (fun q t h => ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩) nopin (by decide)
    (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h38, h43⟩ := h.rep
    have hpos := h.fit.pos
    exact WP.mono (mgfHead_ok (G := G) h.L R (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen)
      fun v I => ⟨(lt_nR hD q 0).mpr (by omega), h.fv.congr (I.L.rsp.trans h.L.rsp.symm) I.wr, h.fit, t, V, W, A,
        h38, h43, I⟩
  refine (two_loop (Ψ := fun _ _ => True) (nR G.D)
    (two_map id (fun p s h => ML.rw hG n h.2 h.1) (round_ct hG n hd hk hn)) fun q j t hj h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨fv, fit, u₀, V, W, A, h38, h43, I⟩ := h
  refine WP.mono (round_ok hG hs hd hk hGh hGl hGv fit A h38 h43 I ((lt_nR hD q j).mp hj)) fun t' ⟨hcf, I'⟩ => ?_
  have e : decide ((j + 1) * G.D < q.dstLen) = decide (j + 1 < nR G.D q) := by
    rw [decide_eq_decide]; exact (lt_nR hD q (j + 1)).symm
  refine ⟨by simp only [eval, hcf, e], fun _ => ⟨fv.congr (I'.L.rsp.trans I.L.rsp.symm) (I'.wr.trans I.wr.symm),
    fit, u₀, V, W, A, h38, h43, I'⟩, fun _ => trivial⟩

end VG.Proof.RsaOaep.X86_64
