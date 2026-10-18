module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
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

`mgfXor lay` is constant time in two runs with the same frame, regions,
`src` and `dst`, and addresses of the streaming functions of MGF1's hash
function (`MQ`), whatever the bytes they hold (`mgf_ct`). In each round
(`round_ct`) the pieces between the calls are checked by the taint analysis
from the frame's public slots (`RW.words`), each call is of the same
function in both runs, with the same arguments (`two_initF`, …); the
rounds are as many as `dstLen` and `hLen` say, by correctness
(`round_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs round xorOut nextCtr initArgs updSrcArgs updCtrArgs finArgs mgfXor ldFn)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map two_loop)
open VG.Proof.HashFns (StreamingOK)

/-- MGF1's public data: the frame, the working space, the other two writable
regions, `src` and `dst` in the working space, the anchor's entry and the
addresses of the streaming functions. -/
structure MQ where
  F : Addr
  S : Addr
  ws : List Region
  src : Nat
  srcLen : Nat
  dst : Nat
  dstLen : Nat
  E : State
  fi : Addr
  fu : Addr
  ff : Addr

/-- The frame's words MGF1 reads, with the counter `c` and `hLen = D`. -/
def mw (D : Nat) (q : MQ) (c k : Nat) : BitVec 64 :=
  if k = 14 then q.S else if k = 15 then off q.S q.src else if k = 16 then BitVec.ofNat 64 q.srcLen
  else if k = 17 then off q.S q.dst else if k = 18 then BitVec.ofNat 64 q.dstLen
  else if k = 19 then BitVec.ofNat 64 c else if k = 43 then BitVec.ofNat 64 D else BitVec.ofNat 64 (c * D)

variable (stack : Nat) (T : Spec.HashFns.Streaming)

/-- A point of the round with counter `c`, calling the streaming functions
`T` whose addresses are in the slots from `sFnG` (words 48 to 50). -/
structure RW (n : Nat) (q : MQ) (c : Nat) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  lt : c * T.S.digestBytes < q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    W 19 = BitVec.ofNat 64 c ∧ W 20 = BitVec.ofNat 64 (c * T.S.digestBytes) ∧
    (W 48 = q.fi ∧ W 49 = q.fu ∧ W 50 = q.ff) ∧ W 43 = BitVec.ofNat 64 T.S.digestBytes
  calls : Calls stack T q.E q.F q.S q.fi q.fu q.ff t

variable {stack T}

theorem RW.words {n : Nat} {q : MQ} {c : Nat} {t : State} (h : RW stack T n q c t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ [14, 15, 16, 17, 18, 19, 20, 43], word t.mem q.F (8 * k) = mw T.S.digestBytes q c k := by
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

/-- The addresses, in their slots. -/
theorem RW.fns {n : Nat} {q : MQ} {c : Nat} {t : State} (h : RW stack T n q c t) :
    t.mem.readW (off q.F sFnG) 64 = q.fi ∧ t.mem.readW (off q.F (sFnG + 8)) 64 = q.fu ∧
      t.mem.readW (off q.F (sFnG + 16)) 64 = q.ff := by
  obtain ⟨V, W, R, -, -, -, ⟨h48, h49, h50⟩, -⟩ := h.rep
  exact ⟨by rw [R.rd (d := sFnG) 48 rfl (by decide), h48], by rw [R.rd (d := sFnG + 8) 49 rfl (by decide), h49],
    by rw [R.rd (d := sFnG + 16) 50 rfl (by decide), h50]⟩

/-- After code that calls nothing and keeps the memory. -/
theorem RW.step {n : Nat} {q : MQ} {c : Nat} {t : State} {cd : Prog isa} (hc : cd.noCalls = true)
    (h : RW stack T n q c t) {Q : State → Prop} (hw : WP isa cd t Q)
    (hk : ∀ t', Q t' → t'.gpr .rsp = t.gpr .rsp ∧ t'.wr = t.wr ∧ t'.mem = t.mem) :
    WP isa cd t fun t' => Q t' ∧ RW stack T n q c t' :=
  WP.mono (Calls.wp hc h.calls hw) fun t' ⟨hq, hc'⟩ =>
    let ⟨hsp, hwr, hm⟩ := hk t' hq
    ⟨hq, h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), h.fit, h.lt, by rw [hm]; exact h.rep, hc'⟩

/-- After a piece, with the slots as they were. -/
theorem RW.after {n : Nat} {q : MQ} {c : Nat} {t t' : State} (h : RW stack T n q c t) (L' : Lay t' q.F q.S)
    (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : MArgs W q.S q.src q.srcLen q.dst q.dstLen) (h19 : W 19 = BitVec.ofNat 64 c)
    (h20 : W 20 = BitVec.ofNat 64 (c * T.S.digestBytes)) (h48 : W 48 = q.fi ∧ W 49 = q.fu ∧ W 50 = q.ff)
    (h43 : W 43 = BitVec.ofNat 64 T.S.digestBytes) (hc : Calls stack T q.E q.F q.S q.fi q.fu q.ff t') :
    RW stack T n q c t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', h.fit, h.lt, ⟨V, W, R, A, h19, h20, h48, h43⟩, hc⟩

variable {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh) (n : Nat)

/-! ## The points of a round -/

abbrev P0 (a : MQ × Nat) (t : State) : Prop := RW stack T n a.1 a.2 t

abbrev P1 (a : MQ × Nat) (t : State) : Prop := RW stack T n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt

abbrev P3 (a : MQ × Nat) (t : State) : Prop :=
  RW stack T n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
    t.gpr .rdx = off a.1.S a.1.src ∧ t.gpr .rcx = BitVec.ofNat 64 a.1.srcLen ∧ t.gpr .r8 = off a.1.S oW

abbrev P5 (a : MQ × Nat) (t : State) : Prop :=
  RW stack T n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 a.1.srcLen ∧
    t.gpr .rdx = off a.1.S oCtr ∧ t.gpr .rcx = BitVec.ofNat 64 4 ∧ t.gpr .r8 = off a.1.S oW

abbrev P7 (a : MQ × Nat) (t : State) : Prop :=
  RW stack T n a.1 a.2 t ∧ t.gpr .rdi = off a.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 (a.1.srcLen + 4) ∧
    t.gpr .rdx = off a.1.S oDig ∧ t.gpr .rcx = off a.1.S oW

theorem ks_lt : ∀ k ∈ [14, 15, 16, 17, 18, 19, 20, 43], k < nW := by decide

/-- The words of `RW`, for any of its slots. -/
theorem RW.sub {m : Nat} {q : MQ} {c : Nat} {t : State} (h : RW stack T m q c t) {ks : List Nat}
    (hks : ∀ k ∈ ks, k ∈ [14, 15, 16, 17, 18, 19, 20, 43]) :
    FrV m q.F q.ws t ∧ ∀ k ∈ ks, word t.mem q.F (8 * k) = mw T.S.digestBytes q c k :=
  ⟨h.words.1, fun k hk => h.words.2 k (hks k hk)⟩

include hT in
theorem round_ct (hn : n = 2 ∨ n = 3 ∨ n = 1) :
    RelCT isa (Two (P0 (stack := stack) (T := T) n)) (round lay) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hT
  have c1 : oSt = 3072 := rfl
  have c2 : oDig = 3328 := rfl
  have c3 : oCtr = 3456 := rfl
  have c4 : oW = 4096 := rfl
  have c5 : oRsa = 8192 := rfl
  have ldT : ∀ d, d = sFnG ∨ d = sFnG + 8 ∨ d = sFnG + 16 →
      ∃ hc, (taint.check (frT [] [] n) (.block (ldFn d)) hc).isSome = true := by
    rintro d (rfl | rfl | rfl) <;> rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold round seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine RelCT.seq (two_pieceF (Ψ := P1 (stack := stack) (T := T) n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw T.S.digestBytes a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun a t h => WP.mono (h.step rfl (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
      fun t' ⟨_, hm, k⟩ => ⟨k.gpr (by decide), k.2.2, hm⟩) fun t' ⟨⟨hdi, _⟩, h'⟩ => ⟨h', hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := P0 (stack := stack) (T := T) n)
    (two_initF hT stack (Φ := P1 (stack := stack) (T := T) n) (sl := sFnG) (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws) (fun a => a.1.E) (fun a => a.1.fi)
      (fun a => a.1.fu) (fun a => a.1.ff) (fun a t h => ⟨h.1.fv, h.1.L, h.1.fns.1, h.2, h.1.calls⟩) (by decide)
      (ldT _ (.inl rfl)))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    exact WP.mono (initF_ok hT hF hh h.1.L R (j := 48) rfl (by decide) h48.1 h.2)
      fun t' ⟨L', _, wr', _, R', _, hh', _⟩ => h.1.after L' wr' R' A h19 h20 h48 h43 ⟨e, hh', hF, hl⟩
  -- `update` with `src`.
  refine RelCT.seq (two_pieceF (Ψ := P3 (stack := stack) (T := T) n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw T.S.digestBytes a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
    exact WP.mono (h.step rfl (updSrc_ok h.L R A) fun t' ⟨_, _, _, _, _, hm, k⟩ => ⟨k.gpr (by decide), k.2.2, hm⟩)
      fun t' ⟨⟨hdi, hsi, hdx, hcx, h8, _⟩, h'⟩ => ⟨h', hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0 (stack := stack) (T := T) n)
    (two_updF hT stack (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws) (fun a => a.1.E) (fun a => a.1.fi)
      (fun a => a.1.fu) (fun a => a.1.ff) (fun a => a.1.src) (fun a => a.1.srcLen) (fun _ => BitVec.ofNat 64 0)
      (Φ := P3 (stack := stack) (T := T) n) (sl := sFnG) (fun a t h => by
        have := h.1.fit.fs
        exact ⟨h.1.fv, h.1.L, h.1.fns.2.1, h.1.calls, by omega, by omega, by omega, h.2.1, h.2.2.1, h.2.2.2.1,
          h.2.2.2.2.1, h.2.2.2.2.2⟩) (by decide) (ldT _ (.inr (.inl rfl))))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    have := h.1.fit.fs
    exact WP.mono (updF_ok hT hF hh h.1.L R (j := 48) rfl (by decide) h48.2.1 (a := a.1.src) (len := a.1.srcLen)
      (by omega) (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', _, wr', _, R', hh', _⟩ =>
      h.1.after L' wr' R' A h19 h20 h48 h43 ⟨e, hh', hF, hl⟩
  -- The counter, and `update` with it.
  refine RelCT.seq (two_pieceF (Ψ := P5 (stack := stack) (T := T) n) [] [14] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw T.S.digestBytes a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.rep
    have := h.lt
    have := h.fit.dstB
    have hc : a.2 ≤ a.2 * T.S.digestBytes := Nat.le_mul_of_pos_right _ hzD
    exact WP.mono (Calls.wp rfl h.calls (updCtr_ok h.L R A.hsl h19 (by omega)))
      fun t' ⟨⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩, hc'⟩ => ⟨h.after L' k.2.2 R' A h19 h20 h48 h43 hc', hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := P0 (stack := stack) (T := T) n)
    (two_updF hT stack (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws) (fun a => a.1.E) (fun a => a.1.fi)
      (fun a => a.1.fu) (fun a => a.1.ff) (fun _ => oCtr) (fun _ => 4) (fun a => BitVec.ofNat 64 a.1.srcLen)
      (Φ := P5 (stack := stack) (T := T) n) (sl := sFnG) (fun a t h => ⟨h.1.fv, h.1.L, h.1.fns.2.1, h.1.calls, by omega, by omega, by omega, h.2.1, h.2.2.1,
        h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) (by decide) (ldT _ (.inr (.inl rfl))))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    exact WP.mono (updF_ok hT hF hh h.1.L R (j := 48) rfl (by decide) h48.2.1 (a := oCtr) (len := 4) (by omega)
      (by omega) (by omega) h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', _, wr', _, R', hh', _⟩ =>
      h.1.after L' wr' R' A h19 h20 h48 h43 ⟨e, hh', hF, hl⟩
  -- `finalize`.
  refine RelCT.seq (two_pieceF (Ψ := P7 (stack := stack) (T := T) n) [] [] (fun a => a.1.F) (fun a => a.1.ws)
    (fun a => mw T.S.digestBytes a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20⟩ := h.rep
    exact WP.mono (h.step rfl (finA_ok h.L R A.hsl) fun t' ⟨_, _, _, _, hm, k⟩ => ⟨k.gpr (by decide), k.2.2, hm⟩)
      fun t' ⟨⟨hdi, hsi, hdx, hcx, _⟩, h'⟩ => ⟨h', hdi, hsi, hdx, hcx⟩
  refine RelCT.seq (two_post (Ψ := P0 (stack := stack) (T := T) n)
    (two_finF hT stack (fun a => a.1.F) (fun a => a.1.S) (fun a => a.1.ws) (fun a => a.1.E) (fun a => a.1.fi)
      (fun a => a.1.fu) (fun a => a.1.ff) (fun _ => oDig) (fun a => BitVec.ofNat 64 (a.1.srcLen + 4))
      (Φ := P7 (stack := stack) (T := T) n) (sl := sFnG) (fun a t h => ⟨h.1.fv, h.1.L, h.1.fns.2.2, h.1.calls, by omega, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2⟩) (by decide) (ldT _ (.inr (.inr rfl))))
    fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    exact WP.mono (finF_ok hT hF hh h.1.L R (j := 48) rfl (by decide) h48.2.2 (o := oDig) (by omega) h.2.1 h.2.2.2.1
      h.2.2.2.2) fun t' ⟨L', _, wr', _, R', hh', _⟩ => h.1.after L' wr' R' A h19 h20 h48 h43 ⟨e, hh', hF, hl⟩
  -- Into `dst`, and the next counter.
  refine RelCT.seq (two_pieceF (Ψ := P0 (stack := stack) (T := T) n) [] [14, 17, 18, 20, 43] (fun a => a.1.F)
    (fun a => a.1.ws) (fun a => mw T.S.digestBytes a.1 a.2) (fun a t h => h.sub (by decide)) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun a t h => ?_) ?_
  · obtain ⟨V, W, R, A, h19, h20, h48, h43⟩ := h.rep
    have := h.fit.fd
    exact WP.mono (Calls.wp rfl h.calls (xorOut_ok h.L R (dst := a.1.dst) (dstLen := a.1.dstLen)
      (done := a.2 * T.S.digestBytes) (by omega) hzD (by omega) A.hdst A.hdl h20 h43 h.lt))
      fun t' ⟨⟨L', k, R'⟩, hc'⟩ => h.after L' k.2.2 R' A h19 h20 h48 h43 hc'
  exact two_taintF [] [] (fun a => a.1.F) (fun a => a.1.ws) (fun a => mw T.S.digestBytes a.1 a.2)
    (fun a t h => h.sub (by decide)) nopin (by decide) (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩)

/-! ## MGF1 -/

variable (stack T) in
/-- Where MGF1 starts: in the frame, with its slots set. -/
structure ME (q : MQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  fit : MFit q.src q.srcLen q.dst q.dstLen
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    (W 48 = q.fi ∧ W 49 = q.fu ∧ W 50 = q.ff) ∧ W 43 = BitVec.ofNat 64 T.S.digestBytes
  calls : Calls stack T q.E q.F q.S q.fi q.fu q.ff t

/-- Before the round with counter `j`. -/
def ML (Gs : Spec.Mgf1.Hash) (q : MQ) (j : Nat) (t : State) : Prop :=
  FrV n q.F q.ws t ∧ MFit q.src q.srcLen q.dst q.dstLen ∧ ∃ e u₀ V W, MArgs W q.S q.src q.srcLen q.dst q.dstLen ∧
    (W 48 = q.fi ∧ W 49 = q.fu ∧ W 50 = q.ff) ∧ W 43 = BitVec.ofNat 64 T.S.digestBytes ∧
    Fns stack e T q.fi q.fu q.ff ∧ Like q.E e ∧
    MgfI stack e u₀ q.F q.S V W (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen
      T.S.digestBytes j t

/-- The number of rounds. -/
def nR (D : Nat) (q : MQ) : Nat := (q.dstLen + D - 1) / D

theorem lt_nR {D : Nat} (hD : 0 < D) (q : MQ) (j : Nat) : j < nR D q ↔ j * D < q.dstLen := by
  unfold nR
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega

include hT in
theorem ML.rw {Gs : Spec.Mgf1.Hash} {q : MQ} {j : Nat} {t : State} (h : ML (stack := stack) (T := T) n Gs q j t)
    (hj : j < nR T.S.digestBytes q) : RW stack T n q j t := by
  obtain ⟨fv, fit, e, u₀, V, W, A, h48, h43, hF, hl, I⟩ := h
  obtain ⟨V', W', R', h19, h20, hW, -⟩ := I.rep
  exact ⟨fv, I.L, fit, (lt_nR (sizes hT).2.2.2.2 q j).mp hj, ⟨V', W', R',
    A.of_eq fun k h1 h2 => hW k (by unfold nW frameBytes; omega) (by omega) (by omega), h19, h20,
    ⟨(hW 48 (by decide) (by decide) (by decide)).trans h48.1, (hW 49 (by decide) (by decide) (by decide)).trans h48.2.1,
      (hW 50 (by decide) (by decide) (by decide)).trans h48.2.2⟩,
    (hW 43 (by decide) (by decide) (by decide)).trans h43⟩, e, I.here, hF, hl⟩

include hT in
/-- `dst ⊕= MGF1(src, dstLen)` in two runs with the same `MQ`. -/
theorem mgf_ct {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = T.S.H.hash x) (hGl : Gs.len = T.S.digestBytes)
    (hGv : Proof.Mgf1.Valid Gs) (hn : n = 2 ∨ n = 3 ∨ n = 1) :
    RelCT isa (Two (ME stack T n)) (mgfXor lay) fun _ _ => True := by
  have hD := (sizes hT).2.2.2.2
  unfold mgfXor
  refine RelCT.seq (two_pieceF (Ψ := fun q t => 0 < nR T.S.digestBytes q ∧ ML (stack := stack) (T := T) n Gs q 0 t)
    [] [] MQ.F MQ.ws (fun _ _ => 0) (fun q t h => ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩) nopin (by decide)
    (by rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h48, h43⟩ := h.rep
    obtain ⟨e, hh, hF, hl⟩ := h.calls
    have hpos := h.fit.pos
    exact WP.mono (mgfHead_ok hh h.L R (Spec.Mgf1.mgf1 Gs (srcB V q.src q.srcLen) q.dstLen) q.dst q.dstLen
      T.S.digestBytes) fun v I => ⟨(lt_nR hD q 0).mpr (by omega), h.fv.congr (I.L.rsp.trans h.L.rsp.symm) I.wr,
        h.fit, e, t, V, W, A, h48, h43, hF, hl, I⟩
  refine (two_loop (Ψ := fun _ _ => True) (nR T.S.digestBytes)
    (two_map id (fun p s h => ML.rw hT n h.2 h.1) (round_ct hT n hn)) fun q j t hj h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨fv, fit, e, u₀, V, W, A, h48, h43, hF, hl, I⟩ := h
  refine WP.mono (round_ok hT hF hGh hGl hGv fit A h48 h43 I ((lt_nR hD q j).mp hj)) fun t' ⟨hcf, I'⟩ => ?_
  have e' : decide ((j + 1) * T.S.digestBytes < q.dstLen) = decide (j + 1 < nR T.S.digestBytes q) := by
    rw [decide_eq_decide]; exact (lt_nR hD q (j + 1)).symm
  refine ⟨by simp only [eval, hcf, e'], fun _ => ⟨fv.congr (I'.L.rsp.trans I.L.rsp.symm) (I'.wr.trans I.wr.symm),
    fit, e, u₀, V, W, A, h48, h43, hF, hl, I'⟩, fun _ => trivial⟩

end VG.Proof.RsaOaep.X86_64
