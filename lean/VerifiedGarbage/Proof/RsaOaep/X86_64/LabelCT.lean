module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the label's hash in constant time

`hashLabel o` is constant time in two runs with the same frame, regions,
label's address and length, and addresses of the streaming functions
(`LQ`), whatever the label (`hashLabel_ct`): the blocks between the calls
are checked by the taint analysis, and each call is of the same function in
both runs, with the same arguments (`two_initF`, …).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs ldFn initF updF finF)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_map)
open VG.Proof.HashFns (StreamingOK)

/-- The label's hash's public data: the frame, the working space, the other
two writable regions, the label's address and length, the anchor's entry
and the addresses of the streaming functions. -/
structure LQ where
  F : Addr
  S : Addr
  ws : List Region
  lab : Addr
  labLen : Nat
  E : State
  fi : Addr
  fu : Addr
  ff : Addr

variable (stack : Nat) (T : Spec.HashFns.Streaming)

/-- A point of `hashLabel`, calling the streaming functions `T` whose
addresses are in the slots from `sFnH` (words 45 to 47). -/
structure LW (n : Nat) (q : LQ) (t : State) : Prop where
  fv : FrV n q.F q.ws t
  L : Lay t q.F q.S
  rep : ∃ V W, Rep t.mem q.F q.S V W ∧ LabAt t q.F q.S W q.lab q.labLen ∧ W 45 = q.fi ∧ W 46 = q.fu ∧
    W 47 = q.ff
  calls : Calls stack T q.E q.F q.S q.fi q.fu q.ff t
  bd : q.lab.toNat + q.labLen ≤ 2 ^ 64
  cd : ∀ x, (⟨q.lab, q.labLen⟩ : Region).Contains x 1 →
    InRegions (q.E.rd ++ q.E.wr ++ abi.reserved stack q.E) x 1

variable {stack T}

/-- After code that calls nothing. -/
theorem LW.step {n : Nat} {q : LQ} {t : State} {c : Prog isa} (hc : c.noCalls = true) (h : LW stack T n q t)
    {Q : State → Prop} (hw : WP isa c t Q) (hk : ∀ t', Q t' → t'.gpr .rsp = t.gpr .rsp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ t'.mem = t.mem) :
    WP isa c t fun t' => Q t' ∧ LW stack T n q t' := by
  obtain ⟨e, hh, hF, hl⟩ := h.calls
  refine WP.mono (WP.here hc hh hw) fun t' ⟨hq, hh'⟩ => ⟨hq, ?_⟩
  obtain ⟨hsp, hrd, hwr, hm⟩ := hk t' hq
  obtain ⟨V, W, R, A, h45⟩ := h.rep
  exact ⟨h.fv.congr hsp hwr, h.L.congr hsp hwr (by rw [hm]), ⟨V, W, hm ▸ R, A.congr hrd hwr rfl rfl, h45⟩,
    ⟨e, hh', hF, hl⟩, h.bd, h.cd⟩

/-- After a call. -/
theorem LW.after {n : Nat} {q : LQ} {t t' : State} (h : LW stack T n q t) (L' : Lay t' q.F q.S)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t'.mem q.F q.S V W)
    (A : LabAt t q.F q.S W q.lab q.labLen) (h45 : W 45 = q.fi ∧ W 46 = q.fu ∧ W 47 = q.ff)
    (hc : Calls stack T q.E q.F q.S q.fi q.fu q.ff t') : LW stack T n q t' :=
  ⟨h.fv.congr (L'.rsp.trans h.L.rsp.symm) hwr, L', ⟨V, W, R, A.congr hrd hwr rfl rfl, h45⟩, hc, h.bd, h.cd⟩

theorem LW.fr {n : Nat} {q : LQ} {t : State} (h : LW stack T n q t) :
    FrV n q.F q.ws t ∧ ∀ k ∈ ([] : List Nat), word t.mem q.F (8 * k) = 0 :=
  ⟨h.fv, fun _ h => absurd h List.not_mem_nil⟩

/-- The addresses, in their slots. -/
theorem LW.fns {n : Nat} {q : LQ} {t : State} (h : LW stack T n q t) :
    t.mem.readW (off q.F sFnH) 64 = q.fi ∧ t.mem.readW (off q.F (sFnH + 8)) 64 = q.fu ∧
      t.mem.readW (off q.F (sFnH + 16)) 64 = q.ff := by
  obtain ⟨V, W, R, -, h45, h46, h47⟩ := h.rep
  exact ⟨by rw [R.rd (d := sFnH) 45 rfl (by decide), h45], by rw [R.rd (d := sFnH + 8) 46 rfl (by decide), h46],
    by rw [R.rd (d := sFnH + 16) 47 rfl (by decide), h47]⟩

/-! ## The points between the calls -/

abbrev Q1 (n : Nat) (q : LQ) (t : State) : Prop := LW stack T n q t ∧ t.gpr .rdi = off q.S oSt

abbrev Q3 (n : Nat) (q : LQ) (t : State) : Prop := LW stack T n q t ∧ t.gpr .rdi = off q.S oSt ∧
  t.gpr .rsi = BitVec.ofNat 64 0 ∧ t.gpr .rdx = q.lab ∧ t.gpr .rcx = BitVec.ofNat 64 q.labLen ∧
  t.gpr .r8 = off q.S oW

abbrev Q5 (n o : Nat) (q : LQ) (t : State) : Prop := LW stack T n q t ∧ t.gpr .rdi = off q.S oSt ∧
  t.gpr .rsi = BitVec.ofNat 64 q.labLen ∧ t.gpr .rdx = off q.S o ∧ t.gpr .rcx = off q.S oW

variable {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)

include hT in
/-- The label's hash to `scratch + o`, in two runs with the same `LQ`. -/
theorem hashLabel_ct (n : Nat) (hn : n = 2 ∨ n = 3) {o : Nat} (ho : o = oDig ∨ o = oLh) :
    RelCT isa (Two (LW stack T n)) (hashLabel o) fun _ _ => True := by
  have hoo : oSt + 256 ≤ o ∧ o + 64 ≤ oW := by rcases ho with rfl | rfl <;> decide
  have hz := sizes hT
  unfold hashLabel seqs seqs seqs seqs seqs
  refine RelCT.seq (two_pieceF (Ψ := Q1 (stack := stack) (T := T) n) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h =>
      WP.mono (h.step rfl (scr_ok h.L (d := .rdi) (by decide) (o := oSt) (by decide))
        fun t' ⟨_, hm, k⟩ => ⟨k.gpr (by decide), k.2.1, k.2.2, hm⟩) fun t' ⟨⟨hdi, _⟩, h'⟩ => ⟨h', hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := LW stack T n)
    (two_initF hT stack (Φ := Q1 (stack := stack) (T := T) n) (sl := sFnH) LQ.F LQ.S LQ.ws LQ.E LQ.fi LQ.fu LQ.ff (fun q t h => ⟨h.1.fv, h.1.L, h.1.fns.1, h.2,
      h.1.calls⟩) (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h45⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    exact WP.mono (initF_ok hT hF hh h.1.L R (j := 45) rfl (by decide) h45.1 h.2)
      fun t' ⟨L', rd', wr', _, R', _, hh', _⟩ => h.1.after L' rd' wr' R' A h45 ⟨e, hh', hF, hl⟩
  refine RelCT.seq (two_pieceF (Ψ := Q3 (stack := stack) (T := T) n) [] [] LQ.F LQ.ws (fun _ _ => 0)
    (fun q t h => h.fr) nopin (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, -⟩ := h.rep
    exact WP.mono (h.step rfl (labA_ok h.L R A) fun t' ⟨_, _, _, _, _, hm, k⟩ => ⟨k.gpr (by decide), k.2.1, k.2.2, hm⟩)
      fun t' ⟨⟨hdi, hsi, hdx, hcx, h8, _⟩, h'⟩ => ⟨h', hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := LW stack T n)
    (two_updExtF hT stack LQ.F LQ.S LQ.ws LQ.E LQ.fi LQ.fu LQ.ff LQ.lab LQ.labLen (fun _ => BitVec.ofNat 64 0)
      (Φ := Q3 (stack := stack) (T := T) n) (sl := sFnH) (fun q t h => by
        obtain ⟨V, W, R, A, -⟩ := h.1.rep
        exact ⟨h.1.fv, h.1.L, h.1.fns.2.1, h.1.calls, A.len, h.1.bd, h.1.cd, A.dS, A.dK, h.2.1, h.2.2.1,
          h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) (by decide)
      (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩))
    fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, h45⟩ := h.1.rep
    obtain ⟨e, hh, hF, hl⟩ := h.1.calls
    have cd : ∀ x, (⟨q.lab, q.labLen⟩ : Region).Contains x 1 → InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1 :=
      fun x hx => by
        rw [hl.rd, hl.wr, show abi.reserved stack e = abi.reserved stack q.E by simp only [abi, hl.sp]]
        exact h.1.cd x hx
    exact WP.mono (updExtF_ok hT hF hh h.1.L R (j := 45) rfl (by decide) h45.2.1 A.len h.1.bd cd A.dS A.dK h.2.1
      h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) fun t' ⟨L', rd', wr', _, R', _, hh', _⟩ =>
        h.1.after L' rd' wr' R' A h45 ⟨e, hh', hF, hl⟩
  refine RelCT.seq (two_pieceF (Ψ := Q5 (stack := stack) (T := T) n o) [] [] LQ.F LQ.ws
    (fun _ _ => 0) (fun q t h => h.fr) nopin (by decide)
    (by rcases ho with rfl | rfl <;> rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩) fun q t h => ?_) ?_
  · obtain ⟨V, W, R, A, -⟩ := h.rep
    exact WP.mono (h.step rfl (labF_ok h.L R A.hll (o := o) (by rcases ho with rfl | rfl <;> decide))
      fun t' ⟨_, _, _, _, hm, k⟩ => ⟨k.gpr (by decide), k.2.1, k.2.2, hm⟩)
      fun t' ⟨⟨hdi, hsi, hdx, hcx, _⟩, h'⟩ => ⟨h', hdi, hsi, hdx, hcx⟩
  exact two_finF hT stack LQ.F LQ.S LQ.ws LQ.E LQ.fi LQ.fu LQ.ff (fun _ => o) (fun q => BitVec.ofNat 64 q.labLen)
    (Φ := Q5 (stack := stack) (T := T) n o) (sl := sFnH) (fun q t h => ⟨h.1.fv, h.1.L, h.1.fns.2.2, h.1.calls, Or.inr hoo, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2⟩) (by decide) (by rcases hn with rfl | rfl <;> exact ⟨_, by taint_decide⟩)

end VG.Proof.RsaOaep.X86_64
