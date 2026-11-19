module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Setup
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPreCall
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Setup
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPreCall
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPkcs1Sig.RISCV64.Sign.Correct`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.RISCV64.Sign.Call`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: the call of `vg_rsa_private_checked`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignArgs.lean`, `SignCall.lean`): the call's
twelve (with `pc`, fourteen: `pre` and `pre_len` too) stack arguments copied
from ours and its arguments in registers
(`callArgs_ok`, into `AtCall`); the regions the call is narrowed to
(`callRd`, `callWr`) and its precondition (`preP_entry`); and
what it writes (`call_ok`, into `AtRet`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign

variable {pc : Bool}

/-- The call's stack arguments. -/
abbrev psaR (pc : Bool) (s : State) : Region := ⟨fb s, if pc then 112 else 96⟩

theorem psa_le : (if pc then 112 else 96) ≤ 112 := by cases pc <;> decide

theorem lt_nCall {i : Nat} (hi : i < 12) : i < nCallArgs pc := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hi]

theorem nCall_nA {i : Nat} (hi : i < nCallArgs pc) : 1 + i < nA pc := by
  cases pc <;> simp only [nCallArgs, nA, Bool.false_eq_true, ↓reduceIte] at * <;> omega_using [hi]

theorem nCall_psa {i : Nat} (hi : i < nCallArgs pc) : 8 * i + 8 ≤ (if pc then 112 else 96) := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at * <;> omega_using [hi]

/-- At the call of `vg_rsa_private_checked`, with `EM` holding `em`. -/
structure AtCall (pc : Bool) (s t : State) (em : List Byte) : Prop extends SMid [] s t where
  em : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .a3).toNat = em
  a0 : t.gpr .a0 = s.gpr .a0
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a2
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a4
  a5 : t.gpr .a5 = s.gpr .a5
  a6 : t.gpr .a6 = fb s + BitVec.ofNat 64 oEM
  a7 : t.gpr .a7 = s.gpr .a3
  psa : ∀ i < nCallArgs pc, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (1 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (pc : Bool) (s w : State) (n : Nat) (t : State) : Prop where
  keep : Kept [.t1] w t
  mem : Frame [psaR pc s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (1 + i)

theorem psa_sub (s : State) : Region.Sub (psaR pc s) (kR s) := by
  have := frame_sub s (d := 0) (n := if pc then 112 else 96) (by cases pc <;> decide)
  rwa [BitVec.add_zero] at this

theorem copy_step {s w : State} (h : SPre pc s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat}
    (hn : n < nCallArgs pc) {t : State} (hc : CI pc s w n t) : WP isa (.block (copyArg n)) t (CI pc s w (n + 1)) := by
  obtain hn1 := nCall_nA hn
  obtain hn8 := nCall_psa hn
  obtain hpl := psa_le (pc := pc)
  obtain hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  unfold copyArg
  refine wp_ld (a := stackArgAddr s (1 + n)) (by rw [hc.keep.get .t6, hw6, ← stackArgAddr_eq]) (arg_al h _)
    (arg_in h (hc.keep.rd.trans hrd) hn1) (fun t₁ o₁ e₁ => ?_) (by cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn <;> omega_using [hn])
  refine wp_sd (a := fb s + BitVec.ofNat 64 (8 * n)) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (fb_al8 h (by omega_using [])) (by rw [o₁.wr, hc.keep.wr, hwr]; exact in_fr s _ (by unfold frameBytes; omega_using [hn8, hpl]))
    (fun t₂ m₂ => wp_nil ?_) (by omega_using [hn8, hpl])
  rw [arg_frame h hmt hn1] at e₁
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, fun i hi => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * n) (n := 8)
      (k := if pc then 112 else 96) (by omega_using [hn8]) (by omega_using [hn8, hpl]))
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hi])) (by omega_arith) (by omega_using [hn8, hpl])) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : SPre pc s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = stackArgAddr s 0)
    (hrd : w.rd = s.rd) (hwr : w.wr = frR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range (nCallArgs pc)).flatMap copyArg)) w (CI pc s w (nCallArgs pc)) :=
  wp_range_flatMap (M := isa) (CI pc s w) (fun _ _ hn hc => copy_step h hw0 hw6 hrd hwr hm hn hc) (nCallArgs pc)
    (Nat.le_refl _) w ⟨Kept.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem callArgs_ok {s u : State} (h : SPre pc s) (A : AtAft s u) {em : List Byte}
    (hem : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .a3).toNat = em) :
    WP isa (.block (callArgs pc)) u fun t => AtCall pc s t em := by
  obtain hpl := psa_le (pc := pc)
  have hk := h.k2
  unfold callArgs argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (imm := 0) (fun w₁ o₁ e₁ => wp_addSp (imm := frameBytes) (fun w₂ o₂ e₂ => ?_) (by decide))
    (by decide)
  rw [A.sp, BitVec.add_zero] at e₁
  obtain P₂ : Only [.t0, .t6] u w₂ := o₁.trans o₂
  obtain w0 : w₂.gpr .t0 = fb s := by rw [o₂.get .t0, e₁]
  obtain w6 : w₂.gpr .t6 = stackArgAddr s 0 := by rw [e₂, o₁.sp, A.sp, stackArgAddr_fb]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w0 w6 (P₂.rd.trans A.rd) (P₂.wr.trans A.wr) (by rw [P₂.mem]; exact A.mem))
    fun v hc => ?_
  obtain v0 : v.gpr .t0 = fb s := by rw [hc.keep.get .t0, w0]
  obtain M : SMid [] s v := A.toMid.keep (P₂.keep.trans hc.keep)
    (A.frameMem (f := 0) (n := if pc then 112 else 96) (.inr (by unfold oSave; omega_using [hpl]))
      (by unfold frameBytes; omega_using [hpl]) (by rw [BitVec.add_zero, ← P₂.mem]; exact hc.mem)).1
    (A.frameMem (f := 0) (n := if pc then 112 else 96) (.inr (by unfold oSave; omega_using [hpl]))
      (by unfold frameBytes; omega_using [hpl]) (by rw [BitVec.add_zero, ← P₂.mem]; exact hc.mem)).2
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_addi (imm := oEM) (fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ =>
    wp_nil ?_) (by decide)
  obtain O : Only [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] v v₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  obtain M₈ : SMid [] s v₈ := M.only O
  obtain hd : ∀ {d n : Nat}, 112 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun {d n} hdn hdn' r hr => by
    rw [List.mem_singleton.mp hr]
    have := Offset.disjoint (fb s) (d := d) (n := n) (e := 0) (k := if pc then 112 else 96) (.inr (by omega_using [hpl, hdn]))
      (by unfold frameBytes at hdn'; omega_using [hdn']) (by omega_using [hpl])
    rwa [BitVec.add_zero] at this
  exact {
    toMid := M₈
    em := by
      rw [O.mem, ← hem, ← P₂.mem]
      exact bytes_of_frame (s := w₂) hc.mem (hd (by decide) (by unfold oEM frameBytes; omega_using [hk])) (by omega_using [])
    a0 := by rw [o₈.get .a0, o₇.get .a0, o₆.get .a0, o₅.get .a0, o₄.get .a0, o₃.get .a0, o₂.get .a0, e₁, M.s1]
    a1 := by rw [o₈.get .a1, o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, e₂, o₁.get .s3, M.s3]
    a2 := by rw [o₈.get .a2, o₇.get .a2, o₆.get .a2, o₅.get .a2, o₄.get .a2, e₃, o₂.get .s2, o₁.get .s2, M.s2]
    a3 := by
      rw [o₈.get .a3, o₇.get .a3, o₆.get .a3, o₅.get .a3, e₄, o₃.get .s3, o₂.get .s3, o₁.get .s3, M.s3]
    a4 := by
      rw [o₈.get .a4, o₇.get .a4, o₆.get .a4, e₅, o₄.get .s4, o₃.get .s4, o₂.get .s4, o₁.get .s4, M.s4]
    a5 := by
      rw [o₈.get .a5, o₇.get .a5, e₆, o₅.get .s5, o₄.get .s5, o₃.get .s5, o₂.get .s5, o₁.get .s5, M.s5]
    a6 := by
      rw [o₈.get .a6, e₇, o₆.get .t0, o₅.get .t0, o₄.get .t0, o₃.get .t0, o₂.get .t0, o₁.get .t0, v0]
    a7 := by rw [e₈, o₇.get .s3, o₆.get .s3, o₅.get .s3, o₄.get .s3, o₃.get .s3, o₂.get .s3, o₁.get .s3, M.s3]
    psa := fun i hi => by rw [O.mem]; exact hc.psa i hi }

/-! ## The call -/

/-- The regions the call reads and writes. -/
abbrev callRd (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, emR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [psaR pc s]

abbrev callWr (s : State) : List Region := [oR s, sR s]

/-- The call's narrowed entry state. -/
abbrev callE (pc : Bool) (s t : State) : State := t.callEntry.withRegions (callRd pc s) (callWr s)

theorem callE_gpr (s t : State) {r : Reg} (hr : r ∉ linkRegs := by decide) : (callE pc s t).gpr r = t.gpr r :=
  State.callEntry_gpr t hr

theorem callE_stackArg {s t : State} {em : List Byte} (A : AtCall pc s t em) {i : Nat} (hi : i < nCallArgs pc) :
    stackArg (callE pc s t) i = stackArg s (1 + i) := by
  show t.mem.readW (stackArgAddr (callE pc s t) i) 64 = _
  rw [stackArgAddr, show (callE pc s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem preP_entry {s t : State} {em : List Byte} (h : SPre pc s) (A : AtCall pc s t em) :
    Rsa.RISCV64.Priv.PreP pc (callE pc s t) := by
  have hk := h.k2
  obtain fbt := fb_toNat h
  obtain kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  obtain sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = fb s := A.sp
  obtain pl := psa_le (pc := pc)
  obtain hOo : (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s := by simp only [oR, h.h1]
  obtain cs := callee_sub s
  obtain es := em_sub h
  obtain ps := psa_sub (pc := pc) s
  obtain hK : Rsa.RISCV64.Priv.kR (callE pc s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  obtain ki : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (emR s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 oEM, _⟩
    rw [fb_off]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [])
      (by unfold oEM Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [hk])).symm
  obtain ka : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨fb s, if pc then 112 else 96⟩
    rw [fb_eq]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [])
      (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [pl])).symm
  obtain cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  obtain g0 : (callE pc s t).gpr .a0 = s.gpr .a0 := (callE_gpr (pc := pc) s t).trans A.a0
  obtain g1 : (callE pc s t).gpr .a1 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a1
  obtain g2 : (callE pc s t).gpr .a2 = s.gpr .a2 := (callE_gpr (pc := pc) s t).trans A.a2
  obtain g3 : (callE pc s t).gpr .a3 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a3
  obtain g4 : (callE pc s t).gpr .a4 = s.gpr .a4 := (callE_gpr (pc := pc) s t).trans A.a4
  obtain g5 : (callE pc s t).gpr .a5 = s.gpr .a5 := (callE_gpr (pc := pc) s t).trans A.a5
  obtain g6 : (callE pc s t).gpr .a6 = fb s + BitVec.ofNat 64 oEM := (callE_gpr (pc := pc) s t).trans A.a6
  obtain g7 : (callE pc s t).gpr .a7 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a7
  obtain hO : Rsa.RISCV64.Priv.oR (callE pc s t) = oR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1, oR, h.h1]
  obtain hN : Rsa.RISCV64.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  obtain hE : Rsa.RISCV64.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  obtain hI : Rsa.RISCV64.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7]
  obtain hP : Rsa.RISCV64.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.RISCV64.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  obtain hQ : Rsa.RISCV64.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.RISCV64.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  obtain hDP : Rsa.RISCV64.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.RISCV64.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  obtain hDQ : Rsa.RISCV64.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.RISCV64.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  obtain hQI : Rsa.RISCV64.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.RISCV64.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  obtain hS : Rsa.RISCV64.Priv.sR (callE pc s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  obtain hA : Rsa.RISCV64.Priv.aR pc (callE pc s t) = psaR pc s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  obtain s1 := sa 1 (by decide)
  obtain s3 := sa 3 (by decide)
  obtain s5 := sa 5 (by decide)
  obtain s7 := sa 7 (by decide)
  obtain s9 := sa 9 (by decide)
  obtain s10 := sa 10 (by decide)
  obtain s11 := sa 11 (by decide)
  obtain wo' : (s.gpr .a0).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 := h.h1 ▸ h.wo
  obtain fa := fb_al h
  refine ⟨by rw [hsp]; exact fa, by rw [hsp]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega_using [fbt, kbt],
    by rw [hsp]; omega_using [fbt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rsa.RISCV64.Priv.rdL, hN, hE, hI, hP, hQ, hDP, hDQ, hQI, hA]
    cases pc
    · rfl
    · simp only [↓reduceIte, Rsa.RISCV64.Priv.preR, callE_stackArg A (i := 12) (by decide),
        callE_stackArg A (i := 13) (by decide)]
      rfl
  · rw [hO, hS]; rfl
  · rw [hO, hN]; exact h.on
  · rw [hO, hE]; exact h.oe
  · rw [hO, hI]; exact (h.ko.sub_left es).symm
  · rw [hO, hP]; exact h.op
  · rw [hO, hQ]; exact h.oq
  · rw [hO, hDP]; exact h.odp
  · rw [hO, hDQ]; exact h.odq
  · rw [hO, hQI]; exact h.oqi
  · rw [hO, hS]; exact h.os
  · rw [hO, hA]; exact (h.ko.sub_left ps).symm
  · rw [hN, hS]; exact h.ns
  · rw [hE, hS]; exact h.es
  · rw [hI, hS]; exact h.ks.sub_left es
  · rw [hP, hS]; exact h.ps
  · rw [hQ, hS]; exact h.qs
  · rw [hDP, hS]; exact h.dps
  · rw [hDQ, hS]; exact h.dqs
  · rw [hQI, hS]; exact h.qis
  · rw [hS, hA]; exact (h.ks.sub_left ps).symm
  · rw [hK, hO]; exact h.ko.sub_left cs'
  · rw [hK, hN]; exact h.kn.sub_left cs'
  · rw [hK, hE]; exact h.ke.sub_left cs'
  · rw [hK, hI]; exact ki
  · rw [hK, hP]; exact h.kp.sub_left cs'
  · rw [hK, hQ]; exact h.kq.sub_left cs'
  · rw [hK, hDP]; exact h.kdp.sub_left cs'
  · rw [hK, hDQ]; exact h.kdq.sub_left cs'
  · rw [hK, hQI]; exact h.kqi.sub_left cs'
  · rw [hK, hS]; exact h.ks.sub_left cs'
  · rw [hK, hA]; exact ka
  · rw [g0, g1]; exact wo'
  · rw [g2, g3]; exact h.wn
  · rw [g4, g5]; exact h.we
  · rw [g6, g7, Offset.toNat_add_ofNat]; unfold oEM; omega_using [hk, fbt]
  · rw [sa 0 (by decide), s1]; exact h.wp
  · rw [sa 2 (by decide), s3]; exact h.wq
  · rw [sa 4 (by decide), s5]; exact h.wdp
  · rw [sa 6 (by decide), s7]; exact h.wdq
  · rw [sa 8 (by decide), s9]; exact h.wqi
  · rw [s10, s11]; exact h.ws
  · rw [g3]; exact h.k1
  · rw [g3]; exact h.k2
  · rw [g1, g3]
  · rw [g7, g3]
  · rw [g5]; exact h.e1
  · rw [g5, g3]; exact h.e2
  · rw [s1]; exact h.p1
  · rw [s1, g3]; exact h.p2
  · rw [s3]; exact h.q1
  · rw [s3, g3]; exact h.q2
  · rw [s5, s1]; exact h.h6
  · rw [s9, s1]; exact h.h10
  · rw [s7, s3]; exact h.h8
  · rw [g3, s11]; exact h.hs
  · rw [s10]; exact h.al

/-- The outcome of `vg_rsa_private_checked` of `em`, from the caller's
buffers. -/
abbrev privOut (s : State) (em : List Byte) (u : State) : Prop :=
  Spec.Rsa.writtenOutcome u.mem (s.gpr .a0) (s.gpr .a3).toNat ((u.gpr .a0).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat))

/-- After the call. -/
structure AtRet (s u : State) (em : List Byte) : Prop extends SMid [oR s, sR s] s u where
  out : privOut s em u

theorem call_covers {s t : State} {em : List Byte} (h : SPre pc s) (A : AtCall pc s t em) :
    Covers (callRd pc s ++ callWr s) (t.rd ++ t.wr) ∧ Covers (callWr s) t.wr := by
  have hk := h.k2
  obtain pl := psa_le (pc := pc)
  obtain hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  obtain hleft : r ∈ rdL pc s → Covers [r] (rdL pc s ++ frR s :: s.wr) := fun h =>
    Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact Covers.right (Covers.one (in_fr s _ (by unfold oEM frameBytes; omega_using [hk])))
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · cases pc
    · simp at hp
    · simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact hleft (by simp [rdL])
  · have := in_fr s s.wr (d := 0) (n := if pc then 112 else 96) (by unfold frameBytes; omega_using [pl])
    rw [BitVec.add_zero] at this
    exact Covers.right (Covers.one this)

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

theorem privP_sdepth : sdepth Impl.Rsa.RISCV64.Priv.codeP = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_entry {s t : State} {em : List Byte} (h : SPre true s) (X : PreX s) (A : AtCall true s t em) :
    Rsa.RISCV64.Priv.PreX (callE true s t) := by
  obtain sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = fb s := A.sp
  obtain fbt := fb_toNat h
  have sp2 := h.sp2
  simp only [↓reduceIte] at sp2
  unfold frameBytes at fbt
  obtain hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.RISCV64.Priv.preR, sa 12 (by decide), sa 13 (by decide)]
  obtain hO : Rsa.RISCV64.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.RISCV64.Priv.oR, callE_gpr (pc := true) s t (r := .a0), callE_gpr (pc := true) s t (r := .a1),
      A.a0, A.a1, oR, h.h1]
  obtain hS : Rsa.RISCV64.Priv.sR (callE true s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  obtain hK : Rsa.RISCV64.Priv.kR (callE true s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  obtain cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := callee_sub s; rwa [fb_eq, BitVec.add_sub_cancel] at this
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP, by rw [hK, hPre]; exact X.kP.sub_left cs',
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr (pc := true) s t (r := .a3), A.a3]
    exact X.pl
  · rw [hsp]; omega_using [fbt]
  · have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    obtain hw := VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (p := stackArg s 13) (n := (stackArg s 14).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega_using [this])
    simp only [Rsa.RISCV64.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .a2), callE_gpr (pc := true) s t (r := .a3), A.a2, A.a3, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), hw]
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.kp.symm (by have := h.wp; omega_using []),
      hb h.kq.symm (by have := h.wq; omega_using [])]
    exact X.hyp rfl
  · rw [sa 12 (by decide)]; exact X.alP

/-- The call of `vg_rsa_private_checked`, or with `pc` of
`vg_rsa_private_checked_precomputed`. -/
theorem call_priv {s t : State} {em : List Byte} (h : SPre pc s) (X : pc = true → PreX s) (A : AtCall pc s t em) :
    WP isa (privCall pc) t fun u => u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      Frame (callWr s ++ [below t.sp Impl.Rsa.RISCV64.Priv.frameBytes]) t.mem u.mem ∧
      (∀ r ∈ preserved, u.gpr r = t.gpr r) ∧
      Rsa.RISCV64.Priv.fnPost (callE pc s t) (u.withRegions (callRd pc s) (callWr s)) := by
  obtain ⟨hc, hw⟩ := call_covers h A
  cases pc with
  | false =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
      (Rsa.RISCV64.Priv.pre_of_preP (preP_entry h A)) hc hw (fun u hrd hwr hsp hf hpres hpost => ?_)
      (by rw [priv_sdepth]; decide)
    rw [priv_sdepth] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩
  | true =>
    refine WP.callAny (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct
      (Rsa.RISCV64.Priv.pre_of_prePX (preP_entry h A) (preX_entry h (X rfl) A)) hc hw
      (fun u hrd hwr hsp hf hpres hpost => ?_) (by rw [privP_sdepth]; decide)
    rw [privP_sdepth] at hf
    exact ⟨hrd, hwr, hsp, hf, hpres, hpost⟩

theorem call_ok {s t : State} {em : List Byte} (h : SPre pc s) (X : pc = true → PreX s) (A : AtCall pc s t em)
    {Q : State → Prop} (hQ : ∀ u, AtRet s u em → Q u) : WP isa (privCall pc) t Q := by
  have hk := h.k2
  obtain cs := callee_sub s
  refine WP.mono (call_priv h X A) fun u ⟨hrd, hwr, hsp, hf, hpres, hpost⟩ => hQ u ?_
  obtain hb : below t.sp Impl.Rsa.RISCV64.Priv.frameBytes =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    rw [A.sp]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  obtain ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega_using []) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega_using [hd])
  obtain g : ∀ r ∈ kept, u.gpr r = t.gpr r := fun r hr => hp r (by revert r; decide)
  refine ⟨{
    sp := hsp.trans A.sp
    rd := hrd.trans A.rd
    wr := hwr.trans A.wr
    s1 := (g _ (by decide)).trans A.s1
    s2 := (g _ (by decide)).trans A.s2
    s3 := (g _ (by decide)).trans A.s3
    s4 := (g _ (by decide)).trans A.s4
    s5 := (g _ (by decide)).trans A.s5
    hi := fun r hr => (g _ (List.mem_append_right _ hr)).trans (A.hi r hr)
    mem := ?_
    sv := A.sv.frame hf fun p hp' r hr =>
      ap (by have := saved_offs p hp'; unfold oRa frameBytes at *; omega_using [this]) r hr }, ?_⟩
  · refine A.mem.sub (fun r hr => ?_) |>.trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., cs⟩
  · have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
    simp only [Rsa.RISCV64.Priv.fnPost, State.withRegions_mem,
      State.withRegions_gpr, State.callEntry_mem, callE_gpr (pc := pc) s t (r := .a0), callE_gpr (pc := pc) s t (r := .a2),
      callE_gpr (pc := pc) s t (r := .a3), callE_gpr (pc := pc) s t (r := .a4), callE_gpr (pc := pc) s t (r := .a5), callE_gpr (pc := pc) s t (r := .a6),
      A.a0, A.a2, A.a3, A.a4, A.a5, A.a6, sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide),
      sa 4 (by decide), sa 6 (by decide), sa 8 (by decide), Nat.reduceAdd, A.em] at hpost
    obtain hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb h.ke.symm (by have := h.we; omega_using []),
      hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb (h.h6 ▸ h.kdp.symm) (by have := h.wdp; omega_using []), hb (h.h8 ▸ h.kdq.symm) (by have := h.wdq; omega_using []),
      hb (h.h10 ▸ h.kqi.symm) (by have := h.wqi; omega_using [])] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign

end

end

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignTail.lean`, `SignCorrect.lean`): zeros to
`out` once the encoding failed (`zeroOut_ok`), `EM` overwritten after the call
(`wipe_ok`), and the function's outcome (`fnPost`, `code_correct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64 (W Buf fillLoop_ok)

variable {pc : Bool}

theorem gpr_ofNat (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by simp

theorem W_nil (s : State) : W s [] s :=
  ⟨Kept.refl _ _, (writeBytes_nil _ _).symm, by rw [List.length_nil, BitVec.add_zero]⟩

/-- Zeros to `out`, once the encoding failed. -/
theorem zeroOut_ok {s u : State} (h : SPre pc s) (A : AtAft s u) (h0 : u.gpr .a0 = 0) :
    WP isa zeroOut u fun v => SMid [oR s, sR s] s v ∧ v.gpr .a0 = 0 ∧
      Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a3).toNat = List.replicate (s.gpr .a3).toNat 0 := by
  have hk := h.k2
  have hk1 := h.k1
  unfold zeroOut
  refine WP.seq (wp_mov fun w₁ o₁ e₁ => wp_mov fun w₂ o₂ e₂ => wp_li (imm := 0) (by decide) fun w o₃ e₃ =>
    wp_nil ?_)
  have P : Only [.a1, .t5, .t0] u w := (o₁.trans (o₂.trans o₃)).mono
  have w1 : w.gpr .a1 = s.gpr .a0 := by rw [o₃.get .a1, o₂.get .a1, e₁, A.s1]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a3).toNat := by rw [o₃.get .t5, e₂, o₁.get .s3, A.s3, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a3).toNat := fun i hi => by
    rw [P.wr, A.wr, h.hwr, w1]
    exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h1]; omega_using [hi]) (by have := h.wo; omega_using [hi])⟩
  refine WP.mono (fillLoop_ok hb (by omega_using []) (acc := []) (by omega_using [hk1]) (by simp) (W_nil w) 0
    (by rw [e₃]; rfl) w5) fun v ⟨⟨_, hm, _⟩, hk2⟩ => ?_
  rw [List.nil_append, w1] at hm
  have hO : (oR s).Contains (s.gpr .a0) (List.replicate (s.gpr .a3).toNat (0 : Byte)).length := by
    rw [List.length_replicate, ← h.h1]; exact Region.contains_self _ _
  have fo : Frame [oR s] u.mem v.mem := by rw [hm, P.mem]; exact writeBytes_frame _ _ _ hO
  refine ⟨A.toMid.keep (P.keep.trans hk2) (A.mem.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩) |>.trans (fo.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩))
    (A.sv.frame fo fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      exact h.ko.sub_left (frame_sub s (by have := saved_offs p hp; unfold oRa frameBytes at *; omega_using [this]))), ?_, ?_⟩
  · rw [hk2.get .a0, P.get .a0]; exact h0
  · rw [hm, P.mem]
    have := Proof.RsaPkcs1Sig.bytesAt_writeBytes u.mem (s.gpr .a0) (List.replicate (s.gpr .a3).toNat (0 : Byte))
      (by simp; omega_using [])
    rwa [List.length_replicate] at this

theorem wo_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

/-- `EM` overwritten with zeros, after the call. -/
theorem wipe_ok {s u : State} {em : List Byte} (h : SPre pc s) (R : AtRet s u em) :
    WP isa wipe u fun v => SMid [oR s, sR s] s v ∧ privOut s em v := by
  have hk := h.k2
  have hk1 := h.k1
  unfold wipe
  refine WP.seq (wp_addSp (imm := 0) fun w₁ o₁ e₁ => wp_addi (imm := oEM) (fun w₂ o₂ e₂ => wp_mov fun w₃ o₃ e₃ =>
    wp_li (imm := 0) (by decide) fun w o₄ e₄ => wp_nil ?_) (by decide))
  rw [R.sp, BitVec.add_zero] at e₁
  have P : Only [.t0, .a1, .t5, .t0] u w := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have w1 : w.gpr .a1 = fb s + BitVec.ofNat 64 oEM := by rw [o₄.get .a1, o₃.get .a1, e₂, e₁]
  have w5 : w.gpr .t5 = BitVec.ofNat 64 (s.gpr .a3).toNat := by
    rw [o₄.get .t5, e₃, o₂.get .s3, o₁.get .s3, R.s3, ← gpr_ofNat]
  have hb : Buf w (s.gpr .a3).toNat := fun i hi => by rw [P.wr, R.wr, w1]; exact em_in h _ hi
  refine WP.mono (fillLoop_ok hb (by omega_using []) (acc := []) (by omega_using [hk1]) (by simp) (W_nil w) 0
    (by rw [e₄]; rfl) w5) fun v ⟨⟨_, hm, _⟩, hk2⟩ => ?_
  rw [List.nil_append, w1] at hm
  have hE : (emR s).Contains (fb s + BitVec.ofNat 64 oEM) (List.replicate (s.gpr .a3).toNat (0 : Byte)).length := by
    rw [List.length_replicate]; exact Region.contains_self _ _
  have fe : Frame [emR s] u.mem v.mem := by rw [hm, P.mem]; exact writeBytes_frame _ _ _ hE
  have hf := R.frameMem (f := oEM) (n := (s.gpr .a3).toNat) (.inl (by decide)) (by unfold oEM frameBytes; omega_using [hk]) fe
  refine ⟨R.toMid.keep (S' := [oR s, sR s]) (P.keep.trans hk2) hf.1 hf.2, ?_⟩
  have hb : Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a3).toNat :=
    bytes_of_frame (s := u) fe (fun r hr => by
      rw [List.mem_singleton.mp hr, show (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s by simp only [oR, h.h1]]
      exact (h.ko.sub_left (em_sub h)).symm) (by omega_using [])
  show Spec.Rsa.writtenOutcome _ _ _ ((v.gpr .a0).setWidth 32) _
  rw [hk2.get .a0, P.get .a0]
  exact wo_congr hb R.out

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      (hid s) (hashOf s))

/-- `signId` from the encoding. -/
theorem signId_eq (s : State) :
    Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
      (hid s) (hashOf s) =
    match encOut s with
    | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) em
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
    | none => .invalid := by
  simp only [Spec.RsaPkcs1Sig.signId, encOut, RsaPkcs1Sig.RISCV64.encodeId, Spec.RsaPkcs1Sig.sign,
    Proof.RsaPkcs1Sig.bytesAt_length]
  cases Spec.RsaPkcs1Sig.Hash.ofId (hid s) with
  | none => rfl
  | some h => cases Spec.RsaPkcs1Sig.encode h (hashOf s) (s.gpr .a3).toNat <;> rfl

/-- After the encoding: zeros and 0 if it failed, else the signature, and `EM`
overwritten. -/
theorem afterEnc_ok {s u : State} (h : SPre pc s) (X : pc = true → PreX s) (B : AtAft s u) :
    WP isa (afterEnc pc) u fun v => SMid [oR s, sR s] s v ∧ fnPost s v := by
  unfold afterEnc fnPost
  rw [signId_eq]
  have he := B.enc
  revert he
  cases encOut s with
  | none =>
    intro h0
    refine WP.ite true (by rw [eval_zero, h0]; rfl) (fun _ => WP.mono (zeroOut_ok h B h0)
      fun v ⟨M, v0, vb⟩ => ⟨M, by rw [v0]; exact ⟨rfl, vb⟩⟩) (fun h => absurd h (by decide))
  | some em =>
    intro ⟨h1, hb⟩
    refine WP.ite false (by rw [eval_zero, h1]; rfl) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (callArgs_ok h B hb) fun t₃ C => ?_)
    exact WP.seq (call_ok h X C fun t₄ R => WP.mono (wipe_ok h R) fun v ⟨M, o⟩ => ⟨M, o⟩)

/-- `writtenOutcome` reads the memory only in the output. -/
private theorem writtenOutcome_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.writtenOutcome m out k r o) :
    Spec.Rsa.writtenOutcome m' out k r o := by
  cases o <;> simp only [Spec.Rsa.writtenOutcome, hb] at h ⊢ <;> exact h

theorem codeG_correct (s : State) (h : SPre pc s) (X : pc = true → PreX s) :
    ∃ tr t, Exec isa (codeG pc) s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa (codeG pc) s fun t => abiPreserved s t ∧ fnPost s t
  unfold codeG
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega_using [this]) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (WP.mono (enc_ok h A) fun t₂ B => ?_)
  refine WP.seq (WP.mono (afterEnc_ok h X B) fun v ⟨M, hp⟩ => WP.mono (restore_ok h M.saves)
    fun w ⟨wa, w0, wm⟩ mL _ fl => ⟨⟨wa.1, wa.2.1, wa.2.2⟩, ?_⟩)
  unfold fnPost at hp ⊢
  -- The `free` loses the frame's bytes, which lie apart from the output.
  refine writtenOutcome_congr (m := w.mem) (List.map_congr_left fun i hi =>
    lost_byte fl (R := ⟨s.gpr .a0, (s.gpr .a3).toNat⟩) (by
      rw [← h.h1]
      have hfb : frameBytes ≤ stackBytes := Nat.le_add_right _ _
      exact h.ko.symm.sub_right (Offset.sub_below _ hfb (by omega_using [hfb]))) (List.mem_range.mp hi)) ?_
  show Spec.Rsa.writtenOutcome w.mem _ _ ((w.gpr .a0).setWidth 32) _
  rw [wm, w0]; exact hp

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  codeG_correct s (sPre_of hpre) nofun

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign

end

end

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`code_correct`),
constant time and a state meeting the precondition. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignVerified.lean`, `SignCT.lean`,
`SignVerified.lean`), two runs with the same public data (`Two E`): the
blocks by the taint analysis, from the stack pointer and the registers that
hold public values; the branch on the encoding's result, which only the
lengths and `hash` decide (`isSome_same`); and the call by
`vg_rsa_private_checked`'s constant time (`RelCT.callEx`), whose public data
at the call the correctness facts fix (`priv_facts`, `pre_leak`, by `Priv.pub_of` or `Priv.pub_ofP`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite two_alloc)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The taint checks -/

section
variable {α : Type} {Φ : α → State → Prop}

theorem setup_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block (save ++ encArgs)) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem encode_taint (h : Pins Φ [.a1, .a2, .a3, .a4, .a5]) :
    RelCT isa (Two Φ) Impl.RsaPkcs1Sig.RISCV64.encode fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem zeroOut_taint (h : Pins Φ [.s1, .s3]) : RelCT isa (Two Φ) zeroOut fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem callArgs_taint (pc : Bool) (h : Pins Φ []) : RelCT isa (Two Φ) (.block (callArgs pc)) fun _ _ => True := by
  cases pc
  · exact two_taint [] h (by taint_decide)
  · exact two_taint [] h (by taint_decide)

theorem wipe_taint (h : Pins Φ [.s3]) : RelCT isa (Two Φ) wipe fun _ _ => True :=
  two_taint _ h (by taint_decide)

theorem restore_taint (h : Pins Φ []) : RelCT isa (Two Φ) (.block restore) fun _ _ => True :=
  two_taint [] h (by taint_decide)

end

/-! ## The public data -/

variable {pc : Bool}

/-- The public data of an entry state `s` is the anchor `a`'s: the pointers
and lengths, `hash`, our stack arguments, the bytes of `n` and `e`, and with
`pc` what may leak of `pre`. -/
structure PubS (pc : Bool) (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a7], s.gpr r = a.gpr r
  h6 : (s.gpr .a6).setWidth 32 = (a.gpr .a6).setWidth 32
  args : ∀ i < nA pc, stackArg s i = stackArg a i
  n : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a2) (a.gpr .a3).toNat
  e : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .a4) (a.gpr .a5).toNat
  leak : pc = true → Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 13) (s.gpr .a3).toNat =
    Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 13) (a.gpr .a3).toNat

theorem pubS_of {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pub s₁ s₂) :
    PubS false s₁ s₂ := by
  have e : stackBytes = 4431 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_thirteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [bytesAt_length, h6])
  refine ⟨hsp.symm, fun r hr => ?_, h9.symm, fun i hi => ?_,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn).symm,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he).symm, nofun⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h10.symm]
  · simp only [nA, Bool.false_eq_true, ↓reduceIte] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm, a9.symm, a10.symm,
      a11.symm, a12.symm]

/-- An entry state with the anchor's public data, and with `pc` `pre`'s facts. -/
structure E (pc : Bool) (a s : State) : Prop where
  pre : SPre pc s
  pub : PubS pc a s
  px : pc = true → PreX s

section
variable {a s₁ s₂ : State}

theorem fb_same (h₁ : E pc a s₁) (h₂ : E pc a s₂) : fb s₁ = fb s₂ := by simp only [fb, h₁.pub.sp, h₂.pub.sp]

theorem gpr_same (h₁ : E pc a s₁) (h₂ : E pc a s₂) {r : Reg}
    (hr : r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a7] := by decide) : s₁.gpr r = s₂.gpr r :=
  (h₁.pub.g r hr).trans (h₂.pub.g r hr).symm

theorem arg_same (h₁ : E pc a s₁) (h₂ : E pc a s₂) {i : Nat} (hi : i < 13 := by decide) :
    stackArg s₁ i = stackArg s₂ i :=
  (h₁.pub.args i (nA_le pc hi)).trans (h₂.pub.args i (nA_le pc hi)).symm

theorem hid_same (h₁ : E pc a s₁) (h₂ : E pc a s₂) : hid s₁ = hid s₂ := by
  simp only [hid, h₁.pub.h6, h₂.pub.h6]

/-- Whether the encoding succeeds depends only on `hash`, the lengths of the
hash value and `k`. -/
theorem isSome_same (h₁ : E pc a s₁) (h₂ : E pc a s₂) : (encOut s₁).isSome = (encOut s₂).isSome := by
  unfold encOut RsaPkcs1Sig.RISCV64.encodeId
  rw [hid_same h₁ h₂, gpr_same h₁ h₂ (r := .a3)]
  cases Spec.RsaPkcs1Sig.Hash.ofId (hid s₂) with
  | none => rfl
  | some h =>
    simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hashOf,
      bytesAt_length, arg_same h₁ h₂ (i := 0)]
    split <;> rfl

end

theorem AtAft.a0_eq {s u : State} (B : AtAft s u) : u.gpr .a0 = if (encOut s).isSome then 1 else 0 := by
  have := B.enc
  revert this
  cases encOut s with
  | none => intro h; exact h
  | some _ => intro h; exact h.1

/-! ## The call -/

theorem priv_facts {a s₁ s₂ t₁ t₂ : State} {em₁ em₂ : List Byte} (h₁ : E pc a s₁) (h₂ : E pc a s₂)
    (A₁ : AtCall pc s₁ t₁ em₁) (A₂ : AtCall pc s₂ t₂ em₂) :
    (callE pc s₁ t₁).sp = (callE pc s₂ t₂).sp ∧
    (∀ r ∈ argRegs, (callE pc s₁ t₁).gpr r = (callE pc s₂ t₂).gpr r) ∧
    (∀ i < nCallArgs pc, stackArg (callE pc s₁ t₁) i = stackArg (callE pc s₂ t₂) i) ∧
    Spec.Rsa.bytesAt (callE pc s₁ t₁).mem ((callE pc s₁ t₁).gpr .a2) ((callE pc s₁ t₁).gpr .a3).toNat =
      Spec.Rsa.bytesAt (callE pc s₂ t₂).mem ((callE pc s₂ t₂).gpr .a2) ((callE pc s₂ t₂).gpr .a3).toNat ∧
    Spec.Rsa.bytesAt (callE pc s₁ t₁).mem ((callE pc s₁ t₁).gpr .a4) ((callE pc s₁ t₁).gpr .a5).toNat =
      Spec.Rsa.bytesAt (callE pc s₂ t₂).mem ((callE pc s₂ t₂).gpr .a4) ((callE pc s₂ t₂).gpr .a5).toNat := by
  have hn : ∀ {s t : State} {em : List Byte}, SPre pc s → AtCall pc s t em →
      Spec.Rsa.bytesAt (callE pc s t).mem ((callE pc s t).gpr .a2) ((callE pc s t).gpr .a3).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.a2, A.a3]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kn.symm)
      (by have := h.wn; omega_using [])
  have he : ∀ {s t : State} {em : List Byte}, SPre pc s → AtCall pc s t em →
      Spec.Rsa.bytesAt (callE pc s t).mem ((callE pc s t).gpr .a4) ((callE pc s t).gpr .a5).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat := fun h A => by
    rw [callE_gpr, callE_gpr, A.a4, A.a5]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ke.symm)
      (by have := h.we; omega_using [])
  refine ⟨by rw [show (callE pc s₁ t₁).sp = fb s₁ from A₁.sp,
      show (callE pc s₂ t₂).sp = fb s₂ from A₂.sp, fb_same h₁ h₂], fun r hr => ?_, fun i hi => ?_,
    by rw [hn h₁.pre A₁, hn h₂.pre A₂, h₁.pub.n, h₂.pub.n], by rw [he h₁.pre A₁, he h₂.pre A₂, h₁.pub.e, h₂.pub.e]⟩
  · rw [callE_gpr s₁ t₁ (fun h => by revert r; decide), callE_gpr s₂ t₂ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, gpr_same h₁ h₂]
    · rw [A₁.a1, A₂.a1, gpr_same h₁ h₂]
    · rw [A₁.a2, A₂.a2, gpr_same h₁ h₂]
    · rw [A₁.a3, A₂.a3, gpr_same h₁ h₂]
    · rw [A₁.a4, A₂.a4, gpr_same h₁ h₂]
    · rw [A₁.a5, A₂.a5, gpr_same h₁ h₂]
    · rw [A₁.a6, A₂.a6, fb_same h₁ h₂]
    · rw [A₁.a7, A₂.a7, gpr_same h₁ h₂]
  · have hi' := nCall_nA hi
    rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, (h₁.pub.args _ hi').trans (h₂.pub.args _ hi').symm]

/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s t : State} {em : List Byte} (X : PreX s) (A : AtCall true s t em) :
    Spec.Rsa.privatePrecomputedLeak (callE true s t).mem (stackArg (callE true s t) 12)
        ((callE true s t).gpr .a3).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 13) (s.gpr .a3).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .a3).toNat ≤ (stackArg s 14).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide),
    callE_gpr (pc := true) s t (r := .a3), A.a3]
  refine congrArg _ ?_
  have subPre : Region.Sub ⟨stackArg s 13, 8 * Spec.Rsa.precomputedWords (s.gpr .a3).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem priv_rel :
    RelCT isa (Two fun a t => ∃ s em, E pc a s ∧ AtCall pc s t em) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct
      Rsa.RISCV64.Priv.code_ct fun u₁ u₂ ⟨_, ⟨s₁, _, h₁, A₁⟩, ⟨s₂, _, h₂, A₂⟩⟩ => ?_
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts h₁ h₂ A₁ A₂
    exact ⟨callRd false s₁, callWr s₁, callRd false s₂, callWr s₂,
      Rsa.RISCV64.Priv.pre_of_preP (preP_entry h₁.pre A₁), Rsa.RISCV64.Priv.pre_of_preP (preP_entry h₂.pre A₂),
      Rsa.RISCV64.Priv.pub_of hsp hr ha hn he,
      (call_covers h₁.pre A₁).1, (call_covers h₁.pre A₁).2, (call_covers h₂.pre A₂).1, (call_covers h₂.pre A₂).2⟩
  | true =>
    refine RelCT.callEx (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct
      Rsa.RISCV64.Priv.codeP_ct fun u₁ u₂ ⟨_, ⟨s₁, _, h₁, A₁⟩, ⟨s₂, _, h₂, A₂⟩⟩ => ?_
    obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts h₁ h₂ A₁ A₂
    have X₁ := h₁.px rfl
    have X₂ := h₂.px rfl
    exact ⟨callRd true s₁, callWr s₁, callRd true s₂, callWr s₂,
      Rsa.RISCV64.Priv.pre_of_prePX (preP_entry h₁.pre A₁) (preX_entry h₁.pre X₁ A₁),
      Rsa.RISCV64.Priv.pre_of_prePX (preP_entry h₂.pre A₂) (preX_entry h₂.pre X₂ A₂),
      Rsa.RISCV64.Priv.pub_ofP hsp hr ha hn he
        (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, h₁.pub.leak rfl, h₂.pub.leak rfl]),
      (call_covers h₁.pre A₁).1, (call_covers h₁.pre A₁).2, (call_covers h₂.pre A₂).1, (call_covers h₂.pre A₂).2⟩

/-! ## The chain -/

theorem sign_rel :
    RelCT isa (Two fun a t => (∃ s, E pc a s ∧ AtAft s t) ∧ isa.eval (.zero .a0) t = some false)
      (.seq (.block (callArgs pc)) (.seq (privCall pc) wipe)) fun _ _ => True := by
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E pc a s ∧ AtCall pc s t em)
    (callArgs_taint pc fun _ _ _ ⟨⟨s₁, h₁, B₁⟩, _⟩ ⟨⟨s₂, h₂, B₂⟩, _⟩ =>
      ⟨by rw [B₁.sp, B₂.sp, fb_same h₁ h₂], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨⟨s, h, B⟩, hz⟩ => ?_) ?_
  · have he := B.enc
    rw [eval_zero, B.a0_eq] at hz
    revert he
    cases hc : encOut s with
    | none => rw [hc] at hz; simp at hz
    | some em => intro ⟨_, hb⟩; exact WP.mono (callArgs_ok h.pre B hb) fun v C => ⟨s, em, h, C⟩
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s em, E pc a s ∧ AtRet s t em) priv_rel
    fun a u ⟨s, em, h, C⟩ => call_ok h.pre h.px C fun v R => ⟨s, em, h, R⟩) ?_
  exact wipe_taint fun _ _ _ ⟨s₁, _, h₁, R₁⟩ ⟨s₂, _, h₂, R₂⟩ =>
    ⟨by rw [R₁.sp, R₂.sp, fb_same h₁ h₂], fun r hr => by
      rw [List.mem_singleton.mp hr, R₁.s3, R₂.s3, gpr_same h₁ h₂]⟩

theorem aft_rel : RelCT isa (Two fun a t => ∃ s, E pc a s ∧ AtAft s t) (afterEnc pc) fun _ _ => True := by
  unfold afterEnc
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, B₁⟩ ⟨s₂, h₂, B₂⟩ => by
      rw [eval_zero, eval_zero, B₁.a0_eq, B₂.a0_eq, isSome_same h₁ h₂])
    (zeroOut_taint fun _ _ _ ⟨⟨s₁, h₁, B₁⟩, _⟩ ⟨⟨s₂, h₂, B₂⟩, _⟩ => ⟨by rw [B₁.sp, B₂.sp, fb_same h₁ h₂],
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [B₁.s1, B₂.s1, gpr_same h₁ h₂]
        · rw [B₁.s3, B₂.s3, gpr_same h₁ h₂]⟩) sign_rel

theorem codeG_rel : RelCT isa (Two (E pc)) (codeG pc) fun _ _ => True := by
  unfold codeG
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E pc a s ∧ AtEnc s t)
    (setup_taint fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ =>
      ⟨by rw [e₁, e₂]; show s₁.sp - _ = s₂.sp - _; rw [h₁.pub.sp, h₂.pub.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a u ⟨s, h, hu⟩ => hu ▸ WP.mono (setup_ok h.pre) fun t ht => ⟨s, h, ht⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E pc a s ∧ AtAft s t)
    (encode_taint fun _ _ _ ⟨s₁, h₁, A₁⟩ ⟨s₂, h₂, A₂⟩ => ⟨by rw [A₁.sp, A₂.sp, fb_same h₁ h₂], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [A₁.a1, A₂.a1, fb_same h₁ h₂]
      · rw [A₁.a2, A₂.a2, gpr_same h₁ h₂]
      · exact BitVec.eq_of_toNat_eq (by rw [A₁.a3, A₂.a3, hid_same h₁ h₂])
      · rw [A₁.a4, A₂.a4, gpr_same h₁ h₂]
      · rw [A₁.a5, A₂.a5, arg_same h₁ h₂]⟩)
    fun a t ⟨s, h, A⟩ => WP.mono (enc_ok h.pre A) fun u B => ⟨s, h, B⟩) ?_
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E pc a s ∧ SMid [oR s, sR s] s t) aft_rel
    fun a t ⟨s, h, B⟩ => WP.mono (afterEnc_ok h.pre h.px B) fun v ⟨M, _⟩ => ⟨s, h, M⟩) ?_
  exact restore_taint fun _ _ _ ⟨s₁, h₁, M₁⟩ ⟨s₂, h₂, M₂⟩ =>
    ⟨by rw [M₁.sp, M₂.sp, fb_same h₁ h₂], fun _ h => absurd h List.not_mem_nil⟩

theorem PubS.refl (s : State) : PubS pc s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, rfl, fun _ => rfl⟩

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre
      (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pub code :=
  RelCT.constantTime ((codeG_rel (pc := false)).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨sPre_of h₁, PubS.refl _, nofun⟩, ⟨sPre_of h₂, pubS_of hp, nofun⟩⟩)
    fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- A modulus of 64 bytes, `e`, the hash value, the primes, exponents and
`qInv` of a byte each, 1056 words of working space; our stack arguments at
`sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a7 => 0x5000
    | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x41
    else bif Nat.beq a.toNat 0x10010 then 1 else bif Nat.beq a.toNat 0x10019 then 0x42
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x43
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x44
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x45
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x1005A then 0x02
    else bif Nat.beq a.toNat 0x10060 then 0x20 else bif Nat.beq a.toNat 0x10061 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x5000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10000, 104⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x4100 ∧ stackArg satState 2 = 1 ∧
    stackArg satState 3 = 0x4200 ∧ stackArg satState 4 = 1 ∧ stackArg satState 5 = 0x4300 ∧
    stackArg satState 6 = 1 ∧ stackArg satState 7 = 0x4400 ∧ stackArg satState 8 = 1 ∧
    stackArg satState 9 = 0x4500 ∧ stackArg satState 10 = 1 ∧ stackArg satState 11 = 0x20000 ∧
    stackArg satState 12 = 1056 := by
  decide

theorem sat : ∃ s, (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes).pre s := by
  refine ⟨satState, ?_⟩
  have e : stackBytes = 4431 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_thirteen, List.append_eq, List.range, List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := sat_args
  have ha : stackArgAddr satState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, ha]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by unfold Spec.Rsa.lenValid; decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem code_verified : Verified RISCV64.target code (Spec.RsaPkcs1Sig.signContract RISCV64.abi stackBytes) :=
  ⟨code_correct, code_constantTime, sat⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
