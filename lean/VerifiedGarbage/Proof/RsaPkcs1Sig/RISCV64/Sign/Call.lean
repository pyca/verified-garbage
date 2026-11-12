module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Setup
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCall
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivVerified
public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith

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
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem nCall_nA {i : Nat} (hi : i < nCallArgs pc) : 1 + i < nA pc := by
  cases pc <;> simp only [nCallArgs, nA, Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem nCall_psa {i : Nat} (hi : i < nCallArgs pc) : 8 * i + 8 ≤ (if pc then 112 else 96) := by
  cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at * <;> omega

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
  have hn1 := nCall_nA hn
  have hn8 := nCall_psa hn
  have hpl := psa_le (pc := pc)
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub s⟩)
  unfold copyArg
  refine wp_ld (a := stackArgAddr s (1 + n)) (by rw [hc.keep.get .t6, hw6, ← stackArgAddr_eq]) (arg_al h _)
    (arg_in h (hc.keep.rd.trans hrd) hn1) (fun t₁ o₁ e₁ => ?_) (by cases pc <;> simp only [nCallArgs, Bool.false_eq_true, ↓reduceIte] at hn <;> omega)
  refine wp_sd (a := fb s + BitVec.ofNat 64 (8 * n)) (by rw [o₁.get .t0, hc.keep.get .t0, hw0])
    (fb_al8 h (by omega)) (by rw [o₁.wr, hc.keep.wr, hwr]; exact in_fr s _ (by unfold frameBytes; omega))
    (fun t₂ m₂ => wp_nil ?_) (by omega)
  rw [arg_frame h hmt hn1] at e₁
  rw [e₁] at m₂
  refine ⟨(hc.keep.trans (o₁.keep.trans m₂.keep)).mono, ?_, fun i hi => ?_⟩
  · rw [m₂.mem, o₁.mem]
    exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * n) (n := 8)
      (k := if pc then 112 else 96) (by omega) (by omega))
  · rw [m₂.mem, o₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
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
  have hpl := psa_le (pc := pc)
  have hk := h.k2
  unfold callArgs argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (imm := 0) (fun w₁ o₁ e₁ => wp_addSp (imm := frameBytes) (fun w₂ o₂ e₂ => ?_) (by decide))
    (by decide)
  rw [A.sp, BitVec.add_zero] at e₁
  have P₂ : Only [.t0, .t6] u w₂ := o₁.trans o₂
  have w0 : w₂.gpr .t0 = fb s := by rw [o₂.get .t0, e₁]
  have w6 : w₂.gpr .t6 = stackArgAddr s 0 := by rw [e₂, o₁.sp, A.sp, stackArgAddr_fb]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok h w0 w6 (P₂.rd.trans A.rd) (P₂.wr.trans A.wr) (by rw [P₂.mem]; exact A.mem))
    fun v hc => ?_
  have v0 : v.gpr .t0 = fb s := by rw [hc.keep.get .t0, w0]
  have M : SMid [] s v := A.toMid.keep (P₂.keep.trans hc.keep)
    (A.frameMem (f := 0) (n := if pc then 112 else 96) (.inr (by unfold oSave; omega))
      (by unfold frameBytes; omega) (by rw [BitVec.add_zero, ← P₂.mem]; exact hc.mem)).1
    (A.frameMem (f := 0) (n := if pc then 112 else 96) (.inr (by unfold oSave; omega))
      (by unfold frameBytes; omega) (by rw [BitVec.add_zero, ← P₂.mem]; exact hc.mem)).2
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_addi (imm := oEM) (fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ =>
    wp_nil ?_) (by decide)
  have O : Only [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] v v₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  have M₈ : SMid [] s v₈ := M.only O
  have hd : ∀ {d n : Nat}, 112 ≤ d → d + n ≤ frameBytes →
      ∀ r ∈ [psaR pc s], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun {d n} hdn hdn' r hr => by
    rw [List.mem_singleton.mp hr]
    have := Offset.disjoint (fb s) (d := d) (n := n) (e := 0) (k := if pc then 112 else 96) (.inr (by omega))
      (by unfold frameBytes at hdn'; omega) (by omega)
    rwa [BitVec.add_zero] at this
  exact {
    toMid := M₈
    em := by
      rw [O.mem, ← hem, ← P₂.mem]
      exact bytes_of_frame (s := w₂) hc.mem (hd (by decide) (by unfold oEM frameBytes; omega)) (by omega)
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
  have fbt := fb_toNat h
  have kbt := kb_toNat h
  unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at kbt
  unfold frameBytes at fbt
  have sa := fun i (hi : i < 12) => callE_stackArg A (i := i) (lt_nCall hi)
  have hsp : (callE pc s t).sp = fb s := A.sp
  have pl := psa_le (pc := pc)
  have hOo : (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s := by simp only [oR, h.h1]
  have cs := callee_sub s
  have es := em_sub h
  have ps := psa_sub (pc := pc) s
  have hK : Rsa.RISCV64.Priv.kR (callE pc s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  have ki : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (emR s) := by
    show Region.Disjoint _ ⟨fb s + BitVec.ofNat 64 oEM, _⟩
    rw [fb_off]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
      (by unfold oEM Impl.Rsa.RISCV64.Priv.frameBytes; omega)).symm
  have ka : Region.Disjoint ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (psaR pc s) := by
    show Region.Disjoint _ ⟨fb s, if pc then 112 else 96⟩
    rw [fb_eq]
    exact (Offset.disjoint_base _ (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)
      (by unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega)).symm
  have cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := cs; rwa [fb_eq, BitVec.add_sub_cancel] at this
  have g0 : (callE pc s t).gpr .a0 = s.gpr .a0 := (callE_gpr (pc := pc) s t).trans A.a0
  have g1 : (callE pc s t).gpr .a1 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a1
  have g2 : (callE pc s t).gpr .a2 = s.gpr .a2 := (callE_gpr (pc := pc) s t).trans A.a2
  have g3 : (callE pc s t).gpr .a3 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a3
  have g4 : (callE pc s t).gpr .a4 = s.gpr .a4 := (callE_gpr (pc := pc) s t).trans A.a4
  have g5 : (callE pc s t).gpr .a5 = s.gpr .a5 := (callE_gpr (pc := pc) s t).trans A.a5
  have g6 : (callE pc s t).gpr .a6 = fb s + BitVec.ofNat 64 oEM := (callE_gpr (pc := pc) s t).trans A.a6
  have g7 : (callE pc s t).gpr .a7 = s.gpr .a3 := (callE_gpr (pc := pc) s t).trans A.a7
  have hO : Rsa.RISCV64.Priv.oR (callE pc s t) = oR s := by simp only [Rsa.RISCV64.Priv.oR, g0, g1, oR, h.h1]
  have hN : Rsa.RISCV64.Priv.nR (callE pc s t) = nR s := by simp only [Rsa.RISCV64.Priv.nR, g2, g3]
  have hE : Rsa.RISCV64.Priv.eR (callE pc s t) = eR s := by simp only [Rsa.RISCV64.Priv.eR, g4, g5]
  have hI : Rsa.RISCV64.Priv.iR (callE pc s t) = emR s := by simp only [Rsa.RISCV64.Priv.iR, g6, g7]
  have hP : Rsa.RISCV64.Priv.pR (callE pc s t) = pR s := by
    simp only [Rsa.RISCV64.Priv.pR, sa 0 (by decide), sa 1 (by decide)]
  have hQ : Rsa.RISCV64.Priv.qR (callE pc s t) = qR s := by
    simp only [Rsa.RISCV64.Priv.qR, sa 2 (by decide), sa 3 (by decide)]
  have hDP : Rsa.RISCV64.Priv.dpR (callE pc s t) = dpR s := by
    simp only [Rsa.RISCV64.Priv.dpR, sa 4 (by decide), sa 5 (by decide)]
  have hDQ : Rsa.RISCV64.Priv.dqR (callE pc s t) = dqR s := by
    simp only [Rsa.RISCV64.Priv.dqR, sa 6 (by decide), sa 7 (by decide)]
  have hQI : Rsa.RISCV64.Priv.qiR (callE pc s t) = qiR s := by
    simp only [Rsa.RISCV64.Priv.qiR, sa 8 (by decide), sa 9 (by decide)]
  have hS : Rsa.RISCV64.Priv.sR (callE pc s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  have hA : Rsa.RISCV64.Priv.aR pc (callE pc s t) = psaR pc s := by
    simp only [Rsa.RISCV64.Priv.aR, stackArgAddr, hsp, Nat.mul_zero, BitVec.add_zero]
  have s1 := sa 1 (by decide)
  have s3 := sa 3 (by decide)
  have s5 := sa 5 (by decide)
  have s7 := sa 7 (by decide)
  have s9 := sa 9 (by decide)
  have s10 := sa 10 (by decide)
  have s11 := sa 11 (by decide)
  have wo' : (s.gpr .a0).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 := h.h1 ▸ h.wo
  have fa := fb_al h
  refine ⟨by rw [hsp]; exact fa, by rw [hsp]; unfold Impl.Rsa.RISCV64.Priv.frameBytes; omega,
    by rw [hsp]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
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
  · rw [g6, g7, Offset.toNat_add_ofNat]; unfold oEM; omega
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
  have pl := psa_le (pc := pc)
  have hw : Covers (callWr s) t.wr := by
    rw [A.wr, h.hwr]
    exact Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  have hleft : r ∈ rdL pc s → Covers [r] (rdL pc s ++ frR s :: s.wr) := fun h =>
    Covers.left (Covers.of_mem fun r' hr' => by rw [List.mem_singleton.mp hr']; exact h)
  simp only [callRd, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp) | rfl
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact Covers.right (Covers.one (in_fr s _ (by unfold oEM frameBytes; omega)))
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · exact hleft (by simp [rdL])
  · cases pc
    · simp at hp
    · simp only [↓reduceIte, List.mem_singleton] at hp
      subst hp; exact hleft (by simp [rdL])
  · have := in_fr s s.wr (d := 0) (n := if pc then 112 else 96) (by unfold frameBytes; omega)
    rw [BitVec.add_zero] at this
    exact Covers.right (Covers.one this)

theorem priv_sdepth : sdepth Impl.Rsa.RISCV64.Priv.code = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

theorem privP_sdepth : sdepth Impl.Rsa.RISCV64.Priv.codeP = Impl.Rsa.RISCV64.Priv.frameBytes := by decide +kernel

/-- With `pc`, the facts of `pre` at the call. -/
theorem preX_entry {s t : State} {em : List Byte} (h : SPre true s) (X : PreX s) (A : AtCall true s t em) :
    Rsa.RISCV64.Priv.PreX (callE true s t) := by
  have sa := fun i (hi : i < 14) => callE_stackArg A (i := i) hi
  have hsp : (callE true s t).sp = fb s := A.sp
  have fbt := fb_toNat h
  have sp2 := h.sp2
  simp only [↓reduceIte] at sp2
  unfold frameBytes at fbt
  have hPre : Rsa.RISCV64.Priv.preR (callE true s t) = preR s := by
    simp only [Rsa.RISCV64.Priv.preR, sa 12 (by decide), sa 13 (by decide)]
  have hO : Rsa.RISCV64.Priv.oR (callE true s t) = oR s := by
    simp only [Rsa.RISCV64.Priv.oR, callE_gpr (pc := true) s t (r := .a0), callE_gpr (pc := true) s t (r := .a1),
      A.a0, A.a1, oR, h.h1]
  have hS : Rsa.RISCV64.Priv.sR (callE true s t) = sR s := by
    simp only [Rsa.RISCV64.Priv.sR, sa 10 (by decide), sa 11 (by decide)]
  have hK : Rsa.RISCV64.Priv.kR (callE true s t) = ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    simp only [Rsa.RISCV64.Priv.kR, Rsa.RISCV64.Priv.fb, hsp, fb_eq, BitVec.add_sub_cancel]
  have cs' : Region.Sub ⟨kb s, Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
    have := callee_sub s; rwa [fb_eq, BitVec.add_sub_cancel] at this
  refine ⟨by rw [hO, hPre]; exact X.oP, by rw [hS, hPre]; exact X.sP, by rw [hK, hPre]; exact X.kP.sub_left cs',
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [sa 12 (by decide), sa 13 (by decide)]; exact X.wP
  · rw [sa 13 (by decide), sa 1 (by decide), sa 3 (by decide), callE_gpr (pc := true) s t (r := .a3), A.a3]
    exact X.pl
  · rw [hsp]; omega
  · have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    have hw := VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (p := stackArg s 13) (n := (stackArg s 14).toNat)
      (fun r hr => by rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact X.kP.symm) (by have := X.wP; omega)
    simp only [Rsa.RISCV64.Priv.PreHyp, State.withRegions_mem, State.callEntry_mem,
      callE_gpr (pc := true) s t (r := .a2), callE_gpr (pc := true) s t (r := .a3), A.a2, A.a3, sa 0 (by decide),
      sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 12 (by decide), sa 13 (by decide), hw]
    rw [hb h.kn.symm (by have := h.wn; omega), hb h.kp.symm (by have := h.wp; omega),
      hb h.kq.symm (by have := h.wq; omega)]
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
  have cs := callee_sub s
  refine WP.mono (call_priv h X A) fun u ⟨hrd, hwr, hsp, hf, hpres, hpost⟩ => hQ u ?_
  have hb : below t.sp Impl.Rsa.RISCV64.Priv.frameBytes =
      ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ := by
    rw [A.sp]
  rw [hb] at hf
  simp only [callWr, List.cons_append, List.nil_append] at hf
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ap : ∀ {d : Nat}, d + 8 ≤ frameBytes → ∀ r ∈ [oR s, sR s, (⟨fb s - BitVec.ofNat 64
      Impl.Rsa.RISCV64.Priv.frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
    intro d hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ko.sub_left (frame_sub s hd)
    · exact h.ks.sub_left (frame_sub s hd)
    · rw [fb_eq, BitVec.add_sub_cancel, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact Offset.disjoint_base _ (by omega) (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)
  have g : ∀ r ∈ kept, u.gpr r = t.gpr r := fun r hr => hp r (by revert r; decide)
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
      ap (by have := saved_offs p hp'; unfold oRa frameBytes at *; omega) r hr }, ?_⟩
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
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega), hb h.ke.symm (by have := h.we; omega),
      hb h.kp.symm (by have := h.wp; omega), hb h.kq.symm (by have := h.wq; omega),
      hb (h.h6 ▸ h.kdp.symm) (by have := h.wdp; omega), hb (h.h8 ▸ h.kdq.symm) (by have := h.wdq; omega),
      hb (h.h10 ▸ h.kqi.symm) (by have := h.wqi; omega)] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
