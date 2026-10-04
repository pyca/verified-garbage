import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 on x86 (32-bit): the quarter round on XMM registers

`vqr a b c d` computes the quarter round on each doubleword of `a, b, c, d`.
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86
open VG.Spec.ChaCha20 (Word quarterRound)

/-! ## The quarter round on XMM registers -/

theorem rot12 (x : Word) : x <<< 12 ||| x >>> 20 = x.rotateLeft 12 := shl_or_shr x (by decide) (by decide)
theorem rot8 (x : Word) : x <<< 8 ||| x >>> 24 = x.rotateLeft 8 := shl_or_shr x (by decide) (by decide)
theorem rot7 (x : Word) : x <<< 7 ||| x >>> 25 = x.rotateLeft 7 := shl_or_shr x (by decide) (by decide)

theorem pslld_12 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 12)) i = dword x i <<< 12 := dword_pslld x _ (by decide) hi
theorem psrld_20 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 20)) i = dword x i >>> 20 := dword_psrld x _ (by decide) hi
theorem pslld_8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 8)) i = dword x i <<< 8 := dword_pslld x _ (by decide) hi
theorem psrld_24 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 24)) i = dword x i >>> 24 := dword_psrld x _ (by decide) hi
theorem pslld_7 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 7)) i = dword x i <<< 7 := dword_pslld x _ (by decide) hi
theorem psrld_25 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 25)) i = dword x i >>> 25 := dword_psrld x _ (by decide) hi

/-- Doubleword `l` of register `r`. -/
abbrev dw (s : State) (r : XReg) (l : Nat) : Word := dword (s.xmm r) l

/-- `vqr a b c d` computes the quarter round on each doubleword of `a, b, c,
d` (four distinct registers other than `xmm7`), writing only them and `xmm7`. -/
theorem vqr_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm7) (hb : b ≠ .xmm7) (hc : c ≠ .xmm7)
    (hd : d ≠ .xmm7) (s : State) :
    WP isa (.block (vqr a b c d)) s fun s' =>
      (∀ l, l < 4 →
        dw s' a l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).1 ∧
        dw s' b l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.1 ∧
        dw s' c l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.2.1 ∧
        dw s' d l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.2.2) ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [vqr, vrot, xb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hab, RegUpd.xmm_setXmm_of_ne _ _ hac,
      RegUpd.xmm_setXmm_of_ne _ _ had, RegUpd.xmm_setXmm_of_ne _ _ hbc, RegUpd.xmm_setXmm_of_ne _ _ hbd,
      RegUpd.xmm_setXmm_of_ne _ _ hcd, RegUpd.xmm_setXmm_of_ne _ _ hab.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hac.symm, RegUpd.xmm_setXmm_of_ne _ _ had.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hbc.symm, RegUpd.xmm_setXmm_of_ne _ _ hbd.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hcd.symm, RegUpd.xmm_setXmm_of_ne _ _ ha, RegUpd.xmm_setXmm_of_ne _ _ hb,
      RegUpd.xmm_setXmm_of_ne _ _ hc, RegUpd.xmm_setXmm_of_ne _ _ hd, RegUpd.xmm_setXmm_of_ne _ _ ha.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hb.symm, RegUpd.xmm_setXmm_of_ne _ _ hc.symm, RegUpd.xmm_setXmm_of_ne _ _ hd.symm,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_rot16 _ hl, pslld_12 _ hl,
      psrld_20 _ hl, pslld_8 _ hl, psrld_24 _ hl, pslld_7 _ hl, psrld_25 _ hl, rot12, rot8, rot7,
      quarterRound, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3, RegUpd.xmm_setXmm_of_ne _ _ h4]

end VG.Proof.ChaCha20.X86
