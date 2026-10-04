import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.X86

/-!
# ChaCha20 on x86 (32-bit): the quarter round on XMM registers

`vqr` computes the quarter round on each doubleword of `xmm0, …, xmm3`.
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

theorem vqr_eq : vqr =
    [xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0, .xop (.pshuflw .xmm3 .xmm3 0xb1),
     .xop (.pshufhw .xmm3 .xmm3 0xb1), xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .pslld .xmm1 (BitVec.ofNat 8 12)),
     .xop (.shift .psrld .xmm4 (BitVec.ofNat 8 20)), xb .por .xmm1 .xmm4,
     xb .paddd .xmm0 .xmm1, xb .pxor .xmm3 .xmm0,
     xb .movdqa .xmm4 .xmm3, .xop (.shift .pslld .xmm3 (BitVec.ofNat 8 8)),
     .xop (.shift .psrld .xmm4 (BitVec.ofNat 8 24)), xb .por .xmm3 .xmm4,
     xb .paddd .xmm2 .xmm3, xb .pxor .xmm1 .xmm2,
     xb .movdqa .xmm4 .xmm1, .xop (.shift .pslld .xmm1 (BitVec.ofNat 8 7)),
     .xop (.shift .psrld .xmm4 (BitVec.ofNat 8 25)), xb .por .xmm1 .xmm4] := rfl

/-- Doubleword `l` of register `r`. -/
abbrev dw (s : State) (r : XReg) (l : Nat) : Word := dword (s.xmm r) l

theorem vqr_ok (s : State) :
    WP isa (.block vqr) s fun s' =>
      (∀ l, l < 4 →
        dw s' .xmm0 l = (quarterRound (dw s .xmm0 l) (dw s .xmm1 l) (dw s .xmm2 l) (dw s .xmm3 l)).1 ∧
        dw s' .xmm1 l = (quarterRound (dw s .xmm0 l) (dw s .xmm1 l) (dw s .xmm2 l) (dw s .xmm3 l)).2.1 ∧
        dw s' .xmm2 l = (quarterRound (dw s .xmm0 l) (dw s .xmm1 l) (dw s .xmm2 l) (dw s .xmm3 l)).2.2.1 ∧
        dw s' .xmm3 l = (quarterRound (dw s .xmm0 l) (dw s .xmm1 l) (dw s .xmm2 l) (dw s .xmm3 l)).2.2.2) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm3 → r ≠ .xmm4 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [vqr_eq]
  apply WP.of_runBlock
  simp only [xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_rot16 _ hl, pslld_12 _ hl,
      psrld_20 _ hl, pslld_8 _ hl, psrld_24 _ hl, pslld_7 _ hl, psrld_25 _ hl, rot12, rot8, rot7,
      quarterRound, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, h3, h4, not_false_eq_true]

end VG.Proof.ChaCha20.X86
