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

theorem ea_setXmm' (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

/-- The quarter round on each doubleword of `a, b, c, d`, and only them and
`xmm7` written. -/
def QrPost (a b c d : XReg) (s s' : State) : Prop :=
  (∀ l, l < 4 →
    dw s' a l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).1 ∧
    dw s' b l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.1 ∧
    dw s' c l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.2.1 ∧
    dw s' d l = (quarterRound (dw s a l) (dw s b l) (dw s c l) (dw s d l)).2.2.2) ∧
  (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
  s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- `vqr a b c d` computes the quarter round on each doubleword of `a, b, c,
d` (four distinct registers other than `xmm7`), writing only them and `xmm7`. -/
theorem vqr_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm7) (hb : b ≠ .xmm7) (hc : c ≠ .xmm7)
    (hd : d ≠ .xmm7) (s : State) : WP isa (.block (vqr a b c d)) s (QrPost a b c d s) := by
  unfold QrPost
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

/-! ## With SSSE3: rotations by `pshufb` -/

/-- The `pshufb` controls of `vqr3`, as 128-bit values. -/
def mask16 : BitVec 128 := 0x0d0c0f0e09080b0a0504070601000302#128
def mask8 : BitVec 128 := 0x0e0d0c0f0a09080b0605040702010003#128

theorem pshufb16_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a mask16 = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 2) % 4) := by
  simp only [XBinOp.eval, ofBytes, mask16]
  rfl

theorem pshufb8_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a mask8 = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 3) % 4) := by
  simp only [XBinOp.eval, ofBytes, mask8]
  rfl

/-- Byte `j` of each doubleword from byte `(j + t) % 4` is a rotation left by `32 - 8 t`. -/
theorem dword_rotBytes (x : BitVec 128) {i t : Nat} (hi : i < 4) (ht : 0 < t ∧ t < 4) :
    dword (ofBytes fun j => byte x (4 * (j / 4) + (j % 4 + t) % 4)) i = (dword x i).rotateLeft (32 - 8 * t) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword, decide_eq_true hm, Bool.true_and,
    show 32 * i + m = 8 * (4 * i + m / 8) + m % 8 by omega, getLsbD_ofBytes _ (by omega) (by omega),
    byte, BitVec.getLsbD_extractLsb', decide_eq_true (by omega), Bool.true_and, BitVec.getLsbD_rotateLeft]
  rw [show (32 - 8 * t) % 32 = 32 - 8 * t by omega]
  by_cases h : m < 32 - 8 * t
  · rw [ite_eq_left h, getLsbD_dword, decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · rw [ite_eq_right h, decide_eq_true hm, Bool.true_and, getLsbD_dword, decide_eq_true (by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem dword_pshufb16 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb x mask16) i = (dword x i).rotateLeft 16 := by
  rw [pshufb16_bytes, dword_rotBytes _ hi (t := 2) (by decide)]

theorem dword_pshufb8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb x mask8) i = (dword x i).rotateLeft 8 := by
  rw [pshufb8_bytes, dword_rotBytes _ hi (t := 3) (by decide)]

/-- `vqr3 a b c d` computes the quarter round on each doubleword of `a, b, c,
d` (four distinct registers other than `xmm7`), writing only them and `xmm7`,
with `edi` pointing at memory holding its controls. -/
theorem vqr3_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm7) (hb : b ≠ .xmm7) (hc : c ≠ .xmm7)
    (hd : d ≠ .xmm7) {p₁ p₂ : Addr} (s : State) (e₁ : s.ea (at_ .edi rot16Off) = p₁)
    (e₂ : s.ea (at_ .edi rot8Off) = p₂) (i₁ : InRegions (s.rd ++ s.wr) p₁ 16)
    (i₂ : InRegions (s.rd ++ s.wr) p₂ 16) (m₁ : s.mem.readW p₁ 128 = mask16)
    (m₂ : s.mem.readW p₂ 128 = mask8) : WP isa (.block (vqr3 a b c d)) s (QrPost a b c d s) := by
  unfold QrPost
  apply WP.of_runBlock
  simp only [vqr3, vrot, xb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, State.load128, ea_setXmm', e₁, e₂, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, i₁, i₂, ite_true, Option.map_some, m₁, m₂, RegUpd.gpr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hab, RegUpd.xmm_setXmm_of_ne _ _ hac,
      RegUpd.xmm_setXmm_of_ne _ _ had, RegUpd.xmm_setXmm_of_ne _ _ hbc, RegUpd.xmm_setXmm_of_ne _ _ hbd,
      RegUpd.xmm_setXmm_of_ne _ _ hcd, RegUpd.xmm_setXmm_of_ne _ _ hab.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hac.symm, RegUpd.xmm_setXmm_of_ne _ _ had.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hbc.symm, RegUpd.xmm_setXmm_of_ne _ _ hbd.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hcd.symm, RegUpd.xmm_setXmm_of_ne _ _ ha, RegUpd.xmm_setXmm_of_ne _ _ hb,
      RegUpd.xmm_setXmm_of_ne _ _ hc, RegUpd.xmm_setXmm_of_ne _ _ hd,
      RegUpd.xmm_setXmm_of_ne _ _ hb.symm, RegUpd.xmm_setXmm_of_ne _ _ hc.symm, RegUpd.xmm_setXmm_of_ne _ _ hd.symm,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_pshufb16 _ hl, dword_pshufb8 _ hl,
      pslld_12 _ hl, psrld_20 _ hl, pslld_7 _ hl, psrld_25 _ hl, rot12, rot7, quarterRound, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3, RegUpd.xmm_setXmm_of_ne _ _ h4]

end VG.Proof.ChaCha20.X86
