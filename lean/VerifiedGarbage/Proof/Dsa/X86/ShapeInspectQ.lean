module

public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadWidths
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.Dsa.X86.Bytes
/-! # Completing public domain-size and oddness validation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeParity.lean`, which only this module imported.
section

/-! # Low-word parity checks before Montgomery initialization -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem word_low_bit (x : BitVec 32) : x &&& 1 = BitVec.ofNat 32 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 32 by omega)]

theorem word_odd_mask (x : BitVec 32) : 0 - (x &&& 1) = mask32 (x.toNat % 2 = 1) := by
  rw [word_low_bit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem modulus_odd_mask (p q : BitVec 32) :
    0 - (p &&& q &&& 1) = mask32 (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1) := by
  rw [word_odd_mask, BitVec.toNat_and]
  simp only [mask32, Nat.and_mod_two_eq_one]

theorem shapeParity_ok {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hz : contextBytes n ≤ size) :
    WP isa (.block (Shape.parity n)) s fun t =>
      shapeWord t base 56 = mask32 (w32 s.mem base (slot n 0) % 2 = 1 ∧ (shapeWord s base 56).toNat % 2 = 1) ∧
      Keeps [.eax, .edx] s t ∧ Outside base 56 4 s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b0
  unfold Shape.parity
  refine wp_movS (readSrc_sc hs (d := slot n 0) (by omega_arith)) fun s1 u1 _ => ?_
  have hs1 := hs.of_keeps u1.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs1 (d := 56) (by omega_arith)) fun s2 u2 => ?_
  refine wp_logicS (.inl rfl) rfl fun s3 u3 => ?_
  refine wp_movS rfl fun s4 u4 _ => ?_
  refine wp_subS rfl fun s5 u5 _ => ?_
  have K : Keeps [.eax, .edx] s s5 := ((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps
  have hs5 := hs.of_keeps K (by decide)
  refine wp_storeS (hs5.ea (d := 56) (by omega_arith)) (hs5.write (d := 56) (n := 4) (by omega_arith)) fun t mt =>
    WP.block_nil ⟨?_, K.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, u5.gpr, u4.gpr,
      u4.other .edx (by decide), u3.gpr, u2.gpr, u1.gpr, u1.mem]
    simp only [ite_true]
    exact modulus_odd_mask _ _
  · rw [mt.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ShapeMasks.lean`, which only this module imported.
section

/-! # Combining supported public-width masks -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Proof.Ecdsa.X86

theorem mask_or (p q : Prop) [Decidable p] [Decidable q] : mask32 p ||| mask32 q = mask32 (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask32, hp, hq, ite_true, ite_false, or_self, or_false, false_or] <;> decide

theorem supported_masks (p q : Nat) (odd : Prop) [Decidable odd] :
    ((mask32 (p = 1024) &&& mask32 (q = 160)) |||
      ((mask32 (q = 224) ||| mask32 (q = 160) ||| mask32 (q = 256)) &&& mask32 (p = 2048)) |||
      (mask32 (p = 3072) &&& mask32 (q = 256))) &&& mask32 odd =
      mask32 (Spec.Dsa.supportedSizes p q ∧ odd) := by
  simp only [mask32_and, mask_or]
  simp only [Spec.Dsa.supportedSizes, and_comm, or_assoc, or_comm]

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem inspectQ_ok {s : State} {base : Addr} {size len p q : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) (R : OperandReady s base 48 (.input .q) len)
    (hq : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = q)
    (P1 : shapeWord s base 32 = mask32 (Spec.Dsa.bitLength p = 1024))
    (P2 : shapeWord s base 36 = mask32 (Spec.Dsa.bitLength p = 2048))
    (P3 : shapeWord s base 40 = mask32 (Spec.Dsa.bitLength p = 3072))
    (Po : (shapeWord s base 56).toNat % 2 = p % 2) :
    WP isa (Shape.inspectQ len) s fun t =>
      shapeWord t base (Layout.field .mask) = mask32
        (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength p) (Spec.Dsa.bitLength q) ∧ (q % 2 = 1 ∧ p % 2 = 1)) ∧
      shapeWord t base 44 = mask32 (Spec.Dsa.bitLength q = 160) ∧
      shapeWord t base 48 = mask32 (Spec.Dsa.bitLength q = 224) ∧
      shapeWord t base 52 = mask32 (Spec.Dsa.bitLength q = 256) ∧
      Keeps shapeClob s t ∧
      Outs base [(0, contextBytes 48), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have hn0 : 0 < (len + 7) / 8 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsaved : 8256 ≤ size := hz
  unfold Shape.inspectQ
  refine WP.seq (WP.mono (loadWidths_ok hs hz rfl h4 hmax hw4 R.toReadableComponent
    ((R.smaller hn).slot (by decide)) hq (by decide) (by decide) (by decide) (by decide))
    fun u ⟨Mu, Q1, Q2, Q3, Ku, Ou⟩ => ?_)
  refine WP.block_append (WP.mono (shapeParity_ok (hs.of_keeps Ku (by decide)) (by omega))
    fun v ⟨Pv, Kv, Ov⟩ => ?_)
  have Ksv := Ku.widen Kv
  have hsV := hs.of_keeps Ksv (by decide)
  have low := modulus_low hn0 Mu
  have parityQ : w32 u.mem base (slot ((len + 7) / 8) 0) % 2 = q % 2 := by omega
  rw [parityQ, loadWidths_header Ou (by decide) (.inr (by decide)), Po] at Pv
  have H1 : shapeWord v base 32 = mask32 (Spec.Dsa.bitLength p = 1024) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P1]
  have H2 : shapeWord v base 36 = mask32 (Spec.Dsa.bitLength p = 2048) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P2]
  have H3 : shapeWord v base 40 = mask32 (Spec.Dsa.bitLength p = 3072) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P3]
  have J1 : shapeWord v base 44 = mask32 (Spec.Dsa.bitLength q = 160) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q1]
  have J2 : shapeWord v base 48 = mask32 (Spec.Dsa.bitLength q = 224) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q2]
  have J3 : shapeWord v base 52 = mask32 (Spec.Dsa.bitLength q = 256) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q3]
  refine WP.mono (shapeCombine_ok hsV hsaved) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, Ksv.widen Kt, ?_⟩
  · rw [Vt, H1, H2, H3, J1, J2, J3, Pv]
    exact supported_masks _ _ _
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J1]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J2]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J3]
  · have Opre := (loadWidths_whole Ou hn (by decide)).trans
      (Ov.mono (o' := 0) (n' := contextBytes 48) (by decide) (by decide))
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
