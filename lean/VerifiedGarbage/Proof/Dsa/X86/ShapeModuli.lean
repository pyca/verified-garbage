module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.SizeBounds
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
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Dsa.X86.DigestWidth
public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Dsa.X86.ShapeInspectP

/-! ### `Dsa.X86.Shape`, which only this module used -/

section

/-! ### `Dsa.X86.ShapeInspectQ`, which only this module used -/

section

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
  have hn : (len + 7) / 8 ≤ 48 := by omega_using [hmax]
  have hn0 : 0 < (len + 7) / 8 := by omega_using [h4]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsaved : 8256 ≤ size := hz
  unfold Shape.inspectQ
  refine WP.seq (WP.mono (loadWidths_ok hs hz rfl h4 hmax hw4 R.toReadableComponent
    ((R.smaller hn).slot (by decide)) hq (by decide) (by decide) (by decide) (by decide))
    fun u ⟨Mu, Q1, Q2, Q3, Ku, Ou⟩ => ?_)
  refine WP.block_append (WP.mono (shapeParity_ok (hs.of_keeps Ku (by decide)) (by omega_using [cb, hsaved]))
    fun v ⟨Pv, Kv, Ov⟩ => ?_)
  have Ksv := Ku.widen Kv
  have hsV := hs.of_keeps Ksv (by decide)
  have low := modulus_low hn0 Mu
  have parityQ : w32 u.mem base (slot ((len + 7) / 8) 0) % 2 = q % 2 := by omega_using [low]
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

end

end

/-! ### `Dsa.X86.DigestPrefix`, which only this module used -/

section

/-! ### `Dsa.X86.DigestClamp`, which only this module used -/

section

/-! # Branch-free clamping to the actual subgroup byte width -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Impl.Mont.X86 VG.Proof.Ecdsa.X86

theorem digestClamp_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 8256 ≤ size) :
    WP isa (.block Shape.digestClamp) s fun t =>
      (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat (s.gpr .edx).toNat ∧
      Keeps [.eax, .ebx, .edx] s t ∧ Outside base (Layout.field .digestPrefixLen) 4 s.mem t.mem := by
  unfold Shape.digestClamp
  refine wp_movS (readSrc_sc hs (d := Layout.field .digestLen) (by change 8240 ≤ size; omega_using [hz])) fun s1 u1 _ => ?_
  refine wp_cmp fun s2 u2 cf2 _ => ?_
  refine wp_sbbS rfl cf2 fun s3 u3 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s4 u4 => ?_
  refine wp_logicS (.inl rfl) rfl fun s5 u5 => ?_
  refine wp_logicS (.inr rfl) rfl fun s6 u6 => ?_
  have K : Keeps [.eax, .ebx, .edx] s s6 :=
    (((((u1.keeps.mono (by decide)).widen (u2.keeps [])).widen u3.keeps).widen u4.keeps).widen u5.keeps).widen u6.keeps
  have hs6 := hs.of_keeps K (by decide)
  refine wp_storeS (hs6.ea (d := Layout.field .digestPrefixLen) (by change 8240 < size; omega_using [hz]))
    (hs6.write (d := Layout.field .digestPrefixLen) (n := 4) (by change 8244 ≤ size; omega_using [hz])) fun t mt =>
    WP.block_nil ⟨?_, K.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, u6.gpr, u5.other .edx (by decide),
      u4.other .edx (by decide), u3.other .edx (by decide), u2.gpr, u1.other .edx (by decide),
      u5.gpr, u4.gpr, u4.other .ebx (by decide), u3.gpr, sbb_mask,
      u3.other .eax (by decide), u3.other .edx (by decide), u2.gpr,
      u1.gpr, u1.other .edx (by decide)]
    simp only [reduceCtorEq, ite_false, ite_true, mask32, decide_eq_true_eq]
    have E := select_val (s.gpr .edx) (shapeWord s base (Layout.field .digestLen))
      (decide ((shapeWord s base (Layout.field .digestLen)).toNat < (s.gpr .edx).toNat))
    simp only [decide_eq_true_eq] at E
    rw [E]
    split <;> simp only [Nat.min_def] <;> split <;> omega_arith
  · rw [mt.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW32_outside _ _ _ (by change 8244 ≤ 2 ^ 64; decide)

end VG.Proof.Dsa.X86

end

end


/-! # The DSA digest-prefix length from validated subgroup masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem digestPrefix_raw {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 8256 ≤ size) :
    WP isa Shape.digestPrefix s fun t =>
      (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat
          ((shapeWord s base 48 &&& 28) ||| (shapeWord s base 44 &&& 20) ||| (shapeWord s base 52 &&& 32)).toNat ∧
      Keeps [.eax, .ebx, .edx] s t ∧ Outside base (Layout.field .digestPrefixLen) 4 s.mem t.mem := by
  unfold Shape.digestPrefix
  refine WP.block_append (WP.mono (digestWidth_ok hs (by omega_using [hz])) fun u ⟨Vu, Ku, Mu⟩ => ?_)
  refine WP.mono (digestClamp_ok (hs.of_keeps Ku (by decide)) hz) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, (Ku.mono (by decide)).trans Kt, Mu ▸ Ot⟩
  rw [Vt, Vu]
  simp only [shapeWord, Mu]

end VG.Proof.Dsa.X86

end

end


/-! # Complete public domain-shape check, including its rejection flag -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shape_ok {s : State} {base : Addr} {size pLen qLen p q : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hp4 : 4 ≤ pLen) (hpmax : pLen ≤ 384) (hq4 : 4 ≤ qLen) (hqmax : qLen ≤ 384)
    (hpw : pLen % 4 = 0) (hqw : qLen % 4 = 0)
    (Rp : OperandReady s base 48 (.input .p) pLen) (Rq : OperandReady s base 48 (.input .q) qLen)
    (hp : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) pLen) = p)
    (hq : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen) = q) :
    WP isa (Shape.check pLen qLen) s fun t =>
      shapeWord t base (Layout.field .mask) = mask32 (shapeValid p q) ∧
      t.zf = some (!decide (shapeValid p q)) ∧
      (shapeValid p q → (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat (Spec.Dsa.bitLength q / 8)) ∧
      Keeps shapeClob s t ∧
      Outs base [(0, contextBytes 48), (Layout.field .digestPrefixLen, 8)] s.mem t.mem := by
  have hsaved : 8256 ≤ size := hz
  unfold Shape.check Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (inspectP_ok hs hz hp4 hpmax hpw Rp hp) fun u ⟨P1, P2, P3, Po, Ku, Ou⟩ => ?_)
  have Rqu := Rq.keep Ku (by decide) Ou (by decide)
  have hqu : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem ((pointerValue base u (.input .q)).setWidth 64) qLen) = q := by
    rw [Rq.bytes Ku (by decide) Ou (by decide), hq]
  refine WP.seq (WP.mono (inspectQ_ok (hs.of_keeps Ku (by decide)) hz hq4 hqmax hqw Rqu hqu P1 P2 P3 Po)
    fun v ⟨Vv, Q1, Q2, Q3, Kv, Ov⟩ => ?_)
  have Opre : Outs base [(0, contextBytes 48), (Layout.field .mask, 4)] s.mem v.mem :=
    (Outs.of_outside Ou (by simp)).trans Ov
  have Dv : shapeWord v base (Layout.field .digestLen) = shapeWord s base (Layout.field .digestLen) := by
    apply BitVec.eq_of_toNat_eq
    have H : val32 v.mem base (Layout.field .digestLen) 1 = val32 s.mem base (Layout.field .digestLen) 1 := by
      apply Opre.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
      · decide
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using H
  have Ksv := Ku.trans Kv
  refine WP.seq (WP.mono (digestPrefix_raw (hs.of_keeps Ksv (by decide)) hsaved)
    fun w ⟨Dw, Kw, Ow⟩ => ?_)
  rw [Dv, Q1, Q2, Q3] at Dw
  have Vw : shapeWord w base (Layout.field .mask) = mask32 (shapeValid p q) := by
    rw [outside_shapeWord Ow (by decide) (.inr (by decide))]
    exact Vv
  have DP : shapeValid p q → (shapeWord w base (Layout.field .digestPrefixLen)).toNat =
      min (shapeWord s base (Layout.field .digestLen)).toNat (Spec.Dsa.bitLength q / 8) := by
    intro hv
    have widths : Spec.Dsa.bitLength q = 160 ∨ Spec.Dsa.bitLength q = 224 ∨ Spec.Dsa.bitLength q = 256 := by
      have H := hv.1
      unfold Spec.Dsa.supportedSizes at H
      omega_using [H]
    rw [Dw, digestWidth_value widths]
  have Ksw := Ksv.widen Kw
  refine WP.seq (wp_movS (readSrc_sc (hs.of_keeps Ksw (by decide))
    (d := Layout.field .mask) (by change 8248 ≤ size; omega_using [hsaved])) fun x ux _ => ?_)
  refine wp_cmpS rfl fun y uy Zy => WP.block_nil ?_
  refine WP.block_nil ⟨?_, ?_, ?_, (Ksw.widen ux.keeps).widen (uy.keeps []), ?_⟩
  · simpa only [shapeWord, uy.mem, ux.mem] using Vw
  · rw [Zy, ux.gpr]
    change some (shapeWord w base (Layout.field .mask) - 0 == 0) = _
    rw [Vw]
    by_cases hv : shapeValid p q <;> simp only [mask32, hv, ite_true, ite_false, decide_true, decide_false] <;> rfl
  · intro hv
    simpa only [shapeWord, uy.mem, ux.mem] using DP hv
  · have Opre' : Outs base [(0, contextBytes 48), (Layout.field .digestPrefixLen, 8)] s.mem v.mem := by
      intro a ha
      apply Opre a
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ha _ (by simp)
      · have H := ha (Layout.field .digestPrefixLen, 8) (by simp)
        change ofs base a < 8240 ∨ 8248 ≤ ofs base a at H
        change ofs base a < 8244 ∨ 8248 ≤ ofs base a
        omega_using [H]
    rw [uy.mem, ux.mem]
    exact Opre'.trans (Outs.of_outside (Ow.mono (n' := 8) (Nat.le_refl _) (by omega_using [])) (by simp))

end VG.Proof.Dsa.X86

end

end

/-! # Successful public shape validation establishes the arithmetic invariants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shapeModuli_ok {s : State} {base : Addr} {size pLen qLen p q : Nat}
    (hs : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen) (Q : CallerBuffer s base size (.input .q) qLen)
    (hp : operandValue s base (.input .p) pLen = p) (hq : operandValue s base (.input .q) qLen = q) :
    WP isa (Shape.check pLen qLen) s fun t =>
      flagW base (Layout.field .mask) t = mask32 (shapeValid p q) ∧
      t.zf = some (!decide (shapeValid p q)) ∧
      (shapeValid p q → Moduli base size pLen qLen p q t ∧
        (pointerValue base t (.input .digestPrefixLen)).toNat =
          min (pointerValue base s (.input .digestLen)).toNat (Spec.Dsa.bitLength q / 8)) ∧
      Keeps shapeClob s t ∧ Outs base shapeRanges s.mem t.mem := by
  have L : 128 ≤ pLen ∧ pLen ≤ 384 ∧ 20 ≤ qLen ∧ qLen ≤ 32 := by
    unfold Spec.Dsa.lengthsValid at widths
    omega_using [widths]
  have sz : 15712 ≤ size := extent
  have ctx : contextBytes 48 ≤ size := by change 7048 ≤ size; omega_using [sz]
  have A : pLen % 4 = 0 ∧ qLen % 4 = 0 := by
    unfold Spec.Dsa.lengthsValid at widths
    omega_using [widths]
  refine WP.mono (shape_ok hs (by change 8256 ≤ size; omega_using [sz])
    (by omega_using [L]) (by omega_using [L]) (by omega_using [L]) (by omega_using [L]) A.1 A.2 (P.ready ctx) (Q.ready ctx) hp hq)
    fun t ⟨F, Z, D, K, O⟩ => ?_
  refine ⟨F, Z, ?_, K, O⟩
  intro valid
  have B := VG.Proof.Dsa.supported_bounds valid.1
  refine ⟨⟨hs.of_keeps K (by decide), extent, widths,
    P.keep_shape O K (by decide) (by decide), Q.keep_shape O K (by decide) (by decide),
    (P.value_keep_shape O K (by decide) (by decide) (by omega_using [sz])).trans hp,
    (Q.value_keep_shape O K (by decide) (by decide) (by omega_using [sz])).trans hq,
    B.1, B.2.1, valid.2.2, valid.2.1⟩, D valid⟩

end VG.Proof.Dsa.X86
