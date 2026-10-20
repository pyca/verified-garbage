module
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: an iteration of `dd4Body`

Bytes `16 k … 16 k + 15` of the input to coefficients `32 k … 32 k + 31` of the output.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

/-- The constants of `dd4Body` besides those of `decV`. -/
abbrev K4 (s : State) : Prop := (∀ j < 16, (vbyte (s.v .v18) j).toNat = 15) ∧ s.v .v19 = 0

/-- Coefficient `32 k + m` of the output for `d = 4`. -/
theorem G4 (s₀ : State) {k m : Nat} (hk : k < 8) (hm : m < 32) :
    DD.G width4 s₀ (32 * k + m) =
      BitVec.ofNat 32 (df 4 (nib (fun j => byte width4 s₀ (16 * k + j)) m)) := by
  rw [show 32 * k + m = width4.c * (16 * k + m / 2) + m % 2 by simp [width4]; omega,
    G_eq width4_ok s₀ (by simp [width4]; omega) (by simp [width4]; omega), show width4.nb = 1 from rfl, num1 rfl]
  simp only [show width4.d = 4 from rfl, df, nib, show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]

theorem step4 {s₀ : State} (hp : Pre width4 s₀) {k : Nat} (hk : k < 8) {s : State}
    (h : DInv width4 16 K4 s₀ k s) :
    WP isa (.block dd4Body) s fun t =>
      DInv width4 16 K4 s₀ (k + 1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k + 1 ≠ 8) := by
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = bP s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [ptr_zero, h.x0]; rfl
  unfold dd4Body
  simp only [List.cons_append]
  refine wp_ldrq (by decide) e0 (h.in16 width4_ok hp (by simp [width4]; omega)) fun s1 h1 => ?_
  let B : Nat → Nat := fun j => byte width4 s₀ (16 * k + j)
  rw [WP.block_append_iff]
  refine WP.mono (dd4Math_ok (h.cs.chg h1.chg) (by rw [h1.get .v18 (by decide)]; exact h.K.1)
    (by rw [h1.get .v19 (by decide)]; exact h.K.2) (B := B)
    (fun j hj => by rw [h1.v]; exact vbyte_input width4_ok hp h.frame (by simp [width4]; omega) hj)
    (fun j _ => byte_lt _)) fun s2 ⟨c2, r0, r1, r2, r3, r6, r7, r20, r21⟩ => ?_
  have g2 : s2.gpr = s.gpr := by rw [c2.gpr, h1.gpr]
  have hw2 : ∀ i, i + 4 ≤ 256 → InRegions s2.wr (coeffAddr (fP s₀) i) 16 := fun i hi => by
    rw [c2.wr, h1.wr]; exact h.out16 hp hi
  have a3 : ∀ i, s2.gpr .x3 + BitVec.ofNat 64 (16 * i) = coeffAddr (fP s₀) (32 * k + 4 * i) := fun i => by
    rw [g2, h.x3, show width4.c * 16 * k = 32 * k from by simp [width4], show 16 * i = 4 * (4 * i) by omega,
      coeffAddr_off]
  have out2 : CoeffsUpTo s2.mem (fP s₀) (32 * k) (DD.G width4 s₀) (old s₀) := by
    rw [c2.mem, h1.mem, show 32 * k = width4.c * 16 * k by simp [width4]]; exact h.out
  have f2 : Frame [polyRegion (fP s₀)] s₀.mem s2.mem := by rw [c2.mem, h1.mem]; exact h.frame
  have v (r : VReg) (o : Nat) (hr : Lanes (s2.v r) fun e => df 4 (nib B (o + e))) (ho : o + 4 ≤ 32) :
      ∀ e < 4, vword (s2.v r) e = DD.G width4 s₀ (32 * k + o + e) :=
    vword_G hr fun e he => by rw [Nat.add_assoc, G4 s₀ hk (by omega)]
  refine wp_strq2 (o := 0) hw2 (a3 0) (by decide) (by omega) out2 f2 (v _ 0 (r0.congr fun _ _ => by
    rw [Nat.zero_add]) (by decide)) (v _ 4 r1 (by decide)) fun s3 t3 o3 f3 => ?_
  refine wp_strq2 (o := 32) (by rw [t3.wr]; exact hw2) (by rw [t3.gpr]; exact a3 2) (by decide) (by omega) o3 f3
    (by rw [t3.v]; exact v _ 8 r2 (by decide)) (by rw [t3.v]; exact v _ 12 r3 (by decide))
    fun s4 t4 o4 f4 => ?_
  refine wp_strq2 (o := 64) (by rw [t4.wr, t3.wr]; exact hw2) (by rw [t4.gpr, t3.gpr]; exact a3 4) (by decide)
    (by omega) o4 f4 (by rw [t4.v, t3.v]; exact v _ 16 r6 (by decide))
    (by rw [t4.v, t3.v]; exact v _ 20 r7 (by decide)) fun s5 t5 o5 f5 => ?_
  refine wp_strq2 (o := 96) (by rw [t5.wr, t4.wr, t3.wr]; exact hw2) (by rw [t5.gpr, t4.gpr, t3.gpr]; exact a3 6)
    (by decide) (by omega) o5 f5 (by rw [t5.v, t4.v, t3.v]; exact v _ 24 r20 (by decide))
    (by rw [t5.v, t4.v, t3.v]; exact v _ 28 r21 (by decide)) fun s6 t6 o6 f6 => ?_
  have t := ((t3.trans t4).trans t5).trans t6
  have k4 : k < 256 / (width4.c * 16) := by simp [width4]; omega
  refine WP.mono (dtail_ok (w := width4) (Ng := 16) (s₀ := s₀) k4 (by rw [t.gpr, g2, h.x0])
    (by rw [t.gpr, g2, h.x3]) (by rw [t.gpr, g2, h.x11]) (by decide) (by decide))
    fun u ⟨o, uv, u0, u3, u11, uc⟩ => ?_
  have hv : u.v = s2.v := by rw [uv, t.v]
  refine ⟨⟨by rw [o.rd, t.rd, c2.rd, h1.rd, h.rd], by rw [o.wr, t.wr, c2.wr, h1.wr, h.wr],
    by rw [o.sp, t.sp, c2.sp, h1.sp, h.sp], u0, u3, u11, ?_, ?_, ?_, ?_⟩,
    by rw [show 256 / (width4.c * 16) = 8 from rfl] at uc; exact uc⟩
  · have := (h.cs.chg h1.chg).chg c2
    exact ⟨by rw [hv]; exact this.q, by rw [hv]; exact this.h⟩
  · exact ⟨fun j hj => by rw [hv, c2.get .v18 (by decide), h1.get .v18 (by decide)]; exact h.K.1 j hj,
      by rw [hv, c2.get .v19 (by decide), h1.get .v19 (by decide)]; exact h.K.2⟩
  · rw [o.mem, show width4.c * 16 * (k + 1) = 32 * k + 8 + 8 + 8 + 8 by simp [width4]; omega]; exact o6
  · rw [o.mem]; exact f6

end VG.Proof.MlKem.AArch64.DD
