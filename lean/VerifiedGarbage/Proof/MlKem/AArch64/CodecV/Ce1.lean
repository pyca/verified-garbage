module
public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks

import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# ML-KEM on AArch64: `ce1Math`

32 compressed coefficients of one bit, paired three times into four bytes.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

/-- The bits `Y (8 j) … Y (8 j + 7)` as a byte. -/
abbrev byte8 (Y : Nat → Nat) (j : Nat) : Nat :=
  Y (8 * j) + Y (8 * j + 1) * 2 + Y (8 * j + 2) * 4 + Y (8 * j + 3) * 8 + Y (8 * j + 4) * 16 +
    Y (8 * j + 5) * 32 + Y (8 * j + 6) * 64 + Y (8 * j + 7) * 128

theorem ce1Math_ok {s : State} (hc : CConsts width1 s) {X : Nat → Nat} (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce1Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      ∀ j < 4, (vbyte (t.v .v0) j).toNat = byte8 (fun i => cf width1 (X i)) j := by
  have hd : WOk width1 := width1_ok
  unfold ce1Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  let Y : Nat → Nat := fun i => cf width1 (X i)
  have hY : ∀ i, Y i < 2 ^ 1 := fun i => cf_lt width1 _
  -- level 1: pairs of bits
  let Z : Nat → Nat := fun i => Y (2 * i) + Y (2 * i + 1) * 2 ^ 1
  have hZ : ∀ i, Z i < 2 ^ 2 := fun i => by have := hY (2 * i); have := hY (2 * i + 1); simp only [Z]; omega
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5))
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 1) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); congr 1; omega)
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  -- the registers of pairs: `v0`–`v3` hold `Z 0 …`, `Z 4 …`, `Z 8 …`, `Z 12 …`
  have q0 : Lanes (s6.v .v0) fun i => Z i := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    (Lanes.chg c4 (by decide) p0))
  have q1 : Lanes (s6.v .v1) fun i => Z (4 + i) := (Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide)
    p1)).congr fun i _ => by
    show Y (8 + 2 * i) + Y (8 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (4 + i)) + Y (2 * (4 + i) + 1) * 2 ^ 1
    rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega]
  have q2 : Lanes (s6.v .v2) fun i => Z (8 + i) := (Lanes.chg c6 (by decide) p2).congr fun i _ => by
    show Y (16 + 2 * i) + Y (16 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (8 + i)) + Y (2 * (8 + i) + 1) * 2 ^ 1
    rw [show 16 + 2 * i = 2 * (8 + i) by omega, show 16 + (2 * i + 1) = 2 * (8 + i) + 1 by omega]
  have q3 : Lanes (s6.v .v3) fun i => Z (12 + i) := p3.congr fun i _ => by
    show Y (24 + 2 * i) + Y (24 + (2 * i + 1)) * 2 ^ 1 = Y (2 * (12 + i)) + Y (2 * (12 + i) + 1) * 2 ^ 1
    rw [show 24 + 2 * i = 2 * (12 + i) by omega, show 24 + (2 * i + 1) = 2 * (12 + i) + 1 by omega]
  -- level 2: nibbles
  let W : Nat → Nat := fun i => Z (2 * i) + Z (2 * i + 1) * 2 ^ 2
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 2) (f := Z) (by decide) (by decide) (by decide) (by decide)
    q0 q1 fun i _ => hZ i) fun s7 ⟨c7, r0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 2) (f := fun i => Z (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c7 (by decide) q2)
    ((Lanes.chg c7 (by decide) q3).congr fun i _ => by show Z (12 + i) = Z (8 + (4 + i)); congr 1; omega)
    fun i _ => hZ _) fun s8 ⟨c8, r1⟩ => ?_
  -- level 3: bytes
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := W) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c8 (by decide) r0)
    (r1.congr fun i _ => by
      show Z (8 + 2 * i) + Z (8 + (2 * i + 1)) * 2 ^ 2 = Z (2 * (4 + i)) + Z (2 * (4 + i) + 1) * 2 ^ 2
      rw [show 8 + 2 * i = 2 * (4 + i) by omega, show 8 + (2 * i + 1) = 2 * (4 + i) + 1 by omega])
    fun i _ => by have := hZ (2 * i); have := hZ (2 * i + 1); simp only [W]; omega)
    fun s9 ⟨c9, u0⟩ => ?_
  refine wp_vop rfl fun s10 h10 => wp_vop rfl fun t h11 => wp_nil ⟨?_, ?_⟩
  · exact ((((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans
      (c9.trans (h10.chg.trans h11.chg))).mono
  intro j hj
  rw [h11.v, h10.v]
  rw [narrow1 u0 (fun j _ => by
    have := hZ (2 * (2 * j)); have := hZ (2 * (2 * j) + 1); have := hZ (2 * (2 * j + 1))
    have := hZ (2 * (2 * j + 1) + 1); simp only [W]; omega) hj]
  simp only [W, Z, Y, byte8]
  rw [show 2 * (2 * (2 * j)) + 1 = 8 * j + 1 by omega, show 2 * (2 * (2 * j)) = 8 * j by omega,
    show 2 * (2 * (2 * j) + 1) + 1 = 8 * j + 3 by omega, show 2 * (2 * (2 * j) + 1) = 8 * j + 2 by omega,
    show 2 * (2 * (2 * j + 1)) + 1 = 8 * j + 5 by omega, show 2 * (2 * (2 * j + 1)) = 8 * j + 4 by omega,
    show 2 * (2 * (2 * j + 1) + 1) + 1 = 8 * j + 7 by omega,
    show 2 * (2 * (2 * j + 1) + 1) = 8 * j + 6 by omega]
  omega

end VG.Proof.MlKem.AArch64.CodecV
