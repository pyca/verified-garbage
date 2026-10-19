module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane

/-!
# ML-KEM on AArch64: `ce4Math`

32 compressed coefficients of four bits, paired into 16 bytes.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem

theorem cf_lt (d x : Nat) : cf d x < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem ce4Math_ok {s : State} (hc : CConsts 4 s) {X : Nat → Nat} (hX : ∀ i < 32, X i < 3329)
    (l0 : Lanes (s.v .v0) fun i => X i) (l1 : Lanes (s.v .v1) fun i => X (4 + i))
    (l2 : Lanes (s.v .v2) fun i => X (8 + i)) (l3 : Lanes (s.v .v3) fun i => X (12 + i))
    (l4 : Lanes (s.v .v4) fun i => X (16 + i)) (l5 : Lanes (s.v .v5) fun i => X (20 + i))
    (l6 : Lanes (s.v .v6) fun i => X (24 + i)) (l7 : Lanes (s.v .v7) fun i => X (28 + i)) :
    WP isa (.block ce4Math) s fun t => VChg [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v19] s t ∧
      ∀ j < 16, (vbyte (t.v .v0) j).toNat = cf 4 (X (2 * j)) + cf 4 (X (2 * j + 1)) * 2 ^ 4 := by
  have hd : (4 : Nat) ∈ compressWidths := by decide
  unfold ce4Math cmp8
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd hc (fun i hi => hX i (by omega)) l0 l1 l2 l3) fun s1 ⟨c1, m0, m1, m2, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmp4_ok hd (hc.chg c1) (X := fun i => X (16 + i)) (fun i hi => hX _ (by omega))
    (Lanes.chg c1 (by decide) l4) ((Lanes.chg c1 (by decide) l5).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l6).congr fun i _ => by congr 1; omega)
    ((Lanes.chg c1 (by decide) l7).congr fun i _ => by congr 1; omega))
    fun s2 ⟨c2, m4, m5, m6, m7⟩ => ?_
  -- the compressed coefficients
  let Y : Nat → Nat := fun i => cf 4 (X i)
  have hY : ∀ i, Y i < 2 ^ 4 := fun i => cf_lt 4 _
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := Y) (by decide) (by decide) (by decide) (by decide)
    (Lanes.chg c2 (by decide) m0) (Lanes.chg c2 (by decide) m1) fun i _ => hY i)
    fun s3 ⟨c3, p0⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := fun i => Y (8 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m2))
    ((Lanes.chg c3 (by decide) (Lanes.chg c2 (by decide) m3)).congr fun i _ => by
      show Y (12 + i) = Y (8 + (4 + i)); rw [← Nat.add_assoc])
    fun i _ => hY _) fun s4 ⟨c4, p1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := fun i => Y (16 + i)) (by decide) (by decide) (by decide)
    (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m4))
    ((Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m5)).congr fun i _ => by
      show Y (16 + (4 + i)) = Y (16 + (4 + i)); rfl)
    fun i _ => hY _) fun s5 ⟨c5, p2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairV_ok (b := 4) (f := fun i => Y (24 + i)) (by decide) (by decide) (by decide)
    (by decide) ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide)
      m6))).congr fun i _ => by show Y (16 + (8 + i)) = Y (24 + i); rw [← Nat.add_assoc])
    ((Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) (Lanes.chg c3 (by decide) m7))).congr
      fun i _ => by show Y (16 + (12 + i)) = Y (24 + (4 + i)); congr 1; omega)
    fun i _ => hY _) fun s6 ⟨c6, p3⟩ => ?_
  refine wp_vop rfl fun s7 h7 => wp_vop rfl fun s8 h8 => wp_vop rfl fun t h9 => wp_nil ⟨?_, ?_⟩
  · exact (((((((c1.trans c2).trans c3).trans c4).trans c5).trans c6).trans h7.chg).trans
      (h8.chg.trans h9.chg)).mono
  intro j hj
  -- the four registers of bytes
  have q0 := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide) (Lanes.chg c4 (by decide) p0))
  have q1 := Lanes.chg c6 (by decide) (Lanes.chg c5 (by decide) p1)
  have q2 := Lanes.chg c6 (by decide) p2
  rw [h9.v, h8.get .v0 (by decide), h8.v, h7.v, h7.get .v2 (by decide), h7.get .v3 (by decide)]
  rw [narrow4 (f := fun j => Y (2 * j) + Y (2 * j + 1) * 2 ^ 4) q0
    (q1.congr fun e _ => by rw [show 8 + 2 * e = 2 * (4 + e) by omega, show 8 + (2 * e + 1) = 2 * (4 + e) + 1 by omega])
    (q2.congr fun e _ => by rw [show 16 + 2 * e = 2 * (8 + e) by omega, show 16 + (2 * e + 1) = 2 * (8 + e) + 1 by omega])
    (p3.congr fun e _ => by rw [show 24 + 2 * e = 2 * (12 + e) by omega, show 24 + (2 * e + 1) = 2 * (12 + e) + 1 by omega])
    (fun j _ => by have := hY (2 * j); have := hY (2 * j + 1); omega) hj]

end VG.Proof.MlKem.AArch64.CodecV
