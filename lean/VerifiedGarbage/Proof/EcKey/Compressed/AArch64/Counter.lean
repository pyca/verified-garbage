module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! # Retain the public outer counter across the inner squaring loop -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

 theorem saveCounter_ok (s : State) :
    WP isa (.block [.vop (.ins .d2 .v27 0 .x19)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      laneOf t .v27 0 = s.gpr .x19 := by
  exact WP.mono (insOf_ok [(.x19, .v27, 0)] s (by decide) (by decide))
    fun _ ⟨g, m, r, w, sp, L, _⟩ => ⟨g, m, r, w, sp, L (.x19, .v27, 0) (by simp)⟩

 theorem descentCounter_ok {s : State} {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hcounter : laneOf s .v27 0 = BitVec.ofNat 64 j) :
    WP isa (.block Impl.EcKey.Compressed.AArch64.descentCounter) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j - 1) ∧ Keeps [.x19] s t := by
  change WP isa (.block (umovOf [(.x19, .v27, 0)] ++ [decCounter])) s _
  rw [WP.block_append_iff]
  refine WP.mono (umovOf_ok [(.x19, .v27, 0)] s (by decide) (by decide))
    fun t ⟨m, r, w, sp, L, G⟩ => ?_
  have e : t.gpr .x19 = BitVec.ofNat 64 j := (L (.x19, .v27, 0) (by simp)).trans hcounter
  refine WP.mono (decCounter_ok t hj hj' e) fun u ⟨v, K⟩ => ?_
  refine ⟨v, ?_⟩
  have K₁ : Keeps [.x19] s t := ⟨G, m, r, w, sp⟩
  exact K₁.trans K

end VG.Proof.EcKey.Compressed.AArch64
