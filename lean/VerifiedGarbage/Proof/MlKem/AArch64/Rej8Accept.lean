module
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Machine-code acceptance bits for eight ML-KEM candidates -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- The SIMD acceptance block preserves memory, scalar registers and every
other vector register; each of its lanes contains exactly its accepted
mask/count weight, or zero. -/
theorem accept_ok (s : State)
    (hq : ∀ e < 8, vhalf (s.v .v19) e = 3329)
    (hw : ∀ e < 8, vhalf (s.v .v20) e = BitVec.ofNat 16 (256 + 2^e))
    (hz : ∀ e < 8, (vhalf (s.v .v0) e).toNat < 4096) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.accept) s fun t =>
      VChg [.v1] s t ∧ ∀ e < 8, vhalf (t.v .v1) e =
        if (vhalf (s.v .v0) e).toNat < 3329 then BitVec.ofNat 16 (256+2^e) else 0 := by
  refine wp_vop (d := .v1) rfl fun a ha =>
    wp_vop (d := .v1) rfl fun b hb =>
    wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨((ha.chg.trans hb.chg).trans ht.chg).mono (by decide), ?_⟩
  intro e he
  rw [ht.v, vhalf_ofVHalves _ he]
  simp only [VMulHOp.lane]
  rw [hb.v, vhalf_map2 _ _ _ he, ha.v, vhalf_map2 _ _ _ he,
    hq e he, hb.get .v20, ha.get .v20, hw e he]
  change ((vhalf (s.v .v0) e - 3329) >>> 15) * BitVec.ofNat 16 (256+2^e) = _
  rw [candidate_bit _ (hz e he)]
  split <;> simp

end VG.Proof.MlKem.AArch64.Rej8
