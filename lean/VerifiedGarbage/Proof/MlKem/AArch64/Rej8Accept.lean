module
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Machine-code acceptance bits for eight ML-KEM candidates -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

/-- One lane of `cmhi` (`3329 > x`) and the weight: the weight exactly when `x < 3329`. -/
theorem cmp_lane (x w : BitVec 16) :
    (if VCmpOp.hi.test (3329 : BitVec 16) x = true then BitVec.allOnes 16 else 0) &&& w =
      if x.toNat < 3329 then w else 0 := by
  by_cases h : x.toNat < 3329
  · simp only [VCmpOp.test, show (3329 : BitVec 16).toNat = 3329 from rfl, gt_iff_lt, h, decide_true,
      ite_true]
    exact BitVec.allOnes_and
  · simp [VCmpOp.test, h]

/-- The SIMD acceptance block preserves memory, scalar registers and every
other vector register; each of its lanes contains exactly its accepted
mask/count weight, or zero. -/
theorem accept_ok (s : State)
    (hq : ∀ e < 8, vhalf (s.v .v19) e = 3329)
    (hw : ∀ e < 8, vhalf (s.v .v20) e = BitVec.ofNat 16 (256 + 2^e))
    (_hz : ∀ e < 8, (vhalf (s.v .v0) e).toNat < 4096) :
    WP isa (.block Impl.MlKem.AArch64.Rej8.accept) s fun t =>
      VChg [.v1] s t ∧ ∀ e < 8, vhalf (t.v .v1) e =
        if (vhalf (s.v .v0) e).toNat < 3329 then BitVec.ofNat 16 (256+2^e) else 0 := by
  refine wp_vop (d := .v1) rfl fun a ha =>
    wp_vop (d := .v1) rfl fun t ht => wp_nil ?_
  refine ⟨(ha.chg.trans ht.chg).mono (by decide), ?_⟩
  intro e he
  rw [ht.v, vhalf_and, ha.v, vhalf_map2 _ _ _ he, ha.get .v20, hw e he, hq e he]
  exact cmp_lane _ _

end VG.Proof.MlKem.AArch64.Rej8
