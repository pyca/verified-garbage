module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorRow
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

/-! Advance the full-scan row pointer and public SIMD row index. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

def advance : List Instr :=
  [.add .x .x16 .x16 .x6, .vop (.add .d2 .v23 .v23 .v24)]

theorem add_dup2 (x y : BitVec 64) :
    VArr.d2.map2 (fun _ a b => a + b) (dup2 x) (dup2 y) = dup2 (x + y) := by
  simp only [VArr.map2, dup2, vdword_ofVDwords_0, vdword_ofVDwords_1]

theorem advance_ok {s : State} {j : Nat}
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j)) (h24 : s.v .v24 = dup2 1) :
    WP isa (.block advance) s fun t =>
      t = (s.write .x .x16 (s.gpr .x16 + s.gpr .x6)).setV .v23 (dup2 (BitVec.ofNat 64 (j + 1))) := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, State.read, BitVec.setWidth_eq,
    runStep_some, exec, VOp.eval, RegUpd.v_write, h23, h24, add_dup2,
    Option.map_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  apply congrArg (fun x => (s.write .x .x16 (s.gpr .x16 + s.gpr .x6)).setV .v23 (dup2 x))
  rw [BitVec.ofNat_add]
  exact congrArg (fun x : BitVec 64 => BitVec.ofNat 64 j + x) (by decide)

theorem inner_eq : inner =
    ([.vop (.cmeq .d2 .v20 .v23 .v22)] : List Instr) ++ loadBits 4 ++ advance := rfl

theorem inner_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) (h24 : s.v .v24 = dup2 1)
    (hld : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block inner) s fun t =>
      ((∀ i < 4, t.v (acc i) = if j = v then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      t.gpr .x16 = s.gpr .x16 + s.gpr .x6 ∧ t.mem = s.mem ∧
      t.v .v23 = dup2 (BitVec.ofNat 64 (j + 1)) ∧ t.v .v22 = s.v .v22 ∧ t.v .v24 = s.v .v24) ∧
      Keep [.x16] s t := by
  refine WP.keep [.x16] ?_ (by decide) (by decide) (by decide +kernel)
  rw [inner_eq, WP.block_append_iff]
  refine WP.mono (selectRow_ok hj hv h23 h22 hld) fun a ⟨ha, ka⟩ => ?_
  refine WP.mono (advance_ok (by rw [ka.v .v23 (by decide)]; exact h23)
    (by rw [ka.v .v24 (by decide)]; exact h24)) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ka.mem, RegUpd.v_setV_self _ _ _, ?_, ?_⟩
  · intro i hi
    have hn : acc i ≠ .v23 := by
      have h : ∀ i < 4, acc i ≠ .v23 := by decide
      exact h i hi
    rw [RegUpd.v_setV_of_ne _ _ hn, RegUpd.v_write, ha i hi]
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_write_self, BitVec.setWidth_eq, ka.gpr]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, ka.v .v22 (by decide)]
  · rw [RegUpd.v_setV_of_ne _ _ (by decide), RegUpd.v_write, ka.v .v24 (by decide)]

end VG.Proof.Bignum.AArch64.WindowVector
