module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToAdditive

/-! ### `Bignum.AArch64.CrtWindowVectorRow`, which this module and modules that import it used -/

section

/-! A complete table-row selection, with fixed-address loads and SIMD masks. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (inner)

theorem compare_ok {s : State} {j v : Nat} (hj : j < 2 ^ 64) (hv : v < 2 ^ 64)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v)) :
    WP isa (.block [.vop (.cmeq .d2 .v20 .v23 .v22)]) s fun t =>
      t.v .v20 = (if j = v then BitVec.allOnes 128 else 0) ∧ VKeep [.v20] s t := by
  have he : (BitVec.ofNat 64 j = BitVec.ofNat 64 v) ↔ j = v := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hv] using this
    · intro h; rw [h]
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, VOp.eval, h23, h22, cmeq_dup2, he,
    Option.map_some, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.v_setV_self _ _ _, VKeep.setV _ _ _⟩

theorem selectRow_ok {s : State} {j v : Nat} (hj : j < 32) (hv : v < 32)
    (h23 : s.v .v23 = dup2 (BitVec.ofNat 64 j))
    (h22 : s.v .v22 = dup2 (BitVec.ofNat 64 v))
    (hld : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (([.vop (.cmeq .d2 .v20 .v23 .v22)] : List Instr) ++ loadBits 4)) s fun t =>
      (∀ i < 4, t.v (acc i) = if j = v then
        s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * i)) 16 else s.v (acc i)) ∧
      VKeep (.v20 :: written) s t := by
  rw [WP.block_append_iff]
  refine WP.mono (compare_ok (by omega_using [hj]) (by omega_using [hv]) h23 h22) fun a ⟨ha, ka⟩ => ?_
  refine WP.mono (loadBits_ok (choose := j = v) 4 (by decide) ha
    (fun i hi => by rw [ka.rd, ka.wr, ka.gpr]; exact hld i hi)) fun t ⟨ht, kt⟩ => ?_
  refine ⟨?_, ka.trans kt⟩
  intro i hi
  rw [ht i hi, ka.mem, ka.gpr, ka.v (acc i) (by
    simpa only [List.mem_singleton] using (acc_facts i hi).1)]
  simp only [hi, true_and]

end VG.Proof.Bignum.AArch64.WindowVector

end

end

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
