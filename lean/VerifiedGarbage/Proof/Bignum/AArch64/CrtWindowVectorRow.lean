module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
  refine WP.mono (compare_ok (by omega) (by omega) h23 h22) fun a ⟨ha, ka⟩ => ?_
  refine WP.mono (loadBits_ok (choose := j = v) 4 (by decide) ha
    (fun i hi => by rw [ka.rd, ka.wr, ka.gpr]; exact hld i hi)) fun t ⟨ht, kt⟩ => ?_
  refine ⟨?_, ka.trans kt⟩
  intro i hi
  rw [ht i hi, ka.mem, ka.gpr, ka.v (acc i) (by
    simpa only [List.mem_singleton] using (acc_facts i hi).1)]
  simp only [hi, true_and]

/-- No SIMD value controls a row's addresses or instruction sequence. -/
theorem inner_ct :
    RelCT isa (Two fun (p : Addr × BitVec 64) s => s.gpr .x16 = p.1 ∧ s.gpr .x6 = p.2)
      (.block inner) (fun _ _ => True) := by
  apply two_taint [.x16, .x6] (hc := .block [])
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowVector
