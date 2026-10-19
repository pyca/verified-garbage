module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoad

import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Clear the four selection accumulators without disturbing scalar state. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

theorem zeroVector_ok (s : State) (r : VReg) :
    WP isa (.block [.vop (.movi0 r)]) s fun t =>
      t.v r = 0 ∧ VKeep [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, VOp.eval, Option.map_some, runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.v_setV_self _ _ _, VKeep.setV _ _ _⟩

theorem clearVectors_ok (rs : List VReg) (s : State) :
    WP isa (.block (rs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ r ∈ rs, t.v r = 0) ∧ VKeep rs s t := by
  induction rs generalizing s with
  | nil => exact WP.block_nil ⟨by simp, ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩⟩
  | cons r rs ih =>
    rw [List.map_cons, show .vop (.movi0 r) :: rs.map (fun r => Instr.vop (.movi0 r)) =
      [.vop (.movi0 r)] ++ rs.map (fun r => Instr.vop (.movi0 r)) from rfl,
      WP.block_append_iff]
    refine WP.mono (zeroVector_ok s r) fun u ⟨hu, ku⟩ => ?_
    refine WP.mono (ih u) fun t ⟨ht, kt⟩ => ⟨?_, ku.trans kt⟩
    intro q hq
    by_cases h : q ∈ rs
    · exact ht q h
    · have he : q = r := (List.mem_cons.mp hq).resolve_right h
      subst q
      exact (kt.v r h).trans hu

theorem clearAccs_ok (s : State) :
    WP isa (.block (accs.map fun r => .vop (.movi0 r))) s fun t =>
      (∀ i < 4, t.v (acc i) = 0) ∧ VKeep accs s t := by
  refine WP.mono (clearVectors_ok accs s) fun t ⟨ht, kt⟩ => ⟨?_, kt⟩
  intro i hi
  exact ht (acc i) ((by decide : ∀ i < 4, acc i ∈ accs) i hi)

end VG.Proof.Bignum.AArch64.WindowVector
