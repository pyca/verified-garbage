module

public import VerifiedGarbage.Impl.Rsa.Arm.RecoverScalar
import VerifiedGarbage.Proof.Rsa.Arm.AddMod
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.RecoverScalar
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

/-! Arithmetic, memory safety and constant time for candidates 2 and 3 of
fused recovery. General candidates retain the existing Montgomery product.
The verified fused recovery pass reuses these helpers without a separate API. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.RecoverScalar
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverScalar

abbrev writes : List Nat := [aW, aW + 1, aW + 2, mXm]

theorem twice_ok {s : State} {B : BitVec 32} {Z w : Nat} (h : Ws s B Z w nArr) :
    WP isa twice s fun t => Ws t B Z w nArr ∧
      Keep B w writes [sC] s.mem t.mem ∧ Rest opRegs s t ∧
      (num s.mem B w aZ = 0 → num s.mem B w mX < num s.mem B w aN →
        2 * num s.mem B w aN ≤ 2 ^ (32 * w) →
        num t.mem B w mXm = (2 * num s.mem B w mX) % num s.mem B w aN) := by
  refine WP.mono (addMod_ok h (o := mXm) (a := mX) (b := mX) (m := aN) (z := aZ) (t := aW)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨ht, keep, rest, value⟩ => ?_
  refine ⟨ht, keep, rest, fun zero bound headroom => ?_⟩
  rw [show 2 * num s.mem B w mX = num s.mem B w mX + num s.mem B w mX by omega]
  exact value zero bound bound headroom

theorem three_ok {s : State} {B : BitVec 32} {Z w : Nat} (h : Ws s B Z w nArr) :
    WP isa three s fun t => Ws t B Z w nArr ∧
      Keep B w writes [sC] s.mem t.mem ∧ Rest opRegs s t ∧
      (num s.mem B w aZ = 0 → num s.mem B w mX < num s.mem B w aN →
        2 * num s.mem B w aN ≤ 2 ^ (32 * w) →
        num t.mem B w mXm = (3 * num s.mem B w mX) % num s.mem B w aN) := by
  unfold three
  refine WP.seq (WP.mono (twice_ok h) fun u ⟨hu, ku, ru, vu⟩ => ?_)
  refine WP.mono (addMod_ok hu (o := mXm) (a := mXm) (b := mX) (m := aN) (z := aZ) (t := aW)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨ht, kt, rt, vt⟩ => ?_
  refine ⟨ht, ku.trans kt, ru.trans rt, fun zero bound headroom => ?_⟩
  have same (j : Nat) (hj : j ∉ writes) (fit : j < nArr) :
      num u.mem B w j = num s.mem B w j :=
    ku.num (fun i hi eq => hj (eq ▸ hi)) (by decide) (h.fit64 fit)
  have mz := same aZ (by decide) (by decide)
  have mn := same aN (by decide) (by decide)
  have mx := same mX (by decide) (by decide)
  have product := vu zero bound headroom
  have positive : 0 < num s.mem B w aN := by omega
  rw [vt (mz.trans zero) (by rw [product, mn]; exact Nat.mod_lt _ positive)
    (by rw [mx, mn]; exact bound) (by rw [mn]; exact headroom), product, mx, mn,
    Nat.mod_add_mod]
  congr 1
  omega

/-- Addresses and loop bounds depend only on the workspace context. -/
theorem scalar_ct (code : Prog isa)
    (check : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) code hc).isSome = true) :
    ConstantTime isa (fun _ => True)
      (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) code := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r7, .r8, .r9]) ?_ check.choose_spec
  intro s t _ _ ⟨h7, h8, h9⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h7
  · exact h8
  · exact h9

theorem twice_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) twice :=
  scalar_ct twice ⟨_, by taint_decide⟩

theorem three_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) three :=
  scalar_ct three ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.RecoverScalar
