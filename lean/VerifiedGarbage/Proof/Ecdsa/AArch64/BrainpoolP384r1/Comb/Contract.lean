module

public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64.Comb
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ecdsa.AArch64.BrainpoolP384r1.Comb.Tables`, which this module and modules that import it used -/

section

/-!
# ECDSA over brainpoolP384r1 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `combCfg.tsym`, not wrapping
around, and apart from the writable regions; their length
(`combCfg_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Comb

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64.BrainpoolP384r1 (combCfg)

/-- The comb's tables at the static `combCfg.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combCfg.combWords.length,
    s.mem.readW (s.syms combCfg.tsym + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0) ∧
  (s.syms combCfg.tsym).toNat + 8 * combCfg.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩ r

theorem combCfg_tbl_len : Impl.BrainpoolP384r1.comb7.length = 55 :=
  by decide +kernel

theorem combCfg_tbl_lenH : ∀ j < 55, (Impl.BrainpoolP384r1.comb7.getD j []).length = 64 :=
  by decide +kernel

/-- `combCfg.combWords` has `55 · 64 · 12` words. -/
theorem combCfg_combWords_length : combCfg.combWords.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := combCfg.n) (R := combCfg.R) (p := combCfg.C.p)
    (H := 64) (tbl := combCfg.tbl) combCfg_tbl_len combCfg_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 combCfg.combWords

theorem satMem_held : ∀ i < combCfg.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combCfg.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [combCfg_combWords_length]; omega_using [])

end VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Comb

end

end

/-!
# ECDSA over brainpoolP384r1 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP384r1.inst` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts combCfg.combConsts`),
by name: `vg_ecdsa_combCfg_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `combCfg.tsym`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Comb

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64.BrainpoolP384r1 (combCfg)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP384r1.curve (ofBytes (bytesAt m d 48)) (hashToInt Spec.BrainpoolP384r1.curve (bytesAt m digest 48))
    (ofBytes (bytesAt m k 48))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 96⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let digest : Region := ⟨s.gpr .x2, 48⟩
    let k : Region := ⟨s.gpr .x3, 48⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms combCfg.tsym, 8 * combCfg.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 96 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 96 = encode Spec.BrainpoolP384r1.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 96 = List.replicate 96 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combCfg.tsym = s₂.syms combCfg.tsym

end VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Comb
