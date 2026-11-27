module

public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.P521.Comb7Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ecdsa.AArch64.P521.Tables`, which this module and modules that import it used -/

section

/-!
# ECDSA over P-521 on AArch64: the comb's tables in a static

What the contracts of the functions that run the comb say of its tables
(`TblHeld`): held at the address of the static `p521.tsym`, not wrapping
around, and apart from the writable regions; their length
(`p521_combWords_length`, from the tables' shape alone); and a memory
holding them, for the contracts' witnesses (`satMem`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P521

open VG VG.AArch64
open VG.Impl.Ecdsa.AArch64 (p521)

/-- The comb's tables at the static `p521.tsym`, held, not wrapping around, and
apart from the regions `wr`. -/
def TblHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < p521.combWords.length,
    s.mem.readW (s.syms p521.tsym + BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0) ∧
  (s.syms p521.tsym).toNat + 8 * p521.combWords.length ≤ 2 ^ 64 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩ r

theorem p521_combConsts : p521.combConsts = [(p521.tsym, p521.combWords)] := rfl

theorem p521_tbl_len : Impl.P521.p521Comb7.length = 83 :=
  Proof.P521.p521Comb7_length

theorem p521_tbl_lenH : ∀ j < 83, (Impl.P521.p521Comb7.getD j []).length = 64 :=
  Proof.P521.p521Comb7_rows

/-- `p521.combWords` has `83 · 64 · 18` words. -/
theorem p521_combWords_length : p521.combWords.length = 95616 :=
  (Proof.Weierstrass.tcombWords_length (n := p521.n) (R := p521.R) (p := p521.C.p)
    (H := 64) (tbl := p521.tbl) p521_tbl_len p521_tbl_lenH).trans rfl

/-- The memory of the contracts' witnesses: the tables at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
tables). -/
@[irreducible] def satMem : Mem := constMem 0x100000 p521.combWords

theorem satMem_held : ∀ i < p521.combWords.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p521.combWords.getD i 0 := by
  unfold satMem
  exact constMem_held _ _ (by rw [p521_combWords_length]; omega_using [])

end VG.Proof.Ecdsa.AArch64.P521

end

end

/-!
# ECDSA over P-521 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P521.inst` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p521.combConsts`),
by name: `vg_ecdsa_p521_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `p521.tsym`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P521

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64 (p521)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P521.curve (ofBytes (bytesAt m d 66)) (hashToInt Spec.P521.curve (bytesAt m digest 66))
    (ofBytes (bytesAt m k 66))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 132⟩
    let d : Region := ⟨s.gpr .x1, 66⟩
    let digest : Region := ⟨s.gpr .x2, 66⟩
    let k : Region := ⟨s.gpr .x3, 66⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms p521.tsym, 8 * p521.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 132 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 132 = encode Spec.P521.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 132 = List.replicate 132 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms p521.tsym = s₂.syms p521.tsym

end VG.Proof.Ecdsa.AArch64.P521
