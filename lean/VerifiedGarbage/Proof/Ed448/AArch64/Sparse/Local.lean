module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ed448.AArch64.Sparse.Static`, which this module and modules that import it used -/

section

/-! Immutable odd-base words and their contract-level memory witness. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse
open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (ofs far)

theorem baseWords_length : baseWords.length=1024:=by simp [baseWords]
theorem baseWords_getD {i:Nat} (hi:i<1024) : baseWords.getD i 0=baseWord i:=by
  simp [baseWords,List.getD_eq_getElem?_getD,hi]

def BaseHeld (s:State) (wr:List Region) : Prop :=
  (∀ i<baseWords.length,s.mem.readW (s.syms baseSym+BitVec.ofNat 64 (8*i)) 64=baseWords.getD i 0) ∧
  (s.syms baseSym).toNat+8*baseWords.length≤2^64 ∧
  ∀ r∈wr,Region.Disjoint ⟨s.syms baseSym,8*baseWords.length⟩ r

theorem baseConsts_eq : baseConsts=[(baseSym,baseWords)]:=rfl
@[irreducible] def satMem : Mem:=constMem 0x100000 baseWords

theorem satMem_held : ∀ i<baseWords.length,
    satMem.readW (0x100000+BitVec.ofNat 64 (8*i)) 64=baseWords.getD i 0:=by
  unfold satMem
  exact constMem_held _ _ (by rw [baseWords_length];omega_using [])

theorem held_baseTable {s:State} {base:Addr} (h:BaseHeld s [⟨base,8192⟩])
    (hr:(⟨s.syms baseSym,8192⟩:Region)∈s.rd) : BaseTableAt s base (s.syms baseSym):=by
  refine ⟨⟨_,List.mem_append_left _ hr,(by simp only [Region.Contains,BitVec.sub_self,BitVec.toNat_zero,Nat.zero_add,Nat.le_refl])⟩,?_,?_⟩
  · intro i hi
    have hd:Region.Disjoint ⟨s.syms baseSym,8192⟩ ⟨base,8192⟩:=by
      have hd:=h.2.2 ⟨base,8192⟩ (by simp)
      simpa only [baseWords_length] using hd
    exact far hd hi (by decide)
  · intro i hi
    rw [←baseWords_getD hi]
    exact h.1 i (by rw [baseWords_length];exact hi)

end VG.Proof.Ed448.AArch64.Sparse

end

end

/-! Untrusted local contract for the sparse verification equation. Timing may
reveal the public signature and challenge scalars, as permitted by the shared
reviewed verification contract. Point coordinates are never public for timing. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Sparse




def signatureScalar (s:State) : Nat:=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .x1+BitVec.ofNat 64 57) 57)
def challengeScalar (s:State) : Nat:=
  Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57)

/-- `vg_ed448_verify_equation(pk = x0, signature = x1, challenge = x2, scratch = x3) -> w0`,
with the odd affine base table at the static `baseSym`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, 114⟩, ⟨s.gpr .x2, 57⟩,
      ⟨s.syms baseSym, 8 * baseWords.length⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ BaseHeld s [⟨s.gpr .x3, 8192⟩]
  post s t := t.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57) then 1 else 0
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.syms baseSym = t.syms baseSym ∧
    signatureScalar s=signatureScalar t ∧ challengeScalar s=challengeScalar t

theorem verifyEquation_noFrames : verifyEquation.noFrames = true := by decide +kernel

/-- `vg_ed448_verify_equation` meets `verifyEquationLocal` and the ABI, in constant time. -/
structure EqOk : Prop where
  ok : ∀ s, verifyEquationLocal.pre s →
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'
  ct : ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation

end VG.Proof.Ed448.AArch64.Sparse
