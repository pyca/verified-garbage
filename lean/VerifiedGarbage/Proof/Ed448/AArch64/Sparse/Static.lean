module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectBase
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Framework.Offset

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
  exact constMem_held _ _ (by rw [baseWords_length];omega)

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
