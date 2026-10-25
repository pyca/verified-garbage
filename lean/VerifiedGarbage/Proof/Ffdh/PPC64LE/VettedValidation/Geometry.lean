module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Table
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainVerified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Covers

/-! The existing shared signature supplies the same input and working-space geometry. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation

def contract := Spec.Ffdh.checkDomainContract (abi.withConsts tableConsts)
def plain (s : State) := stripConsts tableConsts s

theorem pre_plain {s : State} (h : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi).pre (plain s) ∧ ConstsOk tableConsts 0 s :=
  pre_consts.mp h

theorem cd_pre {s : State} (h : contract.pre s) : Domain.cdContract.pre (plain s) :=
  Domain.cd_implies.pre _ (pre_plain h).1

def domain (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat

theorem context {s : State} (h : contract.pre s) :
    Context (s.gpr .r3) (s.gpr .r5).toNat (domain s) s := by
  obtain ⟨rd, _, _, _, _, sizes, shape, _⟩ := cd_pre h
  have len : (domain s).length = (s.gpr .r4).toNat := by
    simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, sizes.1, sizes.2⟩
  · rw [len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [len]
    have read : InRegions ((plain s).rd ++ (plain s).wr) (s.gpr .r3) (s.gpr .r4).toNat :=
      ⟨_, List.mem_append_left _ (by rw [rd]; exact List.mem_cons_self), Region.contains_self _ _⟩
    obtain ⟨r, member, contains⟩ := read
    refine ⟨r, ?_, contains⟩
    rcases List.mem_append.mp member with hr | hw
    · exact List.mem_append_left _ (List.mem_of_mem_take hr)
    · exact List.mem_append_right _ hw
  · rw [len]; rfl
  · rw [len]
    exact shape

end VG.Proof.Ffdh.PPC64LE.VettedValidation
