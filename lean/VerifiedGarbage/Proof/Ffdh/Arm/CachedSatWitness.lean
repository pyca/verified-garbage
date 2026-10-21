module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.TCB.Mem

/-! One real public canonical context shared by cached attempt and search witnesses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSat
open VG VG.Arm

def domainMem (a : Addr) : Byte :=
  if a=0x3000 then 0x80 else if a=0x303f then 1 else if a=0x307f then 2 else 0

@[irreducible] def domain : List Byte := Spec.Rsa.bytesAt domainMem 0x3000 128

@[irreducible] def values : List (BitVec 64) := VG.Proof.Ffdh.generationValues 64 domain

theorem domain_length : domain.length=128 := by
  simp only [domain,Spec.Rsa.bytesAt,List.length_map,List.length_range]

theorem domain_valid : Spec.Ffdh.domainValid 64 domain=true := by
  unfold domain
  decide +kernel

theorem values_length : values.length=275 := by
  rw [values,VG.Proof.Ffdh.generationValues_length]
  rfl

@[irreducible] def withContext (base : Mem) : Mem := fun a =>
  if (a-0x100000).toNat<2200 then constMem 0x100000 values a else base a

theorem outside (base : Mem) {a : Addr} (small : a.toNat<0x100000) : withContext base a=base a := by
  unfold withContext
  apply ite_eq_right
  rw [BitVec.toNat_sub]
  change ¬ (2^64-0x100000+a.toNat)%2^64<2200
  rw [Nat.mod_eq_of_lt (by omega : 2^64-0x100000+a.toNat<2^64)]
  omega

theorem readW_outside (base : Mem) {a : Addr} {w : Nat} (small : a.toNat+w/8≤0x100000) :
    (withContext base).readW a w=base.readW a w := by
  apply Mem.readW_congr
  intro j hj
  apply outside
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : j<2^64),Nat.mod_eq_of_lt (by omega : a.toNat+j<2^64)]
  omega

theorem domain_unchanged (base : Mem) :
    Spec.Rsa.bytesAt (withContext base) 0x3000 128=Spec.Rsa.bytesAt base 0x3000 128 := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  apply outside
  have bound := List.mem_range.mp hi
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : i<2^64)]
  change (0x3000+i)%2^64<0x100000
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem held (base : Mem) (i : Nat) (hi : i<275) :
    (withContext base).readW (0x100000+BitVec.ofNat 64 (8*i)) 64=values.getD i 0 := by
  rw [← constMem_held 0x100000 values (by rw [values_length]; decide) i (by rw [values_length]; exact hi)]
  apply Mem.readW_congr
  intro j hj
  unfold withContext
  apply ite_eq_left
  rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat,Offset.add_sub_cancel_left,BitVec.toNat_ofNat]
  omega

theorem words (base : Mem) : Spec.Rsa.wordsAt (withContext base) 0x100000 275=values := by
  apply List.ext_getElem
  · simp only [Spec.Rsa.wordsAt,List.length_map,List.length_range,values_length]
  · intro i hi hj
    have bound : i<275 := by simpa only [Spec.Rsa.wordsAt,List.length_map,List.length_range] using hi
    simp only [Spec.Rsa.wordsAt,List.getElem_map,List.getElem_range]
    rw [held base i bound,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]

theorem canonical (base : Mem) :
    Spec.Ffdh.generationContextAt (withContext base) 0x100000 275 64 domain := by
  refine ⟨by rfl,?_⟩
  rw [words]
  rw [values]
  exact VG.Proof.Ffdh.generationPrecompute_eq (by rw [domain_length]; decide)
    (VG.Proof.Ffdh.domainValid_mod (k := 64) (dom := domain) domain_valid)

end VG.Proof.Ffdh.Arm.CachedSat
