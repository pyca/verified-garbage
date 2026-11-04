module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # A valid public FFDH domain, witnessing the cached key-generation contracts

`p_len = 64`; its 128 bytes are `p` and `g`, at `0x3000`. -/

@[expose] public section

namespace VG.Proof.Ffdh.CachedSat

open VG

def domainMem (a : Addr) : Byte :=
  if a = 0x3000 then 0x80 else if a = 0x303f then 1 else if a = 0x307f then 2 else 0

@[irreducible] def domain : List Byte := Spec.Rsa.bytesAt domainMem 0x3000 128

theorem domain_length : domain.length = 128 := by
  simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem domain_valid : Spec.Ffdh.domainValid 64 domain = true := by
  unfold domain
  decide +kernel

/-- A memory with the domain's bytes at `0x3000`. -/
theorem bytesAt_eq {m : Mem} (h : ∀ i < 128, m (0x3000 + BitVec.ofNat 64 i) = domainMem (0x3000 + BitVec.ofNat 64 i)) :
    Spec.Rsa.bytesAt m 0x3000 128 = domain := by
  unfold domain Spec.Rsa.bytesAt
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

end VG.Proof.Ffdh.CachedSat
