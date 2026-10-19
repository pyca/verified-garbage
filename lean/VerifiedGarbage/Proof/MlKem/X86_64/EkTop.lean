module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkScalar

/-!
# ML-KEM on x86-64: encapsulation hashing the key

`kemEncaps L v.callee` for any implementation `v` of `vg_mlkem_sample_ntt4`,
with the sponge functions (`EkScalar.lean`), and a state its contract
permits (`encapsSat`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- A state satisfying the precondition of `vg_mlkem*_encaps` for keys of
`ekLen` bytes, ciphertexts of `ctLen` bytes and `scr` bytes of working space. -/
def encapsSat (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000
    | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, ctLen⟩, ⟨0x10000, scr⟩]

end VG.Proof.MlKem.X86_64
