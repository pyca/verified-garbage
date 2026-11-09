module
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Bignum.X86_64.PcCT

/-!
# `vg_rsa_public_precompute` on x86-64: verified against the shared contract

`pcContract` states the shared contract on the registers;
`pcSatState`, a state it allows.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pcContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def pcSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x4000 | .r9 => 1056
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8448⟩]

end VG.Proof.Bignum.X86_64
