module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.Secp256k1Field
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV

/-!
# Arithmetic modulo secp256k1's prime on RISC-V: by register

The functions modulo any four-word modulus (`Proof/Weierstrass/RISCV64/Gen4.lean`)
for secp256k1's `p` (`ok`): each meets its contract by register (`mulRV`,
`addRV`, `subRV`), as the curve code's proofs need.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.Secp256k1Field

open VG VG.RISCV64 VG.Impl.Weierstrass.Mont VG.Impl.Weierstrass.RISCV64.Secp256k1Field
open VG.Proof.Weierstrass.RISCV64 (mulRV addRV subRV)

theorem ok : Gen4.Ok secp256k1p.m := ⟨by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV secp256k1p).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV secp256k1p).post s s' :=
  Gen4.mul_rv rfl ok s hs

theorem add_rv (s : State) (hs : (addRV secp256k1p).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV secp256k1p).post s s' :=
  Gen4.add_rv rfl ok s hs

theorem sub_rv (s : State) (hs : (subRV secp256k1p).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV secp256k1p).post s s' :=
  Gen4.sub_rv rfl ok s hs

end VG.Proof.Weierstrass.RISCV64.Secp256k1Field
