import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# RSAEP from precomputed values on x86-64: helpers for the shared contracts

What the proofs of `pdContract`'s callers against their shared contracts
(`vg_rsa_public_precomputed_checked`'s, `PubChecked.lean`) share: a state
meeting `pdContract.pre`, and the leak of `pre` and `e`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pdContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6008`. -/
def pdSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 16 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The leak of `pre` and `e`, as numbers, determines each when `pre`'s
length is the same. -/
theorem leak_eq2 {a c : List (BitVec 64)} {b d : List Byte} (hl : a.length = c.length)
    (h : a.map (·.toNat) ++ b.map (·.toNat) = c.map (·.toNat) ++ d.map (·.toNat)) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h1,
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h2⟩

end VG.Proof.Bignum.X86_64
