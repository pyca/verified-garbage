module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.WrapTime
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_private_precompute` on x86: verified

Constant time but for `n` (`constantTime`), from `wrapBody_relCT` through
the frame; a state that satisfies the precondition (`satisfiable`); and
`verified`, given `vg_rsa_public_precompute`'s verified code.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86
open VG.Impl.Bignum.X86.PrivPre (code primes)

theorem constantTime {pcName prName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (prst : stackUse primes ≤ 96) (prns : NoSp primes) :
    ConstantTime isa (Spec.Rsa.privatePrecomputeContract abi stackBytes).pre
      (Spec.Rsa.privatePrecomputeContract abi stackBytes).pub (code pcName pc prName primes) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' S₁ S₂ H E₁ E₂
  have R := RelCT.frameAlloc (bytes := Impl.Bignum.X86.PrivPre.frameBytes) (P := fun a b => a = s₁ ∧ b = s₂)
    ((wrapBody_relCT (pcName := pcName) (prName := prName) pv pst pns prst prns (ppABI_of S₁) (ppABI_of S₂)
      (pub_of H)).mono
      (fun a b ⟨x, y, ⟨ex, ey⟩, ha, hb⟩ => by subst ex ey; exact ⟨ha, hb⟩) (fun _ _ h => h))
  exact (R s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ E₁ E₂).1

/-- Disjoint minimum-length buffers. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 20
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 48
    else if a = 0x20018 then 1
    else if a = 0x2001d then 64
    else if a = 0x20020 then 1
    else if a = 0x20025 then 144
    else if a = 0x20028 then 32
    else if a = 0x20029 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 1⟩]
  wr := [⟨4096, 160⟩, ⟨36864, 8448⟩, ⟨0x20004, 40⟩]

theorem satisfiable : ∃ s, (Spec.Rsa.privatePrecomputeContract abi stackBytes).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 20 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 36864 := by decide
  have a9 : arg satState 9 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argSlots, argVal,
    argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, e, esp, satState, stackBytes, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
      Spec.Rsa.modulusWords] using satState

theorem verified {pcName prName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (prst : stackUse primes ≤ 96) (prns : NoSp primes) :
    Verified target (code pcName pc prName primes) (Spec.Rsa.privatePrecomputeContract abi stackBytes) :=
  ⟨correct pv pst pns prst prns, constantTime pv pst pns prst prns, satisfiable⟩

end VG.Proof.Bignum.X86.PrivPre
