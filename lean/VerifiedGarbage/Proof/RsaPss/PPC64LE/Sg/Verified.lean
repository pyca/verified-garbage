module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTMain
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Correct
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Inst
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre

/-!
# RSASSA-PSS signing on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`, with the contract's public data as
`PubS`); a state meeting the precondition for each hash function the other
targets sign with (`sign_sat`); `sign_verified`; and signing for a linked
hash function (`sign_link_verified`), which the registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (HashCT)

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs)
include cH hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.signContract Gs Gs abi stackBytes).pre
      (Spec.RsaPss.signContract Gs Gs abi stackBytes).pub (sign H) :=
  RelCT.constantTime ((code_ct hH cH hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preS_of h₁, pubS_refl s₁, by have := (preS_of h₁).k1; unfold kk; omega⟩,
      preS_of h₂, pubS_of hp, by have := (preS_of h₂).k1; unfold kk; omega⟩) fun _ _ h => h)

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign` against its shared contract, given a state
meeting it. -/
theorem sign_verified (hsat : ∃ s, (Spec.RsaPss.signContract Gs Gs abi stackBytes).pre s) :
    Verified PPC64LE.target (sign H) (Spec.RsaPss.signContract Gs Gs abi stackBytes) :=
  ⟨code_correct hH hGh hGl hGv, code_constantTime hH cH hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting signing's contract for a digest of `D` bytes: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, an empty salt, a working
space of 2080 words, and the stack arguments at `sp + 96`. -/
def signSatState (D : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4200
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x43
    else bif Nat.beq a.toNat 0x10068 then 1 else bif Nat.beq a.toNat 0x10071 then 0x44
    else bif Nat.beq a.toNat 0x10078 then 1 else bif Nat.beq a.toNat 0x10081 then 0x45
    else bif Nat.beq a.toNat 0x10088 then 1 else bif Nat.beq a.toNat 0x10091 then 0x46
    else bif Nat.beq a.toNat 0x10098 then 1 else bif Nat.beq a.toNat 0x100A1 then 0x41
    else bif Nat.beq a.toNat 0x100A9 then 0x47 else bif Nat.beq a.toNat 0x100BA then 0x02
    else bif Nat.beq a.toNat 0x100C0 then 0x20 else bif Nat.beq a.toNat 0x100C1 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4100, D⟩, ⟨0x4700, 0⟩, ⟨0x10060, 104⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

theorem sign_sat {G : Spec.Mgf1.Hash} (hG : G ∈ pssHashes) :
    ∃ s, (Spec.RsaPss.signContract G G abi stackBytes).pre s := by
  refine ⟨signSatState G.len, ?_⟩
  change (Spec.RsaPss.signContract G G abi 3776).pre (signSatState G.len)
  simp only [pssHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  sig_sat_check [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen,
    List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign` for the linked hash function. -/
theorem sign_link_verified {H : Hash} (l : Link H) :
    Verified PPC64LE.target (sign H) (Spec.RsaPss.signContract l.G l.G abi stackBytes) :=
  sign_verified l.ok l.ct l.hash l.len l.valid (sign_sat l.mem)

end VG.Proof.RsaPss.PPC64LE.Sg
