module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.CTMain
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Correct
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Pre
public import VerifiedGarbage.Proof.RsaOaep.Scan

/-!
# RSAES-OAEP decryption on PPC64LE: `Verified`

Untrusted: everything here is checked by Lean. Constant time
(`code_constantTime`, from `code_ct`); a state meeting the precondition,
which does not depend on the hash functions (`dec_sat`); `dec_verified`; and
decryption for two linked hash functions (`dec_link_verified`), which the
registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (hG : HashOK G) (cG : HashCT hG) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include cH cG hHh hHl hHv hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre
      (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pub (decrypt H G) :=
  RelCT.constantTime ((code_ct hH cH hG cG hHh hHl hHv hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preD_of h₁, pubD_refl s₁⟩, preD_of h₂, pubD_of hp⟩) fun _ _ h => h)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` against its shared contract, given a
state meeting it. -/
theorem dec_verified (hsat : ∃ s, (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre s) :
    Verified PPC64LE.target (decrypt H G) (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes) :=
  ⟨code_correct hH hG hHh hHl hHv hGh hGl hGv, code_constantTime hH cH hG cG hHh hHl hHv hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, an empty label, a working space of 2080
words, and the stack arguments at `sp + 96`. -/
def decSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1800 | .r6 => 0x2000 | .r7 => 64 | .r8 => 0x3000 | .r9 => 1
    | .r10 => 0x4200 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10060 then 1
    else bif Nat.beq a.toNat 0x10069 then 0x43 else bif Nat.beq a.toNat 0x10070 then 1
    else bif Nat.beq a.toNat 0x10079 then 0x44 else bif Nat.beq a.toNat 0x10080 then 1
    else bif Nat.beq a.toNat 0x10089 then 0x45 else bif Nat.beq a.toNat 0x10090 then 1
    else bif Nat.beq a.toNat 0x10099 then 0x46 else bif Nat.beq a.toNat 0x100A0 then 1
    else bif Nat.beq a.toNat 0x100A9 then 0x47 else bif Nat.beq a.toNat 0x100B9 then 0x41
    else bif Nat.beq a.toNat 0x100C0 then 64 else bif Nat.beq a.toNat 0x100CA then 0x02
    else bif Nat.beq a.toNat 0x100D0 then 0x20 else bif Nat.beq a.toNat 0x100D1 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x10060, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat (H G : Spec.Mgf1.Hash) : ∃ s, (Spec.RsaOaep.decryptContract H G abi stackBytes).pre s := by
  refine ⟨decSatState, ?_⟩
  -- The precondition does not depend on the hash functions: with them and the
  -- stack literal, `sig_sat_check` decides it in the kernel.
  change (Spec.RsaOaep.decryptContract Spec.Mgf1.md5 Spec.Mgf1.md5 abi 3776).pre decSatState
  sig_sat_check [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen,
    List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` for the linked hash functions. -/
theorem dec_link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified PPC64LE.target (decrypt H G) (Spec.RsaOaep.decryptContract lh.G lg.G abi stackBytes) :=
  dec_verified lh.ok lh.ct lg.ok lg.ct lh.hash lh.len lh.valid lg.hash lg.len lg.valid (dec_sat lh.G lg.G)

end VG.Proof.RsaOaep.PPC64LE.Dec
