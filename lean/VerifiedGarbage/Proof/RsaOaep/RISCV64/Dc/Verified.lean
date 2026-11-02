module

import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.CTMain
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Correct
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Mgf1.Basic

/-!
# RSAES-OAEP decryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Dc/Verified.lean`): constant time
(`code_constantTime`, from `code_ct`); a state meeting the precondition,
which does not depend on the hash functions (`dec_sat`); `dec_verified`; and
decryption for two linked hash functions (`dec_link_verified`, with
encryption's `Link`), which the registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64.Dec

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64.Dec
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (HashCT Link)

section
variable {H G : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : H.F ≤ 208) (hG : HashOK G) (cG : HashCT hG)
  (fG : G.F ≤ 208) {Hs Gs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
include cH fH cG fG hHh hHl hHv hGh hGl hGv

theorem code_constantTime :
    ConstantTime isa (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre
      (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pub (decrypt H G) :=
  RelCT.constantTime ((code_ct hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preD_of h₁, pubD_refl s₁⟩, preD_of h₂, pubD_of hp⟩) fun _ _ h => h)

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` against its shared contract, given a
state meeting it. -/
theorem dec_verified (hsat : ∃ s, (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes).pre s) :
    Verified RISCV64.target (decrypt H G) (Spec.RsaOaep.decryptContract Hs Gs abi stackBytes) :=
  ⟨code_correct hH hG fH fG hHh hHl hHv hGh hGl hGv,
    code_constantTime hH cH fH hG cG fG hHh hHl hHv hGh hGl hGv, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting decryption's contract: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, an empty label, a working space of 2080
words, and the stack arguments at `sp`. -/
def decSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1800 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000 | .a6 => 1
    | .a7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10000 then 1
    else bif Nat.beq a.toNat 0x10009 then 0x43 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x44 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x45 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x46 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x47 else bif Nat.beq a.toNat 0x10059 then 0x41
    else bif Nat.beq a.toNat 0x10060 then 64 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16640⟩]

theorem dec_sat (H G : Spec.Mgf1.Hash) : ∃ s, (Spec.RsaOaep.decryptContract H G abi stackBytes).pre s := by
  refine ⟨decSatState, ?_⟩
  -- The precondition does not depend on the hash functions: with them and the
  -- stack literal, `sig_sat_check` decides it in the kernel.
  change (Spec.RsaOaep.decryptContract Spec.Mgf1.md5 Spec.Mgf1.md5 abi 3472).pre decSatState
  sig_sat_check [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, abi, argRegs, stackArgs_fifteen,
    List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt` for the linked hash functions. -/
theorem dec_link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified RISCV64.target (decrypt H G) (Spec.RsaOaep.decryptContract lh.G lg.G abi stackBytes) :=
  dec_verified lh.ok lh.ct lh.fits lg.ok lg.ct lg.fits lh.hash lh.len lh.valid lg.hash lg.len lg.valid
    (dec_sat lh.G lg.G)

end VG.Proof.RsaOaep.RISCV64.Dec
