module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and `encK`'s public
data with `pre` and its words; it implies the shared contract (`implies`),
which is satisfiable for each of `MdHash`'s hash functions (`sat`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (H G : Spec.Mgf1.Hash)

def contract : Contract isa where
  pre := (Spec.RsaOaep.encryptPrecomputedContract H G abi encStack).pre
  post := post H G
  pub a s := (encK H G).pub a s ∧ stackArg a 7 = stackArg s 7 ∧ stackArg a 8 = stackArg s 8 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 7) (stackArg s 8).toNat

/-- `encSatState`, with 16 words of `pre` at `0x5000`. -/
def satState : State := { encSatState H with
  mem := fun a => if a = 0x10041 then 0x50 else if a = 0x10048 then 16 else (encSatState H).mem a
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 0⟩, ⟨0x4200, 0⟩, ⟨0x4600, H.len⟩, ⟨0x5000, 128⟩, ⟨0x10008, 72⟩] }

/-- The precomputed contract is satisfiable for each of `MdHash`'s hash functions. -/
theorem sat (hH : H ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (Spec.RsaOaep.encryptPrecomputedContract H G abi encStack).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs,
      encStack, stackArgs_nine, List.append_eq] [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512_256

theorem implies (hsat : ∃ s, (Spec.RsaOaep.encryptPrecomputedContract H G abi encStack).pre s) :
    (contract H G).Implies (Spec.RsaOaep.encryptPrecomputedContract H G abi encStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi,
    argRegs, contract, post, Consistent, encK, encStack, stackArgs_nine, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs, contract,
      encStack, stackArgs_nine, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_seven, a0, a1, a2, a3, a4, a5, a6], hn, he⟩, a7, a8, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaOaep.X86_64.Pc
