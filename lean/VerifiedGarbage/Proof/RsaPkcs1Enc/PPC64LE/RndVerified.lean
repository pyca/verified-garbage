module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCorrect
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.RndCorrect
meta import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on PPC64LE: `Verified`

`contract` is the shared contract's precondition, `post`, and its public data
by name (`pub`); it implies the shared contract (`implies`). With
correctness (`code_correct`) and constant time (`code_ct`), `code` is
verified for the `rndStack` bytes of stack its frame and
`vg_rsa_pkcs1_encrypt_precomputed`'s use (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Random

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre
  post := post
  pub := pub

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

/-- A state meeting the precondition: a 512-bit key, an empty message and
tape, and the stack arguments at `sp + 96`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 64 | .r8 => 0x4000 | .r9 => 1
    | .r10 => 0x5000 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10069 then 0x60 else bif Nat.beq a.toNat 0x1007A then 0x02
    else bif Nat.beq a.toNat 0x10080 then 0x70 else bif Nat.beq a.toNat 0x10089 then 0x70
    else bif Nat.beq a.toNat 0x10090 then 0x10 else 0
  rd := [⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 128⟩, ⟨0x10060, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 16⟩, ⟨0x20000, 896⟩]

theorem implies : contract.Implies (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack) where
  pre := fun _ h => h
  post := by
    intro s u _ h
    sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      abi, argRegs, stackArgs_seven, List.append_eq, List.range, List.range.loop]
    obtain ⟨⟨req, h0, h1, hr⟩, hm⟩ := h
    exact ⟨⟨req, by rw [wordsAt_two, h0, h1]; rfl, hr⟩, hm⟩
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      abi, argRegs, stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6⟩ := h
    have hl' : (List.map BitVec.toNat (nB s₁ ++ eB s₁) ++ List.map BitVec.toNat (preW s₁)) ++ trace s₁ =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂) ++ List.map BitVec.toNat (preW s₂)) ++ trace s₂ := hl
    have hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
      simp [nB, eB, kOf, Spec.Rsa.bytesAt, h7, h9]
    have hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
      simp [preW, Spec.Rsa.wordsAt, a6]
    obtain ⟨h12, h3'⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
    obtain ⟨h1, h2⟩ := List.append_inj h12 hl1
    have inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
      fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
    have hne := inj h1
    obtain ⟨hn, he⟩ := List.append_inj hne (by simp [nB, kOf, Spec.Rsa.bytesAt, h7])
    refine ⟨hsp, fun r hr => ?_, fun j hj => ?_, hn, he, inj h2, h3'⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
    · match j, hj with
      | 0, _ => exact a0 | 1, _ => exact a1 | 2, _ => exact a2 | 3, _ => exact a3 | 4, _ => exact a4
      | 5, _ => exact a5 | 6, _ => exact a6
  sat := by
    implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
      stackArgs_seven, List.append_eq, rndStack, frameBytes, Impl.RsaPkcs1Sig.PPC64LE.frameBytes]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_encrypt_random` meets the shared contract. -/
theorem code_verified : Verified target code (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack) :=
  Verified.of_correct (k := contract) code_correct code_ct implies

end VG.Proof.RsaPkcs1Enc.PPC64LE.Rnd
