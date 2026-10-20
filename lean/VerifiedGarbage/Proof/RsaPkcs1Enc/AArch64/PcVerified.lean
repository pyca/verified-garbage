module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on AArch64: the shared contract

`contract` implies the shared contract (`implies`), which a state with 16
words of `pre` meets (`sat`, with the callee's 16 bytes of stack): the
function, calling any precomputed public operation `c`, is verified against
it (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc

open VG VG.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

theorem implies (P : Nat) (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)).pre s) :
    (contract P).Implies (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)) where
  pre := fun _ h => h
  post := by
    rintro s s' - h
    sig_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
      AArch64.abi, AArch64.argRegs, stackArgs_six, List.append_eq]
    exact h
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
      AArch64.abi, AArch64.argRegs, stackArgs_six, List.append_eq] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_split hb (by rw [bytesAt_length, bytesAt_length, h3])
    exact ⟨⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, hn, he⟩, a4, a5, hq'⟩
  sat := hsat

/-- `encSatState`, with 16 words of `pre` at `0x5000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10018 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10008 then 61
    else bif Nat.beq a.toNat 0x10012 then 0x02 else bif Nat.beq a.toNat 0x10019 then 0x04
    else bif Nat.beq a.toNat 0x10021 then 0x50 else bif Nat.beq a.toNat 0x10028 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x5000, 128⟩, ⟨0x10000, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

/-- It meets the shared contract with 16 bytes of stack for the callee. -/
theorem sat : ∃ s, (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (16 + 1088)).pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    AArch64.abi, AArch64.argRegs, stackArgs_six, List.append_eq] [satState, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling the precomputed public
operation `c`, meets the shared contract. -/
theorem code_verified (c : PdChecked)
    (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    Verified AArch64.target (Impl.RsaPkcs1Enc.AArch64.Precomputed.code c.name c.code)
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)) :=
  Verified.of_correct (k := contract c.stack) (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := code_ok c h
    exact ⟨t, s', he, hp⟩) (code_constantTime c) (implies c.stack hsat)

end VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc
