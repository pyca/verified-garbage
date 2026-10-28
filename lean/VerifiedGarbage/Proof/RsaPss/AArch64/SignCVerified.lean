module

import VerifiedGarbage.Proof.RsaPss.AArch64.SignCCt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callee
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignPre
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.SignPre
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCTop

/-!
# RSASSA-PSS signing on AArch64, calling `encode`: `Verified`

The shared contract (`Spec.RsaPss.signContract`, with the stack of the frame
and of the deeper callee, `stk K`) from correctness (`code_ok`), constant
time (`code_ct`) and a state meeting the precondition (`sign_sat`, for the
stack of `vg_rsa_private_checked`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.RsaPkcs1Sig.AArch64.Sgn (stackArgs_thirteen)
open VG.Proof.Pbkdf2.Md.AArch64 (mdHashes)
open VG.Proof.RsaPss.AArch64 (EncImpl)

section
variable {G : Spec.Mgf1.Hash} (e : EncImpl G) (c : PrivChecked) {K : Nat} (heK : e.stack ≤ K) (hcK : c.stack ≤ K)

include heK hcK in
theorem code_correct (s : State) (h : (Spec.RsaPss.signContract G G abi (stk K)).pre s) :
    ∃ t s', Exec isa (signC e.name e.code c.name c.code) s t s' ∧ abiPreserved s s' ∧
      (Spec.RsaPss.signContract G G abi (stk K)).post s s' := by
  obtain ⟨t, s', he, habi, hr⟩ := code_ok e c heK hcK (preS_of G h)
  refine ⟨t, s', he, habi, ?_⟩
  sig_post [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stackArgs_thirteen, List.append_eq]
  exact hr

include heK hcK in
theorem code_constantTime :
    ConstantTime isa (Spec.RsaPss.signContract G G abi (stk K)).pre
      (Spec.RsaPss.signContract G G abi (stk K)).pub (signC e.name e.code c.name c.code) :=
  RelCT.constantTime ((code_ct e c heK hcK).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨preS_of G h₁, PubS.refl s₁⟩, preS_of G h₂, pubS_of G hp⟩) fun _ _ h => h)

include heK hcK in
theorem code_verified (hsat : ∃ s, (Spec.RsaPss.signContract G G abi (stk K)).pre s) :
    Verified AArch64.target (signC e.name e.code c.name c.code) (Spec.RsaPss.signContract G G abi (stk K)) :=
  ⟨code_correct e c heK hcK, code_constantTime e c heK hcK, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A 512-bit modulus, one-byte `e` and key parts, the digest, a one-byte
salt, a working space of 2048 words, and the stack pointer at `2^40`, far
above them. -/
def satState (G : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x1000 | .x3 => 64 | .x4 => 0x2000 | .x5 => 1 | .x6 => 0x3000
    | .x7 => 1 | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000060 then 0x20
    else bif Nat.beq a.toNat 0x10000000001 then 0x60 else bif Nat.beq a.toNat 0x10000000008 then 1
    else bif Nat.beq a.toNat 0x10000000011 then 0x70 else bif Nat.beq a.toNat 0x10000000018 then 1
    else bif Nat.beq a.toNat 0x10000000021 then 0x80 else bif Nat.beq a.toNat 0x10000000028 then 1
    else bif Nat.beq a.toNat 0x10000000031 then 0x90 else bif Nat.beq a.toNat 0x10000000038 then 1
    else bif Nat.beq a.toNat 0x10000000041 then 0xA0
    else bif Nat.beq a.toNat 0x10000000049 then 0xB0 else bif Nat.beq a.toNat 0x10000000050 then 1
    else bif Nat.beq a.toNat 0x1000000005A then 1 else bif Nat.beq a.toNat 0x10000000061 then 8
    else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x6000, 1⟩, ⟨0x7000, 1⟩, ⟨0x8000, 1⟩, ⟨0x9000, 1⟩,
    ⟨0xA000, G.len⟩, ⟨0xB000, 1⟩, ⟨0x10000000000, 104⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 2080 * 8⟩]

/-- `signContract` is satisfiable for each of `MdHash`'s hash functions, with
the stack of the frame and `vg_rsa_private_checked`'s 3248 bytes. -/
theorem sign_sat {G : Spec.Mgf1.Hash} (hG : G ∈ mdHashes) :
    ∃ s, (Spec.RsaPss.signContract G G abi (stk 3248)).pre s := by
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaPss.signContract, Spec.RsaPss.signSig, abi, argRegs, stk, frameBytes,
      stackArgs_thirteen, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using satState Spec.Mgf1.sha512_256

end VG.Proof.RsaPss.AArch64.Sgn
