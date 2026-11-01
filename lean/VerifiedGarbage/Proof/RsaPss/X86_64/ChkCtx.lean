module

import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCtx
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's check of an encoding on x86-64: the contract on the registers

`chkK G` states `Proof.RsaPss.checkEncodingContract G G` (with the stack the
frame and the calls use, `chkStack`) on the registers and the stack
(`chk_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, and the return address of
its calls, which use no stack. -/
def chkStack : Nat := 392 + 8

variable (G : Spec.Mgf1.Hash)

/-- `check_encoding(digest = rdi, em = rsi, em_len = rdx, em_bits = rcx,
salt_len = r8, any_salt_len = r9d, scratch = [rsp + 8], scratch_len = [rsp + 16])`. -/
def chkK : Contract isa where
  pre s :=
    let dg : Region := ⟨s.gpr .rdi, G.len⟩
    let em : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 chkStack, chkStack⟩
    chkStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧
      s.rd = [dg, em, args] ∧ s.wr = [scr] ∧
      dg.Disjoint scr ∧ em.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint dg ∧ ret.Disjoint em ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint dg ∧ stk.Disjoint em ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + G.len ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ Proof.RsaPss.maxEmBits ∧
      (s.gpr .rdx).toNat = Spec.RsaPss.emLength (s.gpr .rcx).toNat ∧
      Proof.RsaPss.encodingScratchWords ≤ (stackArg s 1).toNat
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPss.verifyEncoding G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) G.len)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (s.gpr .rcx).toNat
        (Spec.RsaPss.expectedSaltLen (s.gpr .r8) ((s.gpr .r9).setWidth 32)) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32 ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- A state meeting `chkK.pre`: a 64-byte encoding of 511 bits, a digest,
and the stack arguments at `0x10008`. -/
def chkSatState : State where
  gpr r := match r with
    | .rdi => 0x4600 | .rsi => 0x1000 | .rdx => 64 | .rcx => 511 | .r8 => 0 | .r9 => 0
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000A then 0x02 else if a = 0x10011 then 0x04 else 0
  rd := [⟨0x4600, G.len⟩, ⟨0x1000, 64⟩, ⟨0x10008, 16⟩]
  wr := [⟨0x20000, 1024 * 8⟩]

theorem chk_sat (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.md5
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha1
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha224
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha256
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha384
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha512
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState Spec.Mgf1.sha512_256

theorem chk_implies (hsat : ∃ s, (Proof.RsaPss.checkEncodingContract G G abi chkStack).pre s) :
    (chkK G).Implies (Proof.RsaPss.checkEncodingContract G G abi chkStack) where
  pre := by
    intro s h
    sig_pre [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] at h
    sig_pre [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, chkK, chkStack, stackArgs_two, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, a0, a1⟩ := h
    refine ⟨?_, h9, a0, a1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64
