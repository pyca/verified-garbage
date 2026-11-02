module

import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Proof.RsaPss.EncodingContract
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's encoding on x86-64: the contract on the registers

`encK G` states `Proof.RsaPss.encodeContract G G` (with the stack the frame
and the calls use, `encStack`) on the registers and the stack
(`enc_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, and the return address of
its calls, which use no stack. -/
def encStack : Nat := 392 + 8

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

variable (G : Spec.Mgf1.Hash)

/-- `encode(em = rdi, em_len = rsi, digest = rdx, salt = rcx, salt_len = r8,
em_bits = r9, scratch = [rsp + 8], scratch_len = [rsp + 16])`. -/
def encK : Contract isa where
  pre s :=
    let em : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let dg : Region := ⟨s.gpr .rdx, G.len⟩
    let sa : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩
    encStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧
      s.rd = [dg, sa, args] ∧ s.wr = [em, scr] ∧
      em.Disjoint dg ∧ em.Disjoint sa ∧ em.Disjoint scr ∧ em.Disjoint args ∧
      dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint em ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint em ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + G.len ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ Proof.RsaPss.maxEmBits ∧
      (s.gpr .rsi).toNat = Spec.RsaPss.emLength (s.gpr .r9).toNat ∧
      Proof.RsaPss.encodingScratchWords ≤ (stackArg s 1).toNat
  post s s' :=
    match Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) G.len)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (s.gpr .r9).toNat with
    | some e => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.bytesAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = e
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- A state meeting `encK.pre`: a 64-byte encoding of 511 bits, a digest, an
empty salt, and the stack arguments at `0x10008`. -/
def encSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x4600 | .rcx => 0x4700 | .r8 => 0 | .r9 => 511
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1000A then 0x02 else if a = 0x10011 then 0x04 else 0
  rd := [⟨0x4600, G.len⟩, ⟨0x4700, 0⟩, ⟨0x10008, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 1024 * 8⟩]

/-- `encodeContract` is satisfiable for each of `MdHash`'s hash functions. -/
theorem enc_sat (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (Proof.RsaPss.encodeContract G G abi encStack).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.md5
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha1
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha224
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha256
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha384
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState Spec.Mgf1.sha512_256

theorem enc_implies (hsat : ∃ s, (Proof.RsaPss.encodeContract G G abi encStack).pre s) :
    (encK G).Implies (Proof.RsaPss.encodeContract G G abi encStack) where
  pre := by
    intro s h
    sig_pre [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] at h
    sig_pre [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] at h
    sig_split h
    sig_reduce [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, encK, encStack, stackArgs_two, List.append_eq] at h
    obtain ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, a0, a1⟩ := h
    refine ⟨?_, a0, a1⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64
