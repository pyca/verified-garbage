import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Spec.RsaOaep.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash

/-!
# RSAES-OAEP encryption on x86-64: the contract on the registers

`encK H G` states `Spec.RsaOaep.encryptContract H G` (with the stack the
frame and the calls use, `encStack`) on the registers and the stack
(`enc_implies`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame of 296 bytes, and the 16
bytes below it that the calls of the streaming hash functions use (the
public operation only its return address). -/
def encStack : Nat := 296 + 16

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6] := rfl

variable (H G : Spec.Mgf1.Hash)

/-- `encrypt(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8,
e_len = r9, label = [rsp + 8], label_len, msg, msg_len, seed, scratch,
scratch_len = [rsp + 56])`. -/
def encK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let lb : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let ms : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let sd : Region := ⟨stackArg s 4, H.len⟩
    let scr : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 56⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩
    encStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧
      s.rd = [n, e, lb, ms, sd, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint lb ∧ out.Disjoint ms ∧ out.Disjoint sd ∧
      out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ lb.Disjoint scr ∧ ms.Disjoint scr ∧ sd.Disjoint scr ∧
      scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint lb ∧ ret.Disjoint ms ∧
      ret.Disjoint sd ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint lb ∧ stk.Disjoint ms ∧
      stk.Disjoint sd ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + H.len ≤ 2 ^ 64 ∧
      (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 6).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaOaep.encrypt H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) H.len))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 7).map (stackArg s₁) = (List.range 7).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- A state meeting `encK.pre`: a 512-bit modulus, a one-byte `e`, an empty
label and message, and the seed at `0x4600`. -/
def encSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x41 else if a = 0x10019 then 0x42 else if a = 0x10029 then 0x46
    else if a = 0x10032 then 0x02 else if a = 0x10039 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 0⟩, ⟨0x4200, 0⟩, ⟨0x4600, H.len⟩, ⟨0x10008, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2048 * 8⟩]

/-- `encryptContract` is satisfiable for each of `MdHash`'s hash functions. -/
theorem enc_sat (hH : H ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (Spec.RsaOaep.encryptContract H G abi encStack).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
      stackArgs_seven, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512_256

theorem enc_implies (hsat : ∃ s, (Spec.RsaOaep.encryptContract H G abi encStack).pre s) :
    (encK H G).Implies (Spec.RsaOaep.encryptContract H G abi encStack) where
  pre := by
    intro s h
    sig_pre [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack, stackArgs_seven,
      List.append_eq] at h
    sig_pre [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack, stackArgs_seven,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack, stackArgs_seven,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack,
    stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, abi, argRegs, encK, encStack, stackArgs_seven,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [stackArgs_seven, a0, a1, a2, a3, a4, a5, a6], hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaOaep.X86_64
