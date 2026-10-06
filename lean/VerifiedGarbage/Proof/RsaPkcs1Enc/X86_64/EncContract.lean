import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Encrypt

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the contracts on the registers

`encK` states the shared contract `Spec.RsaPkcs1Enc.encryptContract` (with
the stack the frame and the call use, `encStack`) on the registers and the
stack (`encrypt_implies`).

`pubChkK` is the contract of `vg_rsa_public_checked` on the registers: that
of `vg_rsa_public` (`pubContract`), with BoringSSL's limits on `e`
(`Spec.Rsa.publicOpChecked`). A `PubImpl` is an implementation of it, which
the proof of encryption is written for.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## `vg_rsa_public_checked` -/

/-- `pubContract`, with BoringSSL's limits on `e` (`publicOpChecked`). -/
def pubChkK : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post s s' := Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- An implementation of `vg_rsa_public_checked`: its symbol and code,
correct and constant time under `pubChkK`, making no calls and using no
stack. -/
structure PubImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pubChkK.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pubChkK.post s s'
  ct : ConstantTime isa pubChkK.pre pubChkK.pub code
  nosp : NoSp code
  depth : code.depth = 0
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-! ## Encryption -/

/-- The stack below the stack pointer the function uses: its frame, and the
return address of its call. -/
def encStack : Nat := Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes + 8

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- `vg_rsa_pkcs1_encrypt(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, msg = [rsp + 8], msg_len = [rsp + 16], ps = [rsp + 24],
ps_len = [rsp + 32], scratch = [rsp + 40], scratch_len = [rsp + 48])`,
using `encStack` bytes of stack. -/
def encK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let msg : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let ps : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩
    encStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧
      s.rd = [n, e, msg, ps, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint msg ∧ out.Disjoint ps ∧ out.Disjoint scr ∧
      out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ msg.Disjoint scr ∧ ps.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint msg ∧ ret.Disjoint ps ∧
      ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint msg ∧ stk.Disjoint ps ∧
      stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      (stackArg s 1).toNat + 11 ≤ (s.gpr .rcx).toNat ∧
      (stackArg s 3).toNat = (s.gpr .rcx).toNat - (stackArg s 1).toNat - 3 ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 5).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 6).map (stackArg s₁) = (List.range 6).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- A state meeting `encK.pre`: a 512-bit modulus, a one-byte `e`, an empty
message, a padding string of 61 bytes, and the stack arguments at
`0x10008`. -/
def encSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x40 else if a = 0x10019 then 0x41 else if a = 0x10020 then 61
    else if a = 0x1002A then 0x02 else if a = 0x10031 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x10008, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8192⟩]

theorem encrypt_implies : encK.Implies (Spec.RsaPkcs1Enc.encryptContract abi encStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [stackArgs_six, a0, a1, a2, a3, a4, a5], hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Enc.encryptContract, Spec.RsaPkcs1Enc.encryptSig, abi, argRegs, encK, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_six, List.append_eq] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatState

end VG.Proof.RsaPkcs1Enc.X86_64
