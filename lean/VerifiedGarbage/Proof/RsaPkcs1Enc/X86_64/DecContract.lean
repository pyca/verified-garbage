import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Decrypt
import VerifiedGarbage.Proof.Framework.X86_64.CallSp

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the contracts on the registers

`decK` states the shared contract `Spec.RsaPkcs1Enc.decryptContract` (with
the stack the frame and the calls use, `decStack`) on the registers and the
stack (`decrypt_implies`).

`privK` is the contract of `vg_rsa_private_checked` on the registers, using
`privStack` bytes of stack: that of `Spec.Rsa.privateCheckedContract`. A
`PrivImpl` is an implementation of it, which the proof of decryption is
written for.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## `vg_rsa_private_checked` -/

/-- The stack `vg_rsa_private_checked` uses below its return address. -/
def privStack : Nat := 3248

theorem stackArgs_fourteen (s : State) :
    List.map (stackArg s) (List.range 14) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13] := rfl

/-- `vg_rsa_private_checked(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, input = [rsp + 8], input_len = [rsp + 16],
p = [rsp + 24], p_len = [rsp + 32], q = [rsp + 40], q_len = [rsp + 48],
dp = [rsp + 56], dp_len = [rsp + 64], dq = [rsp + 72], dq_len = [rsp + 80],
qinv = [rsp + 88], qinv_len = [rsp + 96], scratch = [rsp + 104],
scratch_len = [rsp + 112])`, using `privStack` bytes of stack. -/
def privK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let inp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let p : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let q : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dp : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let dq : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let qi : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
    let scr : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 112⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 privStack, privStack⟩
    privStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 120 ≤ 2 ^ 64 ∧
      s.rd = [n, e, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint inp ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint inp ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64 ∧
      (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 3).toNat ∧ (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 5).toNat ∧
      (stackArg s 5).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      (stackArg s 11).toNat = (stackArg s 3).toNat ∧ (stackArg s 9).toNat = (stackArg s 5).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 13).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 3).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 14).map (stackArg s₁) = (List.range 14).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- An implementation of `vg_rsa_private_checked`: its symbol and code,
correct and constant time under `privK`, writing `rsp` only by its own
frames, which with its calls use at most `privStack` bytes of stack. -/
structure PrivImpl where
  name : String
  code : Prog isa
  ok : ∀ s, privK.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ privK.post s s'
  ct : ConstantTime isa privK.pre privK.pub code
  spSafe : code.all (fun i => !isa.writesSp i) = true
  depth : code.x86_64Depth ≤ privStack

/-! ## Decryption -/

/-- The stack below the stack pointer the function uses: its frame, the
return address of its calls, and below it what `vg_rsa_private_checked`
uses (more than HMAC's functions do). -/
def decStack : Nat := Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes + 8 + privStack

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- `vg_rsa_pkcs1_decrypt(out = rdi, out_len = rsi, msg_len = rdx, n = rcx,
n_len = r8, e = r9, e_len = [rsp + 8], d = [rsp + 16], d_len = [rsp + 24],
input = [rsp + 32], input_len = [rsp + 40], p = [rsp + 48], p_len = [rsp + 56],
q = [rsp + 64], q_len = [rsp + 72], dp = [rsp + 80], dp_len = [rsp + 88],
dq = [rsp + 96], dq_len = [rsp + 104], qinv = [rsp + 112],
qinv_len = [rsp + 120], scratch = [rsp + 128], scratch_len = [rsp + 136])`,
using `decStack` bytes of stack: what of the shared contract the proof
uses. -/
def decK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ml : Region := ⟨s.gpr .rdx, 8⟩
    let n : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let e : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
    let d : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let inp : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
    let p : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
    let q : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
    let dp : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
    let dq : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
    let qi : Region := ⟨stackArg s 13, (stackArg s 14).toNat⟩
    let scr : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 136⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩
    decStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 144 ≤ 2 ^ 64 ∧
      s.rd = [n, e, d, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, ml, scr] ∧
      out.Disjoint ml ∧ out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint d ∧ out.Disjoint inp ∧
      out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧
      out.Disjoint scr ∧ out.Disjoint args ∧
      ml.Disjoint n ∧ ml.Disjoint e ∧ ml.Disjoint d ∧ ml.Disjoint inp ∧ ml.Disjoint p ∧ ml.Disjoint q ∧
      ml.Disjoint dp ∧ ml.Disjoint dq ∧ ml.Disjoint qi ∧ ml.Disjoint scr ∧ ml.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ d.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧
      q.Disjoint scr ∧ dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint ml ∧ ret.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint ml ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint d ∧
      stk.Disjoint inp ∧ stk.Disjoint p ∧ stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧
      stk.Disjoint qi ∧ stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧ (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64 ∧
      (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64 ∧ (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat + (stackArg s 14).toNat ≤ 2 ^ 64 ∧
      (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .r8).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .r8).toNat ∧
      (stackArg s 4).toNat = (s.gpr .r8).toNat ∧
      1 ≤ (stackArg s 0).toNat ∧ (stackArg s 0).toNat ≤ (s.gpr .r8).toNat ∧
      1 ≤ (stackArg s 2).toNat ∧ (stackArg s 2).toNat ≤ (s.gpr .r8).toNat ∧
      1 ≤ (stackArg s 6).toNat ∧ (stackArg s 6).toNat < (s.gpr .r8).toNat ∧
      1 ≤ (stackArg s 8).toNat ∧ (stackArg s 8).toNat < (s.gpr .r8).toNat ∧
      (stackArg s 10).toNat = (stackArg s 6).toNat ∧ (stackArg s 14).toNat = (stackArg s 6).toNat ∧
      (stackArg s 12).toNat = (stackArg s 8).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 16).toNat
  post s s' :=
    Spec.RsaPkcs1Enc.writtenMsg s'.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 8).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 8).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 13) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (s.gpr .r8).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 17).map (stackArg s₁) = (List.range 17).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat

/-- A state meeting `decK.pre`: a 512-bit modulus, one-byte `e`, `d`, primes,
exponents and `qInv`, and the stack arguments at `0x10008`. -/
def decSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 1 else if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10021 then 0x41 else if a = 0x10028 then 64 else if a = 0x10031 then 0x42
    else if a = 0x10038 then 1 else if a = 0x10041 then 0x43 else if a = 0x10048 then 1
    else if a = 0x10051 then 0x44 else if a = 0x10058 then 1 else if a = 0x10061 then 0x45
    else if a = 0x10068 then 1 else if a = 0x10071 then 0x46 else if a = 0x10078 then 1
    else if a = 0x10082 then 0x02 else if a = 0x10089 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 64⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x4600, 1⟩, ⟨0x10008, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 8192⟩]

theorem decrypt_implies : decK.Implies (Spec.RsaPkcs1Enc.decryptContract abi decStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h8]) hl
    refine ⟨?_, by simp only [stackArgs_seventeen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16], hn, by have := he; rwa [← a0] at this⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, decK, decStack, privStack, Impl.RsaPkcs1Enc.X86_64.Decrypt.frameBytes, stackArgs_seventeen, List.append_eq] [decSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using decSatState

end VG.Proof.RsaPkcs1Enc.X86_64
