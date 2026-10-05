import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked

/-!
# `vg_rsa_private_checked` on x86-64: the contract on the registers

`chkContract` states the shared contract (with the stack the frame and the
calls use, `stackBytes`) on the registers and the stack
(`private_checked_implies`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer the function uses: its frame, and the
return address of its calls (which use none). -/
def stackBytes : Nat := 3248

theorem stackArgs_fourteen (s : State) :
    List.map (stackArg s) (List.range 14) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13] := rfl

/-- `vg_rsa_private_checked(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, input = [rsp + 8], input_len = [rsp + 16],
p = [rsp + 24], p_len = [rsp + 32], q = [rsp + 40], q_len = [rsp + 48],
dp = [rsp + 56], dp_len = [rsp + 64], dq = [rsp + 72], dq_len = [rsp + 80],
qinv = [rsp + 88], qinv_len = [rsp + 96], scratch = [rsp + 104],
scratch_len = [rsp + 112])`, using `stackBytes` bytes of stack. -/
def chkContract : Contract isa where
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
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 120 ≤ 2 ^ 64 ∧
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

/-- A state meeting `chkContract.pre`: a 512-bit modulus, a one-byte `e`,
one-byte primes, exponents and `qInv`, and the stack arguments at
`0x10008`. -/
def chkSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x40 else if a = 0x10010 then 0x40 else if a = 0x10019 then 0x41
    else if a = 0x10020 then 1 else if a = 0x10029 then 0x42 else if a = 0x10030 then 1
    else if a = 0x10039 then 0x43 else if a = 0x10040 then 1 else if a = 0x10049 then 0x44
    else if a = 0x10050 then 1 else if a = 0x10059 then 0x45 else if a = 0x10060 then 1
    else if a = 0x1006A then 0x02 else if a = 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10008, 112⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8192⟩]

theorem private_checked_implies : chkContract.Implies (Spec.Rsa.privateCheckedContract abi stackBytes) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq] at h
    sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [stackArgs_fourteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13],
      hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, chkContract, stackBytes, stackArgs_fourteen, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using chkSatState

end VG.Proof.Rsa.X86_64
