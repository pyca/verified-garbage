import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Rsa.X86_64.PrivChecked
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx`. -/
section

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
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩
    VG.Proof.Rsa.X86_64.stackBytes ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 120 ≤ 2 ^ 64 ∧
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

theorem private_checked_implies : chkContract.Implies (Spec.Rsa.privateCheckedContract abi VG.Proof.Rsa.X86_64.stackBytes) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq] at h
    sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [VG.Proof.Rsa.X86_64.stackArgs_fourteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13],
      hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, VG.Proof.Rsa.X86_64.chkContract, VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackArgs_fourteen, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Rsa.X86_64.chkSatState

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame`. -/
section

/-!
# `vg_rsa_private_checked` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, and the blocks
that store to its slots and read the function's stack arguments, at
`S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Addresses in the frame -/

theorem ea_sp (t : State) (d : Nat) : t.ea (VG.Impl.Rsa.X86_64.PrivChecked.sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.PrivChecked.sp, BitVec.ofInt_natCast]

theorem ea_sp_off {t : State} {S : Addr} (h : t.gpr .rsp = S) (d : Nat) : t.ea (VG.Impl.Rsa.X86_64.PrivChecked.sp d) = VG.Proof.Bignum.X86_64.off S d := by
  rw [VG.Proof.Rsa.X86_64.ea_sp, h]

/-- The function's stack argument `j`, from the frame at `S = rsp - frameBytes`. -/
theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 frameBytes) (j : Nat) :
    t.ea (VG.Impl.Rsa.X86_64.PrivChecked.arg j) = stackArgAddr s j := by
  rw [VG.Impl.Rsa.X86_64.PrivChecked.arg, VG.Proof.Rsa.X86_64.ea_sp, h, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-! ## The precondition, by name -/

/-- `chkContract.pre`, by name. -/
structure PreF (s : State) : Prop where
  sp1 : VG.Proof.Rsa.X86_64.stackBytes ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 120 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨stackArgAddr s 0, 112⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dis : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dps : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqs : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddps : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddqs : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqis : (⟨stackArg s 10, (stackArg s 11).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dsa : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKi : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wI : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wP : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wQ : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDp : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wDq : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wQi : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wS : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  hil : (stackArg s 1).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 3).toNat
  pl2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 5).toNat
  ql2 : (stackArg s 5).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 7).toNat = (stackArg s 3).toNat
  hqil : (stackArg s 11).toNat = (stackArg s 3).toNat
  hdql : (stackArg s 9).toNat = (stackArg s 5).toNat
  hsl : 16 * (s.gpr .rcx).toNat ≤ (stackArg s 13).toNat

theorem preF_of {s : State} (h : chkContract.pre s) : VG.Proof.Rsa.X86_64.PreF s := by
  simp only [VG.Proof.Rsa.X86_64.chkContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dis, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, -, -, -, -, -, -, -, -, dRs, -, dKo, dKn, dKe, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa,
    wO, wN, wE, wI, wP, wQ, wDp, wDq, wQi, wS, ⟨k1, k2⟩, hsi, hil, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql,
    hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dis, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, dRs, dKo, dKn, dKe, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa, wO, wN, wE, wI, wP, wQ, wDp,
    wDq, wQi, wS, k1, k2, hsi, hil, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, the caller's `out` and the working space:
all the function and its calls may write. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, VG.Proof.Rsa.X86_64.stackBytes⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩

theorem fb_eq (s : State) : VG.Proof.Rsa.X86_64.fb s = VG.Proof.Bignum.X86_64.off (s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) d, n⟩ (VG.Proof.Rsa.X86_64.stkR s) := by
  rw [VG.Proof.Rsa.X86_64.fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold VG.Proof.Rsa.X86_64.stackBytes; omega)

/-- The return address of a call from the frame. -/
theorem ret_sub (s : State) : Region.Sub (below (VG.Proof.Rsa.X86_64.fb s) 8) (VG.Proof.Rsa.X86_64.stkR s) := by
  rw [show below (VG.Proof.Rsa.X86_64.fb s) 8 = ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.Rsa.X86_64.stackBytes, 8⟩ by
    simp only [below, VG.Proof.Rsa.X86_64.fb, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
  exact Region.sub_prefix (by decide)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (VG.Proof.Rsa.X86_64.stkR s).Contains x 1) :
    frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Rsa.X86_64.fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, VG.Proof.Bignum.X86_64.ofs] at hlt ⊢; omega
  have := VG.Proof.Rsa.X86_64.frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] at this
  exact this x hc

/-- Between the calls, from the entry state `s`: in the frame, with `out`,
`n`, `n_len`, `e` and `e_len` in their slots, memory changed only where the
function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨VG.Proof.Rsa.X86_64.fb s, frameBytes⟩ :: s.wr
  mem : Frame [VG.Proof.Rsa.X86_64.stkR s, VG.Proof.Rsa.X86_64.outR s, VG.Proof.Rsa.X86_64.scrR s] s.mem t.mem
  sOut : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oOut = s.gpr .rdi
  sN : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oN = s.gpr .rdx
  sK : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oK = s.gpr .rcx
  sE : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oE = s.gpr .r8
  sEl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : VG.Proof.Rsa.X86_64.Env s t) (hp : VG.Proof.Rsa.X86_64.PreF s) : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Rsa.X86_64.fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by
    have := hp.sp1; simp only [VG.Proof.Rsa.X86_64.fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes VG.Proof.Rsa.X86_64.stackBytes at *
    omega)

/-- A buffer of the caller that the function does not write. -/
theorem Env.bytes {s t : State} (h : VG.Proof.Rsa.X86_64.Env s t) {p : Addr} {len : Nat} (hk : (VG.Proof.Rsa.X86_64.stkR s).Disjoint ⟨p, len⟩)
    (ho : (VG.Proof.Rsa.X86_64.outR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.Rsa.X86_64.scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.mem.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem Env.arg {s t : State} (h : VG.Proof.Rsa.X86_64.Env s t) (hp : VG.Proof.Rsa.X86_64.PreF s) {j : Nat} (hj : j < 14) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 112⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) (frameBytes + 8 + 8 * j) := by
  rw [VG.Proof.Bignum.X86_64.off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem fb_toNat {s : State} (hp : VG.Proof.Rsa.X86_64.PreF s) : (VG.Proof.Rsa.X86_64.fb s).toNat + frameBytes + 8 + 112 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [VG.Proof.Rsa.X86_64.fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes VG.Proof.Rsa.X86_64.stackBytes at *; omega

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem m) :
    Frame [VG.Proof.Rsa.X86_64.stkR s, VG.Proof.Rsa.X86_64.outR s, VG.Proof.Rsa.X86_64.scrR s] s.mem m :=
  fun x hx => h x (.inr (VG.Proof.Rsa.X86_64.outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : VG.Proof.Rsa.X86_64.PreF s) {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 14) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := VG.Proof.Rsa.X86_64.fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [VG.Proof.Rsa.X86_64.stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-! ## The CRT's arguments -/

def slotStores : List Instr :=
  [.store (VG.Impl.Rsa.X86_64.PrivChecked.sp oOut) .rdi, .store (VG.Impl.Rsa.X86_64.PrivChecked.sp oN) .rdx, .store (VG.Impl.Rsa.X86_64.PrivChecked.sp oK) .rcx, .store (VG.Impl.Rsa.X86_64.PrivChecked.sp VG.Impl.Rsa.X86_64.PrivChecked.oE) .r8, .store (VG.Impl.Rsa.X86_64.PrivChecked.sp oEl) .r9]

def copyArg (j : Nat) : List Instr := [.mov .rax (.mem (VG.Impl.Rsa.X86_64.PrivChecked.arg (j + 2))), .store (VG.Impl.Rsa.X86_64.PrivChecked.sp (8 * j)) .rax]

def crtRegs : List Instr :=
  lea .rdi VG.Impl.Rsa.X86_64.PrivChecked.oM ++ [.mov .rsi (.reg .rcx), .mov .r8 (.mem (VG.Impl.Rsa.X86_64.PrivChecked.arg 0)), .mov .r9 (.reg .rcx)]

theorem crtArgs_eq : crtArgs = VG.Proof.Rsa.X86_64.slotStores ++ ((List.range 12).flatMap VG.Proof.Rsa.X86_64.copyArg ++ VG.Proof.Rsa.X86_64.crtRegs) := rfl

theorem slotStores_ok {s t : State} (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) (hs : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Rsa.X86_64.fb s) frameBytes) :
    WP isa (.block VG.Proof.Rsa.X86_64.slotStores) t fun t' => t'.mem =
      ((((t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oOut) (t.gpr .rdi)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oN) (t.gpr .rdx)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oK) (t.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oE) (t.gpr .r8)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) oEl) (t.gpr .r9) ∧
      VG.Proof.MlKem.X86_64.Keep [] t t' :=
  WP.keep [] (by
    xrun [VG.Proof.Rsa.X86_64.slotStores, VG.Proof.Rsa.X86_64.ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oN) (by decide),
      hs.st (d := oK) (by decide), hs.st (d := VG.Impl.Rsa.X86_64.PrivChecked.oE) (by decide), hs.st (d := oEl) (by decide)]) rfl

/-- Stack argument `j + 2` to the frame's word `j`. -/
theorem copyArg_ok {s t : State} (hp : VG.Proof.Rsa.X86_64.PreF s) (hsp : t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s) (hs : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Rsa.X86_64.fb s) frameBytes)
    (hrd : t.rd = s.rd) (ho : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem t.mem) {j : Nat} (hj : j < 12) :
    WP isa (.block (VG.Proof.Rsa.X86_64.copyArg j)) t fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) (8 * j)) (stackArg s (j + 2)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have ha : InRegions (t.rd ++ t.wr) (stackArgAddr s (j + 2)) 8 :=
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
      by rw [stackArgAddr_eq s (j + 2)]; exact Offset.contains_base _ (by omega) (by omega)⟩
  exact WP.keep [.rax] (by
    xrun [VG.Proof.Rsa.X86_64.copyArg, VG.Proof.Rsa.X86_64.ea_arg hsp, VG.Proof.Rsa.X86_64.ea_sp, hsp, ha, VG.Proof.Rsa.X86_64.arg_outside hp ho (show j + 2 < 14 by omega),
      hs.st (d := 8 * j) (by unfold frameBytes; omega)]) rfl

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : VG.Proof.Rsa.X86_64.PreF s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), t.gpr .rsp = VG.Proof.Rsa.X86_64.fb s →
    VG.Proof.Bignum.X86_64.Scr t (VG.Proof.Rsa.X86_64.fb s) frameBytes → t.rd = s.rd → VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem t.mem →
    WP isa (.block ((List.range n).flatMap VG.Proof.Rsa.X86_64.copyArg)) t fun t' => VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem t'.mem ∧
      (∀ i < n, VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) = stackArg s (i + 2)) ∧
      (∀ d, 8 * n ≤ d → d + 8 ≤ frameBytes → VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.Rsa.X86_64.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) d) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t'
  | 0, _, t, _, _, _, ho => WP.block_nil ⟨ho, fun _ h => absurd h (by omega), fun _ _ _ => rfl, Keep.refl _ _⟩
  | n + 1, hn, t, hsp, hs, hrd, ho => by
    have hF := VG.Proof.Rsa.X86_64.fb_toNat hp
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.Rsa.X86_64.copies_ok hp n (by omega) t hsp hs hrd ho) fun t₁ ⟨ho₁, hw₁, hk₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.Rsa.X86_64.copyArg_ok hp ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) (k₁.2.1.trans hrd) ho₁
      (show n < 12 by omega)) fun t' ⟨hm, k'⟩ => ⟨?_, fun i hi => ?_, fun d hd hd' => ?_,
        (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      exact fun x hx => (VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega)).trans
        (ho₁ x hx)
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(VG.Proof.Bignum.X86_64.writeW_outside t₁.mem (VG.Proof.Rsa.X86_64.fb s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
          (.inl (by omega)) (by unfold frameBytes at *; omega)]
        exact hw₁ i hi
      · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
    · rw [hm, (VG.Proof.Bignum.X86_64.writeW_outside t₁.mem (VG.Proof.Rsa.X86_64.fb s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
        (.inr (by omega)) (by unfold frameBytes at *; omega)]
      exact hk₁ d (by omega) hd'

/-- A word past a store to another word of the frame. -/
theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) base d' = VG.Proof.Bignum.X86_64.word m base d' :=
  (VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then VG.Proof.Rsa.X86_64.fb s else s.gpr r := rfl

/-- The frame's push, and the CRT's arguments: `Env`, the CRT's stack
arguments in the frame, and its arguments in registers. -/
theorem crtArgs_ok {s : State} (hp : VG.Proof.Rsa.X86_64.PreF s) :
    WP isa (.block crtArgs) (allocState frameBytes s) fun t => VG.Proof.Rsa.X86_64.Env s t ∧
      VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem t.mem ∧ (∀ i < 12, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) (8 * i) = stackArg s (i + 2)) ∧
      t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx := by
  have hF := VG.Proof.Rsa.X86_64.fb_toNat hp
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = VG.Proof.Rsa.X86_64.fb s := rfl
  have hs : VG.Proof.Bignum.X86_64.Scr A (VG.Proof.Rsa.X86_64.fb s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  rw [VG.Proof.Rsa.X86_64.crtArgs_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.slotStores_ok hsp hs) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : VG.Proof.Bignum.X86_64.Outside (VG.Proof.Rsa.X86_64.fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Rsa.X86_64.fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    simp only [oOut, oN, oK, VG.Impl.Rsa.X86_64.PrivChecked.oE, oEl] at *
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega)]
    rfl
  have hslots : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) oOut = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) oN = s.gpr .rdx ∧
      VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) oK = s.gpr .rcx ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oE = s.gpr .r8 ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [VG.Proof.Rsa.X86_64.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, oOut, oN, oK, VG.Impl.Rsa.X86_64.PrivChecked.oE, oEl]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.copies_ok hp 12 (le_refl _) t₁ ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) k₁.2.1 ho₁)
    fun t₂ ⟨ho₂, hw₂, hk₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hrd₂ : InRegions (t₂.rd ++ t₂.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
      rw [k12.2.1, show A.rd = s.rd from rfl, hp.hrd]
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.mono (WP.keep [.rdi, .rsi, .r8, .r9] (Q := fun t => t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.Rsa.X86_64.fb s) VG.Impl.Rsa.X86_64.PrivChecked.oM ∧
      t.gpr .rsi = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx ∧ t.mem = t₂.mem) (by
    xrun [VG.Proof.Rsa.X86_64.crtRegs, lea, List.cons_append, List.nil_append, sx_ofNat (show VG.Impl.Rsa.X86_64.PrivChecked.oM < 2 ^ 31 by decide), VG.Impl.Rsa.X86_64.PrivChecked.arg, VG.Proof.Rsa.X86_64.ea_sp, hsp,
      show VG.Proof.Rsa.X86_64.fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (VG.Proof.Rsa.X86_64.stackArgAddr_fb s 0).symm, k12.gpr (show Reg.rsp ∉ [] ++ [Reg.rax] by decide),
      k12.gpr (show Reg.rcx ∉ [] ++ [Reg.rax] by decide), hrd₂, VG.Proof.Rsa.X86_64.arg_outside hp ho₂ (show 0 < 14 by decide)]
    exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨hdi, hsi, h8, h9, hm⟩, k⟩ => ?_
  have k' := k12.trans k
  have hw : ∀ d, 96 ≤ d → d + 8 ≤ frameBytes → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.Rsa.X86_64.fb s) d = VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.Rsa.X86_64.fb s) d := fun d hd hd' => by
    rw [hm]; exact hk₂ d (by omega) hd'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hslots
  refine ⟨⟨(k'.gpr (by decide)).trans hsp, k'.2.1, k'.2.2, VG.Proof.Rsa.X86_64.frame_of_outside (hm ▸ ho₂),
      (hw _ (by decide) (by decide)).trans h1, (hw _ (by decide) (by decide)).trans h2,
      (hw _ (by decide) (by decide)).trans h3, (hw _ (by decide) (by decide)).trans h4,
      (hw _ (by decide) (by decide)).trans h5⟩, hm ▸ ho₂, fun i hi => hm ▸ hw₂ i hi, hdi, hsi,
    (k'.gpr (by decide)).trans rfl, (k'.gpr (by decide)).trans rfl, h8, h9⟩

end VG.Proof.Rsa.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl`. -/
section

/-!
# Implementations of `vg_rsa_private_crt` on x86-64

A `CrtImpl` is what `vg_rsa_private_checked` needs of the implementation of
`vg_rsa_private_crt` it calls, so that its proof holds for each of them:
each is a variant of the interface `RsaPrivateCrt` on x86-64
(`Variants/RsaPrivateCrt/X86_64/`), and `vg_rsa_private_checked`
(`Generic/RsaPrivateCrt/X86_64/Rsa.lean`) is emitted once for each. Every
implementation is proven against `crtContract`, and makes no calls. It
comes with the Montgomery multiplication of the implementations of
`vg_rsa_public_precompute` and `vg_rsa_public_precomputed_checked` that
check its result, which need no more CPU features.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64

/-- An implementation of `vg_rsa_private_crt` on x86-64. -/
structure CrtImpl where
  /-- Its symbol and code. -/
  name : String
  code : Prog isa
  /-- It makes no calls. -/
  depth : code.depth = 0
  ok : ∀ s, crtContract.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ crtContract.post s s'
  ct : ConstantTime isa crtContract.pre crtContract.pub code
  /-- It never writes the stack pointer. -/
  nosp : NoSp code
  spSafe : code.all (fun i => !isa.writesSp i) = true
  /-- The Montgomery multiplication of `vg_rsa_public_precompute` and
  `vg_rsa_public_precomputed_checked`, and the suffix of their names. -/
  mont : Mont
  montSuffix : String
  pcMx : (Precompute.code mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  pdMx : (Precomputed.code mont.mm).allInstrs (fun i => !loadsMxcsr i) = true
  pcNosp : NoSp (Precompute.code mont.mm)
  pdNosp : NoSp (Checked.precomputedChecked mont.mm)
  pcDepth : (Precompute.code mont.mm).depth = 0
  pdDepth : (Checked.precomputedChecked mont.mm).depth = 0
  pcSpSafe : (Precompute.code mont.mm).all (fun i => !isa.writesSp i) = true
  pdSpSafe : (Checked.precomputedChecked mont.mm).all (fun i => !isa.writesSp i) = true
  /-- What the names of `vg_rsa_private_checked`'s instances end with (e.g.
  `_adx`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code and that of the public operation require,
  which `vg_rsa_private_checked` requires too. -/
  features : List String

/-- `NoSp` by evaluating the code. -/
theorem noSp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

end VG.Proof.Rsa.X86_64

end
