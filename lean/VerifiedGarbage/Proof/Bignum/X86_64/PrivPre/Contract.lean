module

public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# `vg_rsa_private_precompute` on x86-64: the contract on the registers

`ppContract` states the shared contract on the registers and the stack
(`pp_implies`), with 8 bytes of stack, the return address of the calls of
Montgomery multiplication.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64

/-- `vg_rsa_private_precompute(pre = rdi, pre_len = rsi, n = rdx,
n_len = rcx, p = r8, p_len = r9, q = [rsp + 8], q_len = [rsp + 16],
scratch = [rsp + 24], scratch_len = [rsp + 32])`. -/
def ppContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let p : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let q : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [n, p, q, args] ∧ s.wr = [pre, scr] ∧
      pre.Disjoint n ∧ pre.Disjoint p ∧ pre.Disjoint q ∧ pre.Disjoint scr ∧ pre.Disjoint args ∧
      n.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint pre ∧ ret.Disjoint n ∧ ret.Disjoint p ∧ ret.Disjoint q ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧
      (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
        (stackArg s 1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    match Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) with
    | some ws => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = ws
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat = List.replicate (s.gpr .rsi).toNat 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `ppContract.pre`: a 512-bit modulus, one-byte primes,
and the stack arguments at `0x6008`. -/
def ppSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 20 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x6009 then 0x40 else bif Nat.beq a.toNat 0x6010 then 1
    else bif Nat.beq a.toNat 0x6019 then 0x80 else bif Nat.beq a.toNat 0x6020 then 0x20
    else bif Nat.beq a.toNat 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 160⟩, ⟨0x8000, 8448⟩]

theorem pp_implies : ppContract.Implies (Spec.Rsa.privatePrecomputeContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    refine ⟨?_, a0, a1, a2, a3, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argRegs, ppContract, stackArgs_four, List.append_eq] [ppSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ppSatState

end VG.Proof.Bignum.X86_64.PrivPre
