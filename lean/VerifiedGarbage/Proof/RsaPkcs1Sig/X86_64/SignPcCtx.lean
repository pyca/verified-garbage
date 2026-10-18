module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCtx
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_pkcs1_sign_precomputed` on x86-64: the contract on the registers

`sigPcContract` states the shared contract (with the stack the frame and the
call of `vg_rsa_private_checked_precomputed` use, `sigPcStack`) on the
registers and the stack (`signPc_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_sign_precomputed` uses:
its frame of 1208 bytes, the return address of its call, and the 1208 bytes
its callee `vg_rsa_private_checked_precomputed` uses. -/
def sigPcStack : Nat := 2424

theorem stackArgs_seventeen (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

/-- `vg_rsa_pkcs1_sign_precomputed(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), digest = [rsp + 16],
digest_len = [rsp + 24], p = [rsp + 32], p_len = [rsp + 40], q = [rsp + 48],
q_len = [rsp + 56], dp = [rsp + 64], dp_len = [rsp + 72], dq = [rsp + 80],
dq_len = [rsp + 88], qinv = [rsp + 96], qinv_len = [rsp + 104],
scratch = [rsp + 112], scratch_len = [rsp + 120], pre = [rsp + 128],
pre_len = [rsp + 136])`, using `sigPcStack` bytes of stack. -/
def sigPcContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let dig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let p : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
    let q : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
    let dp : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
    let dq : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
    let qi : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
    let scr : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
    let pre : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 136⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 sigPcStack, sigPcStack⟩
    sigPcStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 144 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, p, q, dp, dq, qi, pre, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint dig ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint pre ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ pre.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint pre ∧
      ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint pre ∧
      stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧ (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64 ∧
      (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64 ∧ (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64 ∧
      (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 4).toNat ∧ (stackArg s 4).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 6).toNat ∧
      (stackArg s 6).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 8).toNat = (stackArg s 4).toNat ∧
      (stackArg s 12).toNat = (stackArg s 4).toNat ∧ (stackArg s 10).toNat = (stackArg s 6).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 14).toNat ∧
      (stackArg s 16).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (stackArg s 4).toNat
        (stackArg s 6).toNat
  post s s' :=
    Spec.Rsa.privatePreOk s.mem (s.gpr .rdx) (s.gpr .rcx).toNat (stackArg s 3) (stackArg s 4).toNat
      (stackArg s 5) (stackArg s 6).toNat (stackArg s 15) (stackArg s 16).toNat →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
        ((stackArg s 0).setWidth 32).toNat
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      (List.range 16).map (fun i => stackArg s₁ (i + 1)) = (List.range 16).map (fun i => stackArg s₂ (i + 1)) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.privatePreLeak s₁.mem (stackArg s₁ 15) (s₁.gpr .rcx).toNat =
        Spec.Rsa.privatePreLeak s₂.mem (stackArg s₂ 15) (s₂.gpr .rcx).toNat

/-- A state meeting `sigPcContract.pre`: `sigSatState`'s, with `pre` of 20
words at `0x5000`. -/
def sigPcSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10078 then 0x20
    else bif Nat.beq a.toNat 0x10011 then 0x40 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x41 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x42 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x43 else bif Nat.beq a.toNat 0x10048 then 1
    else bif Nat.beq a.toNat 0x10051 then 0x44 else bif Nat.beq a.toNat 0x10058 then 1
    else bif Nat.beq a.toNat 0x10061 then 0x45 else bif Nat.beq a.toNat 0x10068 then 1
    else bif Nat.beq a.toNat 0x10072 then 0x02 else bif Nat.beq a.toNat 0x10079 then 0x04
    else bif Nat.beq a.toNat 0x10081 then 0x50 else bif Nat.beq a.toNat 0x10088 then 20 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x5000, 160⟩, ⟨0x10008, 136⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem signPc_implies : sigPcContract.Implies (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigPcStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
      abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
      abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
      abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig,
      abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14, a15, a16⟩ := h
    obtain ⟨hne, hp⟩ := List.append_inj hl (by simp only [List.length_map, List.length_append, bytesAt_length, hcx, h9])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hne
    refine ⟨?_, a0, ?_, hn, he, hp⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.map_append,
        a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16]
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argRegs, sigPcContract, sigPcStack, stackArgs_seventeen, List.append_eq]
    [sigPcSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using sigPcSatState

end VG.Proof.RsaPkcs1Sig.X86_64
