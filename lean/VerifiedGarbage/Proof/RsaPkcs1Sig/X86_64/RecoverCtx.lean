import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the contract on the registers

`recContract` states the shared contract (with the stack the frame and the
call use, `verStack`, as for `vg_rsa_pkcs1_verify`) on the registers and the
stack (`recover_implies`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- `vg_rsa_pkcs1_recover(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def recContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩
    verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, sig, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint sig ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      (∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h ∧
        (s.gpr .rsi).toNat = h.len) ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 4).toNat
  post s s' := ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) h
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      [stackArg s₁ 1, stackArg s₁ 2, stackArg s₁ 3, stackArg s₁ 4] =
        [stackArg s₂ 1, stackArg s₂ 2, stackArg s₂ 3, stackArg s₂ 4] ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `recContract.pre`: a 512-bit modulus, a one-byte `e`,
MD5 (16-byte values), a one-byte signature, and the stack arguments at
`0x10008`. -/
def recSatState : State where
  gpr r := match r with
    | .rdi => 0x5000 | .rsi => 16 | .rdx => 0x1000 | .rcx => 64 | .r8 => 0x2000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x5000, 16⟩, ⟨0x20000, 8192⟩]

theorem leak_eq3 {a b c a' b' c' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (h : (a ++ b ++ c).map (·.toNat) = (a' ++ b' ++ c').map (·.toNat)) : a = a' ∧ b = b' ∧ c = c' := by
  have hi : a ++ b ++ c = a' ++ b' ++ c' :=
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₁ ha
  exact ⟨rfl, rfl, rfl⟩

theorem recover_implies : recContract.Implies (Spec.RsaPkcs1Sig.recoverContract abi verStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    obtain ⟨hn, he, hs⟩ := leak_eq3 (by simp [Spec.Rsa.bytesAt, hcx]) (by simp [Spec.Rsa.bytesAt, h9]) hl
    refine ⟨?_, a0, by rw [a1, a2, a3, a4], hn, he, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, recContract, verStack, stackArgs_five, List.append_eq] [recSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using recSatState

end VG.Proof.RsaPkcs1Sig.X86_64
