import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callee

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: the private-key operation, as a callee

Decryption calls `vg_rsa_private_checked`. A `PrivImpl` is any
implementation of it verified against its shared contract
`Spec.Rsa.privateCheckedContract` with `stack` bytes of stack (at least
16), whose frames fit in them; the proof of decryption is written for any
of them, as for any implementation of the hash functions it calls.

`privK S` is that contract spelt out on the registers and the stack
arguments (`p` … `scratch_len`, from `sp`), with `S + 1` bytes of stack
below `sp`: `priv_correct` and `priv_ct` are the implementation's
correctness and constant time under it.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- An implementation of `vg_rsa_private_checked`: its symbol and code,
verified against the shared contract with `stack` bytes of stack, which
its frames fit in. -/
structure PrivImpl where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (Spec.Rsa.privateCheckedContract AArch64.abi stack)
  pos : 16 ≤ stack
  depth : 16 * code.aarch64Depth ≤ stack
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-- `vg_rsa_private_checked(out = x0, out_len = x1, n = x2, n_len = x3,
e = x4, e_len = x5, input = x6, input_len = x7, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`, the last twelve
on the stack, with `S + 1` bytes of stack below `sp`. -/
def privK (S : Nat) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 96⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 (S + 1), S + 1⟩
    S + 1 ≤ s.sp.toNat ∧ s.sp.toNat + 96 ≤ 2 ^ 64 ∧ s.rd = [n, e, inp, p, q, dp, dq, qi, args] ∧
      s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint inp ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧ (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .x3).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .x3).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 11).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
      (∀ i < 12, stackArg s₁ i = stackArg s₂ i) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

theorem priv_pre {S : Nat} {s : State} (h : (privK S).pre s) :
    (Spec.Rsa.privateCheckedContract AArch64.abi (S + 1)).pre s := by
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [privK] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

theorem priv_post {S : Nat} {s s' : State}
    (h : (Spec.Rsa.privateCheckedContract AArch64.abi (S + 1)).post s s') : (privK S).post s s' := by
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h

theorem priv_pub {S : Nat} {s₁ s₂ : State} (h : (privK S).pub s₁ s₂) :
    (Spec.Rsa.privateCheckedContract AArch64.abi (S + 1)).pub s₁ s₂ := by
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, ha, hn, he⟩ := h
  exact ⟨hsp, by rw [List.map_append, List.map_append, hn, he], h0, h1, h2, h3, h4, h5, h6, h7,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide),
    ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide)⟩

namespace PrivImpl

variable (v : PrivImpl)

/-- `stack - 1`, so that the contract's stack is `S + 1`. -/
def S : Nat := v.stack - 1

theorem stack_eq : v.stack = v.S + 1 := by have := v.pos; unfold S; omega

theorem verified' : Verified AArch64.target v.code (Spec.Rsa.privateCheckedContract AArch64.abi (v.S + 1)) :=
  v.stack_eq ▸ v.verified

theorem correct (s : State) (h : (privK v.S).pre s) :
    ∃ t s', Exec isa v.code s t s' ∧ abiPreserved s s' ∧ (privK v.S).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := v.verified'.1 s (priv_pre h)
  exact ⟨t, s', he, ha, priv_post hp⟩

theorem ct : ConstantTime isa (privK v.S).pre (privK v.S).pub v.code :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    v.verified'.2.1 _ _ _ _ _ _ (priv_pre h₁) (priv_pre h₂) (priv_pub hp) e₁ e₂

theorem depth' : 16 * v.code.aarch64Depth ≤ v.S + 1 := v.stack_eq ▸ v.depth

theorem S15 : 15 ≤ v.S := by have := v.pos; unfold S; omega

end PrivImpl

end VG.Proof.RsaPkcs1Enc.AArch64
