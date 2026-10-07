import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Depth

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the public-key operation, as a callee

Encryption calls `vg_rsa_public_checked`. A `PubImpl` is any implementation
of it verified against its shared contract
`Spec.Rsa.publicCheckedContract` with `stack` bytes of stack, whose frames
fit in them; the proof of encryption is written for any of them.

`pubK S` is that contract spelt out on the registers and the stack
arguments (`scratch` and `scratch_len`, at `sp` and `sp + 8`), with `S + 1`
bytes of stack below `sp`: `pub_correct` and `pub_ct` are the
implementation's correctness and constant time under it.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64

open VG VG.AArch64

/-- An implementation of `vg_rsa_public_checked`: its symbol and code,
verified against the shared contract with `stack` bytes of stack, which
its frames fit in. -/
structure PubImpl where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (Spec.Rsa.publicCheckedContract AArch64.abi stack)
  pos : 0 < stack
  depth : 16 * code.aarch64Depth ≤ stack
  spSafe : code.all (fun i => !isa.writesSp i) = true

/-- `vg_rsa_public_checked(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, input = x6, input_len = x7, scratch, scratch_len)`, the last two
on the stack, with `S + 1` bytes of stack below `sp`. -/
def pubK (S : Nat) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 (S + 1), S + 1⟩
    S + 1 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧ s.rd = [n, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint inp ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧
      (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

theorem pub_pre {S : Nat} {s : State} (h : (pubK S).pre s) :
    (Spec.Rsa.publicCheckedContract AArch64.abi (S + 1)).pre s := by
  sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  simp only [pubK] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

theorem pub_post {S : Nat} {s s' : State}
    (h : (Spec.Rsa.publicCheckedContract AArch64.abi (S + 1)).post s s') : (pubK S).post s s' := by
  sig_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq] at h
  exact h

theorem bytes_map_eq {a b : List Byte} (h : a = b) : a.map (·.toNat) = b.map (·.toNat) := by rw [h]

theorem pub_pub {S : Nat} {s₁ s₂ : State} (h : (pubK S).pub s₁ s₂) :
    (Spec.Rsa.publicCheckedContract AArch64.abi (S + 1)).pub s₁ s₂ := by
  sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, AArch64.abi, AArch64.argRegs,
    _root_.List.range, _root_.List.range.loop, List.append_eq]
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, hn, he⟩ := h
  exact ⟨hsp, by rw [List.map_append, List.map_append, hn, he], h0, h1, h2, h3, h4, h5, h6, h7, a0, a1⟩

namespace PubImpl

variable (v : PubImpl)

/-- `stack - 1`, so that the contract's stack is `S + 1`. -/
def S : Nat := v.stack - 1

theorem stack_eq : v.stack = v.S + 1 := by have := v.pos; unfold S; omega

theorem verified' : Verified AArch64.target v.code (Spec.Rsa.publicCheckedContract AArch64.abi (v.S + 1)) :=
  v.stack_eq ▸ v.verified

theorem correct (s : State) (h : (pubK v.S).pre s) :
    ∃ t s', Exec isa v.code s t s' ∧ abiPreserved s s' ∧ (pubK v.S).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := v.verified'.1 s (pub_pre h)
  exact ⟨t, s', he, ha, pub_post hp⟩

theorem ct : ConstantTime isa (pubK v.S).pre (pubK v.S).pub v.code :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    v.verified'.2.1 _ _ _ _ _ _ (pub_pre h₁) (pub_pre h₂) (pub_pub hp) e₁ e₂

theorem depth' : 16 * v.code.aarch64Depth ≤ v.S + 1 := v.stack_eq ▸ v.depth

end PubImpl

end VG.Proof.RsaPkcs1Enc.AArch64
