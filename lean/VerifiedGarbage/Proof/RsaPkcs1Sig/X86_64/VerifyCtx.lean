import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the contract on the registers

`verContract` states the shared contract (with the stack the frame and the
call use, `verStack`) on the registers and the stack (`verify_implies`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_verify` uses: its
frame, and the return address of its call (whose callee uses none). -/
def verStack : Nat := 2144

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

/-- `vg_rsa_pkcs1_verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx,
hash = r8d, digest = r9, digest_len = [rsp + 8], sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def verContract : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dig : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩
    verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, sig, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
      (List.range 5).map (stackArg s₁) = (List.range 5).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `verContract.pre`: a 512-bit modulus, a one-byte `e`, a
one-byte hash value and signature, and the stack arguments at `0x10008`. -/
def verSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 1 else if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x20000, 8192⟩]

theorem leak_eq4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) = (a' ++ b' ++ c' ++ d').map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₂, rfl⟩ := List.append_inj h₁ (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₂ ha
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem verify_implies : verContract.Implies (Spec.RsaPkcs1Sig.verifyContract abi verStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    obtain ⟨hn, he, hd, hs⟩ := leak_eq4 (by simp [Spec.Rsa.bytesAt, hsi]) (by simp [Spec.Rsa.bytesAt, hcx])
      (by simp [Spec.Rsa.bytesAt, a0]) hl
    refine ⟨?_, h8, by simp only [stackArgs_five, a0, a1, a2, a3, a4], hn, he, hd, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, verContract, verStack, stackArgs_five, List.append_eq] [verSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verSatState

end VG.Proof.RsaPkcs1Sig.X86_64
