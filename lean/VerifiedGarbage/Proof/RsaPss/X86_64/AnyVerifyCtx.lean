module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtx
public import VerifiedGarbage.Spec.RsaPss.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: the contract on the registers

`verifyAnyK` states `Spec.RsaPss.verifyAnyContract` (with the stack the
frame and the calls use, `verifyStack`) on the registers and the stack
(`verifyAny_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPss.X86_64 (verifyStack)

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- The selector of the digest's hash function: stack argument 8. -/
abbrev vhsel (s : State) : Nat := (stackArg s 8).toNat

/-- MGF1's: stack argument 9's. -/
abbrev vmsel (s : State) : Nat := (stackArg s 9).toNat

/-- The cached values are the modulus's. -/
def validCacheA (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat)

/-- `verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8,
digest_len = r9, sig = [rsp + 8], sig_len, any_salt_len, salt_len, scratch,
scratch_len, pre, pre_len, hash, mgf1_hash = [rsp + 80])`. -/
def verifyAnyK : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dg : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let sg : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
    let pr : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩
    verifyStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dg, sg, pr, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dg.Disjoint scr ∧ sg.Disjoint scr ∧ pr.Disjoint scr ∧
      scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dg ∧ ret.Disjoint sg ∧ ret.Disjoint scr ∧
      ret.Disjoint pr ∧ ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dg ∧ stk.Disjoint sg ∧ stk.Disjoint scr ∧
      stk.Disjoint pr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧
      vhsel s ∈ Spec.RsaPss.hashIds ∧ vmsel s ∈ Spec.RsaPss.hashIds ∧
      (∀ H, Spec.HashId.mgf1 (vhsel s) = some H → (s.gpr .r9).toNat = H.len) ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rsi).toNat ∧
      Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat ∧
      (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat
  post s s' :=
    ∀ H G, Spec.HashId.mgf1 (vhsel s) = some H → Spec.HashId.mgf1 (vmsel s) = some G → validCacheA s →
      (s'.gpr .rax).setWidth 32 = if Spec.RsaPss.verify H G
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      (stackArg s₁ 2).setWidth 32 = (stackArg s₂ 2).setWidth 32 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
      stackArg s₁ 4 = stackArg s₂ 4 ∧
      stackArg s₁ 5 = stackArg s₂ 5 ∧ stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧
      stackArg s₁ 8 = stackArg s₂ 8 ∧ stackArg s₁ 9 = stackArg s₂ 9 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 6) (stackArg s₁ 7).toNat =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₂ 6) (stackArg s₂ 7).toNat

/-- A state meeting `verifyAnyK.pre`: a 512-bit modulus, a one-byte `e`, an
MD5 digest, MD5 for MGF1, and the stack arguments at `0x10008`. -/
def verifyAnySatState : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 64 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4600 | .r9 => 16
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10009 then 0x40 else bif Nat.beq a.toNat 0x10010 then 0x40
    else bif Nat.beq a.toNat 0x1002a then 0x02 else bif Nat.beq a.toNat 0x10030 then 0x20
    else bif Nat.beq a.toNat 0x10031 then 0x08 else bif Nat.beq a.toNat 0x10039 then 0x50
    else bif Nat.beq a.toNat 0x10040 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, 16⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10008, 80⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

theorem verifyAny_implies : verifyAnyK.Implies (Spec.RsaPss.verifyAnyContract abi verifyStack) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, verifyStack, stackArgs_ten, List.append_eq] at h
    sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, verifyStack, stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, verifyStack, stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, validCacheA, verifyStack, stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, verifyStack, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hb
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn, he, hp'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, verifyAnyK, verifyStack, stackArgs_ten, List.append_eq] [verifyAnySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using verifyAnySatState

end VG.Proof.RsaPss.X86_64.Any
