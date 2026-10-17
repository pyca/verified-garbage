module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Spec.RsaPss.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing with the hash functions as arguments on x86-64: the contract on the registers

`signAnyK` states `Spec.RsaPss.signAnyContract` (with the stack the frame
and the calls use, `signStack`) on the registers and the stack
(`signAny_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPss.X86_64 (signStack)

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17] := rfl

/-- The selector of the digest's hash function: the low 32 bits of stack
argument 16. -/
abbrev hsel (s : State) : Nat := ((stackArg s 16).setWidth 32).toNat

/-- MGF1's: stack argument 17's. -/
abbrev msel (s : State) : Nat := ((stackArg s 17).setWidth 32).toNat

/-- `sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p = [rsp + 8], p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
digest = [rsp + 88], digest_len, salt, salt_len, scratch, scratch_len,
hash, mgf1_hash = [rsp + 144])`. -/
def signAnyK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let dg : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
    let sa : Region := ⟨stackArg s 12, (stackArg s 13).toNat⟩
    let scr : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 144⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩
    signStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64 ∧
      s.rd = [n, e, p, q, dp, dq, qi, dg, sa, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint dg ∧ out.Disjoint sa ∧ out.Disjoint scr ∧
      out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧
      ret.Disjoint scr ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint p ∧ stk.Disjoint q ∧
      stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧
      stk.Disjoint scr ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64 ∧
      (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64 ∧
      (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64 ∧
      hsel s ∈ Spec.RsaPss.hashIds ∧ msel s ∈ Spec.RsaPss.hashIds ∧
      (∀ H, Spec.HashId.mgf1 (hsel s) = some H → (stackArg s 11).toNat = H.len) ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat
  post s s' :=
    ∀ H G, Spec.HashId.mgf1 (hsel s) = some H → Spec.HashId.mgf1 (msel s) = some G →
      Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 16).map (stackArg s₁) = (List.range 16).map (stackArg s₂) ∧
      (stackArg s₁ 16).setWidth 32 = (stackArg s₂ 16).setWidth 32 ∧
      (stackArg s₁ 17).setWidth 32 = (stackArg s₂ 17).setWidth 32 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- A state meeting `signAnyK.pre`: as `signSatState`, with MD5 for both
hash functions. -/
def signAnySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10080 then 0x20
    else bif Nat.beq a.toNat 0x10009 then 0x41 else bif Nat.beq a.toNat 0x10010 then 1
    else bif Nat.beq a.toNat 0x10019 then 0x42 else bif Nat.beq a.toNat 0x10020 then 1
    else bif Nat.beq a.toNat 0x10029 then 0x43 else bif Nat.beq a.toNat 0x10030 then 1
    else bif Nat.beq a.toNat 0x10039 then 0x44 else bif Nat.beq a.toNat 0x10040 then 1
    else bif Nat.beq a.toNat 0x10049 then 0x45 else bif Nat.beq a.toNat 0x10050 then 1
    else bif Nat.beq a.toNat 0x10059 then 0x46 else bif Nat.beq a.toNat 0x10060 then 16
    else bif Nat.beq a.toNat 0x10069 then 0x47
    else bif Nat.beq a.toNat 0x1007a then 0x02 else bif Nat.beq a.toNat 0x10081 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, 16⟩, ⟨0x4700, 0⟩, ⟨0x10008, 144⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

theorem signAny_implies : signAnyK.Implies (Spec.RsaPss.signAnyContract abi signStack) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq] at h
    sig_pre [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [List.map, List.range, List.range.loop, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12, a13, a14, a15], a16, a17, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, signAnyK, signStack, stackArgs_eighteen, List.append_eq] [signAnySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signAnySatState

end VG.Proof.RsaPss.X86_64.Any
