module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
public import VerifiedGarbage.Spec.RsaPss.AnyHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS signing on x86-64: the contract on the registers

`sK` states `Spec.RsaPss.signAnyContract` (with the stack RSAES-OAEP
decryption uses, `decStack`: the frame, a return address and what
`vg_rsa_private_checked` uses) on the registers and the stack
(`sign_implies`), for the hash functions the selectors name (`sPostH`);
`SPre` is its precondition by name.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 (decStack TabFns)
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

theorem stackArgs_twenty (s : State) :
    List.map (stackArg s) (List.range 20) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19] := rfl

/-- Signing's selectors, `hash` and `mgf1_hash`, and tables, `hash_fns` and
`mgf1_fns`. -/
abbrev sselH (s : State) : Nat := (stackArg s 16).toNat
abbrev sselG (s : State) : Nat := (stackArg s 17).toNat
abbrev stabH (s : State) : Addr := stackArg s 18
abbrev stabG (s : State) : Addr := stackArg s 19

/-- The caller's buffers. -/
abbrev soR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
abbrev snR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev seR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev spR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev sqR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev sdpR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev sdqR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev sqiR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
abbrev sdgR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
abbrev ssaR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat⟩
abbrev sscrR (s : State) : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
abbrev sargsR (s : State) : Region := ⟨stackArgAddr s 0, 160⟩
abbrev stkS (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩

/-- The caller's read-only buffers. -/
def srd (s : State) : List Region :=
  [snR s, seR s, spR s, sqR s, sdpR s, sdqR s, sqiR s, sdgR s, ssaR s, ⟨stabH s, 24⟩, ⟨stabG s, 24⟩, sargsR s]

/-- The precondition of `vg_rsa_pss_sign`, by name. -/
structure SPre (s : State) : Prop where
  sp1 : decStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 168 ≤ 2 ^ 64
  hrd : s.rd = srd s
  hwr : s.wr = [soR s, sscrR s]
  dOn : (soR s).Disjoint (snR s)
  dOe : (soR s).Disjoint (seR s)
  dOp : (soR s).Disjoint (spR s)
  dOq : (soR s).Disjoint (sqR s)
  dOdp : (soR s).Disjoint (sdpR s)
  dOdq : (soR s).Disjoint (sdqR s)
  dOqi : (soR s).Disjoint (sqiR s)
  dOd : (soR s).Disjoint (sdgR s)
  dOsa : (soR s).Disjoint (ssaR s)
  dOs : (soR s).Disjoint (sscrR s)
  dOtH : (soR s).Disjoint ⟨stabH s, 24⟩
  dOtG : (soR s).Disjoint ⟨stabG s, 24⟩
  dOa : (soR s).Disjoint (sargsR s)
  dns : (snR s).Disjoint (sscrR s)
  des : (seR s).Disjoint (sscrR s)
  dps : (spR s).Disjoint (sscrR s)
  dqs : (sqR s).Disjoint (sscrR s)
  ddps : (sdpR s).Disjoint (sscrR s)
  ddqs : (sdqR s).Disjoint (sscrR s)
  dqis : (sqiR s).Disjoint (sscrR s)
  dds : (sdgR s).Disjoint (sscrR s)
  dsas : (ssaR s).Disjoint (sscrR s)
  dstH : (sscrR s).Disjoint ⟨stabH s, 24⟩
  dstG : (sscrR s).Disjoint ⟨stabG s, 24⟩
  dsa : (sscrR s).Disjoint (sargsR s)
  dRO : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (soR s)
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (snR s)
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (seR s)
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (spR s)
  dRq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sqR s)
  dRdp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sdpR s)
  dRdq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sdqR s)
  dRqi : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sqiR s)
  dRd : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sdgR s)
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (ssaR s)
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sscrR s)
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stabH s, 24⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stabG s, 24⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sargsR s)
  dKO : (stkS s).Disjoint (soR s)
  dKn : (stkS s).Disjoint (snR s)
  dKe : (stkS s).Disjoint (seR s)
  dKp : (stkS s).Disjoint (spR s)
  dKq : (stkS s).Disjoint (sqR s)
  dKdp : (stkS s).Disjoint (sdpR s)
  dKdq : (stkS s).Disjoint (sdqR s)
  dKqi : (stkS s).Disjoint (sqiR s)
  dKd : (stkS s).Disjoint (sdgR s)
  dKsa : (stkS s).Disjoint (ssaR s)
  dKs : (stkS s).Disjoint (sscrR s)
  dKtH : (stkS s).Disjoint ⟨stabH s, 24⟩
  dKtG : (stkS s).Disjoint ⟨stabG s, 24⟩
  dKa : (stkS s).Disjoint (sargsR s)
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wP : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wQ : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wDp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wQi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wD : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wSa : (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64
  wS : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  wTH : (stabH s).toNat + 24 ≤ 2 ^ 64
  wTG : (stabG s).toNat + 24 ≤ 2 ^ 64
  iH : sselH s ∈ Spec.RsaPss.hashIds
  iG : sselG s ∈ Spec.RsaPss.hashIds
  dl : ∀ H, Spec.HashId.mgf1 (sselH s) = some H → (stackArg s 11).toNat = H.len
  lv : Spec.Rsa.lenValid (s.gpr .rcx).toNat
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  el1 : 1 ≤ (s.gpr .r9).toNat
  el2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 1).toNat
  pl2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 3).toNat
  ql2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 5).toNat = (stackArg s 1).toNat
  hqil : (stackArg s 9).toNat = (stackArg s 1).toNat
  hdql : (stackArg s 7).toNat = (stackArg s 3).toNat
  hsw : Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat
  fH : TabFns decStack s (sselH s) (stabH s)
  fG : TabFns decStack s (sselG s) (stabG s)

theorem spre_of {s : State} (h : (Spec.RsaPss.signAnyContract abi decStack).pre s) : SPre s := by
  sig_pre [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq] at h
  sig_pre [Spec.RsaPss.signAnyContract, Spec.RsaPss.signAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twenty, List.append_eq] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOp dOq dOdp dOdq dOqi dOd dOsa dOs dOtH dOtG dOa dns des dps dqs ddps ddqs dqis
    dds dsas dstH dstG dsa dRO dRn dRe dRp dRq dRdp dRdq dRqi dRd dRsa dRs dRtH dRtG dRa dKO dKn dKe dKp dKq dKdp dKdq
    dKqi dKd dKsa dKs dKtH dKtG dKa wO wN wE wP wQ wDp wDq wQi wD wSa wS wTH wTG iH iG dl lv hsi el1 el2 pl1 pl2 ql1
    ql2 hdpl hqil hdql hsw fH
  have fG := h
  clear h
  exact ⟨by unfold decStack privStack Impl.RsaOaep.X86_64.frameBytes; omega, sp2, hrd, hwr, dOn, dOe, dOp, dOq,
    dOdp, dOdq, dOqi, dOd, dOsa, dOs, dOtH, dOtG, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, dds, dsas, dstH, dstG,
    dsa, dRO, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRd, dRsa, dRs, dRtH, dRtG, dRa, dKO, dKn, dKe, dKp, dKq, dKdp,
    dKdq, dKqi, dKd, dKsa, dKs, dKtH, dKtG, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wD, wSa, wS, wTH, wTG, iH, iG, dl,
    lv, hsi, el1, el2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsw, fH, fG⟩

variable {s : State}

theorem SPre.k1 (hp : SPre s) : 64 ≤ (s.gpr .rcx).toNat := hp.lv.1
theorem SPre.k2 (hp : SPre s) : (s.gpr .rcx).toNat ≤ 1024 := hp.lv.2

/-- The working space holds ours (`oRsa` bytes) and the private operation's. -/
theorem SPre.hsl (hp : SPre s) : 16 * (s.gpr .rcx).toNat + 32 + 1024 ≤ (stackArg s 15).toNat := by
  have := hp.hsw; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega

/-- The signature for the hash functions `H` and `G`. -/
def sPostH (H G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
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

/-- Entry states agreeing on the registers holding arguments, the stack
arguments, `n`, `e` and the tables. -/
def sPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (List.range 20).map (stackArg s₁) = (List.range 20).map (stackArg s₂) ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 18) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 18) ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 19) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 19) ∧
    abi.sameWorld s₁ s₂

/-- `Spec.RsaPss.signAnyContract` on the registers and the stack. -/
def scontract : Contract isa where
  pre := (Spec.RsaPss.signAnyContract abi decStack).pre
  post s s' := ∀ H G, Spec.HashId.mgf1 (sselH s) = some H → Spec.HashId.mgf1 (sselG s) = some G →
    sPostH H G s s'
  pub := sPub

end VG.Proof.RsaPss.X86_64
