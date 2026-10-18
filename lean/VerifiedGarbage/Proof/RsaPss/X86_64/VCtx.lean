module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
public import VerifiedGarbage.Spec.RsaPss.AnyHash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the precondition by name

`VPre` names the facts of `Spec.RsaPss.verifyAnyContract`'s precondition
(`vpre_of`), with the stack RSAES-OAEP encryption uses (`encStack`: the
frame, and the 16 bytes below it that the calls of the streaming hash
functions use, the public operation only its return address).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 (encStack stkR TabFns)

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- The selectors, `hash` and `mgf1_hash`, and the tables, `hash_fns` and
`mgf1_fns`. -/
abbrev vselH (s : State) : Nat := (stackArg s 8).toNat
abbrev vselG (s : State) : Nat := (stackArg s 9).toNat
abbrev vtabH (s : State) : Addr := stackArg s 10
abbrev vtabG (s : State) : Addr := stackArg s 11

/-- `n`, `e`, the digest, the signature, the working space, `pre` and the
stack arguments. -/
abbrev nR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev dgR (s : State) : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
abbrev sgR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev vscrR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
abbrev vpreR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
abbrev vargsR (s : State) : Region := ⟨stackArgAddr s 0, 96⟩

/-- The caller's read-only buffers. -/
def vrd (s : State) : List Region :=
  [nR s, eR s, dgR s, sgR s, vpreR s, ⟨vtabH s, 24⟩, ⟨vtabG s, 24⟩, vargsR s]

/-- The precondition of `vg_rsa_pss_verify_precomputed`, by name. -/
structure VPre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  hrd : s.rd = vrd s
  hwr : s.wr = [vscrR s]
  dnS : (nR s).Disjoint (vscrR s)
  deS : (eR s).Disjoint (vscrR s)
  ddS : (dgR s).Disjoint (vscrR s)
  dgS : (sgR s).Disjoint (vscrR s)
  dSp : (vscrR s).Disjoint (vpreR s)
  dStH : (vscrR s).Disjoint ⟨vtabH s, 24⟩
  dStG : (vscrR s).Disjoint ⟨vtabG s, 24⟩
  dSa : (vscrR s).Disjoint (vargsR s)
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (nR s)
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (eR s)
  dRd : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (dgR s)
  dRg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (sgR s)
  dRS : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (vscrR s)
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (vpreR s)
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨vtabH s, 24⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨vtabG s, 24⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (vargsR s)
  dKn : (stkR s).Disjoint (nR s)
  dKe : (stkR s).Disjoint (eR s)
  dKd : (stkR s).Disjoint (dgR s)
  dKg : (stkR s).Disjoint (sgR s)
  dKS : (stkR s).Disjoint (vscrR s)
  dKp : (stkR s).Disjoint (vpreR s)
  dKtH : (stkR s).Disjoint ⟨vtabH s, 24⟩
  dKtG : (stkR s).Disjoint ⟨vtabG s, 24⟩
  dKa : (stkR s).Disjoint (vargsR s)
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wD : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wG : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wS : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  wP : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  wTH : (vtabH s).toNat + 24 ≤ 2 ^ 64
  wTG : (vtabG s).toNat + 24 ≤ 2 ^ 64
  iH : vselH s ∈ Spec.RsaPss.hashIds
  iG : vselG s ∈ Spec.RsaPss.hashIds
  dl : ∀ H, Spec.HashId.mgf1 (vselH s) = some H → (s.gpr .r9).toNat = H.len
  lv : Spec.Rsa.lenValid (s.gpr .rsi).toNat
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsg : (stackArg s 1).toNat = (s.gpr .rsi).toNat
  hsl : Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat
  pl : (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat
  fH : TabFns encStack s (vselH s) (vtabH s)
  fG : TabFns encStack s (vselG s) (vtabG s)

theorem stkR_eq (s : State) : stkR s = ⟨s.gpr .rsp - 424#64, 424⟩ := rfl

/-- The contract's precondition, by name. -/
theorem vpre_of {s : State} (h : (Spec.RsaPss.verifyAnyContract abi encStack).pre s) : VPre s := by
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, encStack,
    stackArgs_twelve, List.append_eq] at h
  sig_pre [Spec.RsaPss.verifyAnyContract, Spec.RsaPss.verifyAnySig, abi, argRegs, encStack,
    stackArgs_twelve, List.append_eq] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dnS deS ddS dgS dSp dStH dStG dSa dRn dRe dRd dRg dRS dRp dRtH dRtG dRa dKn dKe dKd
    dKg dKS dKp dKtH dKtG dKa wN wE wD wG wS wP wTH wTG iH iG dl lv L1 L2 hsg hsl pl fH
  exact ⟨sp1, sp2, hrd, hwr, dnS, deS, ddS, dgS, dSp, dStH, dStG, dSa, dRn, dRe, dRd, dRg, dRS, dRp, dRtH, dRtG, dRa,
    dKn, dKe, dKd, dKg, dKS, dKp, dKtH, dKtG, dKa, wN, wE, wD, wG, wS, wP, wTH, wTG, iH, iG, dl, lv, L1, L2, hsg, hsl,
    pl, fH, h⟩

variable {s : State}

theorem VPre.k1 (hp : VPre s) : 64 ≤ (s.gpr .rsi).toNat := hp.lv.1
theorem VPre.k2 (hp : VPre s) : (s.gpr .rsi).toNat ≤ 1024 := hp.lv.2

/-- The working space holds ours (`oRsa` bytes) and the public operation's. -/
theorem VPre.hsl' (hp : VPre s) :
    8 * (((s.gpr .rsi).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 5).toNat := by
  have := hp.hsl
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at this
  omega

/-- A buffer's first byte, and the rest. -/
theorem bytesAt_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m p (n + 1) = m p :: (List.range n).map fun i => m (p + BitVec.ofNat 64 (i + 1)) := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]; rfl

end VG.Proof.RsaPss.X86_64
