module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCtx
public import VerifiedGarbage.Spec.RsaOaep.AnyHash
public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
public import VerifiedGarbage.Proof.HashFns.X86_64.Witness
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP decryption on x86-64: the contract on the registers

`decK` states `Spec.RsaOaep.decryptAnyContract` (with the stack the frame
and the calls use, `decStack`) on the registers and the stack
(`dec_implies`), for the hash functions the selectors name (`decPostH`);
`DPre` is its precondition by name. The callee
`vg_rsa_private_checked` is a `PrivImpl` (`Proof/RsaPkcs1Enc/X86_64/`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (privStack)

/-- The stack below the stack pointer: the frame of 408 bytes, a return
address and what `vg_rsa_private_checked` uses (more than the streaming
hash functions' 16 bytes). -/
def decStack : Nat := Impl.RsaOaep.X86_64.frameBytes + 8 + privStack

theorem stackArgs_twentyone (s : State) :
    List.map (stackArg s) (List.range 21) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17, stackArg s 18, stackArg s 19, stackArg s 20] := rfl

/-- Decryption's selectors, `hash` and `mgf1_hash`, and tables, `hash_fns` and
`mgf1_fns`. -/
abbrev dselH (s : State) : Nat := (stackArg s 17).toNat
abbrev dselG (s : State) : Nat := (stackArg s 18).toNat
abbrev dtabH (s : State) : Addr := stackArg s 19
abbrev dtabG (s : State) : Addr := stackArg s 20

/-- The result of `decrypt(out = rdi, out_len = rsi, msg_len = rdx, n = rcx,
n_len = r8, e = r9, e_len = [rsp + 8], p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, label, label_len, ct, ct_len, scratch, scratch_len,
hash, mgf1_hash, hash_fns, mgf1_fns = [rsp + 168])` with the hash functions
`H` and `G`. -/
def decPostH (H G : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  Spec.RsaOaep.writtenDecrypt s'.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((s'.gpr .rax).setWidth 32)
  (Spec.RsaOaep.decrypt H G (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 2).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 13) (s.gpr .r8).toNat))

/-- Entry states of the same program agreeing on the registers holding
arguments, the stack arguments, `n`, `e` and the tables of the hash
functions' streaming functions. -/
def decPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (List.range 21).map (stackArg s₁) = (List.range 21).map (stackArg s₂) ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ∧
    Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat =
      Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 19) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 19) ∧
    Spec.HashFns.tableWords s₁.mem (stackArg s₁ 20) = Spec.HashFns.tableWords s₂.mem (stackArg s₂ 20) ∧
    abi.sameWorld s₁ s₂

/-- `Spec.RsaOaep.decryptAnyContract` on the registers and the stack: its
precondition, the result for the hash functions the selectors name, and
`decPub`. -/
def decK : Contract isa where
  pre := (Spec.RsaOaep.decryptAnyContract abi decStack).pre
  post s s' := ∀ H G, Spec.HashId.mgf1 (dselH s) = some H → Spec.HashId.mgf1 (dselG s) = some G →
    decPostH H G s s'
  pub := decPub

/-- `decK.pre`, by name. -/
structure DPre (s : State) : Prop where
  sp1 : decStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 176 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩, ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨stackArg s 13, (stackArg s 14).toNat⟩, ⟨dtabH s, 24⟩, ⟨dtabG s, 24⟩, ⟨stackArgAddr s 0, 168⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]
  dOM : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dOlb : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOct : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 168⟩
  dMn : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dMe : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dMp : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dMq : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dMdp : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dMdq : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dMqi : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dMlb : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dMct : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dMs : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dMa : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 168⟩
  dns : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  des : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dps : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dqs : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  ddps : (⟨stackArg s 5, (stackArg s 6).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  ddqs : (⟨stackArg s 7, (stackArg s 8).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dqis : (⟨stackArg s 9, (stackArg s 10).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dlbs : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dcts : (⟨stackArg s 13, (stackArg s 14).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dsa : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 168⟩
  dRO : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRM : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dKO : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKM : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dKlb : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKct : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 168⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wM : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  wN : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wE : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wP : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wQ : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wDp : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wDq : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wQi : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wL : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wC : (stackArg s 13).toNat + (stackArg s 14).toNat ≤ 2 ^ 64
  wS : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .r8).toNat
  hsi : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  hcl : (stackArg s 14).toNat = (s.gpr .r8).toNat
  el1 : 1 ≤ (stackArg s 0).toNat
  el2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  pl1 : 1 ≤ (stackArg s 2).toNat
  pl2 : (stackArg s 2).toNat < (s.gpr .r8).toNat
  ql1 : 1 ≤ (stackArg s 4).toNat
  ql2 : (stackArg s 4).toNat < (s.gpr .r8).toNat
  hdpl : (stackArg s 6).toNat = (stackArg s 2).toNat
  hqil : (stackArg s 10).toNat = (stackArg s 2).toNat
  hdql : (stackArg s 8).toNat = (stackArg s 4).toNat
  hsw : Spec.RsaPss.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 16).toNat
  iH : dselH s ∈ Spec.RsaOaep.hashIds
  iG : dselG s ∈ Spec.RsaOaep.hashIds
  dOtH : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨dtabH s, 24⟩
  dOtG : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨dtabG s, 24⟩
  dMtH : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨dtabH s, 24⟩
  dMtG : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨dtabG s, 24⟩
  dstH : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region).Disjoint ⟨dtabH s, 24⟩
  dstG : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region).Disjoint ⟨dtabG s, 24⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨dtabH s, 24⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨dtabG s, 24⟩
  wTH : (dtabH s).toNat + 24 ≤ 2 ^ 64
  wTG : (dtabG s).toNat + 24 ≤ 2 ^ 64
  fH : TabFns decStack s (dselH s) (dtabH s)
  fG : TabFns decStack s (dselG s) (dtabG s)

theorem DPre.of {s : State} (h : decK.pre s) : DPre s := by
  simp only [decK] at h
  sig_pre [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq] at h
  sig_pre [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOM dOn dOe dOp dOq dOdp dOdq dOqi dOlb dOct dOs dOtH dOtG dOa dMn dMe dMp dMq dMdp dMdq
    dMqi dMlb dMct dMs dMtH dMtG dMa dns des dps dqs ddps ddqs dqis dlbs dcts dstH dstG dsa dRO dRM _ _ _ _ _ _ _ _ _
    dRs _ _ _ dKO dKM dKn dKe dKp dKq dKdp dKdq dKqi dKlb dKct dKs dKtH dKtG dKa wO wM wN wE wP wQ wDp wDq wQi wL
    wC wS wTH wTG iH iG lv hsi hcl el1 el2 pl1 pl2 ql1 ql2 hdpl hqil hdql hsw fH
  have fG := h
  clear h
  exact ⟨by unfold decStack privStack Impl.RsaOaep.X86_64.frameBytes; omega, sp2, hrd, hwr, dOM, dOn, dOe, dOp,
    dOq, dOdp, dOdq, dOqi, dOlb, dOct, dOs, dOa, dMn, dMe, dMp, dMq, dMdp, dMdq, dMqi, dMlb, dMct, dMs, dMa, dns,
    des, dps, dqs, ddps, ddqs, dqis, dlbs, dcts, dsa, dRO, dRM, dRs, dKO, dKM, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi,
    dKlb, dKct, dKs, dKa, wO, wM, wN, wE, wP, wQ, wDp, wDq, wQi, wL, wC, wS, lv, hsi, hcl, el1, el2, pl1, pl2, ql1,
    ql2, hdpl, hqil, hdql, hsw, iH, iG, dOtH, dOtG, dMtH, dMtG, dstH, dstG, dKtH, dKtG, wTH, wTG, fH, fG⟩

/-- A state meeting `decK.pre`: a 512-bit modulus, one-byte `e`, primes,
exponents and `qInv`, an empty label, SHA-1 for both hash functions, with
the table at `0x6000` of the witnesses' streaming functions
(`Witness.funs`), and the stack arguments at `0x10008`. -/
def decSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1800 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := bif Nat.beq a.toNat 0x10088 then 0x20
    else bif Nat.beq a.toNat 0x10008 then 1 else bif Nat.beq a.toNat 0x10011 then 0x41
    else bif Nat.beq a.toNat 0x10018 then 1 else bif Nat.beq a.toNat 0x10021 then 0x42
    else bif Nat.beq a.toNat 0x10028 then 1 else bif Nat.beq a.toNat 0x10031 then 0x43
    else bif Nat.beq a.toNat 0x10038 then 1 else bif Nat.beq a.toNat 0x10041 then 0x44
    else bif Nat.beq a.toNat 0x10048 then 1 else bif Nat.beq a.toNat 0x10051 then 0x45
    else bif Nat.beq a.toNat 0x10058 then 1 else bif Nat.beq a.toNat 0x10061 then 0x46
    else bif Nat.beq a.toNat 0x10071 then 0x47 else bif Nat.beq a.toNat 0x10078 then 64
    else bif Nat.beq a.toNat 0x10082 then 0x02 else bif Nat.beq a.toNat 0x10089 then 0x08
    else bif Nat.beq a.toNat 0x10090 then 1 else bif Nat.beq a.toNat 0x10098 then 1
    else bif Nat.beq a.toNat 0x100A1 then 0x60 else bif Nat.beq a.toNat 0x100A9 then 0x60
    else bif Nat.beq a.toNat 0x6001 then 0x70 else bif Nat.beq a.toNat 0x6009 then 0x71
    else bif Nat.beq a.toNat 0x6011 then 0x72 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩,
    ⟨0x4600, 0⟩, ⟨0x4700, 64⟩, ⟨0x6000, 24⟩, ⟨0x6000, 24⟩, ⟨0x10008, 168⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 2080 * 8⟩]
  funs := HashFns.X86_64.Witness.funs

theorem dec_sat : ∃ s, (Spec.RsaOaep.decryptAnyContract abi decStack).pre s := by
  refine ⟨decSatState, ?_⟩
  sig_pre [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decStack, privStack,
    Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
  sig_and_intros
  all_goals first
    | ((first | rw [show (stackArg decSatState 17).toNat = 1 from by decide]
              | rw [show (stackArg decSatState 18).toNat = 1 from by decide])
       exact HashFns.X86_64.Witness.tableOf_one (s := decSatState) (a₀ := 0x7000) (a₁ := 0x7100) (a₂ := 0x7200)
         rfl rfl rfl (by decide) (by decide) (by decide))
    | (unfold Spec.Rsa.lenValid; decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, decSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

theorem dec_implies : decK.Implies (Spec.RsaOaep.decryptAnyContract abi decStack) where
  pre := fun _ h => h
  post := by
    intro s s' _ h
    sig_post [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decK, decPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq]
    sig_reduce [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decK, decPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq] at h
    sig_simp [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decK, decPostH, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq] [] at h
    exact h
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.decryptAnyContract, Spec.RsaOaep.decryptAnySig, abi, argRegs, decK, decPub, decStack,
      privStack, Impl.RsaOaep.X86_64.frameBytes, stackArgs_twentyone, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i hsp hsw hl hdi hsi hdx hcx h8 h9 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
    have a20 := h
    clear h
    obtain ⟨h2, hG⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, Spec.HashFns.tableWords, h8, a0])
    obtain ⟨hb, hT⟩ := List.append_inj h2 (by simp [Spec.Rsa.bytesAt, h8, a0])
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h8]) hb
    refine ⟨?_, by simp only [stackArgs_twentyone, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17, a18, a19, a20], hn, he, hT, hG, hsw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := dec_sat

end VG.Proof.RsaOaep.X86_64
