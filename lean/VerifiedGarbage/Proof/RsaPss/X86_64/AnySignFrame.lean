module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignFrame
public import VerifiedGarbage.Impl.RsaPss.X86_64.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing on x86-64: the precondition by name, and the frame

`SPreA` names the facts of `signAnyK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

variable (G : Spec.Mgf1.Hash)

/-- `signAnyK.pre`, by name. -/
structure SPreA (s : State) : Prop where
  sp1 : signStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, G.len⟩, ⟨stackArg s 12, (stackArg s 13).toNat⟩, ⟨stackArgAddr s 0, 144⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dps : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqs : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddps : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddqs : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqis : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddgs : (⟨stackArg s 10, G.len⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dsas : (⟨stackArg s 12, (stackArg s 13).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dsa : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dRdp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dRdq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dRqi : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wP : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wQ : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wDp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wQi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wDg : (stackArg s 10).toNat + G.len ≤ 2 ^ 64
  wSa : (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64
  wS : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 1).toNat
  pl2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 3).toNat
  ql2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 5).toNat = (stackArg s 1).toNat
  hqil : (stackArg s 9).toNat = (stackArg s 1).toNat
  hdql : (stackArg s 7).toNat = (stackArg s 3).toNat
  hsl : 16 * (s.gpr .rcx).toNat + 32 + 1024 ≤ (stackArg s 15).toNat
  hk8 : hsel s < 8
  hg8 : msel s < 8
  hdl : (stackArg s 11).toNat = G.len
  hG : Spec.HashId.mgf1 (hsel s) = some G

theorem SPreA.of {s : State} (h : signAnyK.pre s) (hG : Spec.HashId.mgf1 (hsel s) = some G) : SPreA G s := by
  simp only [signAnyK] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOp dOq dOdp dOdq dOqi dOdg dOsa dOs dOa dns des dps dqs ddps
    ddqs dqis ddgs dsas dsa dRo dRn dRe dRp dRq dRdp dRdq dRqi dRdg dRsa dRs dRa dKo dKn dKe dKp dKq
    dKdp dKdq dKqi dKdg dKsa dKs dKa wO wN wE wP wQ wDp wDq wQi wDg wSa wS hh hm hdl _ob1 hsi L1 L2 pl1 pl2
    ql1 ql2 hdpl hqil hdql
  obtain ⟨k1, k2⟩ := _ob1
  have hsl := h
  have hdl := hdl G hG
  simp only [Spec.RsaPss.hashIds, List.mem_cons, List.not_mem_nil, or_false] at hh hm
  rw [hdl] at hrd dOdg dRdg dKdg ddgs wDg
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dsa, dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRa, dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, k1, k2, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsl; omega,
    by omega, by omega, hdl, hG⟩

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem SPreA.outside {s : State} (hp : SPreA G s) {R : Region} (hO : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R)
    (hS : R.Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩) (hK : (stkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (ret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK a (frame_sub s a hc) ha
  · exact hO a hc ha
  · exact hS a ha hc

end VG.Proof.RsaPss.X86_64.Any
