module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignMain
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS signing on x86-64: the precondition by name, and the frame

`SPre` names the facts of `signK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

variable (tsH tsG : List FnTable)

/-- `signK.pre`, by name. -/
structure SPre (s : State) : Prop where
  sp1 : signStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)
  hsy : (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat⟩, ⟨stackArg s 16, 88⟩, ⟨stackArg s 17, 40⟩, ⟨stackArgAddr s 0, 144⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dOtH : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dOtG : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 17, 40⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dps : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqs : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddps : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddqs : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dqis : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  ddgs : (⟨stackArg s 10, (stackArg s 11).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dsas : (⟨stackArg s 12, (stackArg s 13).toNat⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dstH : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dstG : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 17, 40⟩
  dsa : (⟨stackArg s 14, (stackArg s 15).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dRdp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dRdq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dRqi : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 17, 40⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 16, 88⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 17, 40⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 144⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wP : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wQ : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wDp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wQi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wDg : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wSa : (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64
  wS : (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64
  wTH : (stackArg s 16).toNat + 88 ≤ 2 ^ 64
  wTG : (stackArg s 17).toNat + 40 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .rcx).toNat
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
  hsw : Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11)

theorem SPre.of {s : State} (h : (signK tsH tsG).pre s) : SPre tsH tsG s := by
  simp only [signK] at h
  obtain ⟨sp1, sp2, tabH, tabG, hsy, hrd, hwr, dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOtH, dOtG, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dstH, dstG, dsa, dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRtH, dRtG, dRa, dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKtH, dKtG, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, wTH, wTG, lv, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsw, hdl⟩ := h
  exact ⟨sp1, sp2, tabH, tabG, hsy, hrd, hwr, dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOtH, dOtG, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dstH, dstG, dsa, dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRtH, dRtG, dRa, dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKtH, dKtG, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, wTH, wTG, lv, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsw, hdl⟩

variable {tsH tsG}

theorem SPre.k1 {s : State} (hp : SPre tsH tsG s) : 64 ≤ (s.gpr .rcx).toNat := hp.lv.1
theorem SPre.k2 {s : State} (hp : SPre tsH tsG s) : (s.gpr .rcx).toNat ≤ 1024 := hp.lv.2
theorem SPre.hsl {s : State} (hp : SPre tsH tsG s) : 16 * (s.gpr .rcx).toNat + 32 + 1024 ≤ (stackArg s 15).toNat := by
  have := hp.hsw; unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at this; omega

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩

theorem sub_sub' (p : Addr) (a b : Nat) : p - BitVec.ofNat 64 a - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 16) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem SPre.outside {s : State} (hp : SPre tsH tsG s) {R : Region} (hO : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R)
    (hS : R.Disjoint ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩) (hK : (stkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (ret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK a (frame_sub s a hc) ha
  · exact hO a hc ha
  · exact hS a ha hc

end VG.Proof.RsaPss.X86_64
