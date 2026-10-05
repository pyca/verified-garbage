import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
import VerifiedGarbage.Proof.RsaPss.X86_64.SignMain

/-!
# RSASSA-PSS signing on x86-64: the precondition by name, and the frame

`SPre` names the facts of `signK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`stkR`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64

variable (G : Spec.Mgf1.Hash)

/-- `signK.pre`, by name. -/
structure SPre (s : State) : Prop where
  sp1 : signStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩, ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, G.len⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨stackArgAddr s 0, 120⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOdg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dOsa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dps : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqs : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddps : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddqs : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqis : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddgs : (⟨stackArg s 10, G.len⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dsas : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dsa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dRdp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dRdq : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dRqi : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dRsa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 10, G.len⟩
  dKsa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wP : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wQ : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wDp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wQi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wDg : (stackArg s 10).toNat + G.len ≤ 2 ^ 64
  wSa : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wS : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
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
  hsl : 16 * (s.gpr .rcx).toNat + 1024 ≤ (stackArg s 14).toNat

theorem SPre.of {s : State} (h : (signK G).pre s) : SPre G s := by
  simp only [signK] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dsa, dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRa, dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, ⟨k1, k2⟩, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOp, dOq, dOdp, dOdq, dOqi, dOdg, dOsa, dOs, dOa, dns, des, dps, dqs, ddps, ddqs, dqis, ddgs, dsas, dsa, dRo, dRn, dRe, dRp, dRq, dRdp, dRdq, dRqi, dRdg, dRsa, dRs, dRa, dKo, dKn, dKe, dKp, dKq, dKdp, dKdq, dKqi, dKdg, dKsa, dKs, dKa, wO, wN, wE, wP, wQ, wDp, wDq, wQi, wDg, wSa, wS, k1, k2, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsl; omega⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, below `rsp`. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩

theorem sub_sub' (p : Addr) (a b : Nat) : p - BitVec.ofNat 64 a - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem frame_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (stkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem ret_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

/-- An address of an input: in no writable region of the frame's state, nor
below the frame. -/
theorem SPre.outside {s : State} (hp : SPre G s) {R : Region} (hO : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint R)
    (hS : R.Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩) (hK : (stkR s).Disjoint R) {a : Addr}
    (ha : R.Contains a 1) : Outside (⟨fb s, frameBytes⟩ :: s.wr) (fb s) a := by
  refine ⟨fun r hr hc => ?_, fun hc => hK a (ret_sub s a hc) ha⟩
  rw [List.mem_cons, hp.hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hK a (frame_sub s a hc) ha
  · exact hO a hc ha
  · exact hS a ha hc

end VG.Proof.RsaPss.X86_64
