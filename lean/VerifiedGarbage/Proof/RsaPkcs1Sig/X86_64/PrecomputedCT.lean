module

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Precomputed
meta import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode
meta import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed

/-! ### `RsaPkcs1Sig.X86_64.PrecomputedContract`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.X86_64.PrecomputedCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86_64.PrecomputedCtx`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 Ver

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- All seven stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The original padding precondition and the additional read-only cache. -/
structure Pre (s : State) : Prop extends PreV s where
  args : InRegions s.rd (stackArgAddr s 0) 56
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  pre : InRegions s.rd (stackArg s 5) ((stackArg s 6).toNat * 8)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- The shared signature supplies the precondition for both the original
padding code and the precomputed public operation. -/
theorem pre_of {s : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack).pre s) : Pre s := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, verStack, stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, dns, des, dds, dgs, dsp, dsa, -, -, -, -, dRs, -, -,
    dKn, dKe, dKd, dKg, dKs, dKp, dKa, wN, wE, wD, wG, wS, wP, ⟨k1, k2⟩, L1, L2, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 40⟩ ⟨stackArgAddr s 0, 56⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega_using [sp2], ?_, hwr, dns, des, dds, dgs, dsa.sub_right ha, dRs,
    dKn, dKe, dKd, dKg, dKs, dKa.sub_right ha, wN, wE, wD, wG, wS, k1, k2, L1, L2, hsl⟩,
    ?_, dsa.symm, dKa.symm, ?_, dsp.symm, dKp.symm, wP, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 56⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Pc

end

end

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 Ver
open VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 1, (s.gpr .rsi).toNat⟩,
    ⟨fb s, 32⟩]

/-- Any of the seven arguments, unchanged by writes to the frame or scratch. -/
theorem arg_keep {s t : State} (hp : Pre s) (he : Env s t) {j : Nat} (hj : j < 7) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine he.mem.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [Ver.stackArgAddr_eq s j]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.argsStack
    · exact hp.argsScr

theorem arg_read {s t : State} (hp : Pre s) (he : Env s t) {j : Nat} (hj : j < 7) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [he.rd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [Ver.stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- Switch just the modulus arguments after the original argument setup. -/
theorem load_pre {s t : State} (hp : Pre s) (he : Env s t) :
    WP isa (.block [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧
        u.gpr .rdx = stackArg s 5 ∧ u.gpr .rcx = stackArg s 6 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [@arg_ea s, he.rsp, arg_read hp he (show 5 < 7 by decide), arg_read hp he (show 6 < 7 by decide),
    arg_keep hp he (show 5 < 7 by decide), arg_keep hp he (show 6 < 7 by decide)]

theorem call_pre {s t : State} (hp : Pre s) (hsig : stackArg s 2 = s.gpr .rsi) (hsp : t.gpr .rsp = fb s)
    (hw0 : word t.mem (fb s) 0 = stackArg s 1) (hw1 : word t.mem (fb s) 8 = s.gpr .rsi)
    (hw2 : word t.mem (fb s) 16 = stackArg s 3) (hw3 : word t.mem (fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = off (fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 5)
    (hcx : t.gpr .rcx = stackArg s 6) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry hsp _ _ (by omega_using [hi])
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp.toPreV
  have e1 : verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub (em1R s) (stkR s) := frame_sub s (by unfold oEM1 frameBytes; omega_using [hk2])
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have dMA : (em1R s).Disjoint ⟨fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega_using [e2, hk2])
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint (em1R s) := by
    simp only [em1R]; rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega_using [e2, hk2])
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega_using [])
  have wM : (off (fb s) oEM1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega_using [hK1])]; unfold oEM1; omega_using [hK1, e1]), hfb, ← off,
      toNat_off (by omega_using [hK1])]; unfold oEM1; omega_using [hK1, e1, hk2]
  have dKg : (stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rsi).toNat⟩ := by rw [← hsig]; exact hp.dKg
  have dgs : (⟨stackArg s 1, (s.gpr .rsi).toNat⟩ : Region).Disjoint (scrR s) := by rw [← hsig]; exact hp.dgs
  have wG : (stackArg s 1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega_using [hK1], rfl, rfl, hp.preStack.symm.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.preScr, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM, hp.preStack.symm.sub_left sR, hp.dKe.sub_left sR,
    dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.preWrap, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1,
    hp.L2, hp.hsl⟩


theorem call_covers {s t : State} (hp : Pre s) (hsig : stackArg s 2 = s.gpr .rsi) (he : Env s t) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [pubWr, em1R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oEM1, rfl, by dsimp only; unfold oEM1 frameBytes; omega_using [hk2]⟩
    · exact ⟨_, hscr, 0, z _, by simp only [scrR]; omega_using []⟩
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
      ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩,
      ⟨stackArgAddr s 0, 40⟩] (t.rd ++ t.wr) := by rw [he.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [he.rd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · rw [← hsig]
    exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega_using []⟩


theorem pre_words {s : State} {m : Mem} (hp : Pre s) (hf : Frame [stkR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega_using [this]) (by have := hp.preWrap; have := List.mem_range.mp hi; omega_arith)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.preStack
    · exact hp.preScr

theorem call_ok (v : PublicImpl) {s t : State} (hp : Pre s) (hsig : stackArg s 2 = s.gpr .rsi) (he : Env s t)
    (hw0 : word t.mem (fb s) 0 = stackArg s 1) (hw1 : word t.mem (fb s) 8 = s.gpr .rsi)
    (hw2 : word t.mem (fb s) 16 = stackArg s 3) (hw3 : word t.mem (fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = off (fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = stackArg s 5)
    (hcx : t.gpr .rcx = stackArg s 6) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => Env s t' ∧
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
        some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) →
      Spec.Rsa.written t'.mem (off (fb s) oEM1) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat))) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := call_covers hp hsig he
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s) (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide)
    (Pc.call_pre (s := s) (t := t) hp hsig he.rsp hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = stackArg s 1 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans hw0
  have hfE : Frame [stkR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk hs hl =>
    bytes_of_frame hfE hk hs hl
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE, b hp.dKe hp.des.symm (by have := hp.wE; omega_using []),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dgs.symm) (by omega_using [])] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hpre => hpost _ (bytesAt_length ..) hpre, hcs, hmx⟩
  · simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oEM1 frameBytes; omega_using [hk2]))
    · exact .inr (sub_refl _)
    · exact .inl (below_sub s)
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sEl
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sH
  · rw [slot_keep hf (slot_apart hp.toPreV (by decide) (by decide))]; exact he.sD

end VG.Proof.RsaPkcs1Sig.X86_64.Pc

end

end

/-! ### `RsaPkcs1Sig.X86_64.PrecomputedCorrect`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 Ver
open VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)
open Spec.RsaPkcs1Sig

/-- Saving the public operation's status does not change the argument slots. -/
theorem save_ok {s t : State} (hp : Pre s) (he : Env s t) :
    WP isa (.block [.store (sp 0) .rax, .mov32 .rax (.imm 1)]) t fun u =>
      Env s u ∧ u.gpr .rax = 1 ∧ word u.mem (fb s) 0 = t.gpr .rax ∧
      Spec.Rsa.bytesAt u.mem (off (fb s) oEM1) (s.gpr .rsi).toNat =
        Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat := by
  have hr : InRegions t.wr (fb s) 8 := by
    rw [he.wr]
    exact ⟨_, List.mem_cons_self .., by simpa only [BitVec.add_zero] using
      (Offset.contains_base (fb s) (d := 0) (by decide : 0 + 8 ≤ frameBytes) (by decide : 0 < 2 ^ 64))⟩
  have hx : WP isa (.block [.store (sp 0) .rax, .mov32 .rax (.imm 1)]) t fun u =>
      Keep [.rax] t u ∧ u.mem = t.mem.writeW (fb s) (t.gpr .rax) ∧ u.gpr .rax = 1 := by
    refine WP.keep [.rax] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
    xrun [ea_sp, he.rsp, hr]
  refine WP.mono hx fun u ⟨hk, hm, ha⟩ => ?_
  have hf0 : Frame [⟨fb s, 8⟩] t.mem (t.mem.writeW (fb s) (t.gpr .rax)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hf : Frame [stkR s, scrR s] t.mem u.mem := by
    rw [hm]
    exact frame_call (Frame.refl _ _) hf0 fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inl (by simpa only [off, BitVec.add_zero] using frame_sub s (d := 0) (n := 8) (by decide))
  refine ⟨⟨(hk.gpr (by decide)).trans he.rsp, hk.2.1.trans he.rd, hk.2.2.trans he.wr,
    he.mem.trans hf, ?_, ?_, ?_, ?_, ?_, ?_⟩, ha, ?_, ?_⟩
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sN
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sK
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sE
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sEl
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sH
  · rw [hm, word_wo0 _ _ _ (by decide) (by decide)]; exact he.sD
  · rw [hm]; exact word_self0 ..
  · rw [hm]
    unfold Spec.Rsa.bytesAt
    apply List.map_congr_left
    intro i hi
    have hf0 : Frame [⟨fb s, 8⟩] t.mem (t.mem.writeW (fb s) (t.gpr .rax)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact hf0.bytes (R := ⟨off (fb s) oEM1, (s.gpr .rsi).toNat⟩) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      simpa only [off, BitVec.add_zero] using Offset.disjoint (fb s) (d := oEM1) (e := 0)
        (.inr (by decide : 0 + 8 ≤ oEM1)) (by have := hp.k2; unfold oEM1; omega_using [this]) (by decide))
      (by dsimp only; have := hp.k2; omega_using []) (List.mem_range.mp hi)

/-- Combining the padding result with the saved status uses no branch. -/
theorem mask_ok {s t : State} (he : Env s t) :
    WP isa (.block [.mov .rcx (.mem (sp 0)), .alu32 .and .rax (.reg .rcx)]) t fun u =>
      Env s u ∧ (u.gpr .rax).setWidth 32 =
        (t.gpr .rax).setWidth 32 &&& (word t.mem (fb s) 0).setWidth 32 := by
  have hr : InRegions (t.rd ++ t.wr) (fb s) 8 := by
    rw [he.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), by simpa only [BitVec.add_zero] using
      (Offset.contains_base (fb s) (d := 0) (by decide : 0 + 8 ≤ frameBytes) (by decide : 0 < 2 ^ 64))⟩
  have hx : WP isa (.block [.mov .rcx (.mem (sp 0)), .alu32 .and .rax (.reg .rcx)]) t fun u =>
      Keep [.rax, .rcx] t u ∧ u.mem = t.mem ∧ (u.gpr .rax).setWidth 32 =
        (t.gpr .rax).setWidth 32 &&& (word t.mem (fb s) 0).setWidth 32 := by
    refine WP.keep [.rax, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
    xrun [ea_sp, he.rsp, hr, Bignum.word, off]
  exact WP.mono hx fun u ⟨hk, hm, ha⟩ => ⟨he.regs (hk.gpr (by decide)) hm hk.2.1 hk.2.2, ha⟩


/-- The padding check is safe for every cache and correct when the cache matches. -/
theorem after_ok {s t : State} (hp : Pre s) (he : Env s t)
    (hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
        some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) →
      Spec.Rsa.written t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat ((t.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat))) :
    WP isa Impl.RsaPkcs1Sig.X86_64.Precomputed.afterPub t fun u => Env s u ∧
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
        some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) →
       (u.gpr .rax).setWidth 32 = if verifyId
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat) then 1 else 0) := by
  unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.afterPub
  refine WP.seq (WP.mono (save_ok hp he) fun t₁ ⟨he₁, ha₁, hs₁, hb₁⟩ => ?_)
  let em := Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat
  refine WP.seq (WP.mono (afterPub_checked (some em) hp.toPreV he₁ ⟨by rw [ha₁]; decide, hb₁⟩)
    fun t₂ ⟨he₂, ha₂, hs₂⟩ => ?_)
  refine WP.mono (mask_ok he₂) fun u ⟨heu, hau⟩ => ⟨heu, fun hpre => ?_⟩
  have hw' := hw hpre
  rw [hau, hs₂, hs₁, ha₂]
  let nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  let eB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  let gB := Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat
  rw [verifyId_eq nB eB _ _ gB (by simp [nB, gB, bytesAt_length]), bytesAt_length]
  cases ho : Spec.Rsa.publicOpChecked nB eB gB with
  | none =>
    rw [ho] at hw'
    rw [hw'.1]
    have hz (b : Bool) : ((if b then 1 else 0) : BitVec 32) &&& 0 = 0 := by cases b <;> rfl
    exact hz _
  | some out =>
    rw [ho] at hw'
    have hem : em = out := hw'.2
    rw [hem, hw'.1]
    have h1 (b : Bool) : ((if b then 1 else 0) : BitVec 32) &&& 1 = (if b then 1 else 0) := by cases b <;> rfl
    exact h1 _

theorem args_ok {s A : State} (hp : Pre s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block Impl.RsaPkcs1Sig.X86_64.Precomputed.pubArgs) A fun t => Env s t ∧
      word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rsi ∧
      word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
      t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 5 ∧
      t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (Ver.pubArgs_ok hp.toPreV hA hAm) fun t ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs⟩ => ?_
  refine WP.mono (load_pre hp he) fun u ⟨hk, hm, hdx', hcx'⟩ => ?_
  refine ⟨he.regs (hk.gpr (by decide)) hm hk.2.1 hk.2.2, by rw [hm]; exact hw0,
    by rw [hm]; exact hw1, by rw [hm]; exact hw2, by rw [hm]; exact hw3,
    (hk.gpr (by decide)).trans hdi, (hk.gpr (by decide)).trans hsi, hdx', hcx',
    (hk.gpr (by decide)).trans h8, (hk.gpr (by decide)).trans h9, fun r hr hr' => ?_⟩
  rw [hk.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  exact hcs r hr hr'

def post (s u : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat) → verContract.post s u

theorem code_correct (v : PublicImpl) (s : State) (h : (verifyPrecomputedContract abi verStack).pre s) :
    ∃ t s', Exec isa (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  have hp := pre_of h
  have hk2 := hp.k2
  suffices hw : WP isa (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) s fun s' => abiPreserved s s' ∧ post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.code
  refine WP.seq (WP.mono_mx (by decide) (lenCheck_ok hp.toPreV) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  by_cases hsig : stackArg s 2 = s.gpr .rsi
  · refine WP.ite false (by simp [eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
    have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [allocState_gpr, fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    have hfb : fb t₀ = fb s := by simp only [fb, hsp₀]
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold frameBytes; omega_using [this]) ?_
    unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.body
    refine WP.seq (WP.mono_mx (by decide) (args_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (call_ok v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (after_ok hp he₂ hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hax⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2], fun m uu fm => ?_⟩
    rw [hfb] at fm
    have hs := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (d := 0) (n := frameBytes) (by omega_using [])
    simp only [off, BitVec.add_zero] at hs
    refine ⟨⟨fun r hr => ?_, ret_frame hp.toPreV (he₃.mem.trans (fm.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., hs⟩)), ?_⟩, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · have hfr : (freed frameBytes t₃).gpr .rax = t₃.gpr .rax := rfl
      intro hpre
      simpa only [verContract, hfr, hsig] using hax hpre
  · refine WP.ite true (by simp [eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (ret0_ok t₀) fun u ⟨hK, hm, hax⟩ hmx =>
      ⟨⟨fun r hr => ?_, by rw [hm, hm₀], by rw [hmx, hmx₀]⟩, ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · intro _
      simp only [verContract, hax]
      rw [verifyId_len _ (by
        simp only [bytesAt_length]
        intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]
      rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Pc

end

end


@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 Ver

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack).pre
  post := post
  pub a s := verContract.pub a s ∧ stackArg a 5 = stackArg s 5 ∧ stackArg a 6 = stackArg s 6 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

def satState : State := { verSatState with
  mem := fun a => if a = 0x10031 then 0x50 else if a = 0x10038 then 16 else verSatState.mem a
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10008, 56⟩] }

theorem implies : contract.Implies (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, contract, post, verContract, verStack, stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
      abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx, a0, a2])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he, hd, hs⟩ := leak_eq4 (by simp [Spec.Rsa.bytesAt, hsi]) (by simp [Spec.Rsa.bytesAt, hcx])
      (by simp [Spec.Rsa.bytesAt, a0]) hb
    refine ⟨⟨?_, h8, by simp only [stackArgs_five, a0, a1, a2, a3, a4], hn, he, hd, hs⟩, a5, a6, hp'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq]
    [satState, verSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Sig.X86_64.Pc

end

end

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.PcCT

open Ver Pc
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pub_refl (s : State) : contract.pub s s := ⟨Ver.pub_refl s, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem Sib.r8 {a s : State} (h : Sib a s) : (s.gpr .r8).setWidth 32 = (a.gpr .r8).setWidth 32 := h.2.1.2.1.symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 5) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.e {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.1.2.2.2.2.1.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.pre {a s : State} (h : Sib a s) :
    Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat := h.2.2.2.2.symm

theorem Sib.prePtr {a s : State} (h : Sib a s) : stackArg s 5 = stackArg a 5 := h.2.2.1.symm

theorem Sib.preLen {a s : State} (h : Sib a s) : stackArg s 6 = stackArg a 6 := h.2.2.2.1.symm

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- A condition `J` gives as a function of the public data. -/
theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rsi)

def JA (s t : State) : Prop :=
  ∃ t₀, JL s t₀ ∧ stackArg s 2 = s.gpr .rsi ∧ t = allocState frameBytes t₀

def J1 (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rsi ∧
    word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 5 ∧
    t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧ stackArg s 2 = s.gpr .rsi

def J2 (s t : State) : Prop := Env s t

def JS (s t : State) : Prop := Env s t ∧ t.gpr .rax = 1

def J3 (s t : State) : Prop := Env s t ∧ t.zf = some false

def J4 (s t : State) : Prop :=
  Env s t ∧ t.gpr .r8 = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rsi ∧
    t.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧ t.gpr .rsi = s.gpr .r9 ∧ t.gpr .r9 = stackArg s 0

/-! ## The call -/

/-- What the precomputed public operation's contract makes public. -/
theorem pub_view {a s t : State} (S : Sib a s) (h : J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [off (fb a) oEM1, a.gpr .rsi, stackArg a 5, stackArg a 6, a.gpr .rdx, a.gpr .rcx, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = a.gpr .rsi ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := Pc.pre_of S.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rsi) (by decide),
      S.prePtr, S.preLen, S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.gpr (r := .rsi) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)), S.pre]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes he _ _ hp.dKe hp.des.symm (by have := hp.wE; omega_using []), S.e]

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (Pc.pre_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (Pc.pre_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hg₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hg₂⟩ := j₂
  have p₁ := Pc.call_pre (Pc.pre_of S₁.1) hg₁ he₁.rsp hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ := Pc.call_pre (Pc.pre_of S₂.1) hg₂ he₂.rsp hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem lenCheck_two : RelCT isa (Two (At J0)) (.block lenCheck) (Two (At JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin (fun s => s.gpr .rsp) (fun s t h => by rw [h]) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (lenCheck_ok (Pc.pre_of S.1).toPreV) fun _ h => ⟨s, S, h⟩

theorem pubArgs_two : RelCT isa (Two (At JA)) (.block Impl.RsaPkcs1Sig.X86_64.Precomputed.pubArgs) (Two (At J1)) :=
  two_piece [.rsp] (pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [allocState_gpr, fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (args_ok (Pc.pre_of S.1) hA hm₀)
        fun _ ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, _⟩ =>
          ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩

theorem call_two (v : PublicImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) (Two (At J2)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩ =>
    WP.mono (call_ok v (Pc.pre_of S.1) hg he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h =>
      ⟨s, S, h.1⟩

theorem save_two : RelCT isa (Two (At J2))
    (.block [.store (sp 0) .rax, .mov32 .rax (.imm 1)]) (Two (At JS)) :=
  two_piece [.rsp] (pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (save_ok (Pc.pre_of S.1) he) fun _ h => ⟨s, S, h.1, h.2.1⟩

theorem test0_two : RelCT isa (Two (At JS)) (.block test0) (Two (At J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, ha⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ =>
      ⟨s, S, he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hz, ha]; rfl⟩

theorem encArgs_two : RelCT isa (Two fun a t => At J3 a t ∧ isa.eval .e t = some false) (.block encArgs)
    (Two (At J4)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pins_rsp (J := J3) (fun _ _ h => h.1.rsp) _ _ _ h₁.1 h₂.1 _ (List.mem_singleton_self _))
    (by taint_decide)
    fun _ t ⟨⟨s, S, he, _⟩, _⟩ => WP.mono (encArgs_ok (Pc.pre_of S.1).toPreV he)
      fun u ⟨hK, hm, h8, hcx, hdx, hsi, h9⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, hsi, h9⟩

theorem encTail_ct : RelCT isa (Two (At J4)) (.seq encode tail) fun _ _ => True :=
  encTail_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
    · exact pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
    · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => ((s.gpr .r8).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
        (fun _ _ S => by rw [S.r8]) h₁ h₂
    · exact pin (fun s => s.gpr .r9) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => stackArg s 0) (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.arg (by decide)) h₁ h₂

theorem padding_ct : RelCT isa (Two (At JS)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq test0_two (two_ite ?_ ret0_ct (RelCT.seq encArgs_two encTail_ct))
  exact pinEval (fun _ => some false) (fun _ _ h => by simp only [eval, h.2]) (fun _ _ _ => rfl)

theorem padding_two : RelCT isa (Two (At JS)) afterPub (Two (At J2)) :=
  two_post padding_ct fun _ t ⟨s, S, he, ha⟩ =>
    WP.mono (afterPub_checked (some (Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat))
      (Pc.pre_of S.1).toPreV he ⟨by rw [ha]; decide, rfl⟩) fun _ h => ⟨s, S, h.1⟩

theorem mask_ct : RelCT isa (Two (At J2))
    (.block [.mov .rcx (.mem (sp 0)), .alu32 .and .rax (.reg .rcx)]) fun _ _ => True :=
  two_taint [.rsp] (pins_rsp fun _ _ h => h.rsp) (by taint_decide)

theorem afterPub_ct : RelCT isa (Two (At J2)) Impl.RsaPkcs1Sig.X86_64.Precomputed.afterPub fun _ _ => True :=
  RelCT.seq save_two (RelCT.seq padding_two mask_ct)

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At JA))
    (Impl.RsaPkcs1Sig.X86_64.Precomputed.body v.name v.code) fun _ _ => True :=
  RelCT.seq pubArgs_two (RelCT.seq (call_two v) afterPub_ct)

/-! ## The frame -/

theorem code_ct (v : PublicImpl) : RelCT isa (Two (At J0)) (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) fun _ _ => True := by
  unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.code
  refine RelCT.seq lenCheck_two (two_ite ?_ ret0_ct (relCT_alloc ((body_ct v).mono ?_ fun _ _ h => h)))
  · refine pinEval (fun s => some (!(stackArg s 2 == s.gpr .rsi))) (fun s t h => by simp only [eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rsi := fun j e => by
      simp only [eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) :=
  RelCT.constantTime ((code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_verify_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack) :=
  have hct : ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) := code_constantTime v
  Verified.of_correct (k := contract) (Pc.code_correct v) hct Pc.implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) : (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Sig.X86_64.Precomputed.code, Impl.RsaPkcs1Sig.X86_64.Precomputed.body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.PcCT
