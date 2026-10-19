module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 5 and 6 (`pubArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): `Env`, and, if `pre` holds the values for `n`, RSAVP1 of the
signature in `EM₁`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  arg_ea stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

/-! ## The arguments -/

theorem arg_keep {s t : State} (hp : PPreR s) (he : Env s t) {j : Nat} (hj : j < 7) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine he.mem.readW (r := argsR s) ?_ (fun r hr => ?_) (by decide)
  · rw [Ver.stackArgAddr_eq s j]
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.argsStack
    · exact hp.argsOut
    · exact hp.argsScr

theorem arg_read {s t : State} (hp : PPreR s) (he : Env s t) {j : Nat} (hj : j < 7) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [he.rd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [Ver.stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPreR s) (he : Env s t) :
    WP isa (.block [.mov .rdx (.mem (arg 5)), .mov .rcx (.mem (arg 6))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 5 ∧ u.gpr .rcx = stackArg s 6 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [@arg_ea s, he.rsp, arg_read hp he (show 5 < 7 by decide), arg_read hp he (show 6 < 7 by decide),
    arg_keep hp he (show 5 < 7 by decide), arg_keep hp he (show 6 < 7 by decide)]

/-- Before the call, with its arguments in registers and on the stack. -/
def J1 (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 5 ∧
    t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧ stackArg s 2 = s.gpr .rcx

theorem pubArgs_ok {s A : State} (hp : PPreR s) (hsig : stackArg s 2 = s.gpr .rcx)
    (hA : Keep [.rax] (allocState frameBytes s) A) (hAm : A.mem = s.mem) :
    WP isa (.block Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs) A fun t => J1 s t ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs
  rw [WP.block_append_iff]
  refine WP.mono (Rec.pubArgs_ok hp.toPreR hA hAm)
    fun t ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, _, _, h8, h9, hcs⟩ => ?_
  refine WP.mono (load_pre hp he) fun u ⟨hk, hm, hdx', hcx'⟩ => ?_
  refine ⟨⟨he.regs (hk.gpr (by decide)) hm hk.2.1 hk.2.2, by rw [hm]; exact hw0,
    by rw [hm]; exact hw1, by rw [hm]; exact hw2, by rw [hm]; exact hw3,
    (hk.gpr (by decide)).trans hdi, (hk.gpr (by decide)).trans hsi, hdx', hcx',
    (hk.gpr (by decide)).trans h8, (hk.gpr (by decide)).trans h9, hsig⟩, fun r hr hr' => ?_⟩
  rw [hk.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  exact hcs r hr hr'

/-! ## The call -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `sig` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPreR s) (h : J1 s t) :
    pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hsig⟩ := h
  have hsp := he.rsp
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) i = word t.mem (fb s) (8 * i) :=
    fun i hi => stackArg_entry hsp _ _ (by omega)
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp.toPreR
  have e1 : verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub (em1R s) (stkR s) := frame_sub s (by unfold oEM1 frameBytes; omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have hfb : fb s = kb s + BitVec.ofNat 64 8 := fb_eq s
  have dMA : (em1R s).Disjoint ⟨fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint (em1R s) := by
    simp only [em1R]; rw [hfb, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fb s) oEM1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← off, toNat_off (by omega)]; unfold oEM1; omega), hfb, ← off,
      toNat_off (by omega)]; unfold oEM1; omega
  have dKg : (stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rcx).toNat⟩ := by rw [← hsig]; exact hp.dKg
  have dgs : (⟨stackArg s 1, (s.gpr .rcx).toNat⟩ : Region).Disjoint (scrR s) := by rw [← hsig]; exact hp.dgs
  have wG : (stackArg s 1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega, rfl, rfl, hp.preStack.symm.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM,
    hp.dKs.sub_left sM, dMA, hp.preScr, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM,
    hp.preStack.symm.sub_left sR, hp.dKe.sub_left sR, dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM,
    hp.preWrap, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, hp.preLen, trivial, hp.L1, hp.L2,
    hp.hsl⟩

theorem call_covers {s t : State} (hp : PPreR s) (hsig : stackArg s 2 = s.gpr .rcx) (he : Env s t) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨-, cw⟩ := pub_covers hp.toPreR hsig he
  have hk2 := hp.k2
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] (t.rd ++ t.wr) := by
    rw [he.rd]; exact hp.hrd.left
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
      exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPreR s) (hf : Frame [stkR s, outR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro i hi
  apply hf.readW (r := preR s) ?_ ?_ (by decide)
  · exact Offset.contains_base _ (by have := List.mem_range.mp hi; omega)
      (by have := hp.preWrap; have := List.mem_range.mp hi; omega)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.preStack
    · exact hp.preOut
    · exact hp.preScr

/-- Whether `pre` holds the values for `n`. -/
def Consistent (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat)

theorem call_ok (v : PublicImpl) {s t : State} (hp : PPreR s) (h : J1 s t) :
    WP isa (.call v.name v.code) t fun t' => Env s t' ∧
      (Consistent s → Spec.Rsa.written t'.mem (off (fb s) oEM1) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat))) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpre := call_pre hp h
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hsig⟩ := h
  obtain ⟨hc, hw⟩ := call_covers hp hsig he
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s)
    (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = stackArg s 1 :=
    (stackArg_entry he.rsp _ _ (by omega)).trans hw0
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (outR s).Disjoint ⟨p, len⟩ →
      (scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    bytes_of_frame hfE hk ho hs hl
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE, b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dOg) (by rw [← hsig]; exact hp.dgs.symm)
      (by omega)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun hq => hpost _ (bytesAt_length ..) hq,
    hcs, hmx⟩
  · simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (frame_sub s (by unfold oEM1 frameBytes; omega))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sOl
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (slot_apart hp.toPreR (by decide) (by decide))]; exact he.sEl

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc
