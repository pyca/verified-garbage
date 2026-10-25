module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCtx
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the call

The original arguments of the public operation, then `pre` and `pre_len`
from the stack arguments 6 and 7 (`callArgs_ok`); the precondition of
`vg_rsa_public_precomputed_checked` (`call_pre`), and what the call leaves
(`call_ok`): the frame and its slots, as the original call does
(`AfterCall`), and, if `pre` holds the values for `n`, the result of the
public operation in `out`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)

/-! ## The arguments -/

/-- A stack argument, past stores to the frame. -/
theorem arg_keep {s : State} (hp : PPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp.toEPre
  have := hp.sp3
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

theorem arg_read {s t : State} (hp : PPre s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 8) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd]
  apply (Covers.one hp.args).left
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- `pre` and `pre_len` in place of `n` and `n_len`. -/
theorem load_pre {s t : State} (hp : PPre s) (h : PreCall s t) :
    WP isa (.block [.mov .rdx (.mem (arg 6)), .mov .rcx (.mem (arg 7))]) t fun u =>
      Keep [.rdx, .rcx] t u ∧ u.mem = t.mem ∧ u.gpr .rdx = stackArg s 6 ∧ u.gpr .rcx = stackArg s 7 := by
  refine WP.keep [.rdx, .rcx] ?_ rfl |> WP.mono <| fun u ⟨h, k⟩ => ⟨k, h⟩
  xrun [ea_arg (s := s), h.rsp, arg_read hp h.rd (show 6 < 8 by decide), arg_read hp h.rd (show 7 < 8 by decide),
    arg_keep hp h.out (show 6 < 8 by decide), arg_keep hp h.out (show 7 < 8 by decide)]

/-- Before the call, with its arguments in registers. -/
def J5 (s t : State) : Prop :=
  PreCall s t ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 6 ∧
    t.gpr .rcx = stackArg s 7 ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

theorem callArgs_ok {s t : State} (hp : PPre s) (h : PreCall s t) :
    WP isa (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs) t fun u =>
      J5 s u ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  unfold Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs
  rw [WP.block_append_iff]
  refine WP.mono (callArgs_run hp.toEPre h) fun t' ⟨hm, hdi, hsi, _, _, h8, h9, k⟩ => ?_
  have h' : PreCall s t' := ⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd,
    k.2.2.trans h.wr, hm ▸ h.out, hm ▸ h.slots, hm ▸ h.sZ, hm ▸ h.em⟩
  refine WP.mono (load_pre hp h') fun u ⟨k', hm', hdx, hcx⟩ => ?_
  exact ⟨⟨⟨(k'.gpr (by decide)).trans h'.rsp, k'.2.1.trans h'.rd, k'.2.2.trans h'.wr, hm' ▸ h'.out,
    hm' ▸ h'.slots, hm' ▸ h'.sZ, hm' ▸ h'.em⟩, (k'.gpr (by decide)).trans hdi, (k'.gpr (by decide)).trans hsi,
    hdx, hcx, (k'.gpr (by decide)).trans h8, (k'.gpr (by decide)).trans h9⟩, (k.trans k').mono (by decide)⟩

/-! ## The callee's view -/

/-- What `vg_rsa_public_precomputed_checked` reads: `pre`, `e`, `EM` and its
stack arguments. -/
def callRd (s : State) : List Region :=
  [preR s, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩, ⟨fb s, 32⟩]

theorem call_pre {s t : State} (hp : PPre s) (h : J5 s t) :
    Proof.Bignum.X86_64.pdContract.pre (t.callEntry.withRegions (callRd s) (pubWr s)) := by
  obtain ⟨h, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have e0 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have e1 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = s.gpr .rcx := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a1
  have e2 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg s 4 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a2
  have e3 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg s 5 := by
    rw [stackArg_entry h.rsp _ _ (by decide)]; exact h.slots.a3
  simp only [pdContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, h.rsp,
    stackArgAddr_entry h.rsp, e0, e1, e2, e3, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp.toEPre
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e5 : encStack = 1120 := rfl
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfb : fb s = off (kb s) 8 := fb_eq s
  have sM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) := frame_sub s (by omega)
  have sA : Region.Sub ⟨fb s, 32⟩ (stkR s) := by
    have := frame_sub s (d := 0) (n := 32) (by decide); simpa only [off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨kb s, 8⟩ (stkR s) := Region.sub_prefix (by decide)
  have dMA : (⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨fb s, 32⟩ :=
    Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨kb s, 8⟩ : Region).Disjoint ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ := by
    rw [hfb, off_off]; exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨kb s, 8⟩ : Region).Disjoint ⟨fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (off (fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hfb, off_off]; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ := by have := hp.dKo; rwa [hsi'] at this
  have dOq : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint (preR s) := by
    have := hp.preOut; rw [outR, hsi'] at this; exact this.symm
  have dOe : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ := by
    have := hp.dOe; rwa [hsi'] at this
  have dOs : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ := by
    have := hp.dOs; rwa [hsi'] at this
  have wO : (s.gpr .rdi).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by have := hp.wO; omega
  refine ⟨by omega, rfl, rfl, dOq, dOe, (dKo.sub_left sM).symm, dOs, (dKo.sub_left sA).symm, hp.preScr, hp.des,
    (hp.dKs.sub_left sM), (hp.dKs.sub_left sA).symm, dKo.sub_left sR, hp.preStack.symm.sub_left sR,
    hp.dKe.sub_left sR, dRM, hp.dKs.sub_left sR, dRA, wO, hp.preWrap, hp.wE, wM, hp.wS, ⟨hk1, hk2⟩, hp.preLen,
    trivial, hp.L1, hp.L2, hp.hsl⟩

theorem call_covers {s t : State} (hp : PPre s) (h : PreCall s t) :
    Covers (callRd s ++ pubWr s) (t.rd ++ t.wr) ∧ Covers (pubWr s) t.wr := by
  obtain ⟨-, cw⟩ := pub_covers hp.toEPre h
  have hk2 := hp.k2
  have e2 : oEM = 80 := rfl
  have e3 : frameBytes = 1112 := rfl
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  have cr : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩]
      (t.rd ++ t.wr) := by rw [h.rd]; exact hp.hrd.left
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.rd]; exact (Covers.one hp.pre).left
  · exact (Covers.of_mem (by intro r hr; rw [List.mem_singleton.mp hr]; simp)).trans cr
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only; omega⟩
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega⟩

/-- `pre`, unchanged where the function writes. -/
theorem pre_words {s : State} {m : Mem} (hp : PPre s) (hf : Frame [stkR s, outR s, scrR s] s.mem m) :
    Spec.Rsa.wordsAt m (stackArg s 6) (stackArg s 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat := by
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

/-- After the call: the frame, and the public operation's result if `pre`
holds the values for `n`. -/
structure PostCallP (s t : State) : Prop extends AfterCall s t where
  res : Spec.Rsa.publicPrecompute (nB s) = some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) →
    Spec.Rsa.written t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (nB s) (eB s) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)))

theorem call_ok (v : PublicImpl) {s t : State} (hp : PPre s) (hj : J5 s t) :
    WP isa (.call v.name v.code) t fun t' => PostCallP s t' ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hpre := call_pre hp hj
  obtain ⟨h, hdi, hsi, hdx, hcx, h8, h9⟩ := hj
  obtain ⟨hc, hw⟩ := call_covers hp h
  refine WP.call_mx (s := t) (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩) (rd := callRd s)
    (wr := pubWr s) v.ok v.nosp (by rw [v.depth]; decide) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, h.rsp] at hf
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)
  have hE0 : stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb s) oEM := by
    rw [stackArg_entry h.rsp _ _ (by decide)]
    have := h.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  have hem : Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) oEM) (s.gpr .rcx).toNat =
      Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [← h.em]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (callEntry_frame h.rsp).bytes (R := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by show (s.gpr .rcx).toNat ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr]
    exact slot_apart hp.toEPre (d := oEM) (n := (s.gpr .rcx).toNat) (by omega) _
      (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [pdChkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hE0, hem, hm₂,
    hg₂ .rax (by decide)] at hpost
  rw [pre_words hp hfE,
    bytes_of_frame hfE hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm (by have := hp.wE; omega)]
    at hpost
  have hkeep : ∀ {d : Nat}, d + 8 ≤ oEM → word s'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf.readW (Region.contains_self _ _) (slot_apart hp.toEPre (by omega)) (by decide)
  have hkeep0 : s'.mem.readW (fb s) 64 = t.mem.readW (fb s) 64 := by
    have := hkeep (d := 0) (by decide); simp only [Bignum.word, off_zero] at this; exact this
  refine ⟨⟨⟨(hcs .rsp (by decide)).trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    frame_call (frame_of_outside h.out) hf fun r hr => ?_,
    ⟨(hkeep (by decide)).trans h.slots.sOut, (hkeep (by decide)).trans h.slots.sN,
      (hkeep (by decide)).trans h.slots.sK, (hkeep (by decide)).trans h.slots.sE,
      (hkeep (by decide)).trans h.slots.sEl, hkeep0.trans h.slots.a0, (hkeep (by decide)).trans h.slots.a1,
      (hkeep (by decide)).trans h.slots.a2, (hkeep (by decide)).trans h.slots.a3⟩,
    (hkeep (by decide)).trans h.sZ⟩, fun hq => hpost _ (bytesAt_len ..) hq⟩, hcs, hmx⟩
  simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr (.inl (by rw [outR, hsi']; exact sub_refl _))
  · exact .inr (.inr (sub_refl _))
  · exact .inl (ret_sub s)

end VG.Proof.RsaPkcs1Enc.X86_64.Pc
