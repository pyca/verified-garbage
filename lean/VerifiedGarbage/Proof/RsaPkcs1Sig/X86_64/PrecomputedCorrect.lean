import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCall

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum.X86_64 Ver
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
        (.inr (by decide : 0 + 8 ≤ oEM1)) (by have := hp.k2; unfold oEM1; omega) (by decide))
      (by dsimp only; have := hp.k2; omega) (List.mem_range.mp hi)

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
    xrun [ea_sp, he.rsp, hr, Bignum.X86_64.word, off]
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
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold frameBytes; omega) ?_
    unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.body
    refine WP.seq (WP.mono_mx (by decide) (args_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (call_ok v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (after_ok hp he₂ hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hax⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, ret_frame hp.toPreV he₃.mem, ?_⟩, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
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
