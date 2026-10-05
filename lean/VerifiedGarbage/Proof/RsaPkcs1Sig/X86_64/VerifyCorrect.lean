import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-!
# `vg_rsa_pkcs1_verify` on x86-64: correctness

After the call (`afterPub_ok`): the encoding of the hash value into `EM₂`
(`encode_ok`) and the comparison with `EM₁` (`compare_ok`), which is RFC 8017
§8.2.2's verification (`verify_eq_verifyRfc`). With the length check, the
frame's push, the call (`pub_call`) and the pop: `code_correct`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open Spec.RsaPkcs1Sig

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame from `EM₁` on. -/
theorem Env.of {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, ∃ d n, r = ⟨off (fb s) d, n⟩ ∧ oEM1 ≤ d ∧ d + n ≤ frameBytes) : Env s u := by
  have hsl : ∀ {d}, 32 ≤ d → d + 8 ≤ oEM1 → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    slot_keep hf fun r hr => by
      obtain ⟨d', n, rfl, h₁, h₂⟩ := hs r hr
      exact Offset.disjoint _ (.inl (by omega)) (by unfold frameBytes at *; omega)
        (by unfold frameBytes at *; omega)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, frame_call he.mem hf fun r hr => ?_,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl,
    (hsl (by decide) (by decide)).trans he.sH, (hsl (by decide) (by decide)).trans he.sD⟩
  obtain ⟨d, n, rfl, -, h₂⟩ := hs r hr
  exact .inl (frame_sub s h₂)

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE,
    hm ▸ he.sEl, hm ▸ he.sH, hm ▸ he.sD⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : PreV s) (h : d + n ≤ frameBytes) :
    ∀ i < n, InRegions (⟨fb s, frameBytes⟩ :: s.wr) (off (fb s) d + BitVec.ofNat 64 i) 1 := by
  have := fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show off (fb s) d + BitVec.ofNat 64 i = off (fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold frameBytes at *; omega)

/-! ## The blocks after the call -/

theorem test0_ok (t : State) :
    WP isa (.block test0) t fun u => SameF t u ∧ u.zf = some ((t.gpr .rax).setWidth 32 == 0) := by
  xrun [test0]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by rw [sub_beq32]⟩

theorem ret0_ok (t : State) : WP isa ret0 t fun u => Keep [.rax] t u ∧ u.mem = t.mem ∧ u.gpr .rax = 0 := by
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧ u.gpr .rax = 0) (by xrun [ret0]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem result_ok (t : State) :
    WP isa (.block result) t fun u => Keep [.rax] t u ∧ u.mem = t.mem ∧
      u.gpr .rax = if t.gpr .rdx = 0 then 1 else 0 := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdx = t.gpr .rdx ∧
      u.gpr .rax = if t.gpr .rdx = 0 then 1 else 0) (by
    xrun [result]
    by_cases h : t.gpr .rdx = 0
    · rw [h]; decide
    · have hz : ¬ (t.gpr .rdx).toNat < (1 : BitVec 64).toNat := by
        intro h'; apply h; apply BitVec.eq_of_toNat_eq; simp at h' ⊢; omega
      rw [decide_eq_false hz, ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      decide) rfl) fun u ⟨⟨hm, hdx, ha⟩, hK⟩ => ⟨⟨fun r hr => by
      by_cases h : r = .rdx
      · subst h; exact hdx
      · exact hK.gpr (by simp at hr ⊢; exact ⟨hr, h⟩), hK.2⟩, hm, ha⟩

theorem encArgs_ok {s t : State} (hp : PreV s) (he : Env s t) :
    WP isa (.block encArgs) t fun u => Keep [.r8, .rcx, .rdx, .rsi, .r9] t u ∧ u.mem = t.mem ∧
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0 := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r8, .rcx, .rdx, .rsi, .r9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0) (by
    xrun [encArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, he.rsp,
      sx_ofNat (show oEM2 < 2 ^ 31 by decide), hs.ld (d := oK) (by decide), hs.ld (d := oH) (by decide),
      hs.ld (d := oD) (by decide), arg_in hp he.rd (show 0 < 5 by decide), he.arg hp (show 0 < 5 by decide),
      he.sK, he.sH, he.sD]) rfl) fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem cmpArgs_ok {s t : State} (he : Env s t) :
    WP isa (.block cmpArgs) t fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2 := by
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2) (by
    xrun [cmpArgs, lea, List.cons_append, List.nil_append, he.rsp,
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), sx_ofNat (show oEM2 < 2 ^ 31 by decide)]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem bytesAt_eq_iff (m : Mem) (a b : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m a n = Spec.Rsa.bytesAt m b n ↔
      ∀ i < n, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  simp only [Spec.Rsa.bytesAt]
  rw [List.map_inj_left]
  simp only [List.mem_range]

theorem setWidth_byte_eq_zero (d : Byte) : d.setWidth 64 = 0 ↔ d = 0 := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; have := d.isLt; simp at *; omega
  · rintro rfl; rfl

/-! ## Verification by encoding -/

/-- Verification, for a signature of `k` bytes: RSAVP1, then the encoding,
then their comparison. -/
theorem verifyId_eq (nB eB : List Byte) (x : BitVec 32) (H sig : List Byte) (hs : sig.length = nB.length) :
    verifyId nB eB x.toNat H sig =
      match Spec.Rsa.publicOpChecked nB eB sig, encodeId x H nB.length with
      | some em, some em' => em == em'
      | _, _ => false := by
  unfold verifyId encodeId
  cases hid : Hash.ofId x.toNat with
  | none => simp only; split <;> simp_all
  | some h =>
    simp only
    rw [verify_eq_verifyRfc]
    unfold verifyRfc
    rw [ite_eq_left hs]
    cases Spec.Rsa.publicOpChecked nB eB sig <;> cases Spec.RsaPkcs1Sig.encode h H nB.length <;> rfl

theorem afterPub_ok {s t : State} (hp : PreV s) (he : Env s t)
    (hw : Spec.Rsa.written t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat))) :
    WP isa afterPub t fun u => Env s u ∧ (u.gpr .rax).setWidth 32 =
      if verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat) then 1 else 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  set k := (s.gpr .rsi).toNat with hkdef
  set nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) k
  set eB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  set gB := Spec.Rsa.bytesAt s.mem (stackArg s 1) k
  set dB := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  set x := (s.gpr .r8).setWidth 32
  have hnl : nB.length = k := bytesAt_length _ _ _
  have hgl : gB.length = nB.length := by rw [hnl]; exact bytesAt_length _ _ _
  rw [verifyId_eq nB eB x dB gB hgl, hnl]
  unfold afterPub
  refine WP.seq (WP.mono (test0_ok t) fun t₁ ⟨hs₁, hz₁⟩ => ?_)
  have he₁ : Env s t₁ := he.regs (by rw [hs₁.1]) hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2
  have hret0 : ∀ u, Env s u → (∀ o, Spec.Rsa.publicOpChecked nB eB gB = o →
      (match o, encodeId x dB k with | some em, some em' => em == em' | _, _ => false) = false) →
      WP isa ret0 u fun v => Env s v ∧ (v.gpr .rax).setWidth 32 =
        if (match Spec.Rsa.publicOpChecked nB eB gB, encodeId x dB k with
          | some em, some em' => em == em' | _, _ => false) = true then 1 else 0 := fun u hu hf =>
    WP.mono (ret0_ok u) fun v ⟨hK, hm, hax⟩ => ⟨hu.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by
      rw [hf _ rfl, hax]; rfl⟩
  cases hpo : Spec.Rsa.publicOpChecked nB eB gB with
  | none =>
    rw [hpo] at hw
    obtain ⟨hr, -⟩ := hw
    refine WP.ite true (by simp [eval, hz₁, hr]) (fun _ => ?_) (by simp)
    refine WP.mono (hret0 t₁ he₁ fun o ho => ?_) fun v hv => by rw [hpo] at hv; exact hv
    rw [← ho, hpo]
  | some em =>
    rw [hpo] at hw
    obtain ⟨hr, hem⟩ := hw
    refine WP.ite false (by simp [eval, hz₁, hr]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, hsi₂, h9₂⟩ => ?_)
    have he₂ : Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
    have sE2 : Region.Sub ⟨off (fb s) oEM2, k⟩ (stkR s) := frame_sub s (by unfold oEM2 frameBytes; omega)
    have hdl := hp.wD
    have hpre : EPre t₂ x k := {
      rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp [x]
      hk := by rw [hcx₂]
      kle := hk2
      buf := fun i hi => by
        rw [h8₂, he₂.wr]; exact frame_bytes hp (by unfold oEM2 frameBytes; omega) i hi
      rd := fun j hj => by
        rw [hsi₂, he₂.rd, he₂.wr]
        rw [h9₂] at hj
        exact ⟨⟨s.gpr .r9, (stackArg s 0).toNat⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
          Offset.contains_base _ (by omega) (by omega)⟩
      sep := fun j hj i hi => by
        rw [hsi₂, h8₂]
        rw [h9₂] at hj
        exact ne_of_disjoint (hp.dKd.sub_left sE2).symm (by omega) (by omega) hj hi }
    have hdB : Spec.Rsa.bytesAt t₂.mem (t₂.gpr .rsi) (t₂.gpr .r9).toNat = dB := by
      rw [hsi₂, h9₂, hm₂, hs₁.2.1]
      exact bytes_of_frame he.mem hp.dKd hp.dds.symm (by omega)
    refine WP.seq (WP.mono (encode_ok hpre) fun t₃ ⟨hK₃, hpost⟩ => ?_)
    rw [hdB] at hpost
    unfold tail
    refine WP.seq (WP.mono (test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
    cases hE : encodeId x dB k with
    | none =>
      rw [hE] at hpost
      obtain ⟨hax, hm₃⟩ := hpost
      have he₄ : Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
        (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
      refine WP.ite true (by simp [eval, hz₄, hax]) (fun _ => ?_) (by simp)
      refine WP.mono (hret0 t₄ he₄ fun o ho => ?_) fun v hv => by rw [hpo, hE] at hv; exact hv
      rw [← ho, hpo, hE]
    | some em' =>
      rw [hE] at hpost
      obtain ⟨hax, hm₃⟩ := hpost
      have hl' : em'.length = k := by
        unfold encodeId at hE
        split at hE
        · exact VG.Proof.RsaPkcs1Sig.encode_length hE
        · cases hE
      have he₃ : Env s t₃ := Env.of he₂ (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
        fun r hr => ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide, by unfold oEM2 frameBytes; omega⟩
      have he₄ : Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
      refine WP.ite false (by simp [eval, hz₄, hax]) (by simp) (fun _ => ?_)
      refine WP.seq (WP.mono (cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
      have hcx₅ : t₅.gpr .rcx = s.gpr .rsi := by
        rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
      have he₅ : Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
      have hr5 : ∀ i < k, InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
          InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
        rw [hdi₅, hsi₅, he₅.wr]
        obtain ⟨r₁, h₁, c₁⟩ := frame_bytes hp (d := oEM1) (n := k) (by unfold oEM1 frameBytes; omega) i hi
        obtain ⟨r₂, h₂, c₂⟩ := frame_bytes hp (d := oEM2) (n := k) (by unfold oEM2 frameBytes; omega) i hi
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      refine WP.seq (WP.mono (compare_ok (by rw [hcx₅]) (by omega) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
      refine WP.mono (result_ok t₆) fun u ⟨hK, hm, hax'⟩ => ⟨?_, ?_⟩
      · exact (he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2).regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2
      · have sE1 : (⟨off (fb s) oEM1, k⟩ : Region).Disjoint ⟨off (fb s) oEM2, em'.length⟩ := by
          rw [hl']; exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 frameBytes at *; omega)
            (by unfold oEM2 frameBytes at *; omega)
        have h1 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM1) k = em := by
          rw [← hem, hm₃, h8₂]
          simp only [Spec.Rsa.bytesAt]
          refine List.map_congr_left fun i hi => ?_
          refine ((frame_writeBytes t₂.mem _ em').bytes (R := ⟨off (fb s) oEM1, k⟩) (fun r hr => ?_) (by show k ≤ 2 ^ 64; omega)
            (List.mem_range.mp hi)).trans ?_
          · rw [List.mem_singleton.mp hr]; exact sE1
          · rw [hm₂, hs₁.2.1]
        have h2 : Spec.Rsa.bytesAt t₃.mem (off (fb s) oEM2) k = em' := by
          have := bytesAt_writeBytes t₂.mem (off (fb s) oEM2) em' (by omega)
          rw [hl'] at this
          rw [hm₃, h8₂]; exact this
        have hm6 : t₆.mem = t₃.mem := by rw [hm₆, hm₅, hs₄.2.1]
        rw [hax', hdx₆, hdi₅, hsi₅]
        simp only [setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
        by_cases hq : em = em' <;> simp [hq]

/-! ## The arguments and the frame -/

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    word (m.writeW base v) base d' = word m base d' := by
  have := word_wo m base v (d := 0) (d' := d') (.inl (by omega)) (by decide) hd'
  simpa only [Bignum.X86_64.word, off, BitVec.add_zero] using this

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : word (m.writeW base v) base 0 = v := by
  have := word_writeW_self m base 0 v
  simpa only [off, BitVec.add_zero] using this

/-- The frame's push and the arguments of the call. -/
theorem pubArgs_ok {s A : State} (hp : PreV s) (hA : Keep [.rax] (allocState frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block pubArgs) A fun t => Env s t ∧
      word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rsi ∧
      word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
      t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdi ∧
      t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := fb_toNat hp
  rw [pubArgs_eq, WP.block_append_iff]
  refine WP.mono (slotStores_ok hp hA hAm) fun t₁ ⟨k₁, ho₁, hN, hK, hE, hEl, hH, hD⟩ => ?_
  refine WP.mono (callArgs_ok hp k₁ ho₁) fun t ⟨k, hm, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_
  have k' := k₁.trans k
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ frameBytes → word t.mem (fb s) d = word t₁.mem (fb s) d := fun d hd hd' => by
    unfold frameBytes at hd'
    rw [hm, word_wo _ _ _ (d := 24) (.inl (by omega)) (by decide) (by omega),
      word_wo _ _ _ (d := 16) (.inl (by omega)) (by decide) (by omega),
      word_wo _ _ _ (d := 8) (.inl (by omega)) (by decide) (by omega), word_wo0 _ _ _ (by omega) (by omega)]
  refine ⟨⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, frame_of_outside ?_,
      (hw _ (by decide) (by decide)).trans hN, (hw _ (by decide) (by decide)).trans hK,
      (hw _ (by decide) (by decide)).trans hE, (hw _ (by decide) (by decide)).trans hEl,
      (hw _ (by decide) (by decide)).trans hH, (hw _ (by decide) (by decide)).trans hD⟩, ?_, ?_, ?_, ?_,
    hdi, hsi, hdx, hcx, h8, h9, fun r hr hr' => ?_⟩
  · rw [hm]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    rw [writeW_outside _ _ _ (d := 24) (by omega) x (by omega), writeW_outside _ _ _ (d := 16) (by omega) x (by omega),
      writeW_outside _ _ _ (d := 8) (by omega) x (by omega)]
    have := writeW_outside t₁.mem (fb s) (stackArg s 1) (d := 0) (by omega) x (by omega)
    simp only [off, BitVec.add_zero] at this
    rw [this]; exact ho₁ x hx
  · rw [hm]; simp (disch := decide) only [word_wo]; exact word_self0 _ _ _
  · rw [hm]; simp (disch := decide) only [word_wo, word_writeW_self]
  · rw [hm]; simp (disch := decide) only [word_wo, word_writeW_self]
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [k'.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)]
    simp [allocState_gpr, hr']

/-! ## The whole function -/

/-- The state after the frame's pop, from the state `s₂` its body ends in. -/
def freed (bytes : Nat) (s₂ : State) : State :=
  { s₂.setReg .rsp (s₂.gpr .rsp + BitVec.ofNat 64 bytes) with wr := s₂.wr.tail }

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : PreV s) {m : Mem} (h : Frame [stkR s, scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := verStack) (d := 0) (k := 8)
      (by unfold verStack; omega)
    simpa only [stkR, kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRs

theorem arg0_ea (t : State) (j : Nat) : t.ea (arg0 j) = stackArgAddr t j := by
  rw [arg0, ea_sp, stackArgAddr]; congr 2; omega

theorem lenCheck_ok {s : State} (hp : PreV s) :
    WP isa (.block lenCheck) s fun t => Keep [.rax] s t ∧ t.mem = s.mem ∧
      t.zf = some (stackArg s 2 == s.gpr .rsi) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rsi)) (by
    xrun [lenCheck, arg0_ea, arg_in hp rfl (show 2 < 5 by decide), sub_beq64]
    rfl) rfl) fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem verifyId_len {nB eB H sig : List Byte} (x : Nat) (h : sig.length ≠ nB.length) :
    verifyId nB eB x H sig = false := by
  unfold verifyId
  split
  · unfold verify; rw [ite_eq_right_iff.mpr (fun h' => absurd h'.1 h)]
  · rfl

theorem code_correct (v : PubImpl) (s : State) (h : verContract.pre s) :
    ∃ t s', Exec isa (code v.name v.code) s t s' ∧ abiPreserved s s' ∧ verContract.post s s' := by
  have hp := preV_of h
  have hk2 := hp.k2
  suffices hw : WP isa (code v.name v.code) s fun s' => abiPreserved s s' ∧ verContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  unfold code
  refine WP.seq (WP.mono_mx (by decide) (lenCheck_ok hp) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
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
    unfold body
    refine WP.seq (WP.mono_mx (by decide) (pubArgs_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (pub_call v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (afterPub_ok hp he₂ hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hax⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, ret_frame hp he₃.mem, ?_⟩, ?_⟩
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
      simp only [verContract, hfr, hax, hsig]
  · refine WP.ite true (by simp [eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (ret0_ok t₀) fun u ⟨hK, hm, hax⟩ hmx =>
      ⟨⟨fun r hr => ?_, by rw [hm, hm₀], by rw [hmx, hmx₀]⟩, ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · simp only [verContract, hax]
      rw [verifyId_len _ (by
        simp only [bytesAt_length]
        intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]
      rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
