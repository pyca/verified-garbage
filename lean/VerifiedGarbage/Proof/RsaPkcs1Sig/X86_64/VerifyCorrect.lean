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
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .r8 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0 := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r8, .rcx, .rdx, .rsi, .r9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r8 = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .r8 ∧
      u.gpr .rsi = s.gpr .r9 ∧ u.gpr .r9 = stackArg s 0) (by
    xrun [encArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, he.rsp,
      sx_ofNat (show oEM2 < 2 ^ 31 by decide), hs.ld (d := oK) (by decide), hs.ld (d := oH) (by decide),
      hs.ld (d := oD) (by decide), arg_in hp he.rd (show 0 < 5 by decide), he.arg hp (show 0 < 5 by decide),
      he.sK, he.sH, he.sD]) rfl) fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem cmpArgs_ok {s t : State} (hp : PreV s) (he : Env s t) :
    WP isa (.block cmpArgs) t fun u => Keep [.rdi, .rsi, .rcx] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = off (fb s) oEM1 ∧ u.gpr .rsi = off (fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rsi) (by
    xrun [cmpArgs, lea, List.cons_append, List.nil_append, ea_sp, he.rsp,
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), sx_ofNat (show oEM2 < 2 ^ 31 by decide),
      hs.ld (d := oK) (by decide), he.sK]) rfl) fun u ⟨h, hK⟩ => ⟨hK, h⟩

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
      rdx := by rw [hdx₂]
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
      refine WP.seq (WP.mono (cmpArgs_ok hp he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅, hcx₅⟩ => ?_)
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

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
