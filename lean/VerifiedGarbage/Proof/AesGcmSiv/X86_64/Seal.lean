import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the
copy of the tag to `tag` and the restore compute `encryptWith` (RFC 8452
§4) of the arguments (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl)

/-- The return address misses everything the code writes. -/
theorem ret_disj {K W SP D : Addr} {n : Nat} (L : Lay K W SP) (hW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 3816⟩)
    (hD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩) : ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Region.sub_prefix (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact Offset.base_disjoint_below SP (by have := L.sp; omega)
  · exact hD

theorem cryR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ cryR W SP D n, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem polyR_mutW (W SP : Addr) : ∀ r ∈ polyR W SP, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wA (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem tagR_mutW (W SP : Addr) {o : Nat} (ho : o + 16 ≤ 144) : ∀ r ∈ tagR W SP o, ∃ r' ∈ mutW W SP, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sub_wA (by decide)
  · exact sub_wA ho
  · exact sub_wC (by decide) (by decide)
  · exact sub_stk

theorem key_polyR {K W SP : Addr} (L : Lay K W SP) :
    ∀ r ∈ polyR W SP, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

theorem key_tagR {K W SP : Addr} (L : Lay K W SP) {o : Nat} (ho : o + 16 ≤ 248) :
    ∀ r ∈ tagR W SP o, (⟨W + BitVec.ofNat 64 248, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr ho) (by decide) (by omega)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- `vg_aes_gcm_siv_seal`, for its arguments. -/
theorem seal_wp' (v : GcmImpl) {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTw : Covers [⟨T, 16⟩] s.wr)
    (hrT : (⟨SP, 8⟩ : Region).Disjoint ⟨T, 16⟩) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧
      Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12)
        (bytesAt s.mem D n) (bytesAt s.mem A al) = (bytesAt s'.mem D n, bytesAt s'.mem T 16) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => Proof.AesGcm.X86_64.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.GcmSiv.ctxCiph s₁.mem K R = Spec.GcmSiv.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have bN₁ := Ar.nonce.of_eq rd₁ wr₁
  have bA₁ := Ar.aad.of_eq rd₁ wr₁
  have bD₁ := Ar.data.of_eq rd₁ wr₁
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L Ar.rounds E₁ S₁ bN₁ Ar.data.w) fun s₂ Ky => ?_)
  have fK : Frame (mutW W SP) s₁.mem s₂.mem := Ky.frame.sub (keyR_mutW W SP)
  have S₂ := slots_mut L Ar.data.w (fK.sub (mutW_mut W SP D n)) S₁
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env S₂ (bA₁.of_eq Ky.rd Ky.wr) (bD₁.of_eq Ky.rd Ky.wr)
    (bN₁.of_eq Ky.rd Ky.wr) Ky.hkey Ky.acc) fun s₃ Po => ?_)
  have f₃ : Frame (mutW W SP) s₂.mem s₃.mem := Po.frame.sub (polyR_mutW W SP)
  have S₃ := slots_mut L Ar.data.w (f₃.sub (mutW_mut W SP D n)) S₂
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Ar.rounds Po.env S₃ (o := 0) (by decide)) fun s₄ Tg => ?_)
  have f₄ : Frame (mutW W SP) s₃.mem s₄.mem := Tg.frame.sub (tagR_mutW W SP (by decide))
  have S₄ := slots_mut L Ar.data.w (f₄.sub (mutW_mut W SP D n)) S₃
  have f₁₄ : Frame (mutW W SP) s₁.mem s₄.mem := (fK.trans f₃).trans f₄
  -- Counter mode.
  have bD₄ : Buf K W SP s₄ D n := bD₁.of_eq (by rw [Tg.rd, Po.rd, Ky.rd]) (by rw [Tg.wr, Po.wr, Ky.wr])
  refine WP.seq (WP.mono (crypt_ok v L Ar.rounds Tg.env S₄ bD₄
    (by rw [Tg.wr, Po.wr, Ky.wr, wr₁]; exact Ar.dw)) fun s₅ Cr => ?_)
  have f₁₅ : Frame (mutR W SP D n) s₁.mem s₅.mem := (f₁₄.sub (mutW_mut W SP D n)).trans (Cr.frame.sub (cryR_mut W SP D n))
  have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₅.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  have r₅ : s₅.rd = s.rd := by rw [Cr.rd, Tg.rd, Po.rd, Ky.rd, rd₁]
  have w₅ : s₅.wr = s.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, wr₁]
  -- The copy of the tag, and `restore`.
  have hTa : InRegions (s₅.rd ++ s₅.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := Proof.AesGcm.X86_64.in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [r₅, w₅]; exact h
  obtain ⟨s₆, run₆, fT, hT₆, hg₆, rd₆, wr₆⟩ := tagOut_ok Cr.env (by rw [argT_kept fall Ar.argsW Ar.argsD, hT]) hTa
    (by rw [w₅]; exact hTw) Tb.w
  have E₆ : Env K W SP s₆ := Cr.env.of_saved hg₆ rd₆ wr₆
  have dT : ∀ q ∈ [(⟨T, 16⟩ : Region)], ∀ p ∈ saved, (⟨W + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint q := by
    intro q hq p hp
    simp only [List.mem_singleton] at hq; subst hq
    have hd : 144 ≤ p.2 ∧ p.2 + 8 ≤ 192 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (Tb.w.sub_right (Lay.wSub (by omega))).symm
  have sv₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← saved_mut L Ar.data.w f₁₅ sv₁ p hp]
    exact fT.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun q hq => dT q hq p hp) (by decide)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := restore_ok E₆ sv₆
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆]; exact run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, 144) (by decide)
    · exact hg₇ (.rbp, 152) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, 160) (by decide)
    · exact hg₇ (.r13, 168) (by decide)
    · exact hg₇ (.r14, 176) (by decide)
    · exact hg₇ (.r15, 184) (by decide)
  · rw [hm₇, hsp, fT.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hrT) (by decide)]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · have key₃ : Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₂.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Po.frame (key_polyR L) hRb
    have key₄ : Spec.GcmSiv.ctxCiph s₄.mem (W + BitVec.ofNat 64 248) R =
        Spec.GcmSiv.ctxCiph s₃.mem (W + BitVec.ofNat 64 248) R := ctxCiph_frame Tg.frame (key_tagR L (by decide)) hRb
    have n₂ : bytesAt s₂.mem N 12 = bytesAt s.mem N 12 := by rw [buf_mutW bN₁ fK, hent Ar.nonce]
    have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := by rw [buf_mutW bA₁ fK, hent Ar.aad]
    have d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ fK, hent Ar.data]
    have d₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := by rw [buf_mutW bD₁ f₁₄, hent Ar.data]
    have t₅ : bytesAt s₅.mem W 16 = bytesAt s₄.mem W 16 := Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 96) (k := 48) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 1768) (k := 2048) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
    have d₇ : bytesAt s₇.mem D n = bytesAt s₅.mem D n := by
      rw [hm₇]; exact Proof.AesGcm.X86_64.bytesAt_frame fT (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact Tb.d.symm) (by have := Ar.data.lt; omega)
    have tg := Tg.out
    rw [BitVec.add_zero] at tg
    have au := Ky.auth
    have ci := Ky.ciph
    rw [hK₁, hent Ar.nonce] at au ci
    have po := Po.out
    rw [n₂, a₂, d₂] at po
    rw [d₇, hm₇, hT₆, Cr.data, t₅, d₄, key₄, key₃, ci, tg, key₃, ci, po, ← au]
    unfold Spec.GcmSiv.encryptWith
    generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem K R) (Spec.GcmSiv.keyLen R) (bytesAt s.mem N 12) = dk
    obtain ⟨a, e⟩ := dk
    rfl

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) {s : State} (h : sealPre s) :
    WP isa («seal» v.callees) s fun s' => gprPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨⟨Ar, Tb⟩, hTw, hrT⟩ := args_of_seal h
  exact seal_wp' v Ar Tb hTw hrT rfl (ofNat_toNat64 _).symm rfl rfl rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl

end VG.Proof.AesGcmSiv.X86_64
