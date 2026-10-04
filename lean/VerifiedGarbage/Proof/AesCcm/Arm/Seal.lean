import VerifiedGarbage.Proof.AesCcm.Arm.Args
import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers in `W` and keeps `W`, the key schedule and the rounds in
registers (`entry_wp`); `Ctr₀` (`ctrs`) and `mac y` followed by `tag y`
leave the MAC of the payload, encrypted, at `W + y` (`front_wp`); `seal` then
encrypts the data (`ctr`) and restores the registers (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok entry_ok covers_left bytesAt_frame Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix)

/-- What the pieces before the data is written change: `W` but for the
saved registers, and the stack below `sp`. -/
abbrev wR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, blw sp]

theorem w_wR {w sp : BitVec 32} {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ wR w sp, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega)⟩

theorem wR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ wR w sp, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

theorem macR_wR {w sp : BitVec 32} {y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ macR w sp y, ∃ r' ∈ wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_wR (.inl (by omega))
  · exact w_wR (.inl (by decide))
  · exact w_wR (.inr ⟨by decide, by decide⟩)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack below `sp` keeps its bytes. -/
theorem buf_wR {w sp : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf w sp s P len) {m m' : Mem}
    (hf : Frame (wR w sp) m m') : bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- The entry: our caller's registers saved in `W`, and `W`, the key schedule
and the rounds in `r11`, `r9` and `r8`. -/
theorem entry_wp {s₀ : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (eW : stackArg s₀ 4 = w) :
    WP isa (.block entry) s₀ fun s₁ => Env k w s₀.sp R (s₁.gpr .r10).toNat s₁ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → s₁.gpr r = s₀.gpr r) ∧
      s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ SavedAt s₁.mem w s₀ ∧ Frame [savedR w] s₀.mem s₁.mem := by
  obtain ⟨i4, v4⟩ := Ar.stk.at 4 (by decide) (show 4 * 4 = 16 from rfl)
  rw [eW] at v4
  refine entry_ok (off := 16) (by decide) i4 (by rw [v4]; exact Ar.lay.ww) (by rw [v4]; exact Ar.perm.w)
    fun s' g12 g rd wr sp sv fr => ?_
  rw [v4] at g12 sv fr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, g .r1 (by decide), h1], by simp [gpr_setReg, g .r0 (by decide), h0],
    by simp [gpr_setReg], by simp [gpr_setReg, g12], sp, Perm.of_eq Ar.perm rd wr⟩, ?_, rd, wr, sv, fr⟩
  intro r a b c d; simp [gpr_setReg, a, b, c, g r d]

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eW : stackArg s₀ 4 = w)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) =
        (bytesAt s'.mem (State.addr D) n, bytesAt s'.mem (State.addr w) tl) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  refine WP.seq (WP.mono (entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  have hent : ∀ {P : BitVec 32} {len : Nat}, Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  have hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  have hk₁ : Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  have hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  have he₂ : Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  have f₂' : Frame (wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inl (by decide))
  have hk₂ := hk₁.frame (f₂'.sub (wR_mut (D := D) (n := n))) (args_mut Ar) sp₂ rd₂ wr₂
  have rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  have wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  have hnl := length_bytesAt s₀.mem (State.addr N) nl
  have h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  have h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- The MAC.
  refine WP.seq (WP.mono (mac_ok L he₂ hk₂ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq rd₁₂ wr₁₂) (Ar.data.buf.of_eq rd₁₂ wr₁₂))
    fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₂]
  -- The encrypted MAC at `W`.
  refine WP.seq (WP.mono (tag_ok L M.env Ar.rounds h7 h13 c₃ (y := 0) (.inl rfl))
    fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_)
  have f₄' : Frame (wR w s₀.sp) s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  have G₄ : Frame (wR w s₀.sp) s₁.mem s₄.mem := (f₂'.trans (M.frame.sub (macR_wR (.inl rfl)))).trans f₄'
  have F₄ : Frame (mutR w s₀.sp D n) s₁.mem s₄.mem := G₄.sub wR_mut
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, M.rd, rd₁₂]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, M.wr, wr₁₂]
  have c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  have hk₄ := hk₁.frame F₄ (args_mut Ar) (by rw [he₄.sp, he₁.sp]) (by rw [rd₄', rd₁]) (by rw [wr₄', wr₁])
  -- Counter mode.
  refine WP.seq (WP.mono (ctr_ok L he₄ hk₄ Ar.rounds h7 h13 c₄ eD en (Ar.data.of_eq rd₄' wr₄')
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => ?_)
  have F₅ : Frame (mutR w s₀.sp D n) s₁.mem s₅.mem := F₄.trans (f₅.sub ctrR_mut)
  -- `restore`.
  refine WP.mono (restore_ok he₅.r11 L.ww (covers_left he₅.perm.w) (sv₁.frame F₅ (saved_mut Ar)) he₅.sp)
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  have cK : ∀ {m : Mem}, Frame (mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (k_mut Ar) hRb, hK₁]
  have a₂ : bytesAt s₂.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [buf_wR Ar.aad f₂', hent Ar.aad]
  have d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  have d₄ : bytesAt s₄.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf G₄, hent Ar.data.buf]
  have w₅ : bytesAt s₅.mem (State.addr w) 16 = bytesAt s₄.mem (State.addr w) 16 :=
    bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 64) (m := 32) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 384) (m := 2176) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
  have mo := M.out
  rw [BitVec.add_zero] at o₄ mo
  have hY := congrArg List.length o₄
  rw [length_bytesAt, length_xorFrom] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [hm, o₅, cK F₄, d₄, crypt_eq (hBC _)]
  · rw [hm, bytesAt_prefix s₅.mem (State.addr w) Ar.t16, w₅, o₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
      mo, cK (f₂'.sub wR_mut), cK ((f₂'.sub wR_mut).trans (M.frame.sub (macR_mut (.inl rfl)))), a₂, d₂,
      ← mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega)]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  seal_wp' (args_of h) rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm

end VG.Proof.AesCcm.Arm
