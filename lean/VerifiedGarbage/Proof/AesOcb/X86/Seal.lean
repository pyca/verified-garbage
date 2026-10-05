import VerifiedGarbage.Proof.AesOcb.X86.Front

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open`

Untrusted: everything here is checked by Lean. `seal` is `front` (the
ciphertext and the tag at `W`), the copy of the tag to `tag` (`tagOut`) and
`restore` (`seal_wp`); `open` is `front` (the plaintext and the tag at
`W + t2O`), the received tag copied to `W` (`recv`), their comparison
(`cmp`), the mask of the data (`mask`), and `ok` in `eax` before `restore`
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq SavedAt exit_ok covers_left length_bytesAt bytesAt_writeBytes_self
  writeBytes_frame')

/-- The return address misses what `front` writes. -/
theorem ret_front {p : Prm} (L : Lay p) : ∀ r ∈ entryR p :: mutR p, (⟨w64 p.SP, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Region.sub_prefix (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact L.retW.sub_right (Lay.wSub (by decide))
  · exact Proof.AesGcm.X86.ret_below L.sp
  · exact L.retD

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp (v : BlocksImpl) {s : State} (h : sealPre s) :
    WP isa («seal» (callees v)) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  have h₁ := onePre_seal h
  have L := lay_of h₁
  have hTw : Covers [tagR s] s.wr := covers_of_mem (by rw [h.2.1]; simp)
  unfold «seal»
  refine WP.seq (WP.mono (sealFront_ok v h₁) fun s₅ ⟨F, out⟩ => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (tagOut_ok L F.env (by rw [F.wr]; exact hTw)) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have f₆ : Frame [⟨w64 (prmOf s).T, (prmOf s).tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have S₆ : SavedAt s₆.mem (prmOf s).W s := F.saved.frame f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (d := 128) (k := 16) (by decide)).symm
  have hret : s₆.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [f₆.readW (r := ⟨w64 (prmOf s).SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.retT) (by decide)]
    exact F.frame.readW (r := ⟨w64 (prmOf s).SP, 4⟩) (Region.contains_self _ _) (ret_front L) (by decide)
  -- `restore`.
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]; rfl)
    (by rw [rd₆, wr₆]; exact covers_left F.env.perm.w) L.ww S₆ hret) fun s₇ ⟨ab, m₇, _, _, _⟩ => ⟨ab, ?_⟩
  have hd : bytesAt s₆.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.dw; omega)
  have ht : bytesAt s₆.mem (w64 (prmOf s).T) (prmOf s).tl = bytesAt s₅.mem (w64 (prmOf s).W) (prmOf s).tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 (prmOf s).T) (bytesAt s₅.mem (w64 (prmOf s).W) (prmOf s).tl)
      (by rw [length_bytesAt]; have := L.tl16; omega)
    rw [length_bytesAt] at this
    rw [m₆]; exact this
  show _ = (bytesAt s₇.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s₇.mem (w64 (prmOf s).T) (prmOf s).tl)
  rw [m₇, hd, ht]
  exact out

/-- `ok` into `eax`. -/
theorem retEax_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem p.W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by grun [E.ebp, L.aW, E.perm.wR], by gregs [], fun r h₁ => by gregs [h₁], by gmems [], by gmems [],
    by gmems []⟩

/-- `vg_aes_ocb_open`. -/
theorem open_wp (v : BlocksImpl) {s : State} (h : openPre s) :
    WP isa («open» (callees v)) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  have h₁ := onePre_open h
  have L := lay_of h₁
  unfold «open»
  refine WP.seq (WP.mono (openFront_ok v h₁ (bytesAt s.mem (w64 (prmOf s).T) (prmOf s).tl)) fun s₅ ⟨F, out⟩ => ?_)
  set p := prmOf s with hp
  have ht := L.tl16
  -- The received tag.
  refine WP.seq (WP.mono (recv_ok L F.env) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have f₆ : Frame [⟨w64 p.W, p.tl⟩] s₅.mem s₆.mem := by rw [m₆]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have F₆ : Frame (mutR p) s₅.mem s₆.mem := frame_toMut f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wA p.W, by simp, Region.sub_prefix (by omega)⟩
  have E₆ : Env p s₆ := F.env.mut L (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.ebp])
    (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), F.env.esp]) rd₆ wr₆ F₆
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok L E₆) fun s₇ ⟨m₇, g₇, rd₇, wr₇⟩ => ?_)
  have f₇ : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have F₇ : Frame (mutR p) s₆.mem s₇.mem := frame_toMut f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  have E₇ : Env p s₇ := E₆.mut L
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.ebp])
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E₆.esp]) rd₇ wr₇ F₇
  have hok : slotv s₇.mem p.W okO = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [slotv_eq, m₇, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₇ hok) fun s₈ ⟨m₈, g₈, rd₈, wr₈⟩ => ?_)
  have f₈ : Frame [⟨w64 p.D, p.n⟩] s₇.mem s₈.mem := by rw [m₈]; exact writeBytes_frame' _ (length_mask _ _ _ _)
  have F₈ : Frame (mutR p) s₇.mem s₈.mem := frame_toMut f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inMut_d p
  have E₈ : Env p s₈ := E₇.mut L (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.ebp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), E₇.esp]) rd₈ wr₈ F₈
  -- `ok` and `restore`.
  rw [WP.block_append_iff]
  obtain ⟨s₉, run₉, ax₉, g₉, m₉, rd₉, wr₉⟩ := retEax_ok L E₈
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  have fr := (F₆.trans F₇).trans F₈
  have hret : s₉.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [m₉, show s.gpr .esp = p.SP from rfl, ret_mut L fr]
    exact F.frame.readW (r := ⟨w64 p.SP, 4⟩) (Region.contains_self _ _) (ret_front L) (by decide)
  refine WP.mono (exit_ok (s₀ := s) (by rw [g₉ _ (by decide), E₈.ebp])
    (by rw [g₉ _ (by decide), E₈.esp]; rfl) (by rw [rd₉, wr₉]; exact covers_left E₈.perm.w) L.ww
    (by rw [m₉]; exact SavedAt.mut L fr F.saved) hret) fun s₁₀ ⟨ab, m₁₀, ax₁₀, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  have tg₆ : bytesAt s₆.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.T) p.tl := by
    have := bytesAt_writeBytes_self s₅.mem (w64 p.W) (bytesAt s₅.mem (w64 p.T) p.tl)
      (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [m₆, this]
    exact bytes_front L.t_w L.bt L.t_d (by omega) F.frame
  have t2₆ : bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := t2O) (n := p.tl) (d := 0) (k := p.tl) (.inr (by simp only [t2O]; omega))
        (by simp only [t2O]; omega) (by omega)) (by omega)
  have d₇ : bytesAt s₇.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.dw; omega),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w.sub_right (Region.sub_prefix (by omega)))
        (by have := L.dw; omega)]
  have ok₈ : slotv s₈.mem p.W okO = slotv s₇.mem p.W okO :=
    f₈.readW (r := ⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.d_w' (by decide)).symm) (by decide)
  have out₈ : bytesAt s₈.mem (w64 p.D) p.n = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then bytesAt s₇.mem (w64 p.D) p.n else zeros p.n := by
    have hlm := length_mask s₇.mem (w64 p.D) (decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl)) p.n
    have := bytesAt_writeBytes_self s₇.mem (w64 p.D) _ (by rw [hlm]; have := L.dw; omega)
    rw [hlm] at this
    rw [m₈]; exact this
  have eax : s₁₀.gpr .eax = if decide (bytesAt s₆.mem (w64 p.W) p.tl =
      bytesAt s₆.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
    rw [ax₁₀, ax₉, ok₈, hok]
  rw [tg₆, t2₆, d₇] at out₈
  rw [tg₆, t2₆] at eax
  have mem : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₈.mem (w64 p.D) p.n := by rw [m₁₀, m₉]
  show openPost (openResult s) s₁₀ (w64 p.D) p.n
  by_cases hc : bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl = bytesAt s.mem (w64 p.T) p.tl
  · have hc' : bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl := hc.symm
    have r : openResult s = some (bytesAt s₅.mem (w64 p.D) p.n) := out.trans (by simp only [hc, ↓reduceIte])
    have a : s₁₀.gpr .eax = 1 := by rw [eax]; simp only [hc', decide_true, ↓reduceIte]; rfl
    have d : bytesAt s₁₀.mem (w64 p.D) p.n = bytesAt s₅.mem (w64 p.D) p.n := by
      rw [mem, out₈]; simp only [hc', decide_true, ↓reduceIte]
    exact openPost_some r a d
  · have hc' : ¬ bytesAt s.mem (w64 p.T) p.tl = bytesAt s₅.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
      fun e => hc e.symm
    have r : openResult s = none := out.trans (by simp only [hc, ↓reduceIte])
    have a : s₁₀.gpr .eax = 0 := by rw [eax]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
    have d : bytesAt s₁₀.mem (w64 p.D) p.n = zeros p.n := by
      rw [mem, out₈]; simp only [hc', decide_false, Bool.false_eq_true, ↓reduceIte]
    exact openPost_none r a d

end VG.Proof.AesOcb.X86
