import VerifiedGarbage.Proof.AesOcb.X86.BodyCT

/-!
# AES-OCB on x86: `vg_aes_ocb_seal` and `vg_aes_ocb_open` in constant time

Untrusted: everything here is checked by Lean. `front` is its pieces in
sequence, each started from what the pieces before it leave (`front_ct`);
then the copies of the tag, the comparison and the mask, which address `W`,
the tag and the data, their addresses and lengths loaded from their slots
(`seal_ct`, `open_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop restore)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq copyLoop_ct length_bytesAt)

/-- `front`: the entry, the setup, `Offset_0`, `HASH`, the data and the tag. -/
theorem front_ct (v : BlocksImpl) (enc : Bool) (p : Prm) {d : Nat} (hd : d = tagO ∨ d = t2O)
    (hbody : Lay p → CT (BI p) (body (callees v) enc))
    (hbw : Lay p → ∀ t, BI p t → WP isa (body (callees v) enc) t (Env p)) :
    CT (fun s => onePre s ∧ prmOf s = p) (front (callees v) enc d) := by
  by_cases hex : ∃ s, onePre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of hz
  have kL : ∀ {m m' : Mem}, Frame (mutR p) m m' → ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) := fun h => lstar_mut L h
  unfold front
  -- The entry.
  refine CT.seq (J := Env p) (entry_ct p) (fun s ⟨h, hp⟩ => WP.mono (entry_ok h) fun _ En => hp ▸ En.env) ?_
  -- The setup.
  refine CT.seq (J := fun t => Env p t ∧ blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 ckO) = 0 ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt (ctxLstar t.mem (w64 p.K)) 0)
    (setup_ct L fun _ h => h) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, P₂⟩ := setup_ok L E
    have f₂ : Frame (mutR p) t.mem t₂.mem := P₂.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P₂.rd P₂.wr f₂, P₂.ck,
      by rw [P₂.l0, kL f₂]⟩
  -- `Offset_0`.
  refine CT.seq (J := BI p) (nonce_ct v L fun _ h => h.1) (fun t ⟨E, ck, l0⟩ => WP.mono (nonce_ok v L E)
    fun t' P => ⟨P.env, by rw [P.o0, P.ofs], by rw [P.keep (by decide) (by decide), ck],
      by rw [P.keep (by decide) (by decide), l0, kL (wR_mut P.frame)]⟩) ?_
  -- `HASH`.
  have kH : ∀ {m m' : Mem}, Frame (hashR p) m m' → ∀ {d : Nat},
      (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (176 ≤ d ∧ d + 16 ≤ 220) ∨ (224 ≤ d ∧ d + 16 ≤ 264)) →
      blockAtMem m' (w64 p.W + BitVec.ofNat 64 d) = blockAtMem m (w64 p.W + BitVec.ofNat 64 d) :=
    fun {m m'} F {d} hd => Proof.Ocb.blockAtMem_frame F fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Lay.w_w (by simp only [sumO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [lO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [ohO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [kO]; omega) (by omega) (by decide)
      · exact Lay.w_w (by simp only [hlO]; omega) (by omega) (by decide)
      · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
      · exact (L.bw' (by omega)).symm
  refine CT.seq (J := BI p) ((hash_ct v L).mono fun t ⟨E, _, _, l0⟩ => ⟨_, _, _, ⟨L, rfl, rfl, rfl⟩, E, l0⟩)
    (fun t ⟨E, o0, ck, l0⟩ => WP.mono (hash_ok v ⟨L, rfl, rfl, rfl⟩ E l0) fun t' ⟨E', F, _, _, _⟩ =>
      ⟨E', by rw [kH F (by decide), kH F (by decide), o0], by rw [kH F (by decide), ck],
        by rw [kH F (by decide), l0, kL (wR_mut (hashR_wR F))]⟩) ?_
  -- The data and the tag.
  exact CT.seq (J := Env p) (hbody L) (hbw L) (tag_ct v L hd)

/-! ## The tag out and in, the comparison and the mask -/

theorem tagOut_ct {p : Prm} (L : Lay p) : CT (Env p) tagOut := by
  unfold tagOut
  refine CT.seq (J := fun t => t.gpr .edi = p.W ∧ t.gpr .edx = p.T ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv]⟩

theorem recv_ct {p : Prm} (L : Lay p) : CT (Env p) recv := by
  unfold recv
  refine CT.seq (J := fun t => t.gpr .edi = p.T ∧ t.gpr .edx = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) (copyLoop_ct (pin3 fun _ h => h))
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv]⟩

theorem cmp_ct {p : Prm} (L : Lay p) : CT (Env p) cmp := by
  unfold cmp
  refine CT.seq (J := fun t => t.gpr .ebp = p.W ∧ t.gpr .edi = p.W ∧ t.gpr .ecx = BitVec.ofNat 32 p.tl)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_)
    (CT.taint [.ebp, .edi, .ecx] (pin3 fun _ h => h) (by taint_decide))
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  exact WP.of_runBlock ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [E.ebp], by gregs [E.ebp], by gregs [hv]⟩

theorem mask_ct {p : Prm} (L : Lay p) : CT (Env p) mask := by
  unfold mask
  refine load_ct L (r := .edi) (o := dataO) (by decide) (fun t E => ⟨E, E.slots.data⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine load_ct L (r := .ecx) (o := lenO) (by decide)
    (fun t h => ⟨Ld.env (by decide) (by decide) (fun _ h => h) t h, (Ld.env (by decide) (by decide) (fun _ h => h) t h).slots.len⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  exact CT.taint [.ebp, .edi, .ecx] (pin3 fun t h => ⟨Ld.reg (by decide) (fun s h =>
      Ld.reg (by decide) (fun s (h : Env p s) => h.ebp) s h) t h,
    Ld.reg (by decide) (fun s h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) t h,
    by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide)

/-! ## The functions -/

theorem prmOf_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₁ = prmOf s₂ := by
  obtain ⟨hsp, ha⟩ := h
  simp only [prmOf, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide)]

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86.pre sealX86.pub («seal» (callees v)) := by
  refine CT.constantTime prmOf (fun _ _ _ _ h => prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, sealX86.pre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of (onePre_seal hz)
  unfold «seal»
  refine CT.seq (J := fun t => Env p t ∧ Covers [⟨w64 p.T, p.tl⟩] t.wr)
    ((front_ct v true p (.inl rfl) (fun L => bodySeal_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (bodySeal_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨onePre_seal h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (sealFront_ok v (onePre_seal h)) fun _ ⟨F, _⟩ => hp ▸ ⟨F.env, by
      rw [F.wr]; exact covers_of_mem (r := tagR s) (by rw [h.2.1]; simp)⟩) ?_
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((tagOut_ct L).mono fun _ h => h.1)
    (fun t ⟨E, hT⟩ => WP.mono (tagOut_ok L E hT) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86.pre openX86.pub («open» (callees v)) := by
  refine CT.constantTime prmOf (fun _ _ _ _ h => prmOf_eq h) fun p => ?_
  by_cases hex : ∃ s, openX86.pre s ∧ prmOf s = p
  swap
  · exact RelCT.of_false fun s _ h => hex ⟨s, h.1⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have L : Lay p := hzp ▸ lay_of (onePre_open hz)
  unfold «open»
  refine CT.seq (J := Env p)
    ((front_ct v false p (.inr rfl) (fun L => bodyOpen_ct v L) fun L t ⟨E, o0, ck, l0⟩ =>
      WP.mono (bodyOpen_ok v L E rfl o0 ck l0) fun _ B => B.env).mono fun s ⟨h, hp⟩ => ⟨onePre_open h, hp⟩)
    (fun s ⟨h, hp⟩ => WP.mono (openFront_ok v (onePre_open h) []) fun _ ⟨F, _⟩ => hp ▸ F.env) ?_
  -- The received tag.
  refine CT.seq (J := Env p) (recv_ct L) (fun t E => WP.mono (recv_ok L E) fun t' ⟨m, g, rd, wr⟩ => ?_) ?_
  · have ht := L.tl16
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (frame_toMut (rs := [⟨w64 p.W, p.tl⟩]) (by
        rw [m]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _))
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA p.W, by simp, Region.sub_prefix (by omega)⟩)
  -- The comparison.
  refine CT.seq (J := fun t => Env p t ∧ ∃ c : Bool,
      slotv t.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) (cmp_ct L)
    (fun t E => WP.mono (cmp_ok L E) fun t' ⟨m, g, rd, wr⟩ => ⟨?_, decide (bytesAt t.mem (w64 p.W) p.tl =
      bytesAt t.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl), by
        rw [slotv_eq, m, Mem.readW_writeW_self32]; simp only [decide_eq_true_eq]⟩) ?_
  · have f : Frame [⟨w64 p.W + BitVec.ofNat 64 okO, 4⟩] t.mem t'.mem := by
      rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
      (frame_toMut f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  -- The mask, and the result.
  refine CT.seq (J := fun t => t.gpr .ebp = p.W) ((mask_ct L).mono fun _ h => h.1)
    (fun t ⟨E, c, hok⟩ => WP.mono (mask_ok L E hok) fun _ ⟨_, g, _⟩ => by
      rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))

end VG.Proof.AesOcb.X86
