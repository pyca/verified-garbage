import VerifiedGarbage.Proof.Rsa.AArch64.CkCTMain

/-!
# `vg_rsa_check_key` on AArch64: constant time but for `n` and `e`

`entry`, the checks of `e` and `n`, `fail` and `main` (`ckMain_ct`) leak
the same in runs that agree on the public data (`ckCode_ct`): the
contract's `ConstantTime` (`ckCode_constantTime`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- A state the contract allows, with the public data `p`. -/
def CKRel (p : CkP) (s : State) : Prop := ckA.pre s ∧ (ckIn s).pub = p

theorem ckEntry_split : entry = ([.ldrSp .x8 64] : List Instr) ++ entry.drop 1 := rfl

/-- After `entry`'s first instruction. -/
def CK1 (p : CkP) (t : State) : Prop :=
  ∃ s, CKRel p s ∧ t.gpr .x8 = p.B ∧ t.gpr .x2 = p.pE ∧ t.gpr .x3 = BitVec.ofNat 64 p.el ∧
    WP isa (.block (entry.drop 1)) t (CkHeadPost s)

/-- After `entry`. -/
def CK2 (p : CkP) (t : State) : Prop := ∃ s, CKRel p s ∧ CkHeadPost s t

/-- After the check of `e`. -/
def CK3 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)).toNat

/-- After the loads of `n`'s pointer and length. -/
def CK3b (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x2 = p.pN ∧ t.gpr .x3 = BitVec.ofNat 64 p.k ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

/-- After the check of `n`. -/
def CK4 (p : CkP) (t : State) : Prop :=
  ∃ s t₁, CKRel p s ∧ CkHeadPost s t₁ ∧ t.mem = t₁.mem ∧
    Keep [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k).toNat ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true

theorem ckRel_x {p : CkP} {s : State} (h : CKRel p s) :
    s.gpr .x0 = p.pN ∧ s.gpr .x1 = BitVec.ofNat 64 p.k ∧ s.gpr .x2 = p.pE ∧ s.gpr .x3 = BitVec.ofNat 64 p.el := by
  obtain ⟨-, rfl⟩ := h
  exact ⟨rfl, (ofNat_toNat64 _).symm, rfl, (ofNat_toNat64 _).symm⟩

/-- `fail` leaks nothing. -/
theorem ckFail_ct {α : Type} {Φ : α → State → Prop} : RelCT isa (Two Φ) (.block fail) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil)) (by taint_decide)

/-- `entry` leaks the same in runs with the same public data. -/
theorem ckEntry_ct : RelCT isa (Two CKRel) (.block entry) (Two CK2) := by
  rw [ckEntry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := CK1) [.x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(ckRel_x h₁).2.2.1, (ckRel_x h₂).2.2.1]
    · rw [(ckRel_x h₁).2.2.2, (ckRel_x h₂).2.2.2]) (by taint_decide) ?_)
    (two_piece [.x8, .x2, .x3] (fun p s₁ s₂ ⟨_, _, a₁, b₁, c₁, _⟩ ⟨_, _, a₂, b₂, c₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]) (by taint_decide) fun p t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro p s hs
  have c := ckCtx_of hs.1
  have hh : WP isa (.block (([.ldrSp .x8 64] : List Instr) ++ entry.drop 1)) s (CkHeadPost s) := by
    rw [← ckEntry_split]; exact ckHead_ok' c
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 64) 64 = stackArg s 8 := rfl
  have ha8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 64) 8 := c.ha 8 (by decide)
  have ho : 64 % 8 = 0 ∧ 64 < 32768 := ⟨rfl, by decide⟩
  obtain ⟨-, -, h2, h3⟩ := ckRel_x hs
  refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.x8] (Q := fun t => t.gpr .x8 = stackArg s 8)
    (by brun [exec_ldrSp ho ha8, hB']) (by decide) (by decide) (by decide +kernel))) fun t ⟨hw, h8, k⟩ =>
      ⟨s, hs, h8.trans (congrArg CkP.B hs.2), (k.gpr .x2 (by decide)).trans h2, (k.gpr .x3 (by decide)).trans h3, hw⟩

/-- `vg_rsa_check_key` leaks the same in runs that agree on the public
data. -/
theorem ckCode_ct : RelCT isa (Two CKRel) CheckKey.code fun _ _ => True := by
  unfold CheckKey.code
  refine RelCT.seq ckEntry_ct (RelCT.seq (R := Two CK3) ?_ ?_)
  -- The check of `e`.
  · refine two_piece [.x4, .x5] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.x4, h₂.x4, (ckRel_x c₁).2.2.1, (ckRel_x c₂).2.2.1]
      · rw [h₁.x5, h₂.x5, ofNat_toNat64, ofNat_toNat64, (ckRel_x c₁).2.2.2, (ckRel_x c₂).2.2.2])
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := ckCtx_of hs.1
    have heb := c.e.congrK h.inScr h.keep
    have hel : (ckIn s).eb.length = (s.gpr .x3).toNat := bytesAt_length _ _ _
    have hel1 : 1 ≤ (s.gpr .x3).toNat := c.L.el1
    have hel2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat := c.L.el2
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    refine WP.mono (expCheck_ok (eb := (ckIn s).eb) h.x4 h.x5 hel1 (by omega)
      (fun i hi => heb.rd i (by rw [hel]; exact hi)) ?_) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    · rw [← hel]
      refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      exact (heb.val i h1).symm
    · rw [hz, ← hs.2]; rfl
  -- `fail` or the check of `n`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (R := Two CK4) (RelCT.block_append (RelCT.seq (R := Two CK3b) ?_ ?_)) ?_
  · refine two_piece [.x0] (fun p s₁ s₂ ⟨⟨σ₁, t₁, c₁, h₁, _, k₁, _⟩, _⟩ ⟨⟨σ₂, t₂, c₂, h₂, _, k₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [k₁.gpr .x0 (by decide), k₂.gpr .x0 (by decide), h₁.x0, h₂.x0]
      exact (congrArg CkP.B c₁.2).trans (congrArg CkP.B c₂.2).symm) (by taint_decide) ?_
    rintro p t ⟨⟨s, t₁, hs, h, hm, k, hz⟩, he⟩
    have hev : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true := by
      rw [eval_zero, hz] at he
      cases hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)
      · rw [hv] at he; exact absurd he (by decide)
      · rfl
    have c := ckCtx_of hs.1
    have hs₂ := h.scr.congr k.wr
    have hn := hs₂.nowrap
    have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 9).toNat * 8 := c.L.z
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have h0 : t.gpr .x0 = stackArg s 8 := (k.gpr .x0 (by decide)).trans h.x0
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 8) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
    have aN : word t.mem (stackArg s 8) (8 * Public.sN) = s.gpr .x0 := by rw [hm]; exact h.args.n
    have aK : word t.mem (stackArg s 8) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hm]; exact h.args.k
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t' => t'.gpr .x2 = s.gpr .x0 ∧
        t'.gpr .x3 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ t'.mem = t.mem) (by
      brun [h0, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sN (by decide), hl Public.sK (by decide), aN, aK])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h2, h3, hm'⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [h2, ← hs.2]; rfl,
          by rw [h3, ← hs.2]; rfl, hev⟩
  · refine two_piece [.x2, .x3] (fun p s₁ s₂ ⟨_, _, _, _, _, _, a₁, b₁, _⟩ ⟨_, _, _, _, _, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) ?_
    rintro p t ⟨s, t₁, hs, h, hm, k, h2, h3, hev⟩
    have c := ckCtx_of hs.1
    have hnb := c.n.congrK (by rw [hm]; exact h.inScr) (h.keep.trans k)
    have hnl : (ckIn s).nb.length = (s.gpr .x1).toNat := bytesAt_length _ _ _
    have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
    have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
    rw [← hs.2] at h2 h3
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h2 h3 hk1 hk2 hnl
      (fun i hi => hnb.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hz, hm', _⟩, k'⟩ =>
        ⟨s, t₁, hs, h, by rw [hm', hm], (k.trans k').mono (by decide), by rw [hz, ← hs.2]; rfl, hev⟩
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, z₂, _⟩ => by
    rw [eval_zero, eval_zero, z₁, z₂]) (ckFail_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  exact ckMain_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
    ⟨ckIn s, hs.2, ckPre_of (ckCtx_of hs.1) h hm k⟩) h) fun _ _ h => h

/-- `vg_rsa_check_key` is constant time but for `n` and `e`. -/
theorem ckCode_constantTime : ConstantTime isa ckA.pre ckA.pub CheckKey.code := by
  refine RelCT.constantTime (ckCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨(ckIn s₁).pub, ⟨h₁, rfl⟩, ⟨h₂, ?_⟩,
    hp.2.1⟩) fun _ _ h => h)
  obtain ⟨hr, hsp, ha, hn, he⟩ := hp
  have r : ∀ r ∈ argRegs, s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have a : ∀ j < 10, stackArg s₂ j = stackArg s₁ j := fun j hj => by
    have := congrArg (fun l => l[j]?) ha
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have w₁ := h₁.2.2.1
  have w₂ := h₂.2.2.1
  simp only [CkIn.pub, ckIn, CkP.mk.injEq]
  refine ⟨a 8 (by decide), by rw [a 9 (by decide)], by rw [r .x1 (by decide)], by rw [r .x3 (by decide)],
    by rw [r .x5 (by decide)], by rw [r .x7 (by decide)], by rw [a 1 (by decide)], r .x0 (by decide),
    r .x2 (by decide), r .x4 (by decide), r .x6 (by decide), a 0 (by decide), a 2 (by decide), a 4 (by decide),
    a 6 (by decide), hn.symm, he.symm, ?_⟩
  rw [w₁, w₂, a 8 (by decide), a 9 (by decide)]

end VG.Proof.Rsa.AArch64
