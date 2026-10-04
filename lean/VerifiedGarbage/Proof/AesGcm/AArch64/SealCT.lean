import VerifiedGarbage.Proof.AesGcm.AArch64.OneCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry by `entry_rel`,
`j0` and the additional data by `front_rel`, the text by `encBody_rel` and
the tag by `finBody_rel`; the blocks between them by the taint analysis, with
`tag`, which the code loads from memory, public in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `oneCore` gives, with the values of the first run. -/
structure OneFacts (σ σ₀ : State) (n w : Nat) : Prop where
  ol : OneLay σ₀ n w
  hW : stackArg σ w = stackArg σ₀ w
  perm : Perm (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ
  hsp : ∀ i < n, InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 (8 * i)) 8
  nonceR : Covers [⟨σ₀.gpr .x2, (σ₀.gpr .x3).toNat⟩] (σ.rd ++ σ.wr)
  aadR : Covers [⟨σ₀.gpr .x4, (σ₀.gpr .x5).toNat⟩] (σ.rd ++ σ.wr)
  dataW : Covers [⟨σ₀.gpr .x6, (σ₀.gpr .x7).toNat⟩] σ.wr
  args : (args σ n).Disjoint (workR (stackArg σ₀ w))

theorem oneFacts {σ₁ σ₂ : State} {n w : Nat} (hw : w < n) (h₁ : oneCore n w σ₁) (h₂ : oneCore n w σ₂)
    (hq : onePub n σ₁ σ₂) : OneFacts σ₁ σ₁ n w ∧ OneFacts σ₂ σ₁ n w := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qw : stackArg σ₁ w = stackArg σ₂ w := qa w hw
  have o₁ := oneLay h₁
  have o₂ := oneLay h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW, o₁.args⟩,
    ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q2, ← q3] at this; exact this
  · have := o₂.aadR; rw [← q4, ← q5] at this; exact this
  · have := o₂.dataW; rw [← q6, ← q7] at this; exact this
  · have := o₂.args; rw [← qw] at this; exact this

/-- A stack argument, at `sp + j` with `j < 8 * n`, is outside `work`. -/
theorem OneFacts.argW {σ σ₀ : State} {n w : Nat} (f : OneFacts σ σ₀ n w) {j : Nat} (hj : j + 8 ≤ 8 * n) :
    (⟨σ.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR (stackArg σ₀ w)) := by
  refine f.args.sub_left ?_
  show Region.Sub ⟨σ.sp + BitVec.ofNat 64 j, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * n⟩
  rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
  exact Offset.sub_base _ hj

/-- `FrontIn` after the entry. -/
theorem frontIn_of {σ σ₀ τ : State} {n w : Nat} {V : BitVec 64} (f : OneFacts σ σ₀ n w)
    (h3 : σ.gpr .x3 = σ₀.gpr .x3) (h2 : σ.gpr .x2 = σ₀.gpr .x2) (h4 : σ.gpr .x4 = σ₀.gpr .x4)
    (h5 : σ.gpr .x5 = σ₀.gpr .x5) (h6 : σ.gpr .x6 = σ₀.gpr .x6) (h7 : σ.gpr .x7 = σ₀.gpr .x7)
    (a : Env (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ ∧
      τ.gpr .x22 = σ.gpr .x1 ∧ τ.gpr .x23 = σ.gpr .x2 ∧ τ.gpr .x24 = σ.gpr .x3 ∧
      τ.gpr .x26 = σ.gpr .x3 ∧ τ.gpr .x27 = 0 ∧ τ.gpr .x28 = V ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 216) 64 = σ.gpr .x4 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 224) 64 = σ.gpr .x5 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 232) 64 = σ.gpr .x6 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 240) 64 = σ.gpr .x7 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 248) 64 = V ∧
      Frame [entryR (stackArg σ₀ w)] σ.mem τ.mem ∧ SavedAt τ.mem (stackArg σ₀ w) σ ∧ τ.rd = σ.rd ∧
      τ.wr = σ.wr) :
    FrontIn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ.gpr (σ₀.gpr .x2)
      (σ₀.gpr .x4) (σ₀.gpr .x6) (σ₀.gpr .x3).toNat (σ₀.gpr .x5).toNat (σ₀.gpr .x7).toNat τ := by
  obtain ⟨he, _, x23, x24, x26, x27, _, s1, s2, s3, s4, _, _, _, rd, wr⟩ := a
  have sub16 : Region.Sub ⟨stackArg σ₀ w + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₀ w)) := Lay.wSub (by decide)
  exact ⟨he, fun _ _ => rfl, by rw [x23, h2], by rw [x24, h3, ofNat_toNat'], by rw [x26, h3, ofNat_toNat'], x27,
    ⟨by rw [rd, wr]; exact f.nonceR, (σ₀.gpr .x3).isLt, f.ol.nw, f.ol.nonce.sub_right sub16, f.ol.nonce⟩,
    ⟨by rw [rd, wr]; exact f.aadR, (σ₀.gpr .x5).isLt, f.ol.aw, f.ol.aad.sub_right sub16, f.ol.aad⟩,
    by rw [s1, h4], by rw [s2, h5, ofNat_toNat'], by rw [s3, h6], by rw [s4, h7, ofNat_toNat']⟩

/-- The entry of `seal` and `open` and its stash, in two runs: `work` at `sp + k`, and
the stack argument at `sp + j` kept. -/
theorem entryStash_rel {σ₁ σ₂ : State} {n w k j : Nat} (hk : k = 8 ∨ k = 16) (hkw : k = 8 * w) (hj : j = 0 ∨ j = 8)
    (f₁ : OneFacts σ₁ σ₁ n w) (f₂ : OneFacts σ₂ σ₁ n w) (hwn : w < n) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k ++ stashArg j)) TT := by
  subst hkw
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := f₂.hW
  have ts : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block (stashArg j)) h).isSome = true := by
    rcases hj with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine RelCT.block_split (rel_seq (entry_rel hk hW₁ hW₂ (f₁.hsp w hwn) (f₂.hsp w hwn) f₁.perm.w f₂.perm.w qsp hq)
    (oneEntry_ok (by rcases hk with h | h <;> rw [h] <;> decide) hW₁ (f₁.hsp w hwn) rfl f₁.perm)
    (oneEntry_ok (by rcases hk with h | h <;> rw [h] <;> decide) hW₂ (f₂.hsp w hwn) (hq .x0 (by simp)).symm f₂.perm)
    fun τ₁ τ₂ a₁ a₂ => rel_taint [.x19] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac [a₁.1.x19, a₂.1.x19]) ts)

theorem seal_ct (v : GcmImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 1 < 2) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
  have L := f₁.ol.lay
  have hT₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := rfl
  have hT₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 0) 64 = stackArg σ₁ 0 := qt.symm
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 8) 64 = stackArg σ₁ 1 := f₂.hW
  refine rel_seq (entryStash_rel (k := 8) (j := 0) (.inl rfl) rfl (.inl rfl) f₁ f₂ (by decide) qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₁ (f₁.hsp 1 (by decide)) (f₁.hsp 0 (by decide))
      hT₁ (f₁.argW (by decide)) rfl f₁.perm)
    (entryStash_ok (V := stackArg σ₁ 0) (by decide) (by decide) hW₂ (f₂.hsp 1 (by decide)) (f₂.hsp 0 (by decide))
      hT₂ (f₂.argW (by decide)) q0.symm f₂.perm) fun τ₁ τ₂ a₁ a₂ => ?_
  have i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl a₁
  have i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm a₂
  rw [← qsp] at i₂
  obtain ⟨_, x22₁, _, _, _, _, _, _, s2₁, _, s4₁, s5₁, _, _, rd₁, wr₁⟩ := a₁
  obtain ⟨_, x22₂, _, _, _, _, _, _, s2₂, _, s4₂, s5₂, _, _, rd₂, wr₂⟩ := a₂
  rw [← q1] at x22₂
  rw [← q5] at s2₂
  rw [← q7] at s4₂
  have ol := f₁.ol
  have sub16 : Region.Sub ⟨stackArg σ₁ 1 + BitVec.ofNat 64 16, 80⟩ (workR (stackArg σ₁ 1)) := Lay.wSub (by decide)
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := ol.rounds
  have hal := (σ₁.gpr .x5).isLt
  have hn := (σ₁.gpr .x7).isLt
  refine front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  have mkB : ∀ {σ τ u : State}, OneFacts σ σ₁ 2 1 → τ.gpr .x22 = σ₁.gpr .x1 → τ.wr = σ.wr →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp u.gpr (σ₁.gpr .x1).toNat
        (σ₁.gpr .x7).toNat 0 (σ₁.gpr .x6) (Spec.Gcm.zeros (σ₁.gpr .x5).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f x22 wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x22, x22, ofNat_toNat'], hRb, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd⟩, rfl⟩
  have B₁ := mkB f₁ x22₁ wr₁ o₁
  have B₂ := mkB f₂ x22₂ wr₂ o₂
  refine rel_seq (encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  have sl : ∀ {σ τ u w : State}, OneFacts σ σ₁ 2 1 →
      FrontOut (σ₁.gpr .x0) (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      Frame (bodyFrame (stackArg σ₁ 1 + BitVec.ofNat 64 16) (stackArg σ₁ 1) (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        u.mem w.mem → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      w.mem.readW (stackArg σ₁ 1 + BitVec.ofNat 64 d) 64 = τ.mem.readW (stackArg σ₁ 1 + BitVec.ofNat 64 d) 64 :=
    fun _ o fb d h₁ h₂ => by
      rw [slot_kept fb (slots_bodyFrame L ol.data) h₁ h₂, slot_kept o.frame (slots_frontFrame L) h₁ h₂]
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₁.env.x19 (covers_left b₁.env.perm.w) (by rw [sl f₁ o₁ b₁.frame 224 (by decide) (by decide), s2₁,
      ofNat_toNat']) (by rw [sl f₁ o₁ b₁.frame 240 (by decide) (by decide), s4₁, ofNat_toNat']))
    (finPrep_ok (al := (σ₁.gpr .x5).toNat) (n := (σ₁.gpr .x7).toNat) b₂.env.x19 (covers_left b₂.env.perm.w) (by rw [sl f₂ o₂ b₂.frame 224 (by decide) (by decide), s2₂,
      ofNat_toNat']) (by rw [sl f₂ o₂ b₂.frame 240 (by decide) (by decide), s4₂, ofNat_toNat']))
    fun z₁ z₂ ⟨x26₁, x27₁, r₁⟩ ⟨x26₂, x27₂, r₂⟩ => ?_
  refine rel_seq (rel_taint [.x19] (by rw [r₁.sp, r₂.sp, b₁.env.sp, b₂.env.sp])
      (by agree_tac [r₁.others .x19 (by decide), r₂.others .x19 (by decide), b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (ldr28_ok (V := stackArg σ₁ 0) (b₁.env.of_regs r₁) (by rw [r₁.mem, sl f₁ o₁ b₁.frame 248 (by decide) (by decide), s5₁]))
    (ldr28_ok (V := stackArg σ₁ 0) (b₂.env.of_regs r₂) (by rw [r₂.mem, sl f₂ o₂ b₂.frame 248 (by decide) (by decide), s5₂]))
    fun z₁' z₂' ⟨x28₁, r₁'⟩ ⟨x28₂, r₂'⟩ => ?_
  have y22₁ : z₁'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₁'.others _ (by decide), r₁.others _ (by decide), b₁.kept .x22 (by decide), o₁.x22, x22₁, ofNat_toNat']
  have y22₂ : z₂'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₂'.others _ (by decide), r₂.others _ (by decide), b₂.kept .x22 (by decide), o₂.x22, x22₂, ofNat_toNat']
  have e₁ := (b₁.env.of_regs r₁).of_regs r₁'
  have e₂ := (b₂.env.of_regs r₂).of_regs r₂'
  have y26₁ : z₁'.gpr .x26 = _ := (r₁'.others .x26 (by decide)).trans x26₁
  have y26₂ : z₂'.gpr .x26 = _ := (r₂'.others .x26 (by decide)).trans x26₂
  have y27₁ : z₁'.gpr .x27 = _ := (r₁'.others .x27 (by decide)).trans x27₁
  have y27₂ : z₂'.gpr .x27 = _ := (r₂'.others .x27 (by decide)).trans x27₂
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ hRb y26₁ y26₂ y27₁ y27₂ hal hn)
    (finBody_env v L (.inl rfl) e₁ (fun _ _ => rfl) y22₁ hRb y26₁ y27₁ hn)
    (finBody_env v L (.inl rfl) e₂ (fun _ _ => rfl) y22₂ hRb y26₂ y27₂ hn) fun g₁ g₂ h₁ h₂ => ?_
  have c28₁ : g₁.gpr .x28 = stackArg σ₁ 0 := (h₁.2.1 .x28 (by decide)).trans x28₁
  have c28₂ : g₂.gpr .x28 = stackArg σ₁ 0 := (h₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [h₁.1.sp, h₂.1.sp])
    (by agree_tac [h₁.1.x19, h₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64
