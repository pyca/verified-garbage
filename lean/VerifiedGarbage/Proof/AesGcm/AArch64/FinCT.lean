import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish` and `_verify` are constant time

Untrusted: everything here is checked by Lean. The code around `finBody` by
the taint analysis (the tag length and the tags' addresses are public, and
`cmpSeg` compares without a branch); `finBody` by `finBody_rel`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `finBody o`, run, from the state after the entry. -/
theorem finBody_env (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W) {o : Nat} (ho : o = 0 ∨ o = 112)
    {k : Reg → BitVec 64} {R A P : Nat} {τ : State} (he : Env Ctx St W SP τ) (hk : Kept k τ)
    (h22 : τ.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26 : τ.gpr .x26 = BitVec.ofNat 64 A) (h27 : τ.gpr .x27 = BitVec.ofNat 64 P) (hP : P < 2 ^ 64) :
    WP isa (finBody v.callees o) τ fun τ' => Env Ctx St W SP τ' ∧ Kept k τ' ∧
      Frame (finFrame St W o) τ.mem τ'.mem :=
  WP.mono (finBody_ok L v ho (a := Spec.Gcm.zeros A) (c := Spec.Gcm.zeros P)
    (H := blockAt τ.mem (Ctx + BitVec.ofNat 64 240)) he hk h22 hR
    (by rw [Proof.Gcm.length_zeros]; exact h26) (by rw [Proof.Gcm.length_zeros]; exact h27)
    (by rw [Proof.Gcm.length_zeros]; exact hP) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem streamFinish_ct (v : GcmImpl) :
    ConstantTime isa streamFinishAArch64.pre streamFinishAArch64.pub (streamFinish v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, qsp⟩ := hq
  have p₁ : finPre σ₁ := h₁
  have p₂ : finPre σ₂ := h₂
  obtain ⟨L, perm₁, hR, -, -⟩ := lay_of_fin p₁
  obtain ⟨-, perm₂, -, -, -⟩ := lay_of_fin p₂
  rw [← q0, ← q2, ← q6] at perm₂
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := hR
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6] qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6])
      ⟨_, by taint_decide⟩)
    (finishEntry_ok rfl rfl rfl perm₁) (finishEntry_ok q0.symm q2.symm q6.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x22₁, x26₁, x27₁, x28₁, _, _, _⟩ ⟨e₂, k₂, x22₂, x26₂, x27₂, x28₂, _, _, _⟩ => ?_
  rw [← qsp] at e₂
  rw [← q1] at x22₂
  rw [← q3] at x26₂
  rw [← q4] at x27₂
  rw [← q5] at x28₂
  have a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ k₁ k₂ x22₁ x22₂ hRb a26₁ a26₂ a27₁ a27₂
      (σ₁.gpr .x3).isLt (σ₁.gpr .x4).isLt)
    (finBody_env v L (.inl rfl) e₁ k₁ x22₁ hRb a26₁ a27₁ (σ₁.gpr .x4).isLt)
    (finBody_env v L (.inl rfl) e₂ k₂ x22₂ hRb a26₂ a27₂ (σ₁.gpr .x4).isLt) fun τ₁' τ₂' f₁ f₂ => ?_
  have c28₁ : τ₁'.gpr .x28 = σ₁.gpr .x5 := (f₁.2.1 .x28 (by decide)).trans x28₁
  have c28₂ : τ₂'.gpr .x28 = σ₁.gpr .x5 := (f₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [f₁.1.sp, f₂.1.sp])
    (by agree_tac [f₁.1.x19, f₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem streamVerify_ct (v : GcmImpl) :
    ConstantTime isa streamVerifyAArch64.pre streamVerifyAArch64.pub (streamVerify v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩ := hq
  have p₁ : verPre σ₁ := h₁
  have p₂ : verPre σ₂ := h₂
  obtain ⟨L, perm₁, hR, tR₁, dtw⟩ := lay_of_ver p₁
  obtain ⟨-, perm₂, -, tR₂, -⟩ := lay_of_ver p₂
  rw [← q0, ← q2, ← q7] at perm₂
  rw [← q5, ← q6] at tR₂
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := hR
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] qsp
      (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]) ⟨_, by taint_decide⟩)
    (verEntry_ok rfl rfl rfl perm₁) (verEntry_ok q0.symm q2.symm q7.symm perm₂)
    fun τ₁ τ₂ ⟨e₁, k₁, x22₁, x26₁, x27₁, x28₁, x12₁, _, rd₁, wr₁⟩
      ⟨e₂, k₂, x22₂, x26₂, x27₂, x28₂, x12₂, _, rd₂, wr₂⟩ => ?_
  rw [← qsp] at e₂
  rw [← q1] at x22₂
  rw [← q3] at x26₂
  rw [← q4] at x27₂
  rw [← q6] at x28₂
  rw [← q5] at x12₂
  rw [← rd₁, ← wr₁] at tR₁
  rw [← rd₂, ← wr₂] at tR₂
  have t28₁ : τ₁.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have t28₂ : τ₂.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl := (σ₁.gpr .x6).isLt
  refine rel_seq (rel_taint [.x28] (by rw [e₁.sp, e₂.sp]) (by agree_tac [t28₁, t28₂]) ⟨_, by taint_decide⟩)
    (tagLenOk_ok τ₁ t28₁ htl) (tagLenOk_ok τ₂ t28₂ htl) fun τ₁' τ₂' ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  have ge₁ := e₁.of_regs r₁
  have ge₂ := e₂.of_regs r₂
  have gk₁ := k₁.of_others r₁.others
  have gk₂ := k₂.of_others r₂.others
  -- The branch and its run.
  have ev : ∀ {τ : State}, τ.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      isa.eval (.zero .x .x9) τ =
        some (decide ((if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) = 0)) :=
    fun h => eval_zero h (by split <;> decide)
  have tIn : ∀ {τ' : State} (hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true),
      Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' → τ'.gpr .x12 = σ₁.gpr .x5 →
      τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa tagIn τ' fun τ'' => Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' ∧ Kept τ'.gpr τ'' :=
    fun hok he h12 h28 hr => WP.mono (tagIn_ok he.x19 h12 h28 (tagLenOk_le hok) hr he.perm.w
      (dtw.sub_right (Region.sub_prefix (by decide)))) fun _ ⟨_, _, og, sp, rd, wr⟩ =>
        ⟨he.keep (fun r hr => og r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, Kept.of_others (fun _ _ => rfl) og⟩
  have run : ∀ {τ' : State} {k : Reg → BitVec 64}, Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' →
      Kept k τ' → τ'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      τ'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat → τ'.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat →
      τ'.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat → τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      τ'.gpr .x12 = σ₁.gpr .x5 → Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa (.ite (.zero .x .x9) (.block [imm .x0 0])
        (.seq tagIn (.seq (finBody v.callees uO) (.seq cmpSeg (.block verRet))))) τ' fun τ'' =>
        Env (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' := by
    intro τ' k he hk h9 h22 h26 h27 h28 h12 hr
    refine WP.ite _ (ev h9) (fun _ => ?_) (fun hf => ?_)
    · exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
        subst hs'
        exact he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl
    · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true := by
        revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat <;> simp
      refine WP.seq (WP.mono (tIn hok he h12 h28 hr) fun τ₃ ⟨he₃, hk₃⟩ => ?_)
      refine WP.seq (WP.mono (finBody_env v L (.inr rfl) he₃ hk₃ (by rw [hk₃ .x22 (by decide), h22]) hRb
        (by rw [hk₃ .x26 (by decide), h26]) (by rw [hk₃ .x27 (by decide), h27]) (σ₁.gpr .x4).isLt)
        fun τ₄ ⟨he₄, hk₄, _⟩ => ?_)
      refine WP.seq (WP.mono (cmpSeg_ok L he₄ hk₄ (by rw [hk₄ .x28 (by decide), h28])
        (tagLenOk_le hok)) fun τ₅ ⟨x10₅, he₅, _, _, _⟩ => ?_)
      exact WP.mono (verRet_ok (b := decide (bytesAt τ₄.mem (σ₁.gpr .x7 + BitVec.ofNat 64 112)
        (σ₁.gpr .x6).toNat = bytesAt τ₄.mem (σ₁.gpr .x7) (σ₁.gpr .x6).toNat))
        (by rw [x10₅]; simp only [decide_eq_true_eq])) fun _ ⟨_, r⟩ => he₅.of_regs r
  have g9₁ : τ₁'.gpr .x9 = _ := x9₁
  have g9₂ : τ₂'.gpr .x9 = _ := x9₂
  have o22₁ : τ₁'.gpr .x22 = _ := (r₁.others .x22 (by decide)).trans x22₁
  have o22₂ : τ₂'.gpr .x22 = _ := (r₂.others .x22 (by decide)).trans x22₂
  have o26₁ : τ₁'.gpr .x26 = _ := (r₁.others .x26 (by decide)).trans a26₁
  have o26₂ : τ₂'.gpr .x26 = _ := (r₂.others .x26 (by decide)).trans a26₂
  have o27₁ : τ₁'.gpr .x27 = _ := (r₁.others .x27 (by decide)).trans a27₁
  have o27₂ : τ₂'.gpr .x27 = _ := (r₂.others .x27 (by decide)).trans a27₂
  have o28₁ : τ₁'.gpr .x28 = _ := (r₁.others .x28 (by decide)).trans t28₁
  have o28₂ : τ₂'.gpr .x28 = _ := (r₂.others .x28 (by decide)).trans t28₂
  have o12₁ : τ₁'.gpr .x12 = _ := (r₁.others .x12 (by decide)).trans x12₁
  have o12₂ : τ₂'.gpr .x12 = _ := (r₂.others .x12 (by decide)).trans x12₂
  have oR₁ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₁'.rd ++ τ₁'.wr) := by rw [r₁.rd, r₁.wr]; exact tR₁
  have oR₂ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₂'.rd ++ τ₂'.wr) := by rw [r₂.rd, r₂.wr]; exact tR₂
  refine rel_seq (rel_ite (ev g9₁) (ev g9₂) (fun _ => ?_) (fun hf => ?_))
    (run ge₁ gk₁ g9₁ o22₁ o26₁ o27₁ o28₁ o12₁ oR₁) (run ge₂ gk₂ g9₂ o22₂ o26₂ o27₂ o28₂ o12₂ oR₂)
    fun τ₁ τ₂ f₁ f₂ => ?_
  · exact rel_taint [] (by rw [ge₁.sp, ge₂.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · have hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true := by
      revert hf; cases Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat <;> simp
    refine rel_seq (rel_taint [.x19, .x28, .x12] (by rw [ge₁.sp, ge₂.sp])
        (by agree_tac [ge₁.x19, ge₂.x19, o28₁, o28₂, o12₁, o12₂]) ⟨_, by taint_decide⟩)
      (tIn hok ge₁ o12₁ o28₁ oR₁) (tIn hok ge₂ o12₂ o28₂ oR₂) fun τ₃ τ₃' ⟨he₃, hk₃⟩ ⟨he₃', hk₃'⟩ => ?_
    refine rel_seq (finBody_rel L v (.inr rfl) he₃ he₃' hk₃ hk₃'
        (by rw [hk₃ .x22 (by decide), o22₁]) (by rw [hk₃' .x22 (by decide), o22₂]) hRb
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃' .x26 (by decide), o26₂])
        (by rw [hk₃ .x27 (by decide), o27₁]) (by rw [hk₃' .x27 (by decide), o27₂])
        (σ₁.gpr .x3).isLt (σ₁.gpr .x4).isLt)
      (finBody_env v L (.inr rfl) he₃ hk₃ (by rw [hk₃ .x22 (by decide), o22₁]) hRb
        (by rw [hk₃ .x26 (by decide), o26₁]) (by rw [hk₃ .x27 (by decide), o27₁]) (σ₁.gpr .x4).isLt)
      (finBody_env v L (.inr rfl) he₃' hk₃' (by rw [hk₃' .x22 (by decide), o22₂]) hRb
        (by rw [hk₃' .x26 (by decide), o26₂]) (by rw [hk₃' .x27 (by decide), o27₂]) (σ₁.gpr .x4).isLt)
      fun τ₄ τ₄' ⟨he₄, hk₄, _⟩ ⟨he₄', hk₄', _⟩ => ?_
    have c28₁ : τ₄.gpr .x28 = _ := (hk₄ .x28 (by decide)).trans o28₁
    have c28₂ : τ₄'.gpr .x28 = _ := (hk₄' .x28 (by decide)).trans o28₂
    refine rel_seq (rel_taint [.x19, .x28] (by rw [he₄.sp, he₄'.sp])
        (by agree_tac [he₄.x19, he₄'.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩)
      (cmpSeg_ok L he₄ hk₄ c28₁ (tagLenOk_le hok)) (cmpSeg_ok L he₄' hk₄' c28₂ (tagLenOk_le hok))
      fun τ₅ τ₅' ⟨_, he₅, _, _, _⟩ ⟨_, he₅', _, _, _⟩ => ?_
    exact rel_taint [] (by rw [he₅.sp, he₅'.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact rel_taint [.x19] (by rw [f₁.sp, f₂.sp]) (by agree_tac [f₁.x19, f₂.x19]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64
