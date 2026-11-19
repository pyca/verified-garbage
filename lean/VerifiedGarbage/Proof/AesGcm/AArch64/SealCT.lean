module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.BodyCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Impl.Aes.AArch64.Alloc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
meta import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamCryptCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.AArch64.StreamVerify
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.AesGcm.AArch64.Front
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Front
import VerifiedGarbage.Proof.AesGcm.AArch64.Open
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Open
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
public import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.AArch64.FinTag
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contract
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

/-! ### `AesGcm.AArch64.OneCT`, which this module and modules that import it used -/

section

/-! ### `AesGcm.AArch64.FinCT`, which this module and modules that import it used -/

section

/-!
# AES-GCM on AArch64: `vg_aes_gcm_stream_finish` and `_verify` are constant time

Untrusted: everything here is checked by Lean. The code around `finBody` by
the taint analysis (the tag length and the tags' addresses are public, and
`cmpSeg` compares without a branch); `finBody` by `finBody_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- `finBody o`, run, from the state after the entry. -/
theorem finBody_env {Wn : Nat} (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Wn Ctx St W) {o : Nat} (ho : o = 0 ∨ o = 112)
    {k : Reg → BitVec 64} {R A P : Nat} {τ : State} (he : Env Wn Ctx St W SP τ) (hk : Kept k τ)
    (h22 : τ.gpr .x22 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h26 : τ.gpr .x26 = BitVec.ofNat 64 A) (h27 : τ.gpr .x27 = BitVec.ofNat 64 P) (hP : P < 2 ^ 64) :
    WP isa (finBody v.callees o) τ fun τ' => Env Wn Ctx St W SP τ' ∧ Kept k τ' ∧
      Frame (finFrame St W o) τ.mem τ'.mem :=
  WP.mono (finBody_ok L v ho (a := Spec.Gcm.zeros A) (c := Spec.Gcm.zeros P)
    (H := blockAt τ.mem (Ctx + BitVec.ofNat 64 240)) he hk h22 hR
    (by rw [Proof.Gcm.length_zeros]; exact h26) (by rw [Proof.Gcm.length_zeros]; exact h27)
    (by rw [Proof.Gcm.length_zeros]; exact hP) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem streamFinish_ct {Wn : Nat} (v : GcmImpl) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ConstantTime isa (streamFinishAArch64 Wn).pre (streamFinishAArch64 Wn).pub (streamFinish v.callees) := by
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
  obtain a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ k₁ k₂ x22₁ x22₂ hRb a26₁ a26₂ a27₁ a27₂
      (σ₁.gpr .x3).isLt (σ₁.gpr .x4).isLt)
    (finBody_env v L (.inl rfl) e₁ k₁ x22₁ hRb a26₁ a27₁ (σ₁.gpr .x4).isLt)
    (finBody_env v L (.inl rfl) e₂ k₂ x22₂ hRb a26₂ a27₂ (σ₁.gpr .x4).isLt) fun τ₁' τ₂' f₁ f₂ => ?_
  obtain c28₁ : τ₁'.gpr .x28 = σ₁.gpr .x5 := (f₁.2.1 .x28 (by decide)).trans x28₁
  obtain c28₂ : τ₂'.gpr .x28 = σ₁.gpr .x5 := (f₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [f₁.1.sp, f₂.1.sp])
    (by agree_tac [f₁.1.x19, f₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem streamVerify_ct {Wn : Nat} (v : GcmImpl) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) :
    ConstantTime isa (streamVerifyAArch64 Wn).pre (streamVerifyAArch64 Wn).pub (streamVerify v.callees) := by
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
  obtain t28₁ : τ₁.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain t28₂ : τ₂.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat := by rw [x28₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₁ : τ₁.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a26₂ : τ₂.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat := by rw [x26₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₁ : τ₁.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain a27₂ : τ₂.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat := by rw [x27₂, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain htl := (σ₁.gpr .x6).isLt
  refine rel_seq (rel_taint [.x28] (by rw [e₁.sp, e₂.sp]) (by agree_tac [t28₁, t28₂]) ⟨_, by taint_decide⟩)
    (tagLenOk_ok τ₁ t28₁ htl) (tagLenOk_ok τ₂ t28₂ htl) fun τ₁' τ₂' ⟨x9₁, r₁⟩ ⟨x9₂, r₂⟩ => ?_
  obtain ge₁ := e₁.of_regs r₁
  obtain ge₂ := e₂.of_regs r₂
  obtain gk₁ := k₁.of_others r₁.others
  obtain gk₂ := k₂.of_others r₂.others
  -- The branch and its run.
  obtain ev : ∀ {τ : State}, τ.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      isa.eval (.zero .x .x9) τ =
        some (decide ((if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) = 0)) :=
    fun h => eval_zero h (by split <;> decide)
  obtain tIn : ∀ {τ' : State} (hok : Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat = true),
      Env Wn (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' → τ'.gpr .x12 = σ₁.gpr .x5 →
      τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa tagIn τ' fun τ'' => Env Wn (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' ∧ Kept τ'.gpr τ'' :=
    fun hok he h12 h28 hr => WP.mono (tagIn_ok he.x19 h12 h28 (tagLenOk_le hok) hr he.perm.w
      (dtw.sub_right (Region.sub_prefix (by decide)))) fun _ ⟨_, _, og, sp, rd, wr⟩ =>
        ⟨he.keep (fun r hr => og r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp rd wr, Kept.of_others (fun _ _ => rfl) og⟩
  obtain run : ∀ {τ' : State} {k : Reg → BitVec 64}, Env Wn (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ' →
      Kept k τ' → τ'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk (σ₁.gpr .x6).toNat then 1 else 0) →
      τ'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat → τ'.gpr .x26 = BitVec.ofNat 64 (σ₁.gpr .x3).toNat →
      τ'.gpr .x27 = BitVec.ofNat 64 (σ₁.gpr .x4).toNat → τ'.gpr .x28 = BitVec.ofNat 64 (σ₁.gpr .x6).toNat →
      τ'.gpr .x12 = σ₁.gpr .x5 → Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ'.rd ++ τ'.wr) →
      WP isa (.ite (.zero .x .x9) (.block [imm .x0 0])
        (.seq tagIn (.seq (finBody v.callees uO) (.seq cmp (.block verRet))))) τ' fun τ'' =>
        Env Wn (σ₁.gpr .x0) (σ₁.gpr .x2) (σ₁.gpr .x7) σ₁.sp τ'' := by
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
      refine WP.seq (WP.mono (cmp_ok L he₄ hk₄ (by rw [hk₄ .x28 (by decide), h28])
        (tagLenOk_le hok)) fun τ₅ ⟨x10₅, he₅, _, _, _⟩ => ?_)
      exact WP.mono (verRet_ok (b := decide (bytesAt τ₄.mem (σ₁.gpr .x7 + BitVec.ofNat 64 112)
        (σ₁.gpr .x6).toNat = bytesAt τ₄.mem (σ₁.gpr .x7) (σ₁.gpr .x6).toNat))
        (by rw [x10₅]; simp only [decide_eq_true_eq])) fun _ ⟨_, r⟩ => he₅.of_regs r
  have g9₁ : τ₁'.gpr .x9 = _ := x9₁
  have g9₂ : τ₂'.gpr .x9 = _ := x9₂
  obtain o22₁ : τ₁'.gpr .x22 = _ := (r₁.others .x22 (by decide)).trans x22₁
  obtain o22₂ : τ₂'.gpr .x22 = _ := (r₂.others .x22 (by decide)).trans x22₂
  obtain o26₁ : τ₁'.gpr .x26 = _ := (r₁.others .x26 (by decide)).trans a26₁
  obtain o26₂ : τ₂'.gpr .x26 = _ := (r₂.others .x26 (by decide)).trans a26₂
  obtain o27₁ : τ₁'.gpr .x27 = _ := (r₁.others .x27 (by decide)).trans a27₁
  obtain o27₂ : τ₂'.gpr .x27 = _ := (r₂.others .x27 (by decide)).trans a27₂
  obtain o28₁ : τ₁'.gpr .x28 = _ := (r₁.others .x28 (by decide)).trans t28₁
  obtain o28₂ : τ₂'.gpr .x28 = _ := (r₂.others .x28 (by decide)).trans t28₂
  obtain o12₁ : τ₁'.gpr .x12 = _ := (r₁.others .x12 (by decide)).trans x12₁
  obtain o12₂ : τ₂'.gpr .x12 = _ := (r₂.others .x12 (by decide)).trans x12₂
  obtain oR₁ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₁'.rd ++ τ₁'.wr) := by rw [r₁.rd, r₁.wr]; exact tR₁
  obtain oR₂ : Covers [⟨σ₁.gpr .x5, (σ₁.gpr .x6).toNat⟩] (τ₂'.rd ++ τ₂'.wr) := by rw [r₂.rd, r₂.wr]; exact tR₂
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
    obtain c28₁ : τ₄.gpr .x28 = _ := (hk₄ .x28 (by decide)).trans o28₁
    obtain c28₂ : τ₄'.gpr .x28 = _ := (hk₄' .x28 (by decide)).trans o28₂
    refine rel_seq (rel_taint [.x19, .x28] (by rw [he₄.sp, he₄'.sp])
        (by agree_tac [he₄.x19, he₄'.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩)
      (cmp_ok L he₄ hk₄ c28₁ (tagLenOk_le hok)) (cmp_ok L he₄' hk₄' c28₂ (tagLenOk_le hok))
      fun τ₅ τ₅' ⟨_, he₅, _, _, _⟩ ⟨_, he₅', _, _, _⟩ => ?_
    exact rel_taint [] (by rw [he₅.sp, he₅'.sp]) (by agree_tac []) ⟨_, by taint_decide⟩
  · exact rel_taint [.x19] (by rw [f₁.sp, f₂.sp]) (by agree_tac [f₁.x19, f₂.x19]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: what `seal` and `open` share, in two runs

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load (`RelCT.block_split`), and the rest runs from
`x9`, which holds `work` (public) in both runs. Then `j0`, `oneAad` and
`encPrep` (`front_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem RelCT.assoc' {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (Exec.seq_assoc' e₁) (Exec.seq_assoc' e₂)

/-- `oneAad`'s first block. -/
theorem aadBlk_ok {Wn : Nat} {s : State} {W A : Addr} {al : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, Wn⟩] (s.rd ++ s.wr)) (sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al) :
    WP isa (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO, imm .x25 0]) s fun s' =>
      s'.gpr .x23 = A ∧ s'.gpr .x24 = BitVec.ofNat 64 al ∧ s'.gpr .x25 = BitVec.ofNat 64 0 ∧
      Regs [.x23, .x24, .x25] s s' := by
  have q₁ := in_off hr (show 216 + 8 ≤ 512 by decide) (by decide)
  have q₂ := in_off hr (show 224 + 8 ≤ 512 by decide) (by decide)
  refine WP.run ⟨_, by arun [h19, q₁, q₂], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sA]; rfl
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]; rw [← sL]; rfl

/-- `encPrep`. -/
theorem encPrep_ok {Wn : Nat} {s : State} {W D : Addr} {al n : Nat} (h19 : s.gpr .x19 = W)
    (hr : Covers [⟨W, Wn⟩] (s.rd ++ s.wr)) (hlt : al < 2 ^ 64)
    (sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al)
    (sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D)
    (sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n) :
    WP isa (.block encPrep) s fun s' =>
      s'.gpr .x25 = BitVec.ofNat 64 (al % 16) ∧ s'.gpr .x26 = BitVec.ofNat 64 n ∧ s'.gpr .x27 = 0 ∧
      s'.gpr .x28 = D ∧ Regs [.x9, .x10, .x25, .x26, .x27, .x28] s s' := by
  have q₂ := in_off hr (show 224 + 8 ≤ 512 by decide) (by decide)
  have q₃ := in_off hr (show 232 + 8 ≤ 512 by decide) (by decide)
  have q₄ := in_off hr (show 240 + 8 ≤ 512 by decide) (by decide)
  refine WP.run ⟨_, by simp only [encPrep]; arun [h19, q₂, q₃, q₄], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ?_, by simp [gpr_write], ?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 224#64) 8 = s.mem.readW (W + BitVec.ofNat 64 224) 64 from rfl, sL,
      show BitVec.setWidth 64 (15#16) <<< (16 * 0) = BitVec.ofNat 64 15 by decide, and15, toNat_ofNat_of_lt hlt]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 240#64) 8 = s.mem.readW (W + BitVec.ofNat 64 240) 64 from rfl, sN]
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    rw [show s.mem.read (W + 232#64) 8 = s.mem.readW (W + BitVec.ofNat 64 232) 64 from rfl, sD]

/-- What `front_ok` needs of a run. -/
structure FrontIn (Wn : Nat) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (Np A D : Addr) (nl al n : Nat) (s : State) :
    Prop where
  env : Env Wn Ctx St W SP s
  kept : Kept k s
  x23 : s.gpr .x23 = Np
  x24 : s.gpr .x24 = BitVec.ofNat 64 nl
  x26 : s.gpr .x26 = BitVec.ofNat 64 nl
  x27 : s.gpr .x27 = 0
  non : DataOk Wn St W s Np nl
  aad : DataOk Wn St W s A al
  sA : s.mem.readW (W + BitVec.ofNat 64 216) 64 = A
  sL : s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 al
  sD : s.mem.readW (W + BitVec.ofNat 64 232) 64 = D
  sN : s.mem.readW (W + BitVec.ofNat 64 240) 64 = BitVec.ofNat 64 n

/-- What `front_rel` leaves of a run. -/
structure FrontOut (Wn : Nat) (Ctx St W SP : Addr) (k : Reg → BitVec 64) (D : Addr) (al n : Nat) (s₀ s : State) :
    Prop where
  env : Env Wn Ctx St W SP s
  x22 : s.gpr .x22 = k .x22
  x25 : s.gpr .x25 = BitVec.ofNat 64 (al % 16)
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  x27 : s.gpr .x27 = 0
  x28 : s.gpr .x28 = D
  frame : Frame (frontFrame St W) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {Wn : Nat} {Ctx St W SP : Addr} (L : Lay Wn Ctx St W)
include L

/-- `j0`, `oneAad` and `encPrep` in two runs. -/
theorem front_rel (v : GcmImpl) {k₁ k₂ : Reg → BitVec 64} {Np A D : Addr} {nl al n : Nat} {σ₁ σ₂ : State}
    (h₁ : FrontIn Wn Ctx St W SP k₁ Np A D nl al n σ₁) (h₂ : FrontIn Wn Ctx St W SP k₂ Np A D nl al n σ₂)
    {rest : Prog isa}
    (hr : ∀ τ₁ τ₂, FrontOut Wn Ctx St W SP k₁ D al n σ₁ τ₁ → FrontOut Wn Ctx St W SP k₂ D al n σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) rest TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (j0 v.callees) (.seq (oneAad v.callees) (.seq (.block encPrep) rest))) TT := by
  have hlt := h₁.aad.lt
  have j₁ : J0In Wn Ctx St W SP k₁ (blockAt σ₁.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₁ :=
    ⟨h₁.env, h₁.kept, h₁.x23, h₁.x24, h₁.x26, h₁.x27, h₁.non, rfl⟩
  have j₂ : J0In Wn Ctx St W SP k₂ (blockAt σ₂.mem (Ctx + BitVec.ofNat 64 240)) Np nl σ₂ :=
    ⟨h₂.env, h₂.kept, h₂.x23, h₂.x24, h₂.x26, h₂.x27, h₂.non, rfl⟩
  refine rel_seq (j0_rel L v j₁ j₂) (WP.with_rdwr (j0_ok L v j₁)) (WP.with_rdwr (j0_ok L v j₂))
    fun s₁ s₂ ⟨o₁, rd₁, wr₁⟩ ⟨o₂, rd₂, wr₂⟩ => ?_
  have sl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₁.frame (slots_j0Frame L) a b
  have sl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept o₂.frame (slots_j0Frame L) a b
  refine RelCT.assoc' ?_
  refine rel_seq (rel_taint [.x19] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [o₁.env.x19, o₂.env.x19])
      ⟨_, by taint_decide⟩)
    (aadBlk_ok (A := A) (al := al) o₁.env.x19 (covers_left o₁.env.perm.w) (by rw [sl₁ 216 (by decide) (by decide), h₁.sA])
      (by rw [sl₁ 224 (by decide) (by decide), h₁.sL]))
    (aadBlk_ok (A := A) (al := al) o₂.env.x19 (covers_left o₂.env.perm.w) (by rw [sl₂ 216 (by decide) (by decide), h₂.sA])
      (by rw [sl₂ 224 (by decide) (by decide), h₂.sL]))
    fun s₁' s₂' ⟨x23₁, x24₁, x25₁, r₁⟩ ⟨x23₂, x24₂, x25₂, r₂⟩ => ?_
  have a₁ : AbsIn Wn Ctx St W SP k₁ (blockAt s₁'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₁' :=
    ⟨o₁.env.of_regs r₁, o₁.kept.of_others r₁.others, x23₁, x24₁, x25₁, rfl,
      h₁.aad.of_eq (by rw [r₁.rd, rd₁]) (by rw [r₁.wr, wr₁]), rfl⟩
  have a₂ : AbsIn Wn Ctx St W SP k₂ (blockAt s₂'.mem (Ctx + BitVec.ofNat 64 240)) [] A al 0 s₂' :=
    ⟨o₂.env.of_regs r₂, o₂.kept.of_others r₂.others, x23₂, x24₂, x25₂, rfl,
      h₂.aad.of_eq (by rw [r₂.rd, rd₂]) (by rw [r₂.wr, wr₂]), rfl⟩
  refine rel_seq (absorbAl_rel L v (.inr rfl) a₁ a₂) (WP.with_rdwr (absorbAl_ok L (.inr rfl) v a₁))
    (WP.with_rdwr (absorbAl_ok L (.inr rfl) v a₂)) fun t₁ t₂ ⟨b₁, brd₁, bwr₁⟩ ⟨b₂, brd₂, bwr₂⟩ => ?_
  have f₁ : Frame (frontFrame St W) σ₁.mem t₁.mem :=
    (o₁.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₁.mem]; exact b₁.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have f₂ : Frame (frontFrame St W) σ₂.mem t₂.mem :=
    (o₂.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩).trans
      (by rw [← r₂.mem]; exact b₂.frame.sub fun r hr => ⟨r, List.mem_append_right _ hr, fun _ h => h⟩)
  have tl₁ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₁ (slots_frontFrame L) a b
  have tl₂ := fun d (a : 216 ≤ d) (b : d + 8 ≤ 256) => slot_kept f₂ (slots_frontFrame L) a b
  refine rel_seq (rel_taint [.x19] (by rw [b₁.env.sp, b₂.env.sp]) (by agree_tac [b₁.env.x19, b₂.env.x19])
      ⟨_, by taint_decide⟩)
    (encPrep_ok (D := D) (n := n) b₁.env.x19 (covers_left b₁.env.perm.w) hlt (by rw [tl₁ 224 (by decide) (by decide), h₁.sL])
      (by rw [tl₁ 232 (by decide) (by decide), h₁.sD]) (by rw [tl₁ 240 (by decide) (by decide), h₁.sN]))
    (encPrep_ok (D := D) (n := n) b₂.env.x19 (covers_left b₂.env.perm.w) hlt (by rw [tl₂ 224 (by decide) (by decide), h₂.sL])
      (by rw [tl₂ 232 (by decide) (by decide), h₂.sD]) (by rw [tl₂ 240 (by decide) (by decide), h₂.sN]))
    fun u₁ u₂ ⟨e25₁, e26₁, e27₁, e28₁, er₁⟩ ⟨e25₂, e26₂, e27₂, e28₂, er₂⟩ => ?_
  refine hr u₁ u₂ ⟨b₁.env.of_regs er₁, ?_, e25₁, e26₁, e27₁, e28₁, by rw [er₁.mem]; exact f₁,
      by rw [er₁.rd, brd₁, r₁.rd, rd₁], by rw [er₁.wr, bwr₁, r₁.wr, wr₁]⟩
    ⟨b₂.env.of_regs er₂, ?_, e25₂, e26₂, e27₂, e28₂, by rw [er₂.mem]; exact f₂,
      by rw [er₂.rd, brd₂, r₂.rd, rd₂], by rw [er₂.wr, bwr₂, r₂.wr, wr₂]⟩
  · rw [er₁.others _ (by decide), b₁.kept .x22 (by decide)]
  · rw [er₂.others _ (by decide), b₂.kept .x22 (by decide)]

end


/-- The load of `work`, at `sp + k`. -/
theorem ldr9_ok {s : State} {W : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8) :
    WP isa (.block [.ldrSp .x9 k]) s fun s' => s'.gpr .x9 = W ∧ (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  let ⟨s', run, x9, g, sp, _, rd, wr⟩ := ldrSp_ok hk hW hsp
  WP.of_runBlock ⟨s', run, x9, g, sp, rd, wr⟩

/-- The entry of `seal` and `open` in two runs, with `work` at `sp + k`. -/
theorem entry_rel {Wn : Nat} {σ₁ σ₂ : State} {W : Addr} {k : Nat} (hk : k = 8 ∨ k = 16 ∨ k = 24 ∨ k = 40)
    (hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 k) 64 = W) (hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 k) 64 = W)
    (hsp₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 k) 8)
    (hsp₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 k) 8)
    (hw₁ : Covers [⟨W, Wn⟩] σ₁.wr) (hw₂ : Covers [⟨W, Wn⟩] σ₂.wr) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k)) TT := by
  have hk' : k % 8 = 0 ∧ k < 32768 := by rcases hk with rfl | rfl | rfl | rfl <;> decide
  have run : ∀ {σ : State}, σ.mem.readW (σ.sp + BitVec.ofNat 64 k) 64 = W →
      InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 k) 8 → Covers [⟨W, Wn⟩] σ.wr →
      WP isa (.block ([.ldrSp .x9 k] ++ save .x9)) σ fun s' => s'.gpr .x9 = W ∧
        (∀ r, r ≠ .x9 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun hW hsp hw =>
    WP.block_append (WP.mono (ldr9_ok hk' hW hsp) fun s₁ ⟨x9₁, g₁, sp₁, rd₁, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok s₁ .x9 x9₁ (by rw [wr₁]; exact hw)
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], fun r hr => by rw [g₂, g₁ r hr], by rw [sp₂, sp₁]⟩)
  have t₁ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.ldrSp .x9 k]) h).isSome = true := by
    rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs [.x9]) (.block (save .x9)) h).isSome = true := ⟨_, by taint_decide⟩
  show RelCT isa _ (.block ([.ldrSp .x9 k] ++ save .x9 ++ _)) _
  refine RelCT.block_split (rel_seq (RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) t₁)
      (ldr9_ok hk' hW₁ hsp₁) (ldr9_ok hk' hW₂ hsp₂)
      fun τ₁ τ₂ ⟨x9₁, _, sp₁, _, _⟩ ⟨x9₂, _, sp₂, _, _⟩ =>
        rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) t₂))
    (run hW₁ hsp₁ hw₁) (run hW₂ hsp₂ hw₂) fun τ₁ τ₂ ⟨x9₁, g₁, sp₁⟩ ⟨x9₂, g₂, sp₂⟩ => ?_)
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_ ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  · rw [g₁ r h9, g₂ r h9]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

end VG.Proof.AesGcm.AArch64

end

end

/-!
# AES-GCM on AArch64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. The entry by `entry_rel`,
`j0` and the additional data by `front_rel`, the text by `encBody_rel` and
the tag by `finBody_rel`; the blocks between them by the taint analysis, with
`tag`, which the code loads from memory, public in both runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `oneCore` gives, with the values of the first run. -/
structure OneFacts (Wn : Nat) (σ σ₀ : State) (n w : Nat) : Prop where
  ol : OneLay Wn σ₀ n w
  hW : stackArg σ w = stackArg σ₀ w
  perm : Perm Wn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ
  hsp : ∀ i < n, InRegions (σ.rd ++ σ.wr) (σ.sp + BitVec.ofNat 64 (8 * i)) 8
  nonceR : Covers [⟨σ₀.gpr .x2, (σ₀.gpr .x3).toNat⟩] (σ.rd ++ σ.wr)
  aadR : Covers [⟨σ₀.gpr .x4, (σ₀.gpr .x5).toNat⟩] (σ.rd ++ σ.wr)
  dataW : Covers [⟨σ₀.gpr .x6, (σ₀.gpr .x7).toNat⟩] σ.wr
  args : (args σ n).Disjoint (workR Wn (stackArg σ₀ w))

theorem oneFacts {Wn : Nat} {σ₁ σ₂ : State} {n w : Nat} (hw : w < n) (h₁ : oneCore n w σ₁) (h₂ : oneCore n w σ₂)
    (hq : onePub n σ₁ σ₂) : OneFacts Wn σ₁ σ₁ n w ∧ OneFacts Wn σ₂ σ₁ n w := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  obtain qw : stackArg σ₁ w = stackArg σ₂ w := qa w hw
  obtain o₁ := oneLay h₁
  obtain o₂ := oneLay h₂
  refine ⟨⟨o₁, rfl, o₁.perm, o₁.hsp, o₁.nonceR, o₁.aadR, o₁.dataW, o₁.args⟩,
    ⟨o₁, qw.symm, ?_, o₂.hsp, ?_, ?_, ?_, ?_⟩⟩
  · have := o₂.perm; rw [← q0, ← qw] at this; exact this
  · have := o₂.nonceR; rw [← q2, ← q3] at this; exact this
  · have := o₂.aadR; rw [← q4, ← q5] at this; exact this
  · have := o₂.dataW; rw [← q6, ← q7] at this; exact this
  · have := o₂.args; rw [← qw] at this; exact this

/-- A stack argument, at `sp + j` with `j < 8 * n`, is outside `work`. -/
theorem OneFacts.argW {Wn : Nat} {σ σ₀ : State} {n w : Nat} (f : OneFacts Wn σ σ₀ n w) {j : Nat} (hj : j + 8 ≤ 8 * n) :
    (⟨σ.sp + BitVec.ofNat 64 j, 8⟩ : Region).Disjoint (workR Wn (stackArg σ₀ w)) := by
  refine f.args.sub_left ?_
  show Region.Sub ⟨σ.sp + BitVec.ofNat 64 j, 8⟩ ⟨σ.sp + BitVec.ofNat 64 (8 * 0), 8 * n⟩
  rw [show σ.sp + BitVec.ofNat 64 (8 * 0) = σ.sp by rw [Nat.mul_zero, BitVec.add_zero]]
  exact Offset.sub_base _ hj

/-- `FrontIn` after the entry. -/
theorem frontIn_of {Wn : Nat} {σ σ₀ τ : State} {n w : Nat} {V : BitVec 64} (f : OneFacts Wn σ σ₀ n w)
    (h3 : σ.gpr .x3 = σ₀.gpr .x3) (h2 : σ.gpr .x2 = σ₀.gpr .x2) (h4 : σ.gpr .x4 = σ₀.gpr .x4)
    (h5 : σ.gpr .x5 = σ₀.gpr .x5) (h6 : σ.gpr .x6 = σ₀.gpr .x6) (h7 : σ.gpr .x7 = σ₀.gpr .x7)
    (a : Env Wn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ ∧
      τ.gpr .x22 = σ.gpr .x1 ∧ τ.gpr .x23 = σ.gpr .x2 ∧ τ.gpr .x24 = σ.gpr .x3 ∧
      τ.gpr .x26 = σ.gpr .x3 ∧ τ.gpr .x27 = 0 ∧ τ.gpr .x28 = V ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 216) 64 = σ.gpr .x4 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 224) 64 = σ.gpr .x5 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 232) 64 = σ.gpr .x6 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 240) 64 = σ.gpr .x7 ∧
      τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 248) 64 = V ∧
      Frame [entryR (stackArg σ₀ w)] σ.mem τ.mem ∧ SavedAt τ.mem (stackArg σ₀ w) σ ∧ τ.rd = σ.rd ∧
      τ.wr = σ.wr) :
    FrontIn Wn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ.gpr (σ₀.gpr .x2)
      (σ₀.gpr .x4) (σ₀.gpr .x6) (σ₀.gpr .x3).toNat (σ₀.gpr .x5).toNat (σ₀.gpr .x7).toNat τ := by
  obtain hWn := a.perm.hWn
  obtain ⟨he, _, x23, x24, x26, x27, _, s1, s2, s3, s4, _, _, _, rd, wr⟩ := a
  obtain sub16 : Region.Sub ⟨stackArg σ₀ w + BitVec.ofNat 64 16, 80⟩ (workR Wn (stackArg σ₀ w)) := Lay.wSub (by decide)
  exact ⟨he, fun _ _ => rfl, by rw [x23, h2], by rw [x24, h3, ofNat_toNat'], by rw [x26, h3, ofNat_toNat'], x27,
    ⟨by rw [rd, wr]; exact f.nonceR, (σ₀.gpr .x3).isLt, f.ol.nw, f.ol.nonce.sub_right sub16, f.ol.nonce⟩,
    ⟨by rw [rd, wr]; exact f.aadR, (σ₀.gpr .x5).isLt, f.ol.aw, f.ol.aad.sub_right sub16, f.ol.aad⟩,
    by rw [s1, h4], by rw [s2, h5, ofNat_toNat'], by rw [s3, h6], by rw [s4, h7, ofNat_toNat']⟩

/-- The entry of `seal` and `open` and its stash, in two runs: `work` at `sp + k`, and
the stack argument at `sp + j` kept. -/
theorem entryStash_rel {Wn : Nat} {σ₁ σ₂ : State} {n w k j : Nat} (hk : k = 8 ∨ k = 16 ∨ k = 24 ∨ k = 40) (hkw : k = 8 * w) (hj : j = 0 ∨ j = 8)
    (f₁ : OneFacts Wn σ₁ σ₁ n w) (f₂ : OneFacts Wn σ₂ σ₁ n w) (hwn : w < n) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (oneEntry k ++ stashArg j)) TT := by
  subst hkw
  have hW₁ : σ₁.mem.readW (σ₁.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := rfl
  have hW₂ : σ₂.mem.readW (σ₂.sp + BitVec.ofNat 64 (8 * w)) 64 = stackArg σ₁ w := f₂.hW
  obtain ts : ∃ h, (taint.check (Taint.ofRegs [.x19]) (.block (stashArg j)) h).isSome = true := by
    rcases hj with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine RelCT.block_split (rel_seq (entry_rel hk hW₁ hW₂ (f₁.hsp w hwn) (f₂.hsp w hwn) f₁.perm.w f₂.perm.w qsp hq)
    (oneEntry_ok (by rcases hk with h | h | h | h <;> rw [h] <;> decide) hW₁ (f₁.hsp w hwn) rfl f₁.perm)
    (oneEntry_ok (by rcases hk with h | h | h | h <;> rw [h] <;> decide) hW₂ (f₂.hsp w hwn) (hq .x0 (by simp)).symm f₂.perm)
    fun τ₁ τ₂ a₁ a₂ => rel_taint [.x19] (by rw [a₁.1.sp, a₂.1.sp, qsp]) (by agree_tac [a₁.1.x19, a₂.1.x19]) ts)

/-- What the entry of `seal` leaves in a run from `σ`, with the values of the
first run `σ₀`. -/
abbrev SealEntered (Wn : Nat) (w : Nat) (σ σ₀ τ : State) : Prop :=
  Env Wn (σ₀.gpr .x0) (stackArg σ₀ w + BitVec.ofNat 64 16) (stackArg σ₀ w) σ.sp τ ∧
    τ.gpr .x22 = σ.gpr .x1 ∧ τ.gpr .x23 = σ.gpr .x2 ∧ τ.gpr .x24 = σ.gpr .x3 ∧
    τ.gpr .x26 = σ.gpr .x3 ∧ τ.gpr .x27 = 0 ∧ τ.gpr .x28 = stackArg σ₀ 0 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 216) 64 = σ.gpr .x4 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 224) 64 = σ.gpr .x5 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 232) 64 = σ.gpr .x6 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 240) 64 = σ.gpr .x7 ∧
    τ.mem.readW (stackArg σ₀ w + BitVec.ofNat 64 248) 64 = stackArg σ₀ 0 ∧
    Frame [entryR (stackArg σ₀ w)] σ.mem τ.mem ∧ SavedAt τ.mem (stackArg σ₀ w) σ ∧ τ.rd = σ.rd ∧ τ.wr = σ.wr

/-- `seal` after its entry, in two runs. -/
theorem sealRest_rel {Wn : Nat} (v : GcmImpl) {w : Nat} {extra₁ extra₂ extraW₁ extraW₂ : List Region} {σ₁ σ₂ τ₁ τ₂ : State}
    (h₁ : sealPreXW w extra₁ σ₁ extraW₁) (h₂ : sealPreXW w extra₂ σ₂ extraW₂)
    (hq : onePub (w + 1) σ₁ σ₂) (a₁ : SealEntered Wn w σ₁ σ₁ τ₁) (a₂ : SealEntered Wn w σ₂ σ₁ τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (sealRest v.callees) TT := by
  unfold sealRest
  obtain ⟨f₁, f₂⟩ := oneFacts (by omega_using [] : w < w + 1) (sealCore h₁) (sealCore h₂) hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have L := f₁.ol.lay
  obtain i₁ := frontIn_of f₁ rfl rfl rfl rfl rfl rfl a₁
  obtain i₂ := frontIn_of f₂ q3.symm q2.symm q4.symm q5.symm q6.symm q7.symm a₂
  rw [← qsp] at i₂
  obtain ⟨_, x22₁, _, _, _, _, _, _, s2₁, _, s4₁, s5₁, _, _, rd₁, wr₁⟩ := a₁
  obtain ⟨_, x22₂, _, _, _, _, _, _, s2₂, _, s4₂, s5₂, _, _, rd₂, wr₂⟩ := a₂
  rw [← q1] at x22₂
  rw [← q5] at s2₂
  rw [← q7] at s4₂
  have ol := f₁.ol
  obtain sub16 : Region.Sub ⟨stackArg σ₁ w + BitVec.ofNat 64 16, 80⟩ (workR Wn (stackArg σ₁ w)) := Lay.wSub (by decide)
  have hRb : (σ₁.gpr .x1).toNat = 10 ∨ (σ₁.gpr .x1).toNat = 12 ∨ (σ₁.gpr .x1).toNat = 14 := ol.rounds
  obtain hal := (σ₁.gpr .x5).isLt
  obtain hn := (σ₁.gpr .x7).isLt
  refine front_rel L v i₁ i₂ fun u₁ u₂ o₁ o₂ => ?_
  obtain mkB : ∀ {σ τ u : State}, OneFacts Wn σ σ₁ (w + 1) w → τ.gpr .x22 = σ₁.gpr .x1 → τ.wr = σ.wr →
      FrontOut Wn (σ₁.gpr .x0) (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      BodyIn (σ₁.gpr .x0) (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) σ₁.sp u.gpr (σ₁.gpr .x1).toNat
        (σ₁.gpr .x7).toNat 0 (σ₁.gpr .x6) (Spec.Gcm.zeros (σ₁.gpr .x5).toNat) []
        (blockAt u.mem (σ₁.gpr .x0 + BitVec.ofNat 64 240)) u := fun f x22 wr o =>
    ⟨o.env, fun _ _ => rfl, by rw [o.x22, x22, ofNat_toNat'], hRb, by rw [o.x25, Proof.Gcm.length_zeros],
      o.x26, o.x27, o.x28, rfl, by decide,
      ⟨⟨covers_left (by rw [o.wr, wr]; exact f.dataW), hn, ol.dw, ol.data.sub_right sub16, ol.data⟩,
        by rw [o.wr, wr]; exact f.dataW, ol.cd⟩, rfl⟩
  obtain B₁ := mkB f₁ x22₁ wr₁ o₁
  obtain B₂ := mkB f₂ x22₂ wr₂ o₂
  refine rel_seq (encBody_rel L v B₁ B₂ rfl) (WP.with_rdwr (encBody_ok L v B₁ 0))
    (WP.with_rdwr (encBody_ok L v B₂ 0)) fun w₁ w₂ ⟨b₁, _, _⟩ ⟨b₂, _, _⟩ => ?_
  obtain sl : ∀ {σ τ u ω : State}, OneFacts Wn σ σ₁ (w + 1) w →
      FrontOut Wn (σ₁.gpr .x0) (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) σ₁.sp τ.gpr (σ₁.gpr .x6)
        (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat τ u →
      Frame (bodyFrame (stackArg σ₁ w + BitVec.ofNat 64 16) (stackArg σ₁ w) (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        u.mem ω.mem → ∀ d, 216 ≤ d → d + 8 ≤ 256 →
      ω.mem.readW (stackArg σ₁ w + BitVec.ofNat 64 d) 64 = τ.mem.readW (stackArg σ₁ w + BitVec.ofNat 64 d) 64 :=
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
  obtain y22₁ : z₁'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₁'.others _ (by decide), r₁.others _ (by decide), b₁.kept .x22 (by decide), o₁.x22, x22₁, ofNat_toNat']
  obtain y22₂ : z₂'.gpr .x22 = BitVec.ofNat 64 (σ₁.gpr .x1).toNat := by
    rw [r₂'.others _ (by decide), r₂.others _ (by decide), b₂.kept .x22 (by decide), o₂.x22, x22₂, ofNat_toNat']
  obtain e₁ := (b₁.env.of_regs r₁).of_regs r₁'
  obtain e₂ := (b₂.env.of_regs r₂).of_regs r₂'
  obtain y26₁ : z₁'.gpr .x26 = _ := (r₁'.others .x26 (by decide)).trans x26₁
  obtain y26₂ : z₂'.gpr .x26 = _ := (r₂'.others .x26 (by decide)).trans x26₂
  obtain y27₁ : z₁'.gpr .x27 = _ := (r₁'.others .x27 (by decide)).trans x27₁
  obtain y27₂ : z₂'.gpr .x27 = _ := (r₂'.others .x27 (by decide)).trans x27₂
  refine rel_seq (finBody_rel L v (.inl rfl) e₁ e₂ (fun _ _ => rfl)
      (fun _ _ => rfl) y22₁ y22₂ hRb y26₁ y26₂ y27₁ y27₂ hal hn)
    (finBody_env v L (.inl rfl) e₁ (fun _ _ => rfl) y22₁ hRb y26₁ y27₁ hn)
    (finBody_env v L (.inl rfl) e₂ (fun _ _ => rfl) y22₂ hRb y26₂ y27₂ hn) fun g₁ g₂ h₁ h₂ => ?_
  obtain c28₁ : g₁.gpr .x28 = stackArg σ₁ 0 := (h₁.2.1 .x28 (by decide)).trans x28₁
  obtain c28₂ : g₂.gpr .x28 = stackArg σ₁ 0 := (h₂.2.1 .x28 (by decide)).trans x28₂
  exact rel_taint [.x19, .x28] (by rw [h₁.1.sp, h₂.1.sp])
    (by agree_tac [h₁.1.x19, h₂.1.x19, c28₁, c28₂]) ⟨_, by taint_decide⟩

theorem seal_ct {Wn : Nat} (v : GcmImpl) (hWn : 768 ≤ Wn ∧ Wn ≤ 2560 := by first | assumption | decide) : ConstantTime isa (sealAArch64 Wn).pre (sealAArch64 Wn).pub («seal» v.callees) := by
  unfold «seal»
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨f₁, f₂⟩ := oneFacts (by decide : 1 < 2) (sealCore h₁) (sealCore h₂) hq
  have hq₀ := hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  obtain qt : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by decide)
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
      hT₂ (f₂.argW (by decide)) q0.symm f₂.perm) fun _ _ a₁ a₂ => sealRest_rel v (sealPreX_W h₁) (sealPreX_W h₂) hq₀ a₁ a₂

end VG.Proof.AesGcm.AArch64
