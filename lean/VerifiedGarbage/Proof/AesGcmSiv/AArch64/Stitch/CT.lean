module

import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Fn
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.FnCT
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Polyval
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Keys
import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Derive
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Impl.AesGcmSiv.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Absorb
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Steps
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: the functions are constant time

Untrusted: everything here is checked by Lean. As
`Proof.AesGcmSiv.AArch64.seal_ct` and `open_ct`: the batches, which call
nothing, pass the taint analysis (`Stitch/Taint.lean`); the blocks after
them go as `Proof.AesGcmSiv.AArch64.crypt_rel`'s, from block `8 ⌊n / 128⌋`
(`cryptRest_rel`), and the rest of the data is absorbed by `absorb`
(`absorb_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs CtrSt pubRegs rel_env rel_loop BL cryptBlock_rel
  cryptBlockL_ok cryptTailRest_check tag_rel tag_ok absorb_rel absorb_ok lens_ok mov2_ok polyA_check polyD_check
  lensBlock_check tagIn_check tagIn_ok chunkB_rel keys_rel keys_ok entry_rel entry_ok entry_pub rel_ldrT recv_ok
  recv_check sealEnd_check openEnd_check args_of_seal args_of_open TagSlot prmOf KeysPost TagPost CryptPost PolyPost
  cryptHead_ok cryptHead_check sealPre openPre cryR polyR bytesAt_keep)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ctr rel_ite rel_taint ct_of GcmImpl eval_zero eval_nonzero Others
  lsr_ofNat)
open VG.Proof.Gcm.AArch64.Pmull (PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)
open VG.Impl.AesGcmSiv.AArch64.Stitch

/-! ## Counter mode past the batches -/

/-- `rest` and the number of blocks past the batches. -/
theorem restC_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block (rest ++ ([.lsr .x .x9 .x28 4] : List Instr))) t fun t' => BL p (8 * (p.n / 128)) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * (8 * (p.n / 128))) / 16) := by
  have hn := L.n_lt
  rw [WP.block_append_iff]
  refine WP.mono (rest_ok L E) fun t₁ ⟨x27₁, x28₁, E₁, _, _, _, _⟩ => ?_
  refine WP.run ⟨_, by grun [], rfl⟩ fun t₂ ht₂ => ?_
  have e : 16 * (8 * (p.n / 128)) = 128 * (p.n / 128) := by omega
  refine ⟨⟨by rw [← ht₂]; exact E₁.write (by decide) _, ?_, ?_⟩, ?_⟩
  · rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x27₁, e]
  · rw [← ht₂, gpr_write_of_ne _ _ _ (by decide), x28₁, e]
  · rw [← ht₂, e]
    simp [gpr_write, State.read, x28₁, lsr_ofNat _ _ (show p.n - 128 * (p.n / 128) < 2 ^ 64 by omega)]

/-- The whole blocks of counter mode from block `b`, for their registers. -/
theorem cryptMidFrom_ok (v : GcmImpl) {p : Prm} (L : Lay p) {b : Nat} (hb : 16 * b ≤ p.n) {t : State}
    (B : BL p b t) (h9 : t.gpr .x9 = BitVec.ofNat 64 ((p.n - 16 * b) / 16)) :
    WP isa (.ite (.zero .x .x9) (.block []) (.loop (Impl.AesGcmSiv.AArch64.cryptBlock v.callees) (.nonzero .x .x9))) t
      (BL p (p.n / 16)) := by
  have hn := L.n_lt
  refine WP.ite (decide ((p.n - 16 * b) / 16 = 0)) (eval_zero h9 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (p.n - 16 * b) / 16 = 0 := by simpa using ht
    rw [show p.n / 16 = b by omega]; exact WP.block_nil B
  · have h0 : (p.n - 16 * b) / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ b ≤ j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - b) t ⟨b, rfl, Nat.le_refl _, by omega, B⟩
    rintro k t' ⟨j, rfl, hbj, hj, B'⟩
    refine WP.mono (cryptBlockL_ok v L (j := j) (by omega) B') fun t'' ⟨B'', x9⟩ => ?_
    have ev := eval_nonzero x9 (by omega)
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega), he ▸ B''⟩
    · right
      exact ⟨ev.trans (by simp; omega), p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, by omega, B''⟩

/-- `cryptRest`, in two runs with the same public arguments. -/
theorem cryptRest_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (cryptRest v.callees) TT := by
  have hn := L.n_lt
  have hb : 16 * (8 * (p.n / 128)) ≤ p.n := by omega
  refine rel_seq (rel_env E₁ E₂ [] (by simp) restC_check) (restC_ok L E₁) (restC_ok L E₂)
    fun u₁ u₂ ⟨B₁, x9₁⟩ ⟨B₂, x9₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_zero x9₁ (by omega)) (eval_zero x9₂ (by omega))
      (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun hf => ?_))
    (cryptMidFrom_ok v L hb B₁ x9₁) (cryptMidFrom_ok v L hb B₂ x9₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : (p.n - 16 * (8 * (p.n / 128))) / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ 8 * (p.n / 128) ≤ j ∧ j < p.n / 16 ∧ BL p j t₁ ∧
        BL p j t₂) (fun k t₁ t₂ ⟨j, hk, hbj, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 8 * (p.n / 128))
      ⟨8 * (p.n / 128), rfl, Nat.le_refl _, by omega, B₁, B₂⟩
    refine Proof.AesGcmSiv.AArch64.rel_wpQ
      (cryptBlock_rel v L J₁.env J₂.env (j := j) (by omega) J₁.x27 J₂.x27 J₁.x28 J₂.x28)
      (cryptBlockL_ok v L (by omega) J₁) (cryptBlockL_ok v L (by omega) J₂) fun a b ⟨K₁, x9₁⟩ ⟨K₂, x9₂⟩ => ?_
    have ev₁ := eval_nonzero x9₁ (by omega)
    have ev₂ := eval_nonzero x9₂ (by omega)
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : j + 1 ≠ p.n / 16 := by simp at hc; omega
    exact ⟨p.n / 16 - (j + 1), by omega, j + 1, rfl, by omega, by omega, K₁, K₂⟩
  -- The last bytes.
  have x28₁ : w₁.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₁.x28]; congr 1; omega
  have x28₂ : w₂.gpr .x28 = BitVec.ofNat 64 (p.n % 16) := by rw [C₂.x28]; congr 1; omega
  refine rel_ite (eval_zero x28₁ (by omega)) (eval_zero x28₂ (by omega))
    (fun _ => RelCT.block_nil fun _ _ _ => trivial) (fun _ => ?_)
  refine rel_seq (tag_rel v L C₁.env C₂.env (o := 224) (by decide)) (tag_ok v L C₁.env (o := 224) (by decide))
    (tag_ok v L C₂.env (o := 224) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.x27, .x28] (by simp [T₁.x27, T₂.x27, T₁.x28, T₂.x28, C₁.x27, C₂.x27, C₁.x28, C₂.x28])
    cryptTailRest_check

/-- `cryptHead`: the counter block from the tag. -/
theorem cryptHeadC_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (.block Impl.AesGcmSiv.AArch64.cryptHead) t fun t₁ => Env p t₁ ∧
      CtrSt p.W (Spec.GcmSiv.initialCounter (bytesAt t.mem p.W 16)) 0 t₁.mem := by
  obtain ⟨t₁, run₁, hm₁, _, _, _, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  exact WP.of_runBlock ⟨t₁, run₁, E.keep (fun r hr => ho₁ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁,
    by rw [hm₁]; exact headMem_ctr _⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (crypt e3 v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (cryptHeadC_ok L E₁) (cryptHeadC_ok L E₂)
    fun u₁ u₂ ⟨F₁, C₁⟩ ⟨F₂, C₂⟩ => ?_
  refine rel_seq (rel_env F₁ F₂ [] (by simp) (ctrB_check e3)) (ctrBatches_ok e3 L F₁ C₁) (ctrBatches_ok e3 L F₂ C₂)
    fun w₁ w₂ B₁ B₂ => ?_
  exact cryptRest_rel v L B₁.env B₂.env

/-! ## Absorbing the data -/

/-- `rest` then `absorb`: the data past its batches absorbed, in two runs
with the same public arguments. -/
theorem restAbs_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block rest) (Impl.AesGcmSiv.AArch64.absorb v.callees)) TT := by
  have hn := L.n_lt
  refine rel_seq (rel_env E₁ E₂ [] (by simp) rest_check) (rest_ok L E₁) (rest_ok L E₂)
    fun c₁ c₂ ⟨x27₁, x28₁, G₁, _, _, _, _⟩ ⟨x27₂, x28₂, G₂, _, _, _, _⟩ => ?_
  have dW : (⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩ : Region).Disjoint
      ⟨p.W, 3808⟩ := L.d_w.sub_left (Offset.sub_base p.D (by omega))
  have hc : ∀ {c : State}, Env p c →
      Covers [⟨p.D + BitVec.ofNat 64 (128 * (p.n / 128)), p.n - 128 * (p.n / 128)⟩] (c.rd ++ c.wr) := fun G =>
    Proof.AesGcm.AArch64.covers_left (Proof.AesGcm.AArch64.covers_off G.perm.d (by omega) hn)
  exact absorb_rel v L G₁ G₂ (by omega) (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 * (p.n / 128)) (by omega)]
      have := L.dw; have := Nat.mod_le (p.D.toNat + 128 * (p.n / 128)) (2 ^ 64); omega)
    dW (hc G₁) (hc G₂) x27₁ x27₂ x28₁ x28₂

/-- `polyData`, in two runs with the same public arguments. -/
theorem polyData_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (polyData e3 v.callees) TT :=
  rel_seq (rel_env E₁ E₂ [] (by simp) (polyB_check e3)) (polyBatches_ok hP gh e3 L E₁)
    (polyBatches_ok hP gh e3 L E₂)
    fun _ _ A₁ A₂ => restAbs_rel v L A₁.env A₂.env

/-- The lengths, in two runs with the same public arguments. -/
theorem lens_rel (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (Impl.AesGcmSiv.AArch64.lens v.callees) TT := by
  have wL : ∀ {d : State}, Env p d → WP isa (.block Impl.AesGcmSiv.AArch64.lensBlock) d fun t =>
      Env p t ∧ t.gpr .x27 = p.W + BitVec.ofNat 64 224 ∧ t.gpr .x28 = BitVec.ofNat 64 16 := fun E => by
    have w₀ := E.perm.wW (show 224 + 8 ≤ 3808 by decide)
    have w₈ := E.perm.wW (show 232 + 8 ≤ 3808 by decide)
    refine WP.run ⟨_, by simp only [Impl.AesGcmSiv.AArch64.lensBlock]; grun [E.x19, E.x24, E.x26, w₀, w₈], rfl⟩
      fun t ht => ?_
    subst ht
    refine ⟨E.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]) rfl rfl rfl,
      by simp [gpr_write, E.x19], by simp [gpr_write, Proof.AesGcmSiv.AArch64.movz_lit (show 16 < 2 ^ 16 by decide)]⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) lensBlock_check) (wL E₁) (wL E₂)
    fun f₁ f₂ ⟨K₁, x27₁, x28₁⟩ ⟨K₂, x27₂, x28₂⟩ => chunkB_rel v L K₁ K₂ x27₁ x27₂ x28₁ x28₂

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (polyval e3 v.callees) TT := by
  refine rel_seq (rel_env E₁ E₂ [] (by simp) polyA_check) (mov2_ok E₁ (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok E₂ (a := .x23) (b := .x24) (by decide) (by decide)) fun a₁ a₂ ⟨G₁, a27₁, a28₁, _, rd₁, wr₁⟩
      ⟨G₂, a27₂, a28₂, _, rd₂, wr₂⟩ => ?_
  rw [E₁.x23] at a27₁; rw [E₁.x24] at a28₁; rw [E₂.x23] at a27₂; rw [E₂.x24] at a28₂
  have hc₁ : Covers [⟨p.A, p.al⟩] (a₁.rd ++ a₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨p.A, p.al⟩] (a₂.rd ++ a₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ a27₁ a27₂ a28₁ a28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w a27₁ a28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w a27₂ a28₂)
    fun b₁ b₂ B₁ B₂ => ?_
  refine rel_seq (polyData_rel hP gh e3 v L B₁.env B₂.env) (polyData_ok hP gh e3 v L B₁.env)
    (polyData_ok hP gh e3 v L B₂.env) fun d₁ d₂ D₁ D₂ => ?_
  exact rel_seq (lens_rel v L D₁.env D₂.env) (lens_ok v L D₁.env) (lens_ok v L D₂.env) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check

/-! ## Decryption -/

open VG.Proof.AesGcmSiv.AArch64 (key_cryR absR) in
/-- The key schedule, after code that writes only what counter mode and the
batches' POLYVAL write. -/
theorem ciph_cryAbs {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR p.W p.D p.n ++ absR p.W) m m') :
    Spec.GcmSiv.ctxCiph m' (p.W + BitVec.ofNat 64 240) p.R = Spec.GcmSiv.ctxCiph m (p.W + BitVec.ofNat 64 240) p.R := by
  have hR := L.rounds_le
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => ?_) (by omega)]
  rcases List.mem_append.mp hr with hr | hr
  · exact (key_cryR L r hr).sub_left (Region.sub_prefix hR)
  · simp only [absR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.w_w (.inr (by omega)) (by omega) (by decide)
    · exact L.w_w (.inl (by omega)) (by omega) (by decide)

/-- `openData`, in two runs with the same public arguments. -/
theorem openData_rel (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) {p : Prm} (L : Lay p) {σ₁ σ₂ : State}
    (E₁ : Env p σ₁) (E₂ : Env p σ₂) : RelCT isa (Eq2 σ₁ σ₂) (openData e3 v.callees) TT := by
  have wR : ∀ {u w : State} {icb : List Byte}, OBatchPost p (Spec.GcmSiv.ctxCiph u.mem (p.W + BitVec.ofNat 64 240) p.R)
      icb (bytesAt u.mem p.D p.n) u w → WP isa (cryptRest v.callees) w (Env p) := fun B =>
    WP.mono (cryptRest_ok v L B.env (Proof.Cmac.bytesAt_length _ _ _) B.ctr B.data (ciph_cryAbs L B.frame))
      fun _ T => T.env
  refine rel_seq (rel_env E₁ E₂ [] (by simp) cryptHead_check) (cryptHeadC_ok L E₁) (cryptHeadC_ok L E₂)
    fun u₁ u₂ ⟨F₁, C₁⟩ ⟨F₂, C₂⟩ => ?_
  refine rel_seq (rel_env F₁ F₂ [] (by simp) (openB_check e3)) (openBatches_ok hP gh e3 L F₁ C₁)
    (openBatches_ok hP gh e3 L F₂ C₂) fun w₁ w₂ B₁ B₂ => ?_
  exact rel_seq (cryptRest_rel v L B₁.env B₂.env) (wR B₁) (wR B₂) fun _ _ G₁ G₂ => restAbs_rel v L G₁ G₂

/-! ## The functions -/

theorem seal_ct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    ConstantTime isa Proof.AesGcmSiv.AArch64.sealAArch64.pre Proof.AesGcmSiv.AArch64.sealAArch64.pub
      («seal» e3 v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -, hA₁⟩ := args_of_seal h₁
  obtain ⟨-, P₂, -, hA₂⟩ := args_of_seal h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  refine rel_seq (keys_rel v L E₁ E₂) (keys_ok v L E₁) (keys_ok v L E₂) fun a₁ a₂ K₁ K₂ => ?_
  refine rel_seq (polyval_rel hP gh e3 v L K₁.env K₂.env) (polyval_ok hP gh e3 v L K₁.env K₁.hkey K₁.acc)
    (polyval_ok hP gh e3 v L K₂.env K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  refine rel_seq (tag_rel v L P₁.env P₂.env (o := 0) (by decide)) (tag_ok v L P₁.env (o := 0) (by decide))
    (tag_ok v L P₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  refine rel_seq (crypt_rel e3 v L T₁.env T₂.env) (crypt_ok e3 v L T₁.env) (crypt_ok e3 v L T₂.env)
    fun d₁ d₂ C₁ C₂ => ?_
  have sl : ∀ {τ a b c d : State}, TagSlot (prmOf σ₁) τ.mem → KeysPost (prmOf σ₁) τ a → PolyPost (prmOf σ₁) a b →
      TagPost (prmOf σ₁) 0 b c → CryptPost (prmOf σ₁) c d → TagSlot (prmOf σ₁) d.mem := fun S K P T C =>
    (((S.frame K.frame (by disj_tac L)).frame P.frame (by disj_tac L)).frame T.frame (by disj_tac L)).frame C.frame
      (by disj_tac L)
  exact rel_ldrT (l := Impl.AesGcmSiv.AArch64.tagOut.tail ++ Impl.AesGcm.AArch64.restore) C₁.env C₂.env
    (sl S₁ K₁ P₁ T₁ C₁) (sl S₂ K₂ P₂ T₂ C₂) sealEnd_check

theorem open_ct (hP : PrepPow) (gh : Gh8Ok) (e3 : Bool) (v : GcmImpl) :
    ConstantTime isa Proof.AesGcmSiv.AArch64.openAArch64.pre Proof.AesGcmSiv.AArch64.openAArch64.pub
      («open» e3 v.callees) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, hA₁⟩ := args_of_open h₁
  obtain ⟨-, P₂, hA₂⟩ := args_of_open h₂
  refine rel_seq (entry_rel hp hA₁ hA₂) (entry_ok P₁ hA₁) (entry_pub hp P₂ hA₂)
    fun τ₁ τ₂ ⟨E₁, _, _, S₁, _⟩ ⟨E₂, S₂⟩ => ?_
  have wr : ∀ {τ : State}, Env (prmOf σ₁) τ → TagSlot (prmOf σ₁) τ.mem →
      WP isa (.block Impl.AesGcmSiv.AArch64.recv) τ (Env (prmOf σ₁)) :=
    fun E S => by
      obtain ⟨t, run, -, -, -, ho, sp, rd, wr⟩ := recv_ok L E S
      exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_ldrT (l := Impl.AesGcmSiv.AArch64.recv.tail) E₁ E₂ S₁ S₂ recv_check) (wr E₁ S₁) (wr E₂ S₂)
    fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel v L R₁ R₂) (keys_ok v L R₁) (keys_ok v L R₂) fun a₁ a₂ K₁ K₂ => ?_
  -- The additional data.
  refine rel_seq (rel_env K₁.env K₂.env [] (by simp) polyA_check)
    (mov2_ok K₁.env (a := .x23) (b := .x24) (by decide) (by decide))
    (mov2_ok K₂.env (a := .x23) (b := .x24) (by decide) (by decide)) fun b₁ b₂ ⟨G₁, b27₁, b28₁, _⟩
      ⟨G₂, b27₂, b28₂, _⟩ => ?_
  rw [K₁.env.x23] at b27₁; rw [K₁.env.x24] at b28₁; rw [K₂.env.x23] at b27₂; rw [K₂.env.x24] at b28₂
  have hc₁ : Covers [⟨(prmOf σ₁).A, (prmOf σ₁).al⟩] (b₁.rd ++ b₁.wr) := G₁.perm.aad
  have hc₂ : Covers [⟨(prmOf σ₁).A, (prmOf σ₁).al⟩] (b₂.rd ++ b₂.wr) := G₂.perm.aad
  refine rel_seq (absorb_rel v L G₁ G₂ L.al_lt L.aw L.a_w hc₁ hc₂ b27₁ b27₂ b28₁ b28₂)
    (absorb_ok v L G₁ hc₁ L.al_lt L.aw L.a_w b27₁ b28₁) (absorb_ok v L G₂ hc₂ L.al_lt L.aw L.a_w b27₂ b28₂)
    fun c₁ c₂ B₁ B₂ => ?_
  -- The data, decrypted and absorbed.
  refine rel_seq (openData_rel hP gh e3 v L B₁.env B₂.env) (openData_ok hP gh e3 v L B₁.env)
    (openData_ok hP gh e3 v L B₂.env) fun d₁ d₂ O₁ O₂ => ?_
  -- The lengths and the tag input.
  refine rel_seq (lens_rel v L O₁.env O₂.env) (lens_ok v L O₁.env) (lens_ok v L O₂.env) fun e₁ e₂ D₁ D₂ => ?_
  have wT : ∀ {d : State}, Env (prmOf σ₁) d →
      WP isa (.block Impl.AesGcmSiv.AArch64.tagIn) d (Env (prmOf σ₁)) := fun E => by
    obtain ⟨t, run, -, ho, sp, rd, wr⟩ := tagIn_ok E
    exact WP.of_runBlock ⟨t, run, E.keep (fun r hr => ho r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr⟩
  refine rel_seq (rel_env D₁.env D₂.env [] (by simp) tagIn_check) (wT D₁.env) (wT D₂.env) fun f₁ f₂ T₁ T₂ => ?_
  -- Its tag at `W + 224`, the comparison and the mask.
  exact rel_seq (tag_rel v L T₁ T₂ (o := 224) (by decide)) (tag_ok v L T₁ (o := 224) (by decide))
    (tag_ok v L T₂ (o := 224) (by decide)) fun _ _ X₁ X₂ => rel_env X₁.env X₂.env [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.AArch64.Stitch
