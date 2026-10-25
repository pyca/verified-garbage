module

import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Polyval
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Polyval
import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
meta import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Absorb
public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp

/-!
# AES-GCM-SIV on PPC64LE: POLYVAL in two runs

Untrusted: everything here is checked by Lean. `polyval`, run from two
states in the same environment, leaks the same: the code between calls by
the taint analysis (`rel_env`), from the pointer `r23` and the count `r24`,
which are public in both runs, and each call of `vg_ghash` by its proof
(`rel_gh`). The loop of chunks relates two runs after the same number of
blocks, which the correctness proofs describe (`CInv`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_lsr)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_ite eval_zero eval_nonzero)
open VG.Proof.AesCcm.PPC64LE (Runs Runs.of_wp Runs.mono Runs.and rel_seqR rel_of_eq2 rel_post rel_iteZ)
open VG.Spec.Aes (bytesAt)

/-- The additional data as the bytes to absorb. -/
theorem movA_wp {c : Cx} {σ : State} (E : Env c σ) :
    WP isa (.block [Impl.AesGcm.PPC64LE.mov .r23 .r18, Impl.AesGcm.PPC64LE.mov .r24 .r19]) σ fun t =>
      PK σ t ∧ t.mem = σ.mem ∧ t.gpr .r23 = c.A ∧ t.gpr .r24 = BitVec.ofNat 64 c.al :=
  VG.Proof.AesCcm.PPC64LE.wp_mv fun t₁ u₁ => VG.Proof.AesCcm.PPC64LE.wp_mv fun t₂ u₂ =>
    WP.block_nil ⟨(PK.ofUpd u₁).trans (PK.ofUpd u₂), by rw [u₂.mem, u₁.mem],
      by rw [u₂.other _ (by decide), u₁.gpr, E.r18], by rw [u₂.gpr, u₁.other _ (by decide), E.r19]⟩

/-- The data as the bytes to absorb. -/
theorem movD_wp {c : Cx} {σ : State} (E : Env c σ) :
    WP isa (.block [Impl.AesGcm.PPC64LE.mov .r23 .r20, Impl.AesGcm.PPC64LE.mov .r24 .r21]) σ fun t =>
      PK σ t ∧ t.mem = σ.mem ∧ t.gpr .r23 = c.D ∧ t.gpr .r24 = BitVec.ofNat 64 c.n :=
  VG.Proof.AesCcm.PPC64LE.wp_mv fun t₁ u₁ => VG.Proof.AesCcm.PPC64LE.wp_mv fun t₂ u₂ =>
    WP.block_nil ⟨(PK.ofUpd u₁).trans (PK.ofUpd u₂), by rw [u₂.mem, u₁.mem],
      by rw [u₂.other _ (by decide), u₁.gpr, E.r20], by rw [u₂.gpr, u₁.other _ (by decide), E.r21]⟩

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- A chunk of the `m` bytes at `Q`. -/
theorem chunk_rel {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ₁ : Src c σ₁ Q (16 * (m / 16)))
    (hQ₂ : Src c σ₂ Q (16 * (m / 16))) (h23₁ : σ₁.gpr .r23 = Q) (h23₂ : σ₂.gpr .r23 = Q)
    (h24₁ : σ₁.gpr .r24 = BitVec.ofNat 64 m) (h24₂ : σ₂.gpr .r24 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 σ₁ σ₂) chunk TT := by
  unfold chunk
  refine rel_seqR (rel_env [.r23, .r24] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h23₁, h23₂]
      · rw [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (chunkPre_wp L E₁ hm h16 hQ₁ h23₁ h24₁)) (Runs.of_wp (chunkPre_wp L E₂ hm h16 hQ₂ h23₂ h24₂))
    fun ρ₁ ρ₂ P₁ P₂ => ?_
  have hsp₁ : ρ₁.sp = ρ₂.sp := by rw [P₁.pk.sp, P₂.pk.sp, hsp]
  refine rel_seqR (rel_gh P₁.call P₂.call hsp₁) (gh_runs (E₁.of_pk P₁.pk) P₁.call)
    (gh_runs (E₂.of_pk P₂.pk) P₂.call) fun ω₁ ω₂ G₁ G₂ => ?_
  refine rel_env [.r24] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, hsp₁]) (fun r hr => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [G₁.2.2 .r24 (by simp), G₂.2.2 .r24 (by simp), P₁.r24, P₂.r24]

end

/-- The chunks of the `m` bytes at `Q`, in two runs from `σ₁` and `σ₂`. -/
theorem chunks_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (h16 : 16 ≤ m) (hQ₁ : Src c σ₁ Q (16 * (m / 16)))
    (hQ₂ : Src c σ₂ Q (16 * (m / 16))) (h23₁ : σ₁.gpr .r23 = Q) (h23₂ : σ₂.gpr .r23 = Q)
    (h24₁ : σ₁.gpr .r24 = BitVec.ofNat 64 m) (h24₂ : σ₂.gpr .r24 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 σ₁ σ₂) (.loop chunk (.nonzero .d .r11)) TT := by
  refine (RelCT.loop (Q := TT) (fun k (a b : State) => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧
      CInv c σ₁ Q m d a ∧ CInv c σ₂ Q m d b) (fun k => ?_) (m / 16 - 0)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨0, rfl, by omega_arith,
        ⟨⟨PK.refl _, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
          by rw [h23₁, Nat.mul_zero, BitVec.add_zero], by rw [h24₁, Nat.mul_zero, Nat.sub_zero]⟩,
        ⟨⟨PK.refl _, Frame.refl _ _, by simp [elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
          by rw [h23₂, Nat.mul_zero, BitVec.add_zero], by rw [h24₂, Nat.mul_zero, Nat.sub_zero]⟩⟩)
    fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨d, hk, hd, J₁, J₂⟩ => ?_
  have F₁ := E₁.of_pk J₁.abs.pk
  have F₂ := E₂.of_pk J₂.abs.pk
  have S₁ : Src c a (Q + BitVec.ofNat 64 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
    (hQ₁.slice (by omega_arith) (by omega_arith)).of_eq J₁.abs.pk.rd J₁.abs.pk.wr
  have S₂ : Src c b (Q + BitVec.ofNat 64 (16 * d)) (16 * ((m - 16 * d) / 16)) :=
    (hQ₂.slice (by omega_arith) (by omega_arith)).of_eq J₂.abs.pk.rd J₂.abs.pk.wr
  refine (rel_post (chunk_rel L F₁ F₂ (by rw [J₁.abs.pk.sp, J₂.abs.pk.sp, hsp]) (by omega_arith) (by omega_arith) S₁ S₂
      J₁.r23 J₂.r23 J₁.r24 J₂.r24)
    (Runs.of_wp (chunk_wp L F₁ (by omega_arith) (by omega_arith) S₁ J₁.r23 J₁.r24))
    (Runs.of_wp (chunk_wp L F₂ (by omega_arith) (by omega_arith) S₂ J₂.r23 J₂.r24))).mono (fun _ _ h => h)
    fun a' b' ⟨C₁, C₂⟩ => ?_
  obtain ⟨I₁', r11₁⟩ := J₁.step L hQ₁ hd C₁
  obtain ⟨I₂', r11₂⟩ := J₂.step L hQ₂ hd C₂
  have ev₁ := eval_nonzero r11₁ (by omega_arith)
  have ev₂ := eval_nonzero r11₂ (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial,
    fun ht => ⟨m / 16 - (d + min (m / 16 - d) 64), ?_, d + min (m / 16 - d) 64, rfl, ?_, I₁', I₂'⟩⟩
  · rw [ev₁] at ht; simp at ht; omega_arith
  · rw [ev₁] at ht; simp at ht; omega_arith

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `absTail`: the last `r` bytes at `P`. -/
theorem absTail_rel {P : Addr} {r : Nat} (hr1 : 1 ≤ r) (hr : r < 16) (hc₁ : Covers [⟨P, r⟩] (σ₁.rd ++ σ₁.wr))
    (hc₂ : Covers [⟨P, r⟩] (σ₂.rd ++ σ₂.wr)) (hd : (⟨P, r⟩ : Region).Disjoint ⟨c.W, 3824⟩)
    (h23₁ : σ₁.gpr .r23 = P) (h23₂ : σ₂.gpr .r23 = P) (h24₁ : σ₁.gpr .r24 = BitVec.ofNat 64 r)
    (h24₂ : σ₂.gpr .r24 = BitVec.ofNat 64 r) : RelCT isa (Eq2 σ₁ σ₂) absTail TT := by
  unfold absTail
  refine rel_seqR (rel_env [.r23, .r24] E₁ E₂ hsp (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · rw [h23₁, h23₂]
      · rw [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (absTailPre_wp L E₁ hr1 hr hc₁ hd h23₁ h24₁)) (Runs.of_wp (absTailPre_wp L E₂ hr1 hr hc₂ hd h23₂ h24₂))
    fun ρ₁ ρ₂ T₁ T₂ => ?_
  exact chunk_rel L (E₁.of_pk T₁.pk) (E₂.of_pk T₂.pk) (by rw [T₁.pk.sp, T₂.pk.sp, hsp]) (m := 16) (by decide)
    (by decide) (srcB L (E₁.of_pk T₁.pk).perm) (srcB L (E₂.of_pk T₂.pk).perm) T₁.r23 T₂.r23 T₁.r24 T₂.r24

/-- `absorb`: the `m` bytes at `Q`. -/
theorem absorb_rel {Q : Addr} {m : Nat} (hm : m < 2 ^ 64) (hQ₁ : Src c σ₁ Q m) (hQ₂ : Src c σ₂ Q m)
    (hd : (⟨Q, m⟩ : Region).Disjoint ⟨c.W, 3824⟩) (h23₁ : σ₁.gpr .r23 = Q) (h23₂ : σ₂.gpr .r23 = Q)
    (h24₁ : σ₁.gpr .r24 = BitVec.ofNat 64 m) (h24₂ : σ₂.gpr .r24 = BitVec.ofNat 64 m) :
    RelCT isa (Eq2 σ₁ σ₂) absorb TT := by
  unfold absorb wholeLeft
  have run : ∀ {σ : State}, Env c σ → σ.gpr .r24 = BitVec.ofNat 64 m →
      Runs (.block [.lsr .d .r11 .r24 4]) σ fun t =>
        Proof.ChaCha20Poly1305.PPC64LE.Upd σ t .r11 (BitVec.ofNat 64 (m / 16)) := fun E h24 =>
    Runs.of_wp (wp_lsr (by decide) fun t u => WP.block_nil
      ⟨by rw [u.gpr, h24, ofNat_lsr 4 hm], u.other, u.mem, u.rd, u.wr, u.sp, u.lr⟩)
  refine rel_seqR (rel_env [.r24] E₁ E₂ hsp (by simp [h24₁, h24₂]) ⟨_, by taint_decide⟩) (run E₁ h24₁)
    (run E₂ h24₂) fun τ₁ τ₂ u₁ u₂ => ?_
  have F₁ := E₁.of_pk (PK.ofUpd u₁)
  have F₂ := E₂.of_pk (PK.ofUpd u₂)
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [u₁.sp, u₂.sp, hsp]
  have q23₁ : τ₁.gpr .r23 = Q := by rw [u₁.other _ (by decide), h23₁]
  have q23₂ : τ₂.gpr .r23 = Q := by rw [u₂.other _ (by decide), h23₂]
  have q24₁ : τ₁.gpr .r24 = BitVec.ofNat 64 m := by rw [u₁.other _ (by decide), h24₁]
  have q24₂ : τ₂.gpr .r24 = BitVec.ofNat 64 m := by rw [u₂.other _ (by decide), h24₂]
  have R₁ : Src c τ₁ Q m := hQ₁.of_eq u₁.rd u₁.wr
  have R₂ : Src c τ₂ Q m := hQ₂.of_eq u₂.rd u₂.wr
  refine rel_seqR ?_ (Runs.of_wp (absMid_wp L F₁ hm R₁ q23₁ q24₁ u₁.gpr))
    (Runs.of_wp (absMid_wp L F₂ hm R₂ q23₂ q24₂ u₂.gpr)) fun ρ₁ ρ₂ ⟨P₁, r23₁, r24₁⟩ ⟨P₂, r23₂, r24₂⟩ => ?_
  · refine rel_ite (eval_zero u₁.gpr (by omega_arith)) (eval_zero u₂.gpr (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩
    · have h0 : m / 16 ≠ 0 := by simpa using hf
      exact chunks_rel L F₁ F₂ hsp₁ hm (by omega_arith) (R₁.take (by omega_arith)) (R₂.take (by omega_arith)) q23₁ q23₂ q24₁ q24₂
  · have G₁ := F₁.of_pk P₁.pk
    have G₂ := F₂.of_pk P₂.pk
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [P₁.pk.sp, P₂.pk.sp, hsp₁]
    refine rel_ite (eval_zero r24₁ (by omega_arith)) (eval_zero r24₂ (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩
    · have h0 : m % 16 ≠ 0 := by simpa using hf
      have hs₁ := R₁.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)
      have hs₂ := R₂.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)
      exact absTail_rel L G₁ G₂ hsp₂ (by omega_arith) (by omega_arith) (by rw [P₁.pk.rd, P₁.pk.wr]; exact hs₁.rd)
        (by rw [P₂.pk.rd, P₂.pk.wr]; exact hs₂.rd) (hd.sub_left (Offset.sub_base Q (by omega_arith))) r23₁ r23₂ r24₁ r24₂

/-- `lens`. -/
theorem lens_rel : RelCT isa (Eq2 σ₁ σ₂) lens TT := by
  unfold lens
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (lensBlk_wp E₁))
    (Runs.of_wp (lensBlk_wp E₂)) fun ρ₁ ρ₂ ⟨pk₁, _, r23₁, r24₁⟩ ⟨pk₂, _, r23₂, r24₂⟩ => ?_
  exact chunk_rel L (E₁.of_pk pk₁) (E₂.of_pk pk₂) (by rw [pk₁.sp, pk₂.sp, hsp]) (m := 16) (by decide) (by decide)
    (srcB L (E₁.of_pk pk₁).perm) (srcB L (E₂.of_pk pk₂).perm) r23₁ r23₂ r24₁ r24₂

/-- `polyval`. -/
theorem polyval_rel : RelCT isa (Eq2 σ₁ σ₂) polyval TT := by
  unfold polyval
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (movA_wp E₁))
    (Runs.of_wp (movA_wp E₂)) fun τ₁ τ₂ ⟨pk₁, m₁, a₁, l₁⟩ ⟨pk₂, m₂, a₂, l₂⟩ => ?_
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (absorb_rel L F₁ F₂ hsp₁ L.al_lt (srcA L F₁.perm) (srcA L F₂.perm) L.a_w a₁ a₂ l₁ l₂)
    (Runs.of_wp (absorb_wp L F₁ L.al_lt (srcA L F₁.perm) L.a_w a₁ l₁))
    (Runs.of_wp (absorb_wp L F₂ L.al_lt (srcA L F₂.perm) L.a_w a₂ l₂)) fun ρ₁ ρ₂ A₁ A₂ => ?_
  have G₁ := F₁.of_pk A₁.pk
  have G₂ := F₂.of_pk A₂.pk
  have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [A₁.pk.sp, A₂.pk.sp, hsp₁]
  refine rel_seqR (rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (movD_wp G₁))
    (Runs.of_wp (movD_wp G₂)) fun ω₁ ω₂ ⟨pk₃, _, d₁, n₁⟩ ⟨pk₄, _, d₂, n₂⟩ => ?_
  have H₁ := G₁.of_pk pk₃
  have H₂ := G₂.of_pk pk₄
  have hsp₃ : ω₁.sp = ω₂.sp := by rw [pk₃.sp, pk₄.sp, hsp₂]
  refine rel_seqR (absorb_rel L H₁ H₂ hsp₃ L.n_lt (srcD L H₁.perm) (srcD L H₂.perm) L.d_w d₁ d₂ n₁ n₂)
    (Runs.of_wp (absorb_wp L H₁ L.n_lt (srcD L H₁.perm) L.d_w d₁ n₁))
    (Runs.of_wp (absorb_wp L H₂ L.n_lt (srcD L H₂.perm) L.d_w d₂ n₂)) fun υ₁ υ₂ B₁ B₂ => ?_
  have I₁ := H₁.of_pk B₁.pk
  have I₂ := H₂.of_pk B₂.pk
  have hsp₄ : υ₁.sp = υ₂.sp := by rw [B₁.pk.sp, B₂.pk.sp, hsp₃]
  refine rel_seqR (lens_rel L I₁ I₂ hsp₄) (Runs.of_wp (lens_wp L I₁)) (Runs.of_wp (lens_wp L I₂))
    fun φ₁ φ₂ C₁ C₂ => ?_
  exact rel_env [] (I₁.of_pk C₁.pk) (I₂.of_pk C₂.pk) (by rw [C₁.pk.sp, C₂.pk.sp, hsp₄]) (by simp)
    ⟨_, by taint_decide⟩

end

end VG.Proof.AesGcmSiv.PPC64LE
