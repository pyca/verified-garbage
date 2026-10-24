module

import VerifiedGarbage.Proof.AesSiv.PPC64LE.Rel
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.CtrLoop
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Mac
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.CtrLoop
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
meta import VerifiedGarbage.Proof.AesSiv.PPC64LE.Mac
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Env
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT

/-!
# AES-SIV on PPC64LE: CTR in two runs

Untrusted: everything here is checked by Lean. `ctrWhole`, a block of the
rest (`ctrBody`) and the whole of `ctr src`, run from two states in the same
environment, leak the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and the data pointer and
length left, `r19` and `r20`, which are public in both runs, and each call of
`vg_aes_ctr32` by its proof (`rel_ctr`). The counter `Q` is the IV's and
differs between the runs, but only its bytes in memory, never an address or
a branch. The loop of blocks relates two runs after the same number of
blocks, which the correctness proofs describe (`CInv`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li)
open VG.Proof.AesCcm.PPC64LE (wp_mv Runs Runs.of_wp rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesCtr.PPC64LE (CtrCall ctr_call)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_ite eval_zero eval_nonzero)
open VG.Spec.Aes (bytesAt)

/-- `ctrPre`: the arguments of `vg_aes_ctr32` for the keystream block. -/
theorem ctrPre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block ctrPre) s fun s' => PK s s' ∧ s'.gpr .r19 = s.gpr .r19 ∧ s'.gpr .r20 = s.gpr .r20 ∧
      CtrCall s' (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) (c.W + BitVec.ofNat 64 ksO)
        (c.W + BitVec.ofNat 64 scrO) c.R 1 := by
  unfold ctrPre
  simp only [List.append_assoc]
  refine zero16_wp E (d := ksO) (by decide) (by decide) fun s₁ pk₁ g₁ _ => ?_
  have E₁ := E.of_pk pk₁
  refine copy16_wp E₁ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₂ pk₂ g₂ _ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) (by decide)
    fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s₂ s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk (pk₁.trans (pk₂.trans pk₈))
  refine ⟨pk₁.trans (pk₂.trans pk₈),
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁],
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁], ?_⟩
  exact cargs L E₈ (E₈.perm.wC (by decide)) (by rw [L.wrapW (by decide)]; have := L.ww; simp only [ksO]; omega)
    (L.c_w' (by decide) (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
    (L.w_w (.inl (by decide)) (by decide) (by decide))
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, g₁, E.r15])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, g₁, E.r16])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, g₁, E.r14])
    (by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁, E.r14])
    (by simp (disch := decide) only [u₈.gpr])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, g₁, E.r14])

/-- What a call of `vg_aes_ctr32` keeps. -/
theorem ctrCall_keep {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Runs Impl.AesCtr.PPC64LE.ctrCall s fun t => PK s t ∧ t.gpr .r19 = s.gpr .r19 ∧ t.gpr .r20 = s.gpr .r20 :=
  Runs.of_wp (WP.mono (ctr_call h) fun _ h' =>
    ⟨PK.ofSaved h'.rd h'.wr h'.sp h'.saved, h'.saved _ (by decide), h'.saved _ (by decide)⟩)

/-- What a block of CTR leaves, from block `i`. -/
theorem ctrBody_runs {c : Cx} (L : Lay c) {s₀ s : State} {q : List Byte} {i : Nat} (E₀ : Env c s₀)
    (hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63) (I : CInv c s₀ q i s) (hi : 16 * i < c.n) :
    Runs ctrBody s (Stepped c s₀ q i s) :=
  Runs.of_wp (by unfold ctrBody; exact ctrHead_wp L I hi E₀ fun _ H => ctrTail_wp L I hi E₀ hlow64 H)

/-! ## Two runs -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `ctrWhole`: the whole blocks by one call. -/
theorem ctrWhole_rel : RelCT isa (Eq2 σ₁ σ₂) ctrWhole TT := by
  unfold ctrWhole
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (wholePre_wp L E₁))
    (Runs.of_wp (wholePre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, r19₁, r20₁, _, C₁⟩ ⟨pk₂, r19₂, r20₂, _, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a19₁, a20₁⟩ ⟨k₂, a19₂, a20₂⟩ => ?_
  exact rel_env [.r19, .r20] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a19₁, a19₂, r19₁, r19₂]) (agree_cons (by rw [a20₁, a20₂, r20₁, r20₂]) agree_nil))
    ⟨_, by taint_decide⟩

/-- A block of CTR, from two states that agree on the data pointer and the
length left. -/
theorem ctrBody_rel (h19 : σ₁.gpr .r19 = σ₂.gpr .r19) (h20 : σ₁.gpr .r20 = σ₂.gpr .r20) :
    RelCT isa (Eq2 σ₁ σ₂) ctrBody TT := by
  unfold ctrBody
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (ctrPre_wp L E₁))
    (Runs.of_wp (ctrPre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, r19₁, r20₁, C₁⟩ ⟨pk₂, r19₂, r20₂, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a19₁, a20₁⟩ ⟨k₂, a19₂, a20₂⟩ => ?_
  exact rel_env [.r19, .r20] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a19₁, a19₂, r19₁, r19₂, h19]) (agree_cons (by rw [a20₁, a20₂, r20₁, r20₂, h20]) agree_nil))
    ⟨_, by taint_decide⟩

/-- `ctr src`: CTR from the counter of the IV at `W + src`. -/
theorem ctr_rel {src : Nat} (hsrc : src + 16 ≤ cntO) (hsrc8 : src % 8 = 0) : RelCT isa (Eq2 σ₁ σ₂) (ctr src) TT := by
  have hn := L.n_lt
  have hk := wholeOf_le c.n
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [])) (.block (counter src)) h).isSome = true := by
    have : src = 0 ∨ src = 8 ∨ src = 16 ∨ src = 24 ∨ src = 32 ∨ src = 40 ∨ src = 48 := by
      simp only [cntO] at hsrc; omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The counter `Q`, in each run.
  have start : ∀ {σ : State}, Env c σ → Runs (.block (counter src)) σ fun τ => PK σ τ ∧ ∃ q : List Byte,
      q.length = 16 ∧ Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31 ∧ Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63 ∧
        CntAt τ.mem c.W q 0 := fun E =>
    Runs.of_wp (by
      rw [← List.append_nil (counter src)]
      exact counter_wp E hsrc hsrc8 fun _ pk _ hq =>
        WP.block_nil ⟨pk, _, length_counter _, counter_low _, counter_low64 _, cnt_init hq⟩)
  unfold ctr
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil t) (start E₁) (start E₂)
    fun τ₁ τ₂ ⟨pk₁, Q₁, hl₁, lo₁, hi₁, q₁⟩ ⟨pk₂, Q₂, hl₂, lo₂, hi₂, q₂⟩ => ?_
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (ctrWhole_rel L F₁ F₂ hspτ) (Runs.of_wp (ctrWhole_wp L F₁ hl₁ lo₁ hi₁ q₁))
    (Runs.of_wp (ctrWhole_wp L F₂ hl₂ lo₂ hi₂ q₂)) fun ρ₁ ρ₂ I₁ I₂ => ?_
  refine rel_ite (eval_zero I₁.r20 (by omega)) (eval_zero I₂.r20 (by omega)) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] (F₁.of_pk I₁.pk) (F₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hspτ]) agree_nil
      ⟨_, by taint_decide⟩
  have h0 : 16 * wholeOf c.n < c.n := by
    have : c.n - 16 * wholeOf c.n ≠ 0 := by simpa using hf
    omega
  refine (RelCT.loop (Q := TT) (fun m (a b : State) => ∃ i, m = c.n - 16 * i ∧ 16 * i < c.n ∧
      CInv c τ₁ Q₁ i a ∧ CInv c τ₂ Q₂ i b) (fun m => ?_) (c.n - 16 * wholeOf c.n)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨wholeOf c.n, rfl, h0, I₁, I₂⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨i, hm, hi, J₁, J₂⟩ => ?_
  refine (rel_post (ctrBody_rel L (F₁.of_pk J₁.pk) (F₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hspτ])
      (by rw [J₁.r19, J₂.r19]) (by rw [J₁.r20, J₂.r20]))
    (ctrBody_runs L F₁ hi₁ J₁ hi) (ctrBody_runs L F₂ hi₂ J₂ hi)).mono (fun _ _ h => h) fun a' b' ⟨S₁, S₂⟩ => ?_
  have ev₁ := eval_nonzero S₁.r20 (by omega)
  have ev₂ := eval_nonzero S₂.r20 (by omega)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
  rw [ev₁] at ht
  have hgt : 16 < c.n - 16 * i := by simp at ht; omega
  have mk : ∀ {τ u u' : State} {q : List Byte}, CInv c τ q i u → Stepped c τ q i u u' →
      CInv c τ q (i + 1) u' := fun J S =>
    ⟨J.pk.trans S.pk, S.r19, by rw [S.r20]; congr 1; omega, by omega, S.cnt, by rw [S.data]; congr 1; omega,
      S.frame⟩
  exact ⟨c.n - 16 * (i + 1), by omega, i + 1, rfl, by omega, mk J₁ S₁, mk J₂ S₂⟩

end

end VG.Proof.AesSiv.PPC64LE
