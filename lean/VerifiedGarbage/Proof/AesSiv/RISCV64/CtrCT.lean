module

import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
public import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Mac
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# AES-SIV on RISC-V: CTR in two runs

Untrusted: everything here is checked by Lean. `ctrWhole`, a block of the
rest (`ctrBody`) and the whole of `ctr src`, run from two states in the same
environment, leak the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and the data pointer and
length left, `s6` and `s7`, which are public in both runs, and each call of
`vg_aes_ctr32` by its proof (`rel_ctr`). The counter `Q` is the IV's and
differs between the runs, but only its bytes in memory, never an address or
a branch. The loop of blocks relates two runs after the same number of
blocks, which the correctness proofs describe (`CInv`). As on PPC64LE
(`Proof/AesSiv/PPC64LE/CtrCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR rel_of_eq2 rel_post)
open VG.Proof.AesCtr.RISCV64 (CtrCall ctr_call)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Spec.Aes (bytesAt)

/-- `ctrPre`: the arguments of `vg_aes_ctr32` for the keystream block. -/
theorem ctrPre_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block ctrPre) s fun s' => PK s s' ∧ s'.gpr .s6 = s.gpr .s6 ∧ s'.gpr .s7 = s.gpr .s7 ∧
      CtrCall s' (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) (c.W + BitVec.ofNat 64 ksO)
        (c.W + BitVec.ofNat 64 384) c.R 1 := by
  unfold ctrPre
  simp only [List.append_assoc]
  refine zero16_wp L E (d := ksO) (by decide) (by decide) fun s₁ pk₁ g₁ _ => ?_
  have E₁ := E.of_pk pk₁
  refine copy16_wp L E₁ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₂ pk₂ g₂ _ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (imm := 272) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ => wp_li (imm := 1) (by decide) fun s₈ u₈ =>
    WP.block_nil ?_
  have pk₈ : PK s₂ s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk (pk₁.trans (pk₂.trans pk₈))
  refine ⟨pk₁.trans (pk₂.trans pk₈),
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁],
    by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁], ?_⟩
  exact cargsW L E₈ (o := cbO) (by decide) (d := ksO) (by decide) (.inr (by decide))
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, g₁, E.s2])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, g₁, E.s3])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, g₁, E.s1])
    (by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1])
    (by simp (disch := decide) only [u₈.gpr])
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, g₁, E.s1]; rfl)

/-- What a call of `vg_aes_ctr32` keeps. -/
theorem ctrCall_keep {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Runs Impl.AesCtr.RISCV64.ctrCall s fun t => PK s t ∧ t.gpr .s6 = s.gpr .s6 ∧ t.gpr .s7 = s.gpr .s7 :=
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
    (Runs.of_wp (wholePre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, s6₁, s7₁, _, C₁⟩ ⟨pk₂, s6₂, s7₂, _, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a6₁, a7₁⟩ ⟨k₂, a6₂, a7₂⟩ => ?_
  exact rel_env [.s6, .s7] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a6₁, a6₂, s6₁, s6₂]) (agree_cons (by rw [a7₁, a7₂, s7₁, s7₂]) agree_nil))
    ⟨_, by taint_decide⟩

/-- A block of CTR, from two states that agree on the data pointer and the
length left. -/
theorem ctrBody_rel (h6 : σ₁.gpr .s6 = σ₂.gpr .s6) (h7 : σ₁.gpr .s7 = σ₂.gpr .s7) :
    RelCT isa (Eq2 σ₁ σ₂) ctrBody TT := by
  unfold ctrBody
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (ctrPre_wp L E₁))
    (Runs.of_wp (ctrPre_wp L E₂)) fun τ₁ τ₂ ⟨pk₁, s6₁, s7₁, C₁⟩ ⟨pk₂, s6₂, s7₂, C₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (rel_ctr C₁ C₂ hspτ) (ctrCall_keep C₁) (ctrCall_keep C₂)
    fun ρ₁ ρ₂ ⟨k₁, a6₁, a7₁⟩ ⟨k₂, a6₂, a7₂⟩ => ?_
  exact rel_env [.s6, .s7] (E₁.of_pk (pk₁.trans k₁)) (E₂.of_pk (pk₂.trans k₂)) (by rw [k₁.sp, k₂.sp, hspτ])
    (agree_cons (by rw [a6₁, a6₂, s6₁, s6₂, h6]) (agree_cons (by rw [a7₁, a7₂, s7₁, s7₂, h7]) agree_nil))
    ⟨_, by taint_decide⟩

/-- `ctr src`: CTR from the counter of the IV at `W + src`. -/
theorem ctr_rel {src : Nat} (hsrc : src + 16 ≤ cntO) (hsrc8 : src % 8 = 0) : RelCT isa (Eq2 σ₁ σ₂) (ctr src) TT := by
  have hn := L.n_lt
  have hk := wholeOf_le c.n
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [])) (.block (counter src)) h).isSome = true := by
    have : src = 0 ∨ src = 8 ∨ src = 16 ∨ src = 24 ∨ src = 32 ∨ src = 40 ∨ src = 48 := by
      simp only [cntO] at hsrc; omega_arith
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The counter `Q`, in each run.
  have start : ∀ {σ : State}, Env c σ → Runs (.block (counter src)) σ fun τ => PK σ τ ∧ ∃ q : List Byte,
      q.length = 16 ∧ Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31 ∧ Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63 ∧
        CntAt τ.mem c.W q 0 := fun E =>
    Runs.of_wp (by
      rw [← List.append_nil (counter src)]
      exact counter_wp L E hsrc hsrc8 fun _ pk _ hq =>
        WP.block_nil ⟨pk, _, length_counter _, counter_low _, counter_low64 _, cnt_init hq⟩)
  unfold ctr
  refine rel_seqR (rel_env [] E₁ E₂ hsp agree_nil t) (start E₁) (start E₂)
    fun τ₁ τ₂ ⟨pk₁, Q₁, hl₁, lo₁, hi₁, q₁⟩ ⟨pk₂, Q₂, hl₂, lo₂, hi₂, q₂⟩ => ?_
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hspτ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  refine rel_seqR (ctrWhole_rel L F₁ F₂ hspτ) (Runs.of_wp (ctrWhole_wp L F₁ hl₁ lo₁ hi₁ q₁))
    (Runs.of_wp (ctrWhole_wp L F₂ hl₂ lo₂ hi₂ q₂)) fun ρ₁ ρ₂ I₁ I₂ => ?_
  refine rel_ite (evalZ I₁.s7 (by omega_arith)) (evalZ I₂.s7 (by omega_arith)) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] (F₁.of_pk I₁.pk) (F₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hspτ]) agree_nil
      ⟨_, by taint_decide⟩
  have h0 : 16 * wholeOf c.n < c.n := by
    have : c.n - 16 * wholeOf c.n ≠ 0 := by simpa using hf
    omega_arith
  refine (RelCT.loop (Q := TT) (fun m (a b : State) => ∃ i, m = c.n - 16 * i ∧ 16 * i < c.n ∧
      CInv c τ₁ Q₁ i a ∧ CInv c τ₂ Q₂ i b) (fun m => ?_) (c.n - 16 * wholeOf c.n)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨wholeOf c.n, rfl, h0, I₁, I₂⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨i, hm, hi, J₁, J₂⟩ => ?_
  refine (rel_post (ctrBody_rel L (F₁.of_pk J₁.pk) (F₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hspτ])
      (by rw [J₁.s6, J₂.s6]) (by rw [J₁.s7, J₂.s7]))
    (ctrBody_runs L F₁ hi₁ J₁ hi) (ctrBody_runs L F₂ hi₂ J₂ hi)).mono (fun _ _ h => h) fun a' b' ⟨S₁, S₂⟩ => ?_
  have ev₁ := evalNZ S₁.s7 (by omega_arith)
  have ev₂ := evalNZ S₂.s7 (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
  rw [ev₁] at ht
  have hgt : 16 < c.n - 16 * i := by simp at ht; omega_arith
  have mk : ∀ {τ u u' : State} {q : List Byte}, CInv c τ q i u → Stepped c τ q i u u' →
      CInv c τ q (i + 1) u' := fun J S =>
    ⟨J.pk.trans S.pk, S.s6, by rw [S.s7]; congr 1; omega_arith, by omega_arith, S.cnt,
      by rw [S.data]; congr 1; omega_arith, S.frame⟩
  exact ⟨c.n - 16 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, mk J₁ S₁, mk J₂ S₂⟩

end

end VG.Proof.AesSiv.RISCV64
