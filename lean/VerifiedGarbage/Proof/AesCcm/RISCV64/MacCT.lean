module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.CallArgs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.CallArgs
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Impl.AesCcm.RISCV64
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.AesCcm.RISCV64.Header
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Header
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp

/-!
# AES-CCM on RISCV64: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states in the same environment, leaks the same: the code between
calls by the taint analysis (`rel_env`), from the environment's registers
and those on which the two runs agree (the pointer and the length of the
string being absorbed, in `s5` and `s6`, which the correctness proofs pin),
and each call of `vg_cmac_aes_update` by its proof (`rel_upd`), from the
arguments `CallArgs.lean` gives it.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Impl.AesCbc.RISCV64 (mov)

/-- Code without calls that writes none of the environment's registers. -/
theorem Runs.env {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true) (hd : ∀ r ∈ keepRegs, r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s fun s' => Env c s' ∧ s'.sp = s.sp :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ => ⟨E.of_pk (PK.ofKeep k sp hd), sp⟩

/-! ## What the pieces set -/

/-- The pointer to and the length of the associated data, from their slots. -/
theorem aadLd_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .s5 .s1 aadO, .load .d .s6 .s1 alenO]) s fun s' =>
      s'.gpr .s5 = c.A ∧ s'.gpr .s6 = BitVec.ofNat 64 c.al ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 216) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 224) (by decide) (by rw [u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, S.aad], by rw [u₂.gpr, u₁.mem, S.alen], E.of_pk pk₂, pk₂.sp⟩

/-- The pointer to and the length of the data. -/
theorem dataArgs_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [mov .s5 .s9, mov .s6 .s10]) s fun s' =>
      s'.gpr .s5 = c.D ∧ s'.gpr .s6 = BitVec.ofNat 64 c.n ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, E.s9], by rw [u₂.gpr, u₁.other _ (by decide), E.s10],
    E.of_pk pk₂, pk₂.sp⟩

/-- The length's last 4 bits. -/
theorem mask15_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.logicImm .and .s8 .s6 15]) s fun s' =>
      s'.gpr .s8 = s.gpr .s6 &&& BitVec.ofInt 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.s5, .s6], s'.gpr r = s.gpr r := by
  refine wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := PK.ofUpd u₂
  refine ⟨u₂.gpr, E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide)]

/-! ## What every run of a piece keeps -/

theorem updBlock_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (updBlock y) s (Kept c s) := by
  unfold updBlock
  exact Runs.seq (Runs.of_wp (updArgs1_wp L E hy)) fun _ ⟨U, K⟩ => (upd_runs K.1 U).mono fun _ K' => K.trans K'

theorem b0_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (b0 y) s (Kept c s) := by
  unfold b0
  refine Runs.seq (Runs.kept E [.t1, .t2, .t3] (by decide +kernel)) fun _ K => ?_
  refine Runs.seq (Runs.kept K.1 [.t0, .t1, .t2] (by rcases hy with rfl | rfl <;> decide +kernel)
    (hn := by rcases hy with rfl | rfl <;> decide +kernel)) fun _ K' => ?_
  exact (updBlock_runs L K'.1 hy).mono fun _ K'' => K.trans (K'.trans K'')

/-! ## Two runs -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
  {y : Nat} (hy : y = 0 ∨ y = 96)
include L E₁ E₂ hsp hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (updArgs y ++ [.addi .a3 .s1 (bO : Int), .li .a4 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (Runs.of_wp (updArgs1_wp L E₁ hy))
    (Runs.of_wp (updArgs1_wp L E₂ hy)) fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `absTail y`, from two states that agree on the string and the length of
its tail. -/
theorem absTail_rel (hr : ∀ r ∈ [Reg.s5, .s6, .s8], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail y) TT := by
  unfold absTail
  exact RelCT.assoc (rel_seqR (rel_env [.s5, .s6, .s8] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.t0, .a0, .a1, .a2] (by decide +kernel))
    (Runs.env E₂ [.t0, .a0, .a1, .a2] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `absorbPad y`, for the `len` bytes at `P`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h18₁ : σ₁.gpr .s5 = P) (h18₂ : σ₂.gpr .s5 = P) (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 len)
    (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s5, .s6]))
      (.block (updArgs y ++ [mov .a3 .s5, .shift .srl .d .a4 .s6 4])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold absorbPad
  refine rel_seqR (rel_env [.s5, .s6] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂]) t)
    (Runs.of_wp (absArgs_wp L E₁ hy hP₁ h18₁ h19₁)) (Runs.of_wp (absArgs_wp L E₂ hy hP₂ h18₂ h19₂))
    fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => ?_
  refine rel_seqR (rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (upd_runs K₁.1 U₁) (upd_runs K₂.1 U₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  have q : ∀ r ∈ [Reg.s5, .s6], ρ₁.gpr r = ρ₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a₁.2.2 .s5 (by simp), a₂.2.2 .s5 (by simp), h18₁, h18₂]
    · rw [a₁.2.2 .s6 (by simp), a₂.2.2 .s6 (by simp), h19₁, h19₂]
  refine rel_seqR (rel_env [.s5, .s6] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) q ⟨_, by taint_decide⟩)
    (Runs.of_wp (mask15_wp G₁.1)) (Runs.of_wp (mask15_wp G₂.1)) fun κ₁ κ₂ ⟨s8₁, F₁, sp₁, k₁⟩ ⟨s8₂, F₂, sp₂, k₂⟩ => ?_
  have hsp' : κ₁.sp = κ₂.sp := by rw [sp₁, sp₂, a₁.2.1, a₂.2.1, hsp]
  have q21 : κ₁.gpr .s8 = κ₂.gpr .s8 := by rw [s8₁, s8₂, q .s6 (by simp)]
  refine rel_iteZ q21 (rel_env [] F₁ F₂ hsp' (by simp) ⟨_, by taint_decide⟩) ?_
  refine absTail_rel L F₁ F₂ hsp' hy fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [k₁ .s5 (by simp), k₂ .s5 (by simp), q .s5 (by simp)]
  · rw [k₁ .s6 (by simp), k₂ .s6 (by simp), q .s6 (by simp)]
  · exact q21

/-- `aadHead y`, from two states that agree on the associated data. -/
theorem aadHead_rel (hr : ∀ r ∈ [Reg.s5, .s6], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead y) TT := by
  unfold aadHead
  exact RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (rel_seqR
    (rel_env [.s5, .s6] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .s5, .s6, .s7, .s8] (by decide +kernel))
    (Runs.env E₂ [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .s5, .s6, .s7, .s8] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy))))

/-- The associated data, if there is any. -/
theorem aadPart_rel (h18₁ : σ₁.gpr .s5 = c.A) (h18₂ : σ₂.gpr .s5 = c.A)
    (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 c.al) (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .s6) (.block []) (.seq (aadHead y) (absorbPad y))) TT := by
  have ha := L.al_lt
  refine rel_ite (eval_z h19₁ ha) (eval_z h19₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := by simpa using hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seqR (aadHead_rel L E₁ E₂ hsp hy fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂])
    (Runs.of_wp (aadHead_wp L E₁ hy hA₁ h18₁ h19₁ (by omega)))
    (Runs.of_wp (aadHead_wp L E₂ hy hA₂ h18₂ h19₂ (by omega))) fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : Proof.AesCcm.headLen c.al ≤ c.al := by unfold Proof.AesCcm.headLen; omega
  exact absorbPad_rel L (E₁.of_pk A₁.abs.pk) (E₂.of_pk A₂.abs.pk) (by rw [A₁.abs.pk.sp, A₂.abs.pk.sp, hsp]) hy
    ((hA₁.drop hn1).of_eq A₁.abs.pk.rd A₁.abs.pk.wr) ((hA₂.drop hn1).of_eq A₂.abs.pk.rd A₂.abs.pk.wr)
    A₁.s5 A₂.s5 A₁.s6 A₂.s6

/-- `b0 y`, from two states that agree on the length of the associated data. -/
theorem b0_rel (hs6 : σ₁.gpr .s6 = σ₂.gpr .s6) : RelCT isa (Eq2 σ₁ σ₂) (b0 y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6])) (.seq flagsSeg (.block (b0Seg y))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold b0
  exact RelCT.assoc (rel_seqR (rel_env [.s6] E₁ E₂ hsp (by simpa using hs6) t)
    (Runs.env E₁ [.t0, .t1, .t2, .t3] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    (Runs.env E₂ [.t0, .t1, .t2, .t3] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `mac y`. -/
theorem mac_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) : RelCT isa (Eq2 σ₁ σ₂) (mac y) TT := by
  unfold mac
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (aadLd_wp L E₁ S₁))
    (Runs.of_wp (aadLd_wp L E₂ S₂)) fun τ₁ τ₂ ⟨x18₁, x19₁, F₁, sp₁⟩ ⟨x18₂, x19₂, F₂, sp₂⟩ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, hsp]
  refine rel_seqR (b0_rel L F₁ F₂ hsp₁ hy (by rw [x19₁, x19₂])) (b0_runs L F₁ hy) (b0_runs L F₂ hy)
    fun κ₁ κ₂ B₁ B₂ => ?_
  have hsp₂ : κ₁.sp = κ₂.sp := by rw [B₁.2.1, B₂.2.1, hsp₁]
  have y18₁ : κ₁.gpr .s5 = c.A := by rw [B₁.2.2 .s5 (by simp), x18₁]
  have y18₂ : κ₂.gpr .s5 = c.A := by rw [B₂.2.2 .s5 (by simp), x18₂]
  have y19₁ : κ₁.gpr .s6 = BitVec.ofNat 64 c.al := by rw [B₁.2.2 .s6 (by simp), x19₁]
  have y19₂ : κ₂.gpr .s6 = BitVec.ofNat 64 c.al := by rw [B₂.2.2 .s6 (by simp), x19₂]
  refine rel_seqR (aadPart_rel L B₁.1 B₂.1 hsp₂ hy y18₁ y18₂ y19₁ y19₂)
    (Runs.of_wp (aad_wp L B₁.1 hy y18₁ y19₁)) (Runs.of_wp (aad_wp L B₂.1 hy y18₂ y19₂)) fun ρ₁ ρ₂ P₁ P₂ => ?_
  have G₁ := B₁.1.of_pk P₁.pk
  have G₂ := B₂.1.of_pk P₂.pk
  have hsp₃ : ρ₁.sp = ρ₂.sp := by rw [P₁.pk.sp, P₂.pk.sp, hsp₂]
  refine rel_seqR (rel_env [] G₁ G₂ hsp₃ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (dataArgs_wp G₁))
    (Runs.of_wp (dataArgs_wp G₂)) fun ω₁ ω₂ ⟨z18₁, z19₁, H₁, sp₁'⟩ ⟨z18₂, z19₂, H₂, sp₂'⟩ => ?_
  exact absorbPad_rel L H₁ H₂ (by rw [sp₁', sp₂', hsp₃]) hy (L.bufD H₁.perm) (L.bufD H₂.perm) z18₁ z18₂ z19₁ z19₂

end

end VG.Proof.AesCcm.RISCV64
