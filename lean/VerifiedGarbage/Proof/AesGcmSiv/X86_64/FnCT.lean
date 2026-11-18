module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Entry
meta import VerifiedGarbage.Proof.Framework.X86_64.Narrow
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Fn
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Derive
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Polyval
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `AesGcmSiv.X86_64.PolyvalCT`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86-64: the keys and POLYVAL are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`), from a slot; the code around the calls
passes the taint analysis, and each call has the same arguments in both runs.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl KeyCall key_rel key_call)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- Where a run of `derive` starts: its state and nonce. -/
abbrev DStart (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (σ : State) : Prop :=
  One K W SP R N A D al n σ ∧ Buf K W SP σ N 12

theorem slots_derR {K W SP : Addr} (L : Lay K W SP) : ∀ q ∈ derR W SP, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint q := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- A run of `deriveBlocks` after block `i`, from some start. -/
def DB (K W SP : Addr) (R : Nat) (N A D : Addr) (al n i : Nat) (t : State) : Prop :=
  ∃ σ, DStart K W SP R N A D al n σ ∧ BInv K W SP σ N (R / 2 - 1) i t

theorem DB.one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n i : Nat} {t : State}
    (h : DB K W SP R N A D al n i t) : One K W SP R N A D al n t :=
  let ⟨_, ⟨O, _⟩, I⟩ := h
  ⟨I.env, O.sl.of_frame I.frame (slots_derR L), I.wr.trans O.wr⟩

theorem DB.agree {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n i : Nat} {t₁ t₂ : State}
    (h₁ : DB K W SP R N A D al n i t₁) (h₂ : DB K W SP R N A D al n i t₂) :
    Both K W SP R N A D al n [.rbx, .rbp, .rdi] t₁ t₂ := by
  refine ⟨h₁.one L, h₂.one L, fun r hr => ?_⟩
  obtain ⟨_, _, I₁⟩ := h₁
  obtain ⟨_, _, I₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [I₁.rbx, I₂.rbx]
  · rw [I₁.rbp, I₂.rbp]
  · rw [I₁.rdi, I₂.rdi]

theorem dbInit_check : ∃ hc, (taint.check (sivT []) (.block (([.mov32 .rbx (imm 0)] : List Instr) ++
    ptr .rdi .r15 revO ++ ([.mov .rbp (.mem (at_ .r15 roundsO)), .shift .shr .rbp 1, .alu .sub .rbp (imm 1)] :
      List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dbStep_check : ∃ hc, (taint.check (sivT [.rbx, .rbp, .rdi]) (.block blkBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem daArgs_check : ∃ hc, (taint.check (sivT [.rbp]) (.block deriveArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dkInit_check : ∃ hc, (taint.check (sivT [.rbp])
    (.block (ptr .rsi .r15 revO ++ ptr .rdi .r15 akO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dkStep_check : ∃ hc, (taint.check (sivT [.rsi, .rdi, .rcx]) (.block keepBody) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dbStep_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) {i : Nat} (hi : i < R / 2 - 1) {t : State}
    (h : DB K W SP R N A D al n i t) :
    WP isa (.block blkBody) t fun t' =>
      DB K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)) :=
  let ⟨σ, St, I⟩ := h
  WP.mono (blkStep_ok L St.1.sl St.2 hDW (by omega_arith) hi I) fun _ ⟨I', z⟩ => ⟨⟨σ, St, I'⟩, z⟩

/-- `deriveBlocks`, in two runs with the same public arguments. -/
theorem blocks_rel {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → DStart K W SP R N A D al n t₁ ∧ DStart K W SP R N A D al n t₂) :
    RelCT isa P deriveBlocks fun t₁ t₂ =>
      DB K W SP R N A D al n (R / 2 - 1) t₁ ∧ DB K W SP R N A D al n (R / 2 - 1) t₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun _ h => nomatch h⟩)
    dbInit_check).wp (F₁ := DB K W SP R N A D al n 0) (F₂ := DB K W SP R N A D al n 0)
    fun t₁ t₂ h => ⟨WP.mono (derInit_ok (hP _ _ h).1.1.env hR (hP _ _ h).1.1.sl) fun _ I => ⟨t₁, (hP _ _ h).1, I⟩,
      WP.mono (derInit_ok (hP _ _ h).2.1.env hR (hP _ _ h).2.1.sl) fun _ I => ⟨t₂, (hP _ _ h).2, I⟩⟩
  refine RelCT.seq r₁ ?_
  refine (RelCT.loop (fun m t₁ t₂ => ∃ i, m = (R / 2 - 1) - i ∧ i < R / 2 - 1 ∧ DB K W SP R N A D al n i t₁ ∧
      DB K W SP R N A D al n i t₂) (fun m => ?_) ((R / 2 - 1) - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, by omega_arith, h.2.1, h.2.2⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hi : i < R / 2 - 1
  · by_cases hm : m = (R / 2 - 1) - i
    · subst hm
      have r := (rel_taintC [.rbx, .rbp, .rdi] (P := fun t₁ t₂ => DB K W SP R N A D al n i t₁ ∧
          DB K W SP R N A D al n i t₂) hDW hn (fun t₁ t₂ h => DB.agree L h.1 h.2) dbStep_check).wp
        (F₁ := fun (t' : State) => DB K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
        (F₂ := fun (t' : State) => DB K W SP R N A D al n (i + 1) t' ∧ t'.zf = some (decide (i + 1 = R / 2 - 1)))
        fun t₁ t₂ h => ⟨dbStep_wp L hR hDW hi h.1, dbStep_wp L hR hDW hi h.2⟩
      refine r.mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨_, ⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : i + 1 = R / 2 - 1 := by simpa using hc
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : i + 1 ≠ R / 2 - 1 := by simpa using hc
        exact ⟨(R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hi h.2.1

/-- The call's arguments, in a run of `derive`. -/
def DA (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop :=
  Proof.AesOcb.X86_64.BCall t K (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1768) R (R / 2 - 1) ∧
    t.gpr .rsp = SP ∧ One K W SP R N A D al n t ∧ t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1)

/-- A run of `derive` after its call. -/
def DC (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop :=
  One K W SP R N A D al n t ∧ t.gpr .rbp = BitVec.ofNat 64 (R / 2 - 1)

theorem daArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (h : DB K W SP R N A D al n (R / 2 - 1) t) :
    WP isa (.block deriveArgs) t (DA K W SP R N A D al n) := by
  have O := h.one L
  obtain ⟨_, _, B⟩ := h
  obtain ⟨t₂, run₂, rdi, rsi, rdx, rcx, r8, sv₂, m₂, rd₂, wr₂⟩ := deriveArgs_ok O.env O.sl B.rbp
  have E₂ : Env K W SP t₂ := O.env.of_saved sv₂ rd₂ wr₂
  exact WP.of_runBlock ⟨t₂, run₂, bargsK L E₂ hR (by omega_arith) rdi rsi rdx rcx r8, E₂.rsp,
    ⟨E₂, by rw [m₂]; exact O.sl, wr₂.trans O.wr⟩, by rw [sv₂ _ (by decide), B.rbp]⟩

theorem dCall_wp (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} {t : State} (h : DA K W SP R N A D al n t) :
    WP isa (.call eb.enc.name eb.enc.code) t (DC K W SP R N A D al n) := by
  obtain ⟨bc, hsp, O, bp⟩ := h
  have hc : R / 2 - 1 ≤ 6 := by omega_arith
  refine WP.mono (Proof.AesOcb.X86_64.blk_call eb.encOk eb.encNosp eb.encDepth bc) fun t₃ P => ?_
  have fP := P.frame
  rw [hsp] at fP
  refine ⟨⟨O.env.of_saved P.saved P.rd P.wr, O.sl.of_frame fP (fun q hq => ?_), P.wr.trans O.wr⟩,
    by rw [P.saved _ (by decide), bp]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inl (by omega_arith)) (by decide) (by omega_arith)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- A run of `deriveKeep` after `j` halves. -/
structure DK (K W SP : Addr) (R : Nat) (N A D : Addr) (al n j : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  rsi : t.gpr .rsi = W + BitVec.ofNat 64 (488 + 16 * j)
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (16 + 8 * j)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (R / 2 - 1 - j)

theorem DK.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n j : Nat} {t₁ t₂ : State}
    (h₁ : DK K W SP R N A D al n j t₁) (h₂ : DK K W SP R N A D al n j t₂) :
    Both K W SP R N A D al n [.rsi, .rdi, .rcx] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.rsi, h₂.rsi]
    · rw [h₁.rdi, h₂.rdi]
    · rw [h₁.rcx, h₂.rcx]⟩

theorem dkInit_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : DC K W SP R N A D al n t) :
    WP isa (.block (ptr .rsi .r15 revO ++ ptr .rdi .r15 akO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) t
      (DK K W SP R N A D al n 0) := by
  obtain ⟨O, bp⟩ := h
  obtain ⟨t₄, run₄, si₄, di₄, cx₄, g₄, m₄, rd₄, wr₄⟩ := keepInit_run O.env bp
  exact WP.of_runBlock ⟨t₄, run₄, ⟨⟨O.env.keep g₄ rd₄ wr₄, by rw [m₄]; exact O.sl, wr₄.trans O.wr⟩,
    by rw [si₄], by rw [di₄], by rw [cx₄, Nat.sub_zero]⟩⟩

theorem dkStep_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {j : Nat} (hj : j + 2 ≤ R / 2 - 1) {t : State} (h : DK K W SP R N A D al n j t) :
    WP isa (.block keepBody) t fun t' =>
      DK K W SP R N A D al n (j + 2) t' ∧ t'.zf = some (decide (R / 2 - 1 - j = 2)) := by
  have O := h.one
  obtain ⟨t', run', hm', si', di', cx', zf', hg', hrd', hwr'⟩ :=
    keepStep_run L (by omega_arith) hj O.env h.rsi h.rdi h.rcx
  have fr : Frame [⟨W + BitVec.ofNat 64 (16 + 8 * j), 16⟩] t.mem t'.mem := by
    rw [hm', h.rdi]; exact Proof.Cmac.frame_store2 _ _ _
  exact WP.of_runBlock ⟨t', run', ⟨⟨O.env.keep hg' hrd' hwr', O.sl.of_frame fr (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by omega_arith)) (by decide) (by omega_arith)),
    hwr'.trans O.wr⟩, si', di', cx'⟩, zf'⟩

/-- `deriveKeep`, in two runs after the call. -/
theorem keep_rel {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → DC K W SP R N A D al n t₁ ∧ DC K W SP R N A D al n t₂) :
    RelCT isa P deriveKeep fun t₁ t₂ => One K W SP R N A D al n t₁ ∧ One K W SP R N A D al n t₂ := by
  have r₁ := (rel_taintC [.rbp] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.1, (hP _ _ h).2.1, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hP _ _ h).1.2, (hP _ _ h).2.2]⟩)
    dkInit_check).wp (F₁ := DK K W SP R N A D al n 0) (F₂ := DK K W SP R N A D al n 0)
    fun t₁ t₂ h => ⟨dkInit_wp (hP _ _ h).1, dkInit_wp (hP _ _ h).2⟩
  refine RelCT.seq r₁ ?_
  have hev : (R / 2 - 1) % 2 = 0 := by rcases hR with h | h <;> subst h <;> decide
  refine (RelCT.loop (fun m t₁ t₂ => ∃ j, m = (R / 2 - 1) - j ∧ (j + 2 ≤ R / 2 - 1 ∧ j % 2 = 0) ∧
      DK K W SP R N A D al n j t₁ ∧ DK K W SP R N A D al n j t₂) (fun m => ?_) ((R / 2 - 1) - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, ⟨by omega_arith, rfl⟩, h.2.1, h.2.2⟩) fun _ _ h => h
  refine RelCT.exists_ fun j => ?_
  by_cases hj : j + 2 ≤ R / 2 - 1 ∧ j % 2 = 0
  · by_cases hm : m = (R / 2 - 1) - j
    · subst hm
      have r := (rel_taintC [.rsi, .rdi, .rcx] (P := fun t₁ t₂ => DK K W SP R N A D al n j t₁ ∧
          DK K W SP R N A D al n j t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) dkStep_check).wp
        (F₁ := fun (t' : State) => DK K W SP R N A D al n (j + 2) t' ∧ t'.zf = some (decide (R / 2 - 1 - j = 2)))
        (F₂ := fun (t' : State) => DK K W SP R N A D al n (j + 2) t' ∧ t'.zf = some (decide (R / 2 - 1 - j = 2)))
        fun t₁ t₂ h => ⟨dkStep_wp L hR hj.1 h.1, dkStep_wp L hR hj.1 h.2⟩
      refine r.mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨_, ⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun _ => ⟨I₁.one, I₂.one⟩, fun hc => ?_⟩
      rw [eval_ne z₁] at hc
      have he : R / 2 - 1 - j ≠ 2 := by simpa using hc
      exact ⟨(R / 2 - 1) - (j + 2), by omega_arith, j + 2, rfl, ⟨by omega_arith, by omega_arith⟩, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hj h.2.1

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → DStart K W SP R N A D al n t₁ ∧ DStart K W SP R N A D al n t₂) :
    RelCT isa P (derive ⟨eb.enc.name, eb.enc.code⟩) fun t₁ t₂ =>
      One K W SP R N A D al n t₁ ∧ One K W SP R N A D al n t₂ := by
  refine RelCT.seq (blocks_rel L hR hDW hn hP) ?_
  have r₂ := (rel_taintC [.rbp] (P := fun t₁ t₂ => DB K W SP R N A D al n (R / 2 - 1) t₁ ∧
      DB K W SP R N A D al n (R / 2 - 1) t₂) hDW hn (fun t₁ t₂ h => ⟨h.1.one L, h.2.one L, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, _, I₁⟩ := h.1
      obtain ⟨_, _, I₂⟩ := h.2
      rw [I₁.rbp, I₂.rbp]⟩) daArgs_check).wp
    (F₁ := DA K W SP R N A D al n) (F₂ := DA K W SP R N A D al n)
    fun t₁ t₂ h => ⟨daArgs_wp L hR h.1, daArgs_wp L hR h.2⟩
  have r₃ := (Proof.AesOcb.X86_64.blk_rel eb.encOk eb.encCt (name := eb.enc.name)
    (P := fun t₁ t₂ => True ∧ DA K W SP R N A D al n t₁ ∧ DA K W SP R N A D al n t₂)
    fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := DC K W SP R N A D al n) (F₂ := DC K W SP R N A D al n)
    fun t₁ t₂ h => ⟨dCall_wp eb L hR h.2.1, dCall_wp eb L hR h.2.2⟩
  exact RelCT.seq r₂ (RelCT.seq r₃ (keep_rel L hR hDW hn fun _ _ h => ⟨h.2.1, h.2.2⟩))

theorem expArgs_check : ∃ hc, (taint.check (sivT []) (.block (ptr .rdi .r15 ekO ++
    ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
      .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hkey_check : ∃ hc, (taint.check (sivT []) (.block hkey) hc).isSome = true := ⟨_, by taint_decide⟩

theorem expArgs_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr} {al n : Nat}
    {t : State} (O : One K W SP R N A D al n t) :
    WP isa (.block (ptr .rdi .r15 ekO ++ ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6),
      .alu .add .rsi (.reg .rsi), .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++
      ptr .rcx .r15 scrO)) t fun t₁ =>
      KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768)
        (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP := by
  obtain ⟨t₁, run₁, -, rdi, rsi, rdx, rcx, hg₁, hrd₁, hwr₁⟩ := expArgs_ok hR O.env O.sl
  have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
  have hl : Spec.GcmSiv.keyLen R = 16 ∨ Spec.GcmSiv.keyLen R = 32 := by unfold Spec.GcmSiv.keyLen; omega_arith
  exact WP.of_runBlock ⟨t₁, run₁, kargs L E₁ hl rdi rsi rdx rcx, E₁.rsp⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel (v : GcmImpl) (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (One K W SP R N A D al n t₁ ∧ Buf K W SP t₁ N 12) ∧
      (One K W SP R N A D al n t₂ ∧ Buf K W SP t₂ N 12)) :
    RelCT isa P (keys v.callees ⟨eb.enc.name, eb.enc.code⟩) fun _ _ => True := by
  refine RelCT.seq (derive_rel eb L hR hDW hn hP) ?_
  have one_exp : ∀ {t : State}, One K W SP R N A D al n t → WP isa (.seq (.block (ptr .rdi .r15 ekO ++
      ([.mov .rsi (.mem (at_ .r15 roundsO)), .alu .sub .rsi (imm 6), .alu .add .rsi (.reg .rsi),
        .alu .add .rsi (.reg .rsi)] : List Instr) ++ ptr .rdx .r15 skO ++ ptr .rcx .r15 scrO))
      (.call v.key.fn.name v.key.fn.code)) t (One K W SP R N A D al n) :=
    fun O => WP.mono (expand_ok v L hR O.env O.sl) fun t' X => ⟨X.env, O.sl.of_frame X.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm), X.wr.trans O.wr⟩
  have r₁ := (rel_taintC [] (P := fun t₁ t₂ => One K W SP R N A D al n t₁ ∧
      One K W SP R N A D al n t₂) hDW hn (fun t₁ t₂ h => ⟨h.1, h.2, fun _ h => nomatch h⟩)
    expArgs_check).wp
    (F₁ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨expArgs_wp L hR h.1, expArgs_wp L hR h.2⟩
  have r₂ := (RelCT.seq r₁ (key_rel v.key fun t₁ t₂ h =>
    ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)).wp
    (F₁ := One K W SP R N A D al n) (F₂ := One K W SP R N A D al n)
    fun t₁ t₂ h => ⟨one_exp h.1, one_exp h.2⟩
  exact RelCT.seq r₂ (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨h.2.1, h.2.2, fun _ h => nomatch h⟩) hkey_check)

/-- `keysS`, in two runs with the same public arguments. -/
theorem keysS_rel (eb : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → (One K W SP R N A D al n t₁ ∧ Buf K W SP t₁ N 12) ∧
      (One K W SP R N A D al n t₂ ∧ Buf K W SP t₂ N 12)) :
    RelCT isa P (keysS ⟨eb.enc.name, eb.enc.code⟩) fun _ _ => True :=
  RelCT.seq (derive_rel eb L hR hDW hn hP)
    (rel_taintC [] hDW hn (fun _ _ h => ⟨h.1, h.2, fun _ h => nomatch h⟩) hkey_check)

/-- `expand`, in two runs with the same public arguments. -/
theorem expand_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → One K W SP R N A D al n t₁ ∧ One K W SP R N A D al n t₂) :
    RelCT isa P (expand v.callees) fun _ _ => True := by
  have r₁ := (rel_taintC [] (P := fun t₁ t₂ => One K W SP R N A D al n t₁ ∧
      One K W SP R N A D al n t₂) hDW hn (fun t₁ t₂ h => ⟨h.1, h.2, fun _ h => nomatch h⟩)
    expArgs_check).wp
    (F₁ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => KeyCall t₁ (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248)
      (W + BitVec.ofNat 64 1768) (Spec.GcmSiv.keyLen R) ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨expArgs_wp L hR h.1, expArgs_wp L hR h.2⟩
  exact (RelCT.seq r₁ (key_rel v.key fun t₁ t₂ h =>
    ⟨_, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)).mono hP fun _ _ _ => trivial

end VG.Proof.AesGcmSiv.X86_64

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. Both runs absorb the same
chunks of blocks: their number depends only on the lengths, which are
public; the code around each call of `vg_ghash` passes the taint analysis,
and each call has the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl GhCall gh_rel gh_call toNat_ofNat_of_lt)

/-- `(a; (b; c)); d`, related as `a; (b; (c; d))`. -/
theorem rel_assoc3 {P Q : State → State → Prop} {a b c d : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b c)) d) Q) : RelCT isa P (.seq a (.seq b (.seq c d))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `(a; (b; (c; (d; e)))); g`, related as `a; (b; (c; (d; (e; g))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e g : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e g))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
  | seq d₁ e₁ => cases e₁ with | seq e₁' g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
  | seq d₂ e₂ => cases e₂ with | seq e₂' g₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ e₁')))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ e₂')))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-! ## The chunks -/

/-- A run of the chunks of `b` blocks at `Q`, after `d` of them, with
`nr` bytes left after them. -/
structure AInv (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d : Nat) (t : State) :
    Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t Q (16 * b)
  res : Buf K W SP t (Q + BitVec.ofNat 64 (16 * b)) nr
  r12 : t.gpr .r12 = Q + BitVec.ofNat 64 (16 * d)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (b - d)
  rbp : t.gpr .rbp = BitVec.ofNat 64 nr

theorem AInv.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} {t₁ t₂ : State}
    (h₁ : AInv K W SP R N A D al n Q b nr d t₁) (h₂ : AInv K W SP R N A D al n Q b nr d t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp] t₁ t₂ :=
  ⟨h₁.one, h₂.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r12, h₂.r12]
    · rw [h₁.rbx, h₂.rbx]
    · rw [h₁.rbp, h₂.rbp]⟩

/-- A chunk after its call, or up to it: the run, `k`, and the call's arguments. -/
structure AMid (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (b nr d k : Nat) (t : State) :
    Prop where
  inv : AInv K W SP R N A D al n Q b nr d t
  r14 : t.gpr .r14 = BitVec.ofNat 64 k

theorem AMid.agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d k : Nat} {t₁ t₂ : State}
    (h₁ : AMid K W SP R N A D al n Q b nr d k t₁) (h₂ : AMid K W SP R N A D al n Q b nr d k t₂) :
    Both K W SP R N A D al n [.r12, .rbx, .rbp, .r14] t₁ t₂ :=
  ⟨h₁.inv.one, h₂.inv.one, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.inv.r12, h₂.inv.r12]
    · rw [h₁.inv.rbx, h₂.inv.rbx]
    · rw [h₁.inv.rbp, h₂.inv.rbp]
    · rw [h₁.r14, h₂.r14]⟩

theorem chunkPre_wp (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat}
    (hd : d < b) {t : State} (I : AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq (revSel wide) (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) t
      fun t₅ => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅ := by
  have hQ : Buf K W SP t (Q + BitVec.ofNat 64 (16 * d)) (16 * (b - d)) := I.buf.slice (by omega_arith)
  refine WP.mono (chunkPre_ok wide L I.one.env (by omega_arith) hQ I.r12 I.rbx) fun t₅ Pr => ⟨Pr.call, Pr.env.rsp, ?_, Pr.r14⟩
  refine ⟨⟨Pr.env, I.one.sl.of_frame Pr.frame (fun q hq => ?_), Pr.wr.trans I.one.wr⟩, I.buf.of_eq Pr.rd Pr.wr,
    I.res.of_eq Pr.rd Pr.wr, by rw [Pr.regs _ (by simp), I.r12], by rw [Pr.regs _ (by simp), I.rbx], by rw [Pr.regs _ (by simp), I.rbp]⟩
  simp only [List.mem_singleton] at hq; subst hq
  exact L.w_w (.inl (by decide)) (by decide) (by omega_arith)

theorem chunkCalled_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {b nr d k : Nat} {t : State} (h : GhCall t (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
      (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) k ∧ t.gpr .rsp = SP ∧
      AMid K W SP R N A D al n Q b nr d k t) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) t (AMid K W SP R N A D al n Q b nr d k) := by
  obtain ⟨gc, hsp, M⟩ := h
  refine WP.mono (gh_call v.gh gc) fun t₆ P => ?_
  have fc := P.frame
  rw [hsp] at fc
  refine ⟨⟨⟨M.inv.one.env.of_saved P.saved P.rd P.wr, M.inv.one.sl.of_frame fc (fun q hq => ?_),
    P.wr.trans M.inv.one.wr⟩, M.inv.buf.of_eq P.rd P.wr, M.inv.res.of_eq P.rd P.wr, by rw [P.saved _ (by decide), M.inv.r12],
    by rw [P.saved _ (by decide), M.inv.rbx], by rw [P.saved _ (by decide), M.inv.rbp]⟩,
    by rw [P.saved _ (by decide), M.r14]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

/-- The end of a chunk: the pointer and the count past it. -/
theorem chunkEnd_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hd : d < b)
    {t : State} (M : AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t) :
    WP isa (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)]) t
      fun t' => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
        t'.zf = some (decide (b - (d + min (b - d) 64) = 0)) := by
  have hbl : b < 2 ^ 60 := by have := M.inv.buf.lt; omega_arith
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨M.inv.one.env.keep (fun r hr => ?_) rfl rfl, M.inv.one.sl, M.inv.one.wr⟩, M.inv.buf.of_eq rfl rfl,
      M.inv.res.of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.r12, M.r14,
        Proof.AesGcm.X86_64.times16_val, add_ofNat_assoc, Nat.mul_add]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx, M.r14]
      rw [Proof.AesGcm.X86_64.ofNat_sub (by omega_arith) (by omega_arith), Nat.sub_sub]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbp]
  · simp only [zf_setReg, zf_arithFlags, gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, M.inv.rbx,
      M.r14, Proof.AesGcm.X86_64.sub_beq (show b - d < 2 ^ 64 by omega_arith) (show min (b - d) 64 < 2 ^ 64 by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

theorem chunkPre_check (wide : Bool) : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.seq (.block [.mov32 .r14 (imm 64), .alu .cmp .rbx (.reg .r14)])
      (.seq (.ite .b (.block [.mov .r14 (.reg .rbx)]) (.block []))
      (.seq (.block (([.mov .rsi (.reg .r12)] : List Instr) ++ ptr .rdi .r15 revO))
      (.seq (revSel wide) (.block (ghArgs ++ ptr .rdx .r15 revO ++ ([.mov .rcx (.reg .r14)] : List Instr))))))) hc).isSome =
    true := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp, .r14])
    (.block [.mov .rax (.reg .r14), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .r12 (.reg .rax), .alu .sub .rbx (.reg .r14)])
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs after the same blocks. -/
theorem chunk_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr d : Nat} (hd : d < b) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr d t₁ ∧ AInv K W SP R N A D al n Q b nr d t₂)
      (absorbChunk v.callees wide)
      fun t₁ t₂ => (AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₁ ∧
          t₁.zf = some (decide (b - (d + min (b - d) 64) = 0))) ∧
        (AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t₂ ∧
          t₂.zf = some (decide (b - (d + min (b - d) 64) = 0))) := by
  refine rel_assoc5 ?_
  have r₁ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ => AInv K W SP R N A D al n Q b nr d t₁ ∧
      AInv K W SP R N A D al n Q b nr d t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2) (chunkPre_check wide)).wp
    (F₁ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    (F₂ := fun (t₅ : State) => GhCall t₅ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₅.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₅)
    fun t₁ t₂ h => ⟨chunkPre_wp wide L hd h.1, chunkPre_wp wide L hd h.2⟩
  have r₂ := (gh_rel v.gh (P := fun t₁ t₂ => True ∧ (GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
        (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₁.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁) ∧
      (GhCall t₂ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (min (b - d) 64) ∧ t₂.gpr .rsp = SP ∧
        AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂))
    fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    (F₂ := AMid K W SP R N A D al n Q b nr d (min (b - d) 64))
    fun t₁ t₂ h => ⟨chunkCalled_wp v L h.2.1, chunkCalled_wp v L h.2.2⟩
  have r₃ := (rel_taintC [.r12, .rbx, .rbp, .r14] (P := fun t₁ t₂ => True ∧
      AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₁ ∧ AMid K W SP R N A D al n Q b nr d (min (b - d) 64) t₂)
      hDW hn (fun t₁ t₂ h => h.2.1.agree h.2.2) chunkEnd_check).wp
    (F₁ := fun (t' : State) => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    (F₂ := fun (t' : State) => AInv K W SP R N A D al n Q b nr (d + min (b - d) 64) t' ∧
      t'.zf = some (decide (b - (d + min (b - d) 64) = 0)))
    fun t₁ t₂ h => ⟨chunkEnd_wp hd h.2.1, chunkEnd_wp hd h.2.2⟩
  exact (RelCT.seq r₁ (RelCT.seq r₂ r₃)).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

/-- The chunks, in two runs. -/
theorem chunks_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hb : 1 ≤ b) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr 0 t₁ ∧ AInv K W SP R N A D al n Q b nr 0 t₂)
      (.loop (absorbChunk v.callees wide) .ne)
      fun t₁ t₂ => AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂ := by
  refine (RelCT.loop (fun m t₁ t₂ => ∃ d, m = b - d ∧ d < b ∧ AInv K W SP R N A D al n Q b nr d t₁ ∧
      AInv K W SP R N A D al n Q b nr d t₂) (fun m => ?_) (b - 0)).mono
    (fun t₁ t₂ h => ⟨0, rfl, hb, h⟩) fun _ _ h => h
  refine RelCT.exists_ fun d => ?_
  by_cases hd : d < b
  · by_cases hm : m = b - d
    · subst hm
      refine (chunk_rel v wide L hDW hn hd).mono (fun t₁ t₂ h => ⟨h.2.2.1, h.2.2.2⟩)
        fun t₁ t₂ ⟨⟨I₁, z₁⟩, ⟨I₂, z₂⟩⟩ => ⟨by rw [eval_ne z₁, eval_ne z₂], fun hc => ?_, fun hc => ?_⟩
      · rw [eval_ne z₁] at hc
        have he : d + min (b - d) 64 = b := by simp at hc; omega_arith
        rw [he] at I₁ I₂
        exact ⟨I₁, I₂⟩
      · rw [eval_ne z₁] at hc
        have he : b - (d + min (b - d) 64) ≠ 0 := by simpa using hc
        exact ⟨b - (d + min (b - d) 64), by omega_arith, d + min (b - d) 64, rfl, by omega_arith, I₁, I₂⟩
    · exact RelCT.of_false fun _ _ h => hm h.1
  · exact RelCT.of_false fun _ _ h => hd h.2.1

/-! ## The last bytes and `absorb` -/

theorem tailPre_check : ∃ hc, (taint.check (sivT [.r12, .rbx, .rbp])
    (.seq (.block (zero16 bO ++ ptr .rdi .r15 bO ++ ([.mov .rsi (.reg .r12), .mov .rcx (.reg .rbp)] : List Instr)))
      (.seq copyLoop (.block (([.mov .rax (.mem (at_ .r15 bO)), .mov .rdx (.mem (at_ .r15 (bO + 8))), .bswap .rax,
        .bswap .rdx] : List Instr) ++ store2 (at_ .r15 revO) .rdx .rax ++ ghArgs ++
        ptr .rdx .r15 revO ++ ([.mov32 .rcx (imm 1)] : List Instr))))) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absTail_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {b nr : Nat} (hr1 : 1 ≤ nr)
    (hr : nr < 16) :
    RelCT isa (fun t₁ t₂ => AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂)
      (absorbTail v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, AInv K W SP R N A D al n Q b nr b t → WP isa _ t fun t₃ =>
      GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP := fun I =>
    WP.mono (tailPre_ok L I.one.env hr1 hr I.res I.r12 I.rbp) fun _ Tp => ⟨Tp.call, Tp.env.rsp⟩
  refine rel_assoc3 (RelCT.seq ((rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      AInv K W SP R N A D al n Q b nr b t₁ ∧ AInv K W SP R N A D al n Q b nr b t₂) hDW hn
      (fun t₁ t₂ h => h.1.agree h.2) tailPre_check).wp
    (F₁ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    (F₂ := fun (t₃ : State) => GhCall t₃ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₃.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre h.1, pre h.2⟩) ?_)
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

/-- What `absorb` is given: `nb` bytes at `Q`. -/
structure AbsIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (nb : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  buf : Buf K W SP t Q nb
  r12 : t.gpr .r12 = Q
  rbp : t.gpr .rbp = BitVec.ofNat 64 nb

theorem absHead_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {nb : Nat} {t : State}
    (h : AbsIn K W SP R N A D al n Q nb t) :
    WP isa (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) t
      fun t₁ => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)) := by
  have hn := h.buf.lt
  have hand := Proof.AesGcm.X86_64.and15 (BitVec.ofNat 64 nb)
  rw [toNat_ofNat_of_lt hn, Proof.AesGcm.X86_64.imm_eq (by decide)] at hand
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · refine ⟨⟨h.one.env.keep (fun r hr => ?_) rfl rfl, h.one.sl, h.one.wr⟩, (h.buf.take (by omega_arith)).of_eq rfl rfl,
      (h.buf.slice (by omega_arith)).of_eq rfl rfl, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.r12, Nat.mul_zero,
        BitVec.add_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp,
        Proof.AesGcm.X86_64.shr4 _ hn, Nat.sub_zero]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.rbp, hand]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
      reduceCtorEq, h.rbp, Proof.AesGcm.X86_64.shr4 _ hn]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]

theorem absHead_check : ∃ hc, (taint.check (sivT [.r12, .rbp])
    (.block [.mov .rbx (.reg .rbp), .shift .shr .rbx 4, .alu .and .rbp (imm 15), .alu .test .rbx (.reg .rbx)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem absTest_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr} {b nr d : Nat} (hnr : nr < 16)
    {t : State} (I : AInv K W SP R N A D al n Q b nr d t) :
    WP isa (.block [.alu .test .rbp (.reg .rbp)]) t fun t' =>
      AInv K W SP R N A D al n Q b nr d t' ∧ t'.zf = some (decide (nr = 0)) := by
  refine WP.of_runBlock ⟨_, by srun [], ?_, ?_⟩
  · exact ⟨⟨I.one.env.keep (fun _ _ => by simp only [gpr_arithFlags]) rfl rfl, I.one.sl, I.one.wr⟩,
      I.buf.of_eq rfl rfl, I.res.of_eq rfl rfl, by simp only [gpr_arithFlags, I.r12], by simp only [gpr_arithFlags, I.rbx],
      by simp only [gpr_arithFlags, I.rbp]⟩
  · simp only [zf_arithFlags, I.rbp]
    rw [Proof.AesGcm.X86_64.and_self_beq (by omega_arith)]

/-- `absorb`, in two runs with the same public arguments. -/
theorem absorb_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {nb : Nat} {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → AbsIn K W SP R N A D al n Q nb t₁ ∧ AbsIn K W SP R N A D al n Q nb t₂) :
    RelCT isa P (absorb v.callees wide) fun _ _ => True := by
  have r₁ := (rel_taintC [.r12, .rbp] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [(hP _ _ h).1.r12, (hP _ _ h).2.r12]
      · rw [(hP _ _ h).1.rbp, (hP _ _ h).2.rbp]⟩) absHead_check).wp
    (F₁ := fun (t₁ : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    (F₂ := fun (t₁ : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧ t₁.zf = some (decide (nb / 16 = 0)))
    fun t₁ t₂ h => ⟨absHead_wp (hP _ _ h).1, absHead_wp (hP _ _ h).2⟩
  have r₂ : RelCT isa (fun t₁ t₂ => True ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₁ ∧
        t₁.zf = some (decide (nb / 16 = 0))) ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) 0 t₂ ∧
        t₂.zf = some (decide (nb / 16 = 0))))
      (.ite .e (.block []) (.loop (absorbChunk v.callees wide) .ne))
      fun t₁ t₂ => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) ?_ ?_
    · refine RelCT.block_nil fun t₁ t₂ h => ?_
      have h0 : nb / 16 = 0 := by have := h.2; rw [eval_e h.1.2.1.2] at this; simpa using this
      have a := h.1.2.1.1
      have b := h.1.2.2.1
      rw [h0] at a b ⊢
      exact ⟨a, b⟩
    · by_cases h0 : nb / 16 = 0
      · refine RelCT.of_false fun t₁ t₂ h => ?_
        have := h.2
        rw [eval_e h.1.2.1.2] at this
        simp [h0] at this
      · exact (chunks_rel v wide L hDW hn (b := nb / 16) (by omega_arith)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
          fun _ _ h => h
  have r₃ := (rel_taintC [.r12, .rbx, .rbp] (P := fun t₁ t₂ =>
      AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
      AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂) hDW hn (fun t₁ t₂ h => h.1.agree h.2)
      test_check).wp
    (F₁ := fun (t : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    (F₂ := fun (t : State) => AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t ∧
      t.zf = some (decide (nb % 16 = 0)))
    fun t₁ t₂ h => ⟨absTest_wp (by omega_arith) h.1, absTest_wp (by omega_arith) h.2⟩
  have r₄ : RelCT isa (fun t₁ t₂ => True ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₁ ∧
        t₁.zf = some (decide (nb % 16 = 0))) ∧ (AInv K W SP R N A D al n Q (nb / 16) (nb % 16) (nb / 16) t₂ ∧
        t₂.zf = some (decide (nb % 16 = 0))))
      (.ite .e (.block []) (absorbTail v.callees)) fun _ _ => True := by
    refine RelCT.ite (fun t₁ t₂ h => by rw [eval_e h.2.1.2, eval_e h.2.2.2]) (RelCT.block_nil fun _ _ _ => trivial) ?_
    by_cases h0 : nb % 16 = 0
    · refine RelCT.of_false fun t₁ t₂ h => ?_
      have := h.2
      rw [eval_e h.1.2.1.2] at this
      simp [h0] at this
    · exact (absTail_rel v L hDW hn (by omega_arith) (by omega_arith)).mono (fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩)
        fun _ _ _ => trivial
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

/-! ## The lengths, and `polyval` -/

theorem lensArgs_check : ∃ hc, (taint.check (sivT []) (.block (([.mov .rax (.mem (at_ .r15 lenO)),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
    .mov .rdx (.mem (at_ .r15 alenO)), .alu .add .rdx (.reg .rdx),
    .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .bswap .rdx] :
      List Instr) ++ store2 (at_ .r15 bO) .rax .rdx ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `lens`, in two runs with the same public arguments. -/
theorem lens_rel (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → One K W SP R N A D al n t₁ ∧ One K W SP R N A D al n t₂) :
    RelCT isa P (lens v.callees) fun _ _ => True := by
  have pre : ∀ {t : State}, One K W SP R N A D al n t → WP isa (.block (([.mov .rax (.mem (at_ .r15 lenO)),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .bswap .rax,
      .mov .rdx (.mem (at_ .r15 alenO)), .alu .add .rdx (.reg .rdx),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .bswap .rdx] :
        List Instr) ++ store2 (at_ .r15 bO) .rax .rdx ++ ghArgs ++ ptr .rdx .r15 bO ++ ([.mov32 .rcx (imm 1)] : List Instr))) t fun t₁ =>
      GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP := fun O => by
    obtain ⟨t₁, run₁, -, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ := lensArgs_ok O.env O.sl.alen O.sl.len hal hn'
    have E₁ : Env K W SP t₁ := O.env.of_saved hg₁ hrd₁ hwr₁
    exact WP.of_runBlock ⟨t₁, run₁, gargs L E₁ (d := 128) (n := 1) (by decide) (by decide) rdi₁ rsi₁ rdx₁ rcx₁ r8₁,
      E₁.rsp⟩
  refine RelCT.seq ((rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1, (hP _ _ h).2, fun _ h => nomatch h⟩)
    lensArgs_check).wp
    (F₁ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    (F₂ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 128)
        (W + BitVec.ofNat 64 1512) 1 ∧ t₁.gpr .rsp = SP)
    fun t₁ t₂ h => ⟨pre (hP _ _ h).1, pre (hP _ _ h).2⟩) ?_
  exact gh_rel v.gh fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩

theorem tagIn_check : ∃ hc, (taint.check (sivT []) (.block tagIn) hc).isSome = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem polyD_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the public arguments and the buffers of the additional data
and the data. -/
structure Bufs (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (t : State) : Prop where
  one : One K W SP R N A D al n t
  aad : Buf K W SP t A al
  data : Buf K W SP t D n

theorem Bufs.of_eq {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t t' : State}
    (h : Bufs K W SP R N A D al n t) (E : Env K W SP t') (hf : Frame (absR W SP) t.mem t'.mem) (L : Lay K W SP)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) : Bufs K W SP R N A D al n t' :=
  ⟨⟨E, Slots.absR L h.one.sl hf, hwr.trans h.one.wr⟩, h.aad.of_eq hrd hwr, h.data.of_eq hrd hwr⟩

theorem polyBlk_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) {o₁ o₂ : Nat} {Q : Addr} {nb : Nat} (hQ : Buf K W SP t Q nb)
    (h₁ : t.mem.readW (W + BitVec.ofNat 64 o₁) 64 = Q) (h₂ : t.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 nb)
    (ho₁ : o₁ + 8 ≤ 3816) (ho₂ : o₂ + 8 ≤ 3816) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂))]) t
      fun t' => AbsIn K W SP R N A D al n Q nb t' ∧ Bufs K W SP R N A D al n t' := by
  have h15 := h.one.env.r15
  have r₁ := h.one.env.perm.wR ho₁
  have r₂ := h.one.env.perm.wR ho₂
  refine WP.of_runBlock ⟨_, by srun [h15, r₁, r₂], ?_⟩
  have E' : Env K W SP ((t.setReg .r12 (t.mem.readW (W + BitVec.ofNat 64 o₁) 64)).setReg .rbp
      (t.mem.readW (W + BitVec.ofNat 64 o₂) 64)) :=
    h.one.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]) rfl rfl
  exact ⟨⟨⟨E', h.one.sl, h.one.wr⟩, hQ.of_eq rfl rfl, by simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h₁],
    by simp only [gpr_setReg, ite_true, h₂]⟩, ⟨E', h.one.sl, h.one.wr⟩, h.aad.of_eq rfl rfl, h.data.of_eq rfl rfl⟩

theorem absorb_bufs (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    {Q : Addr} {nb : Nat} {t : State} (h : AbsIn K W SP R N A D al n Q nb t ∧ Bufs K W SP R N A D al n t) :
    WP isa (absorb v.callees wide) t (Bufs K W SP R N A D al n) :=
  WP.mono (absorb_ok v wide L h.1.one.env h.1.buf h.1.r12 h.1.rbp) fun _ P => h.2.of_eq P.env P.frame L P.rd P.wr

/-- `polyvalLong`, in two runs with the same public arguments. -/
theorem polyvalLong_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (polyvalLong v.callees wide) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    polyA_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n A al t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).1 (hP _ _ h).1.aad (hP _ _ h).1.one.sl.aad
        (hP _ _ h).1.one.sl.alen (by decide) (by decide),
      polyBlk_wp (o₁ := aadO) (o₂ := alenO) (hP _ _ h).2 (hP _ _ h).2.aad (hP _ _ h).2.one.sl.aad
        (hP _ _ h).2.one.sl.alen (by decide) (by decide)⟩
  have r₂ := (absorb_rel v wide L hDW hn (Q := A) (nb := al) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n A al t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n A al t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) polyD_check).wp
    (F₁ := fun (t : State) => AbsIn K W SP R N A D al n D n t ∧ Bufs K W SP R N A D al n t)
    (F₂ := fun (t : State) => AbsIn K W SP R N A D al n D n t ∧ Bufs K W SP R N A D al n t)
    fun t₁ t₂ h => ⟨polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.1 h.2.1.data h.2.1.one.sl.data h.2.1.one.sl.len
        (by decide) (by decide),
      polyBlk_wp (o₁ := dataO) (o₂ := lenO) h.2.2 h.2.2.data h.2.2.one.sl.data h.2.2.one.sl.len (by decide)
        (by decide)⟩
  have r₄ := (absorb_rel v wide L hDW hn (Q := D) (nb := n) (P := fun t₁ t₂ => True ∧
      (AbsIn K W SP R N A D al n D n t₁ ∧ Bufs K W SP R N A D al n t₁) ∧
      (AbsIn K W SP R N A D al n D n t₂ ∧ Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨absorb_bufs v wide L h.2.1, absorb_bufs v wide L h.2.2⟩
  have lens_bufs : ∀ {t : State}, Bufs K W SP R N A D al n t → WP isa (lens v.callees) t (Bufs K W SP R N A D al n) :=
    fun h => WP.mono (lens_ok v L h.one.env h.one.sl.alen h.one.sl.len hal hn') fun _ P =>
      h.of_eq P.env P.frame L P.rd P.wr
  have r₅ := (lens_rel v L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧
      Bufs K W SP R N A D al n t₂) fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨lens_bufs h.2.1, lens_bufs h.2.2⟩
  have r₆ := rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ r₆))))

/-! ## POLYVAL in one call -/

/-- A run before staging `nb` bytes at `Q` from block `k` of `W + 488`. -/
structure SIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (Q : Addr) (nb k : Nat) (t : State) : Prop where
  bufs : Bufs K W SP R N A D al n t
  buf : Buf K W SP t Q nb
  r12 : t.gpr .r12 = Q
  rbp : t.gpr .rbp = BitVec.ofNat 64 nb
  rdi : t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * k)

/-- A run having staged blocks up to block `k`. -/
def SAt (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (k : Nat) (t : State) : Prop :=
  Bufs K W SP R N A D al n t ∧ t.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * k)

theorem stage_check (wide : Bool) : ∃ hc, (taint.check (sivT [.r12, .rbp, .rdi]) (stage wide) hc).isSome = true := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem polyOneA_check : ∃ hc, (taint.check (sivT []) (.block (ptr .rdi .r15 revO ++
    ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem lensAt_check : ∃ hc, (taint.check (sivT [.rdi]) (.block lensAt) hc).isSome = true := ⟨_, by taint_decide⟩

theorem polyCond_check : ∃ hc, (taint.check (sivT []) (.block [.mov .rax (.mem (at_ .r15 alenO)), .shift .shr .rax 4,
    .mov .rdx (.mem (at_ .r15 lenO)), .shift .shr .rdx 4, .alu .add .rax (.reg .rdx), .alu .cmp .rax (imm 62)])
    hc).isSome = true := ⟨_, by taint_decide⟩

theorem stage_wp (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat} {Q : Addr}
    {nb k : Nat} (hk : k + nb / 16 < 64) {t : State} (h : SIn K W SP R N A D al n Q nb k t) :
    WP isa (stage wide) t (SAt K W SP R N A D al n (k + (nb + 15) / 16)) :=
  WP.mono (stage_ok wide L h.bufs.one.env h.buf h.r12 h.rbp hk h.rdi) fun _ P =>
    ⟨h.bufs.of_eq P.env (Frame.stR_absR (by have := P.le; omega_arith) P.frame) L P.rd P.wr,
      by rw [P.rdi, elems_pad16_length_eq]⟩

/-- `stage`, in two runs with the same public arguments. -/
theorem stage_rel (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) {Q : Addr} {nb k : Nat} (hk : k + nb / 16 < 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → SIn K W SP R N A D al n Q nb k t₁ ∧ SIn K W SP R N A D al n Q nb k t₂) :
    RelCT isa P (stage wide) fun t₁ t₂ => True ∧ SAt K W SP R N A D al n (k + (nb + 15) / 16) t₁ ∧
      SAt K W SP R N A D al n (k + (nb + 15) / 16) t₂ :=
  (rel_taintC [.r12, .rbp, .rdi] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.bufs.one, (hP _ _ h).2.bufs.one, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [(hP _ _ h).1.r12, (hP _ _ h).2.r12]
      · rw [(hP _ _ h).1.rbp, (hP _ _ h).2.rbp]
      · rw [(hP _ _ h).1.rdi, (hP _ _ h).2.rdi]⟩) (stage_check wide)).wp
    (F₁ := SAt K W SP R N A D al n (k + (nb + 15) / 16)) (F₂ := SAt K W SP R N A D al n (k + (nb + 15) / 16))
    fun t₁ t₂ h => ⟨stage_wp wide L hk (hP _ _ h).1, stage_wp wide L hk (hP _ _ h).2⟩

theorem polyOneA_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block (ptr .rdi .r15 revO ++
      ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr))) t
      (SIn K W SP R N A D al n A al 0) := by
  have h15 := h.one.env.r15
  have rA := h.one.env.perm.wR (show 216 + 8 ≤ 3816 by decide)
  have rL := h.one.env.perm.wR (show 224 + 8 ≤ 3816 by decide)
  have sA := h.one.sl.aad
  have sL := h.one.sl.alen
  obtain ⟨t₁, run₁, hdi₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      (ptr .rdi .r15 revO ++ [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))]) t = some t₁ ∧
      t₁.gpr .rdi = W + BitVec.ofNat 64 (488 + 16 * 0) ∧ t₁.gpr .r12 = A ∧ t₁.gpr .rbp = BitVec.ofNat 64 al ∧
      (∀ r, r ≠ .rdi → r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rA, rL], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, sA]
    · simp only [gpr_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, sL]
    · intro r h₁ h₂ h₃; simp only [gpr_arithFlags, gpr_setReg, h₁, h₂, h₃, ite_false]
    all_goals rfl
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, ⟨⟨E₁, hm₁ ▸ h.one.sl, hwr₁.trans h.one.wr⟩, h.aad.of_eq hrd₁ hwr₁,
    h.data.of_eq hrd₁ hwr₁⟩, h.aad.of_eq hrd₁ hwr₁, h12₁, hbp₁, hdi₁⟩

theorem polyOneD_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n k : Nat} {t : State}
    (h : SAt K W SP R N A D al n k t) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) t
      (SIn K W SP R N A D al n D n k) := by
  obtain ⟨B, hdi⟩ := h
  have h15 := B.one.env.r15
  have rD := B.one.env.perm.wR (show 232 + 8 ≤ 3816 by decide)
  have rN := B.one.env.perm.wR (show 240 + 8 ≤ 3816 by decide)
  have sD := B.one.sl.data
  have sN := B.one.sl.len
  obtain ⟨t₁, run₁, h12₁, hbp₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))] t = some t₁ ∧
      t₁.gpr .r12 = D ∧ t₁.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .r12 → r ≠ .rbp → t₁.gpr r = t.gpr r) ∧
      t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by srun [h15, rD, rN], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sD]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, sN]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₁ : Env K W SP t₁ := B.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, ⟨⟨E₁, hm₁ ▸ B.one.sl, hwr₁.trans B.one.wr⟩, B.aad.of_eq hrd₁ hwr₁,
    B.data.of_eq hrd₁ hwr₁⟩, B.data.of_eq hrd₁ hwr₁, h12₁, hbp₁, by rw [hg₁ _ (by decide) (by decide), hdi]⟩

theorem lensAt_wp {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n k : Nat} (hk : k < 64)
    (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64) {t : State} (h : SAt K W SP R N A D al n k t) :
    WP isa (.block lensAt) t fun t₁ => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
      (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) (k + 1) ∧ t₁.gpr .rsp = SP ∧
      Bufs K W SP R N A D al n t₁ := by
  obtain ⟨B, hdi⟩ := h
  obtain ⟨t₁, run₁, hm₁, rdi₁, rsi₁, r8₁, rdx₁, rcx₁, hg₁, hrd₁, hwr₁⟩ :=
    lensAt_ok B.one.env hk hdi B.one.sl.alen B.one.sl.len hal hn'
  have E₁ : Env K W SP t₁ := B.one.env.of_saved hg₁ hrd₁ hwr₁
  have fL : Frame (absR W SP) t.mem t₁.mem := by
    rw [hm₁]
    have mR : (⟨W + BitVec.ofNat 64 488, 1024⟩ : Region) ∈ absR W SP := by simp
    exact ((Frame.refl _ _).writeW mR _ (Offset.contains W (by omega_arith) (by omega_arith) (by have := L.ww; omega_arith))).writeW mR _
      (by rw [add_ofNat_assoc]; exact Offset.contains W (by omega_arith) (by omega_arith) (by have := L.ww; omega_arith))
  exact WP.of_runBlock ⟨t₁, run₁, gargs L E₁ (d := 488) (n := k + 1) (by decide) (by omega_arith) rdi₁ rsi₁ rdx₁ rcx₁ r8₁,
    E₁.rsp, B.of_eq E₁ fL L hrd₁ hwr₁⟩

theorem ghBufs_wp (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n k : Nat} {t : State}
    (h : GhCall t (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
      (W + BitVec.ofNat 64 1512) k ∧ t.gpr .rsp = SP ∧ Bufs K W SP R N A D al n t) :
    WP isa (.call v.gh.fn.name v.gh.fn.code) t (Bufs K W SP R N A D al n) := by
  obtain ⟨gc, hsp, B⟩ := h
  refine WP.mono (gh_call v.gh gc) fun t₁ Q => ?_
  have fc := Q.frame
  rw [hsp] at fc
  exact B.of_eq (B.one.env.of_saved Q.saved Q.rd Q.wr) (fc.mono fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> simp) L Q.rd Q.wr

/-- `polyvalOne`, in two runs with the same public arguments. -/
theorem polyvalOne_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    (hsz : al / 16 + n / 16 ≤ 61) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (polyvalOne v.callees wide) fun _ _ => True := by
  have r₁ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    polyOneA_check).wp
    (F₁ := SIn K W SP R N A D al n A al 0) (F₂ := SIn K W SP R N A D al n A al 0)
    fun t₁ t₂ h => ⟨polyOneA_wp (hP _ _ h).1, polyOneA_wp (hP _ _ h).2⟩
  have r₂ := stage_rel wide L hDW hn (Q := A) (nb := al) (k := 0) (by omega_arith)
    (P := fun t₁ t₂ => True ∧ SIn K W SP R N A D al n A al 0 t₁ ∧ SIn K W SP R N A D al n A al 0 t₂)
    fun t₁ t₂ h => ⟨h.2.1, h.2.2⟩
  have r₃ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ SAt K W SP R N A D al n (0 + (al + 15) / 16) t₁ ∧
      SAt K W SP R N A D al n (0 + (al + 15) / 16) t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.one, h.2.2.1.one, fun _ h => nomatch h⟩) polyD_check).wp
    (F₁ := SIn K W SP R N A D al n D n (0 + (al + 15) / 16)) (F₂ := SIn K W SP R N A D al n D n (0 + (al + 15) / 16))
    fun t₁ t₂ h => ⟨polyOneD_wp h.2.1, polyOneD_wp h.2.2⟩
  have r₄ := stage_rel wide L hDW hn (Q := D) (nb := n) (k := 0 + (al + 15) / 16) (by omega_arith)
    (P := fun t₁ t₂ => True ∧ SIn K W SP R N A D al n D n (0 + (al + 15) / 16) t₁ ∧
      SIn K W SP R N A D al n D n (0 + (al + 15) / 16) t₂)
    fun t₁ t₂ h => ⟨h.2.1, h.2.2⟩
  have hk : 0 + (al + 15) / 16 + (n + 15) / 16 < 64 := by omega_arith
  have r₅ := (rel_taintC [.rdi] (P := fun t₁ t₂ => True ∧
      SAt K W SP R N A D al n (0 + (al + 15) / 16 + (n + 15) / 16) t₁ ∧
      SAt K W SP R N A D al n (0 + (al + 15) / 16 + (n + 15) / 16) t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.one, h.2.2.1.one, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) lensAt_check).wp
    (F₁ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
      (W + BitVec.ofNat 64 1512) (0 + (al + 15) / 16 + (n + 15) / 16 + 1) ∧ t₁.gpr .rsp = SP ∧
      Bufs K W SP R N A D al n t₁)
    (F₂ := fun (t₁ : State) => GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
      (W + BitVec.ofNat 64 1512) (0 + (al + 15) / 16 + (n + 15) / 16 + 1) ∧ t₁.gpr .rsp = SP ∧
      Bufs K W SP R N A D al n t₁)
    fun t₁ t₂ h => ⟨lensAt_wp L hk hal hn' h.2.1, lensAt_wp L hk hal hn' h.2.2⟩
  have r₆ := (gh_rel v.gh (P := fun t₁ t₂ => True ∧ (GhCall t₁ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80)
        (W + BitVec.ofNat 64 488) (W + BitVec.ofNat 64 1512) (0 + (al + 15) / 16 + (n + 15) / 16 + 1) ∧
        t₁.gpr .rsp = SP ∧ Bufs K W SP R N A D al n t₁) ∧
      (GhCall t₂ (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 488)
        (W + BitVec.ofNat 64 1512) (0 + (al + 15) / 16 + (n + 15) / 16 + 1) ∧ t₂.gpr .rsp = SP ∧
        Bufs K W SP R N A D al n t₂))
    fun t₁ t₂ h => ⟨_, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2.1, h.2.2.2.1]⟩).wp
    (F₁ := Bufs K W SP R N A D al n) (F₂ := Bufs K W SP R N A D al n)
    fun t₁ t₂ h => ⟨ghBufs_wp v L h.2.1, ghBufs_wp v L h.2.2⟩
  have r₇ := rel_taintC [] (P := fun t₁ t₂ => True ∧ Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.one, h.2.2.one, fun _ h => nomatch h⟩) tagIn_check
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇)))))

theorem polyCond_wp {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} (L : Lay K W SP) {t : State}
    (h : Bufs K W SP R N A D al n t) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 alenO)), .shift .shr .rax 4, .mov .rdx (.mem (at_ .r15 lenO)),
      .shift .shr .rdx 4, .alu .add .rax (.reg .rdx), .alu .cmp .rax (imm 62)]) t fun t₁ =>
      Bufs K W SP R N A D al n t₁ ∧ t₁.cf = some (decide (al / 16 + n / 16 < 62)) := by
  obtain ⟨t₁, run₁, hcf₁, hg₁, hm₁, hrd₁, hwr₁⟩ := polyCond_run h.one.env h.one.sl h.aad.lt h.data.lt
  have E₁ : Env K W SP t₁ := h.one.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  exact WP.of_runBlock ⟨t₁, run₁, h.of_eq E₁ (by rw [hm₁]; exact Frame.refl _ _) L hrd₁ hwr₁, hcf₁⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {al n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → Bufs K W SP R N A D al n t₁ ∧ Bufs K W SP R N A D al n t₂) :
    RelCT isa P (polyval v.callees wide) fun _ _ => True := by
  have r₀ := (rel_taintC [] hDW hn (fun t₁ t₂ h => ⟨(hP _ _ h).1.one, (hP _ _ h).2.one, fun _ h => nomatch h⟩)
    polyCond_check).wp
    (F₁ := fun (t : State) => Bufs K W SP R N A D al n t ∧ t.cf = some (decide (al / 16 + n / 16 < 62)))
    (F₂ := fun (t : State) => Bufs K W SP R N A D al n t ∧ t.cf = some (decide (al / 16 + n / 16 < 62)))
    fun t₁ t₂ h => ⟨polyCond_wp L (hP _ _ h).1, polyCond_wp L (hP _ _ h).2⟩
  refine RelCT.seq r₀ (RelCT.ite (fun t₁ t₂ h => by
    show t₁.cf.map (!·) = t₂.cf.map (!·); rw [h.2.1.2, h.2.2.2]) ?_ ?_)
  · exact polyvalLong_rel v wide L hDW hn hal hn' fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
  · by_cases hs : al / 16 + n / 16 < 62
    · exact polyvalOne_rel v wide L hDW hn hal hn' (by omega_arith) fun t₁ t₂ h => ⟨h.1.2.1.1, h.1.2.2.1⟩
    · refine RelCT.of_false fun t₁ t₂ h => ?_
      have := h.2
      rw [show isa.eval .ae t₁ = t₁.cf.map (!·) from rfl, h.1.2.1.2] at this
      simp [hs] at this

end VG.Proof.AesGcmSiv.X86_64

end

end

/-!
# AES-GCM-SIV on x86-64: `vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` are constant time

Untrusted: everything here is checked by Lean. The entry, which loads `W`
from the stack first, passes the taint analysis from the public arguments
(`entry_rel`); between the pieces each run has the public arguments, its
buffers and the tag's address on the stack (`St`), which every piece keeps
(by correctness), and the pieces are related from it (`keys_rel`,
`polyval_rel`, `tag_rel`, `crypt_rel`, and the taint analysis for the
comparison, the mask and the restore). The copies of the tag load its
address from the stack first, the same in both runs, and the taint analysis
checks the rest (`rel_loadT`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl in_off)

/-- The address of the tag `T`, at `SP + 16`, where the run may read it,
apart from what the pieces write, and the tag, which it may read. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8
  w : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨W, 3816⟩
  d : (⟨SP + BitVec.ofNat 64 8, 24⟩ : Region).Disjoint ⟨D, n⟩
  tb : TagBuf W SP D n T
  trd : Covers [⟨T, 16⟩] (s.rd ++ s.wr)

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : ArgT W SP D n T s)
    (hf : Frame (mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgT W SP D n T s' :=
  ⟨by rw [argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d, h.tb, by rw [hrd, hwr]; exact h.trd⟩

/-- A run between the pieces: the public arguments, the buffers and the
tag's address. -/
structure St (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop where
  bufs : Bufs K W SP R N A D al n t
  nonce : Buf K W SP t N 12
  argT : ArgT W SP D n T t

theorem St.frame {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t t' : State}
    (h : St K W SP R N A D al n T t) (E : Env K W SP t') {rs : List Region} (hf : Frame rs t.mem t'.mem)
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 200, 48⟩ : Region).Disjoint r) (hm : Frame (mutR W SP D n) t.mem t'.mem)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    St K W SP R N A D al n T t' :=
  ⟨⟨⟨E, h.bufs.one.sl.of_frame hf hd, hwr.trans h.bufs.one.wr⟩, h.bufs.aad.of_eq hrd hwr, h.bufs.data.of_eq hrd hwr⟩,
    h.nonce.of_eq hrd hwr, h.argT.mut hm hrd hwr⟩

/-- `St`, and the keys' results that POLYVAL needs. -/
def StK (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 64) =
      GcmSiv.Polyval.mulXG (Spec.GcmSiv.ofBytes (bytesAt t.mem (W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt t.mem (W + BitVec.ofNat 64 80) = 0

theorem keys_st (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) : WP isa (keys v.callees ⟨eb.enc.name, eb.enc.code⟩) t (StK K W SP R N A D al n T) :=
  WP.mono (keys_ok v eb L hR h.bufs.one.env h.bufs.one.sl h.nonce h.bufs.data.w) fun _ Ky =>
    ⟨h.frame Ky.env Ky.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Ky.frame.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) Ky.rd Ky.wr,
      Ky.hkey, Ky.acc⟩

theorem keysS_st (eb : Proof.Aes.X86_64.BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (keysS ⟨eb.enc.name, eb.enc.code⟩) t (StK K W SP R N A D al n T) :=
  WP.mono (keysS_ok eb L hR h.bufs.one.env h.bufs.one.sl h.nonce h.bufs.data.w) fun _ Ky =>
    ⟨h.frame Ky.env Ky.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Ky.frame.sub (keyR_mutW W SP)).sub (mutW_mut W SP D n)) Ky.rd Ky.wr,
      Ky.hkey, Ky.acc⟩

theorem expand_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (expand v.callees) t (St K W SP R N A D al n T) :=
  WP.mono (expand_ok v L hR h.bufs.one.env h.bufs.one.sl) fun _ X =>
    h.frame X.env X.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((X.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_wC (by decide) (by decide)
        · exact sub_wC (by decide) (by decide)
        · exact sub_stk).sub (mutW_mut W SP D n)) X.rd X.wr

theorem polyval_st (v : GcmImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StK K W SP R N A D al n T t) : WP isa (polyval v.callees wide) t (St K W SP R N A D al n T) :=
  WP.mono (polyval_ok v wide L h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.aad h.1.bufs.data h.1.nonce h.2.1 h.2.2)
    fun _ Po => h.1.frame Po.env Po.frame (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) ((Po.frame.sub (polyR_mutW W SP)).sub (mutW_mut W SP D n)) Po.rd Po.wr

theorem tag_st (v : GcmImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {o : Nat} (ho : o = 0 ∨ o = 128) {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (tag v.callees o) t (St K W SP R N A D al n T) :=
  WP.mono (tag_ok v L hR h.bufs.one.env h.bufs.one.sl ho) fun _ Tg => h.frame Tg.env Tg.frame (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho])
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) ((Tg.frame.sub (tagR_mutW W SP (by omega_using [ho]))).sub (mutW_mut W SP D n))
    Tg.rd Tg.wr

theorem crypt_st0 (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) : WP isa (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t (St K W SP R N A D al n T) :=
  WP.mono (crypt_ok v eb wide L hR h.bufs.one.env h.bufs.one.sl h.bufs.data
    (by rw [h.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr =>
    h.frame Cr.env Cr.frame (slots_cryR L h.bufs.data) (Cr.frame.sub (cryR_mut W SP D n)) Cr.rd Cr.wr

theorem crypt_st (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} {t : State} (h : StK K W SP R N A D al n T t) : WP isa (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) t (StK K W SP R N A D al n T) := by
  refine WP.mono (crypt_ok v eb wide L hR h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp))) fun _ Cr => ?_
  have dK : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 96 → ∀ q ∈ cryR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
      · exact L.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
      · exact L.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
      · exact (L.stk_w' (by omega_using [h₂])).symm
      · exact (h.1.bufs.data.w.sub_right (Lay.wSub (by omega_using [h₂]))).symm
  refine ⟨h.1.frame Cr.env Cr.frame (slots_cryR L h.1.bufs.data) (Cr.frame.sub (cryR_mut W SP D n)) Cr.rd Cr.wr,
    ?_, ?_⟩
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.1,
      Proof.AesGcm.X86_64.bytesAt_frame Cr.frame (dK (by decide) (by decide)) (by decide)]
  · rw [Proof.AesGcm.X86_64.blockAt_frame Cr.frame (dK (by decide) (by decide)), h.2.2]

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by srun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 24) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 24))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 16`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s fun s₁ => Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
      InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8 := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ := entry_ok Ar.perm hsp Ar.args hn hW hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8 := by
    have h := in_off (d := 8) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ?_, by rw [rd₁, wr₁]; exact hTr⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R al n : Nat} (Ar : Args s K W SP N A D R al n)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 24) 8 := by
  have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-! ## The tag's address -/

/-- What the copies of the tag need of a run: `r15` and `rsp` hold `W` and
`SP`, and the address of the tag `T` is at `SP + 16`, where the run may read
it. -/
def TagIn (W SP T : Addr) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

theorem St.tagIn {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {σ s : State}
    (h : St K W SP R N A D al n T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : TagIn W SP T s :=
  ⟨by rw [← hg]; exact h.bufs.one.env.r15, by rw [← hg]; exact h.bufs.one.env.rsp, by rw [← hm]; exact h.argT.val,
    hc _ _ h.argT.rd⟩

/-- `mov rcx, [rsp + 16]`: the tag's address in `rcx`. -/
theorem loadT_ok {W SP T : Addr} {s : State} (h : TagIn W SP T s) :
    WP isa (.block [.mov .rcx (.mem (at_ .rsp 16))]) s fun s' =>
      s'.gpr .rcx = T ∧ s'.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s'.gpr r = s.gpr r := by
  obtain ⟨h15, hsp, hT, hr⟩ := h
  refine WP.of_runBlock ⟨_, by srun [hsp, hr], ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, hT]
  · simp only [gpr_setReg, ite_false, reduceCtorEq, h15]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem loadT_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (at_ .rsp 16))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `mov rcx, [rsp + 16]` and then `c`, which the taint analysis checks with
`rcx` and `r15` public, in two runs with the same `W`, `SP` and tag
address. -/
theorem rel_loadT {W SP T : Addr} {P : State → State → Prop} {l : List Instr}
    (hP : ∀ s₁ s₂, P s₁ s₂ → TagIn W SP T s₁ ∧ TagIn W SP T s₂)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block l) hc).isSome = true) :
    RelCT isa P (.block (([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ l)) fun _ _ => True := by
  have a := (rel_taintR (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨-, a₁, -⟩, ⟨-, a₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) loadT_check).wp
    (F₁ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    (F₂ := fun (s : State) => s.gpr .rcx = T ∧ s.gpr .r15 = W ∧ ∀ r, r ≠ .rcx → s.gpr r = s.gpr r)
    fun _ _ h => ⟨WP.mono (loadT_ok (hP _ _ h).1) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩,
      WP.mono (loadT_ok (hP _ _ h).2) fun _ h => ⟨h.1, h.2.1, fun _ _ => rfl⟩⟩
  exact RelCT.block_append (M := isa) (RelCT.seq a (rel_taintR [.rcx, .r15] (fun _ _ h r hr => by
    obtain ⟨-, ⟨c₁, w₁, -⟩, ⟨c₂, w₂, -⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [c₁, c₂]
    · rw [w₁, w₂]) hc))

/-! ## `seal` -/

/-- `s` with the tag read only, and the data and `W` its writable regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, 16⟩]) [⟨D, n⟩, ⟨W, 3816⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] ∧ St K W SP R N A D al n T (narrowT D n T W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hwr : s.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩])
    (h : Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.mem.readW (SP + BitVec.ofNat 64 16) 64 = T ∧ InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 16) 8) :
    SealIn K W SP R N A D al n T s₁ := by
  obtain ⟨E, S, rd, wr, hT, hTr⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, 16⟩, ⟨W, 3816⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((narrowT D n T W s₁).rd ++ (narrowT D n T W s₁).wr) := by
    rw [hwr₁]; exact covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → Buf K W SP (narrowT D n T W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.aad, hb Ar.data⟩, hb Ar.nonce,
    ⟨hT, hc _ _ hTr, Ar.argsW, Ar.argsD, Tb, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩⟩

theorem entry_seal {s : State} (hp : sealPre s) :
    WP isa (.block entry) s (SealIn (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  WP.mono (entry_post (args_of_seal hp).1.1 rfl (ofNat_toNat64 _).symm rfl rfl rfl
      (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl)
    fun _ h => sealIn_of (args_of_seal hp).1.1 (args_of_seal hp).1.2 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_seal hp'

/-- `seal` after its entry, up to the copy of the tag. -/
abbrev sealFront (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) : Prog isa :=
  .seq (.seq (.seq (.seq (keysS ⟨eb.enc.name, eb.enc.code⟩) (polyval v.callees wide)) (expand v.callees))
    (tag v.callees tagO)) (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide)

theorem sealFront_st (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} {t : State} (h : St K W SP R N A D al n T t) :
    WP isa (sealFront v eb wide) t (St K W SP R N A D al n T) :=
  WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (WP.seq (WP.mono (keysS_st eb L hR h)
    fun _ h => polyval_st v wide L h)) fun _ h => expand_st v L hR h))
    fun _ h => tag_st v L hR (by decide) h)) fun _ h => crypt_st0 v eb wide L hR h)

/-- `sealFront`, in two runs. -/
theorem sealFront_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14)
    {N A D T : Addr} {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64)
    (hn' : n < 2 ^ 64) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (sealFront v eb wide) fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂ := by
  have r₁ := (keysS_rel eb L hR hDW hn fun t₁ t₂ h => ⟨⟨(hP _ _ h).1.bufs.one, (hP _ _ h).1.nonce⟩,
      ⟨(hP _ _ h).2.bufs.one, (hP _ _ h).2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keysS_st eb L hR (hP _ _ h).1, keysS_st eb L hR (hP _ _ h).2⟩
  have r₂ := (polyval_rel v wide L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨polyval_st v wide L h.2.1, polyval_st v wide L h.2.2⟩
  have r₂' := (expand_rel v L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨expand_st v L hR h.2.1, expand_st v L hR h.2.2⟩
  have r₃ := (tag_rel v L hR hDW hn (o := tagO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₄ := (crypt_rel v eb wide L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.bufs.data⟩, ⟨h.2.2.bufs.one, h.2.2.bufs.data⟩⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨crypt_st0 v eb wide L hR h.2.1, crypt_st0 v eb wide L hR h.2.2⟩
  exact (RelCT.seq (RelCT.seq (RelCT.seq (RelCT.seq r₁ r₂) r₂') r₃) r₄).mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩

theorem tagOut_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block (tagOut.tail ++ restore)) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_siv_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {s₀ s₀' : State} (hp : sealPre s₀) (hp' : sealPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  refine RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc ?_)))
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront v eb wide)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9)
        (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1) s₂)
    [⟨arg s₀ 1, 16⟩] [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]
    (sealFront_rel v eb wide L Ar.rounds Ar.data.w hn Ar.aad.lt Ar.data.lt
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 1, 16⟩, ⟨arg s₀ 2, 3816⟩] →
          Covers ([⟨arg s₀ 1, 16⟩] ++ [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩]) s.wr ∧
          Covers [⟨s₀.gpr .r9, (arg s₀ 0).toNat⟩, ⟨arg s₀ 2, 3816⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealFront_st v eb wide L Ar.rounds p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealFront_st v eb wide L Ar.rounds p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (rel_loadT (l := tagOut.tail ++ restore) (fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.tagIn g₁ h₁ c₁, m₂.tagIn g₂ h₂ c₂⟩) tagOut_check)

/-! ## `open` -/

theorem entry_st {s : State} {K W SP N A D T : Addr} {R al n : Nat}
    (Ar : Args s K W SP N A D R al n) (Tb : TagBuf W SP D n T) (hTr : Covers [⟨T, 16⟩] (s.rd ++ s.wr))
    (hwr : s.wr = [⟨D, n⟩, ⟨W, 3816⟩]) (hsp : s.gpr .rsp = SP)
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    WP isa (.block entry) s (St K W SP R N A D al n T) :=
  WP.mono (entry_post Ar hsp hn hT hW hdi hsi hdx hcx hr8 hr9) fun _ ⟨E₁, S₁, rd₁, wr₁, hT₁, hTa₁⟩ =>
    ⟨⟨⟨E₁, S₁, wr₁.trans hwr⟩, Ar.aad.of_eq rd₁ wr₁, Ar.data.of_eq rd₁ wr₁⟩, Ar.nonce.of_eq rd₁ wr₁,
      ⟨hT₁, hTa₁, Ar.argsW, Ar.argsD, Tb, by rw [rd₁, wr₁]; exact hTr⟩⟩

theorem entry_open {s : State} (hp : openPre s) :
    WP isa (.block entry) s (St (s.gpr .rdi) (arg s 2) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r9) (s.gpr .r8).toNat (arg s 0).toNat (arg s 1)) :=
  entry_st (args_of_open hp).1.1 (args_of_open hp).1.2 (args_of_open hp).2 hp.2.1 rfl (ofNat_toNat64 _).symm rfl rfl
    rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (St (s₀.gpr .rdi) (arg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (arg s₀ 0).toNat (arg s₀ 1)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), q1, q2, q3, q4, q5, q6, q7]
  exact entry_open hp'

theorem recv_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block recv) t (St K W SP R N A D al n T) := by
  obtain ⟨t', run', fR, -, hg', hrd', hwr'⟩ := recv_ok h.bufs.one.env h.argT.val h.argT.rd
    (h.argT.tb.buf h.argT.trd)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fR (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using L.w_w (a := 200) (n := 48) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide))
    (fR.sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨wA W, by mem_lit, Region.sub_prefix (by decide)⟩)
    hrd' hwr'⟩

theorem recv_split : recv = ([.mov .rcx (.mem (at_ .rsp 16))] : List Instr) ++ recv.tail := rfl

theorem recv_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx, .r15]) (.block recv.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (taint.check (sivT []) (.block Impl.AesGcmSiv.X86_64.cmp) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ hc, (taint.check (sivT []) mask hc).isSome = true := ⟨_, by taint_decide⟩

theorem fin_check : ∃ hc, (taint.check (sivT [])
    (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `St`, with `ok` at `W + 192` either 1 or 0. -/
def StO (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (T : Addr) (t : State) : Prop :=
  St K W SP R N A D al n T t ∧
    (t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 ∨ t.mem.readW (W + BitVec.ofNat 64 192) 64 = 0#64)

theorem cmp_st {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : St K W SP R N A D al n T t) : WP isa (.block Impl.AesGcmSiv.X86_64.cmp) t (StO K W SP R N A D al n T) := by
  obtain ⟨t', run', hm', hg', hrd', hwr'⟩ := cmp_ok h.bufs.one.env
  have fO : Frame [wO W] t.mem t'.mem := by
    rw [hm']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine WP.of_runBlock ⟨t', run', h.frame (h.bufs.one.env.of_saved hg' hrd' hwr') fO (fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (fO.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩) hrd' hwr', ?_⟩
  rw [hm', Mem.readW_writeW_self64]
  split
  · exact .inl rfl
  · exact .inr rfl

theorem mask_st {K W SP : Addr} {R : Nat} {N A D T : Addr} {al n : Nat} {t : State}
    (h : StO K W SP R N A D al n T t) : WP isa mask t (St K W SP R N A D al n T) := by
  have hok : t.mem.readW (W + BitVec.ofNat 64 192) 64 =
      if t.mem.readW (W + BitVec.ofNat 64 192) 64 = 1#64 then 1#64 else 0#64 := by
    rcases h.2 with h' | h' <;> rw [h'] <;> decide
  refine WP.mono (mask_ok h.1.bufs.one.env h.1.bufs.one.sl h.1.bufs.data
    (by rw [h.1.bufs.one.wr]; exact Proof.AesGcm.X86_64.covers_of_mem (by simp)) hok) fun _ Mk =>
    h.1.frame Mk.env Mk.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact (h.1.bufs.data.w.sub_right (Lay.wSub (by decide))).symm)
      (Mk.frame.sub fun q hq => ⟨q, by simp only [List.mem_singleton] at hq; subst hq; simp, fun _ h => h⟩)
      Mk.rd Mk.wr

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 14) {N A D T : Addr}
    {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3816⟩) (hn : n ≤ 2 ^ 64) (hal : al < 2 ^ 64) (hn' : n < 2 ^ 64)
    {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂) :
    RelCT isa P (.seq (.block recv) (.seq (keys v.callees ⟨eb.enc.name, eb.enc.code⟩) (.seq (crypt v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) (.seq (polyval v.callees wide)
      (.seq (tag v.callees bO) (.seq (.block Impl.AesGcmSiv.X86_64.cmp) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))))
      fun _ _ => True := by
  have r₀ := (rel_loadT (l := recv.tail) (fun t₁ t₂ h =>
      ⟨(hP _ _ h).1.tagIn rfl rfl (Covers.refl _), (hP _ _ h).2.tagIn rfl rfl (Covers.refl _)⟩) recv_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨by rw [← recv_split]; exact recv_st L (hP _ _ h).1, by rw [← recv_split]; exact recv_st L (hP _ _ h).2⟩
  have r₁ := (keys_rel v eb L hR hDW hn (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨⟨h.2.1.bufs.one, h.2.1.nonce⟩, ⟨h.2.2.bufs.one, h.2.2.nonce⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨keys_st v eb L hR h.2.1, keys_st v eb L hR h.2.2⟩
  have r₂ := (crypt_rel v eb wide L hR hDW hn (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h =>
      ⟨⟨h.2.1.1.bufs.one, h.2.1.1.bufs.data⟩, ⟨h.2.2.1.bufs.one, h.2.2.1.bufs.data⟩⟩).wp
    (F₁ := StK K W SP R N A D al n T) (F₂ := StK K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨crypt_st v eb wide L hR h.2.1, crypt_st v eb wide L hR h.2.2⟩
  have r₃ := (polyval_rel v wide L hDW hn hal hn' (P := fun t₁ t₂ => True ∧ StK K W SP R N A D al n T t₁ ∧
      StK K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.1.bufs, h.2.2.1.bufs⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨polyval_st v wide L h.2.1, polyval_st v wide L h.2.2⟩
  have r₄ := (tag_rel v L hR hDW hn (o := bO) (by decide) (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧
      St K W SP R N A D al n T t₂) fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨tag_st v L hR (by decide) h.2.1, tag_st v L hR (by decide) h.2.2⟩
  have r₅ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) cmp_check).wp
    (F₁ := StO K W SP R N A D al n T) (F₂ := StO K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨cmp_st L h.2.1, cmp_st L h.2.2⟩
  have r₆ := (rel_taintC [] (P := fun t₁ t₂ => True ∧ StO K W SP R N A D al n T t₁ ∧ StO K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.1.bufs.one, h.2.2.1.bufs.one, fun _ h => nomatch h⟩) mask_check).wp
    (F₁ := St K W SP R N A D al n T) (F₂ := St K W SP R N A D al n T)
    fun t₁ t₂ h => ⟨mask_st h.2.1, mask_st h.2.2⟩
  have r₇ := rel_taintC [] (P := fun t₁ t₂ => True ∧ St K W SP R N A D al n T t₁ ∧ St K W SP R N A D al n T t₂)
    hDW hn (fun t₁ t₂ h => ⟨h.2.1.bufs.one, h.2.2.bufs.one, fun _ h => nomatch h⟩) fin_check
  rw [recv_split]
  exact RelCT.seq r₀ (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (RelCT.seq r₄ (RelCT.seq r₅ (RelCT.seq r₆ r₇))))))

/-- `vg_aes_gcm_siv_open`, in two runs with the same public arguments. -/
theorem open_rel (v : GcmImpl) (eb : Proof.Aes.X86_64.BlocksImpl) (wide : Bool) {s₀ s₀' : State} (hp : openPre s₀) (hp' : openPre s₀') (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees ⟨eb.enc.name, eb.enc.code⟩ wide) fun _ _ => True := by
  have Ar := (args_of_open hp).1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 2 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel v eb wide Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.aad.lt Ar.data.lt
    fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesGcmSiv.X86_64
