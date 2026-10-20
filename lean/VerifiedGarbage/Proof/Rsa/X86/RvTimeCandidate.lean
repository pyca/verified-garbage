module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
import VerifiedGarbage.Proof.Rsa.X86.RvWindowExp
import VerifiedGarbage.Proof.Rsa.X86.RvWindowTable
import VerifiedGarbage.Proof.Rsa.X86.RvWindowLoop
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A candidate's exponentiation leaks only public data

Two runs of a candidate's exponentiation (`CandidateData`) over the same
geometry leak the same trace: the pieces between Montgomery products by
their taint checks, and each product by `mmul_relCT`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live ls : List Nat} {m : Nat}

theorem KS.stage {liveW : List Nat} (h : KS g s0 A live AW liveW V ls s) : MulPost g s := ⟨_, _, _, _, _, _, _, h⟩

/-- What `KS.mulY` needs: the Montgomery product's precondition. -/
theorem KS.mulYPre {b y z : Nat} (h : KS g s0 A live AW [wRc, wR] V ls s)
    (hY : mY ∈ live) (hb : b ∈ live) (hB : mBase ∈ live) (hI : sInv ∈ ls) (value : A mBase = m)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (positive : 0 < m) (hl : ∀ j ∈ live, j = mY ∨ j ∉ montWrites mY)
    (hy : A mY = y * 2 ^ (64 * g.n) % m) (hz : A b = z * 2 ^ (64 * g.n) % m) :
    MulPre g mY mY b s :=
  ⟨_, _, _, _, _, _, _, _, h, h.montReady hB hI value bound inverse, hY, hb,
    by rw [hy]; exact Nat.mod_lt _ positive, by rw [hz]; exact Nat.mod_lt _ positive, hl, by decide⟩

end

/-- A piece checked by `τA`, between stages, with each run's correctness. -/
theorem pub_relCT {g : Geo} (pg : PubG g) {c : Prog isa}
    (hc : (VG.Taint.check taint τA c (VG.Taint.hintOf taint τA c)).isSome = true)
    {P Q P' Q' : State → Prop} (hP : ∀ s, P s → MulPost g s) (hQ : ∀ t, Q t → MulPost g t)
    (left : ∀ s, P s → WP isa c s P') (right : ∀ t, Q t → WP isa c t Q') :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => P' s ∧ Q' t) :=
  stage_relCT (fun s t _ _ _ _ ⟨hs, ht⟩ es et => by
    obtain ⟨_, _, _, _, _, _, _, h⟩ := hP s hs
    obtain ⟨_, _, _, _, _, _, _, j⟩ := hQ t ht
    exact ⟨pub_trace pg hc h j es et, trivial⟩) left right

/-- A Montgomery product between stages, with each run's correctness. -/
theorem mmul_stage {g : Geo} (pg : PubG g) {o a b : Nat} (ho : MontIndex o) (ha : MontIndex a)
    (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hT : (VG.Taint.check taint τF (.block (VG.Impl.Rsa.X86.RecoverRt.mulArgs o a b)) (.block [])).isSome = true)
    (hC : (VG.Taint.check taint τA (.block (VG.Impl.Rsa.X86.RecoverRt.clrTop o))
      (VG.Taint.hintOf taint τA (.block (VG.Impl.Rsa.X86.RecoverRt.clrTop o)))).isSome = true)
    {P Q P' Q' : State → Prop} (hP : ∀ s, P s → MulPre g o a b s) (hQ : ∀ t, Q t → MulPre g o a b t)
    (left : ∀ s, P s → WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) s P')
    (right : ∀ t, Q t → WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) t Q') :
    RelCT isa (fun s t => P s ∧ Q t) (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) (fun s t => P' s ∧ Q' t) :=
  stage_relCT ((mmul_relCT pg ho ha hb ho0 hT ⟨_, hC⟩).mono (fun s t h => ⟨hP s h.1, hQ t h.2⟩)
    fun _ _ h => h) left right

/-- `candMont_ok`'s product: its precondition. -/
theorem candMont_pre {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) {s : State}
    (h : C.Align (alignShifts g eLen dLen) s) : MulPre g mG mG mR2 s := by
  have positive : 0 < m := by have := C.large; omega
  unfold CandidateData.Align AI at h
  have mr := h.montReady (m := m) (by simp [liveExp]) (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY), upd_ne _ _ (by decide : mBase ≠ mG)] using C.value)
    C.bound (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using C.inverse)
  exact ⟨_, _, _, _, _, _, _, _, h, mr, by simp [liveExp], by simp [liveExp],
    by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self] using C.baseBound,
    by simpa only [upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), C.r2] using
      Nat.mod_lt (2 ^ (128 * g.n)) positive, by decide, by decide⟩

theorem tableCopyCheck (i : Nat) (hi : i < 14) :
    (VG.Taint.check taint τA (VG.Impl.Rsa.X86.KeyRt.copy VG.Impl.Rsa.X86.RecoverRt.nar (i + 2) mXm)
      (VG.Taint.hintOf taint τA (VG.Impl.Rsa.X86.KeyRt.copy VG.Impl.Rsa.X86.RecoverRt.nar (i + 2) mXm))).isSome =
      true := by
  match i, hi with
  | 0, _ => exact tableCopy0Check
  | 1, _ => exact tableCopy1Check
  | 2, _ => exact tableCopy2Check
  | 3, _ => exact tableCopy3Check
  | 4, _ => exact tableCopy4Check
  | 5, _ => exact tableCopy5Check
  | 6, _ => exact tableCopy6Check
  | 7, _ => exact tableCopy7Check
  | 8, _ => exact tableCopy8Check
  | 9, _ => exact tableCopy9Check
  | 10, _ => exact tableCopy10Check
  | 11, _ => exact tableCopy11Check
  | 12, _ => exact tableCopy12Check
  | 13, _ => exact tableCopy13Check

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live ls : List Nat}

/-- A table step's product: its precondition, and a stage after it. -/
theorem TI.mulPre {m b i : Nat} (h : TI g s0 A AW V live ls m b i s) (L : TableLive live)
    (hG : mG ∈ live) (hB : mBase ∈ live)
    (hI : sInv ∈ ls) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (positive : 0 < m)
    (base : A mG = b * 2 ^ (64 * g.n) % m) (hi : i < 14) :
    MulPre g mXm mXm mG s := by
  have aboveA (j : Nat) (hj : j ∈ live) (k : Nat) (hk : k ≤ 16) : tableA A g.n m b k j = A j := by
    have := L.above j hj
    simp only [tableA, show ¬ j < k by omega, ↓reduceIte]
  have notX (j : Nat) (hj : j ∈ live) : j ≠ mXm := fun e => L.xm (e ▸ hj)
  unfold TI at h
  have mr := h.montReady (m := m) (by simp [hB]) hI
    (by rw [upd_ne _ _ (by decide), aboveA _ hB _ (by omega)]; exact value) bound inverse
  refine ⟨_, _, _, _, _, _, _, _, h, mr, by simp, by simp [hG],
    by rw [upd_self]; exact Nat.mod_lt _ positive,
    by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega), base]; exact Nat.mod_lt _ positive, ?_, by decide⟩
  intro j hj
  simp only [List.mem_cons, List.mem_append, List.mem_range] at hj
  rcases hj with e | lo | hi
  · exact .inl e
  · right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mXm mAcc; omega
  · have := L.above j hi
    have := notX j hi
    right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mAcc; omega

end

theorem tableStep_trace {g : Geo} (pg : PubG g) {s0 t0 s t : State} {A B AW BW V W : Nat → Nat}
    {live ls : List Nat} {m b m' b' i : Nat} (hi : i < 14) (L : TableLive live)
    (hG : mG ∈ live) (hB : mBase ∈ live) (hI : sInv ∈ ls)
    (h : TI g s0 A AW V live ls m b i s) (vA : A mBase = m) (bA : m < 2 ^ (64 * g.n))
    (iA : (m * V sInv + 1) % 2 ^ 32 = 0) (pA : 0 < m) (gA : A mG = b * 2 ^ (64 * g.n) % m)
    (j : TI g t0 B BW W live ls m' b' i t) (vB : B mBase = m') (bB : m' < 2 ^ (64 * g.n))
    (iB : (m' * W sInv + 1) % 2 ^ 32 = 0) (pB : 0 < m') (gB : B mG = b' * 2 ^ (64 * g.n) % m')
    {tr ur : List Leak} {sf tf : State}
    (es : Exec isa (VG.Impl.Rsa.X86.RecoverRt.tableStep i) s tr sf)
    (et : Exec isa (VG.Impl.Rsa.X86.RecoverRt.tableStep i) t ur tf) : tr = ur := by
  have pre₁ := h.mulPre L hG hB hI vA bA iA pA gA hi
  have pre₂ := j.mulPre L hG hB hI vB bB iB pB gB hi
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mXm_mXm_mGCheck
        ⟨_, clrTop_mXmCheck⟩ _ _ _ _ _ _ ⟨pre₁, pre₂⟩ e1 f1).1
      obtain ⟨_, _, _, _, _, _, _, _, h₁, mr₁, ha₁, hb₁, hA₁, hB₁, hl₁, hlW₁⟩ := pre₁
      obtain ⟨_, _, _, _, _, _, _, _, h₂, mr₂, ha₂, hb₂, hA₂, hB₂, hl₂, hlW₂⟩ := pre₂
      obtain ⟨_, hu, _⟩ := wp_result (h₁.mmul mr₁ (by decide) (by decide) (by decide) (by decide) ha₁ hb₁
        hA₁ hB₁ hl₁ hlW₁) e1
      obtain ⟨_, hv, _⟩ := wp_result (h₂.mmul mr₂ (by decide) (by decide) (by decide) (by decide) ha₂ hb₂
        hA₂ hB₂ hl₂ hlW₂) f1
      have eq2 := pub_trace pg (tableCopyCheck i hi) hu hv e2 f2
      rw [eq1, eq2]

end VG.Proof.Rsa.X86.Recover
