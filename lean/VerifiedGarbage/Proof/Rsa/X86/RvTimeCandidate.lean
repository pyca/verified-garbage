module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateData
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowTable

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

/-- A Montgomery product between stages, with each run's correctness. -/
theorem mmul_stage {g : Geo} (pg : PubG g) {o a b : Nat} (ho : MontIndex o) (ha : MontIndex a)
    (hb : MontIndex b) (ho0 : o ≠ mBase)
    (hT : (VG.Taint.check sseTaint τF (.block (VG.Impl.Rsa.X86.RecoverRt.mulArgs o a b)) (.block [])).isSome = true)
    (hC : (VG.Taint.check sseTaint τA (.block (VG.Impl.Rsa.X86.RecoverRt.clrTop o))
      (VG.Taint.hintOf sseTaint τA (.block (VG.Impl.Rsa.X86.RecoverRt.clrTop o)))).isSome = true)
    {P Q P' Q' : State → Prop} (hP : ∀ s, P s → MulPre g o a b s) (hQ : ∀ t, Q t → MulPre g o a b t)
    (left : ∀ s, P s → WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) s P')
    (right : ∀ t, Q t → WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) t Q') :
    RelCT isa (fun s t => P s ∧ Q t) (VG.Impl.Rsa.X86.RecoverRt.mmul o a b) (fun s t => P' s ∧ Q' t) :=
  stage_relCT ((mmul_relCT pg ho ha hb ho0 hT ⟨_, hC⟩).mono (fun s t h => ⟨hP s h.1, hQ t h.2⟩)
    fun _ _ h => h) left right

/-- `candMont_ok`'s product: its precondition. -/
theorem candMont_pre {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) {s : State}
    (h : C.Align (alignShifts g eLen dLen) s) : MulPre g mG mG mR2 s := by
  have positive : 0 < m := by have := C.large; omega_arith
  unfold CandidateData.Align AI at h
  have mr := h.montReady (m := m) (by simp [liveExp]) (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY), upd_ne _ _ (by decide : mBase ≠ mG)] using C.value)
    C.bound (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using C.inverse)
  exact ⟨_, _, _, _, _, _, _, _, h, mr, by simp [liveExp], by simp [liveExp],
    by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self] using C.baseBound,
    by simpa only [upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), C.r2] using
      Nat.mod_lt (2 ^ (128 * g.n)) positive, by decide, by decide⟩

theorem tableCopyCheck (i : Nat) (hi : i < 14) :
    (VG.Taint.check sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy VG.Impl.Rsa.X86.RecoverRt.nar (i + 2) mXm)
      (VG.Taint.hintOf sseTaint τA (VG.Impl.Rsa.X86.KeyRt.copy VG.Impl.Rsa.X86.RecoverRt.nar (i + 2) mXm))).isSome =
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
    simp only [tableA, show ¬ j < k by omega_arith, ↓reduceIte]
  have notX (j : Nat) (hj : j ∈ live) : j ≠ mXm := fun e => L.xm (e ▸ hj)
  unfold TI at h
  have mr := h.montReady (m := m) (by simp [hB]) hI
    (by rw [upd_ne _ _ (by decide), aboveA _ hB _ (by omega_arith)]; exact value) bound inverse
  refine ⟨_, _, _, _, _, _, _, _, h, mr, by simp, by simp [hG],
    by rw [upd_self]; exact Nat.mod_lt _ positive,
    by rw [upd_ne _ _ (by decide), aboveA _ hG _ (by omega_arith), base]; exact Nat.mod_lt _ positive, ?_, by decide⟩
  intro j hj
  simp only [List.mem_cons, List.mem_append, List.mem_range] at hj
  rcases hj with e | lo | hi
  · exact .inl e
  · right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mXm mAcc; omega_arith
  · have := L.above j hi
    have := notX j hi
    right; simp only [montWrites, List.mem_cons, List.not_mem_nil, or_false]; unfold mAcc; omega_arith

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

section
variable {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)

/-- The facts the table's construction needs of a candidate's Montgomery form. -/
theorem CandidateData.montFacts :
    candMontA C.A C.V g.n m mBase = m ∧ candMontA C.A C.V g.n m aO = 2 ^ (64 * g.n) % m ∧
      candMontA C.A C.V g.n m mG = (C.V sCand + 2) * 2 ^ (64 * g.n) % m ∧
      (m * upd C.V sCnt 0 sInv + 1) % 2 ^ 32 = 0 := by
  refine ⟨?_, ?_, ?_, by rw [upd_ne _ _ (by decide)]; exact C.inverse⟩
  · simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact C.value
  · simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact C.one
  · simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_self]

theorem tableSteps_trace (pg : PubG g) :
    ∀ k ≤ 14, ∀ s t, TI g C.s0 (candMontA C.A C.V g.n m) (upd C.AW wRc (alignedExp g (C.AW wR) eLen dLen))
        (upd C.V sCnt 0) liveExp slotsExp m (C.V sCand + 2) 0 s →
      TI g D.s0 (candMontA D.A D.V g.n m) (upd D.AW wRc (alignedExp g (D.AW wR) eLen dLen))
        (upd D.V sCnt 0) liveExp slotsExp m (D.V sCand + 2) 0 t →
      ∀ {tr ur : List Leak} {sf tf : State},
        Exec isa (VG.Impl.Rsa.X86.RecoverRt.tableSteps k) s tr sf →
        Exec isa (VG.Impl.Rsa.X86.RecoverRt.tableSteps k) t ur tf → tr = ur := by
  have positive : 0 < m := by have := C.large; omega_arith
  obtain ⟨vC, oC, bC, iC⟩ := C.montFacts
  obtain ⟨vD, oD, bD, iD⟩ := D.montFacts
  intro k hk
  induction k with
  | zero =>
    intro s t hs ht tr ur sf tf es et
    unfold TI at hs ht
    exact pub_trace pg nilCheck hs ht es et
  | succ k ih =>
    intro s t hs ht tr ur sf tf es et
    cases es with
    | @seq _ _ _ u _ _ _ e1 e2 =>
      cases et with
      | @seq _ _ _ v _ _ _ f1 f2 =>
        have eq1 := ih (by omega_arith) s t hs ht e1 f1
        have hu := wp_result (tableSteps_ok liveExp_table (by decide) (by decide) (by decide) vC C.bound iC
          C.odd positive bC k (by omega_arith) s hs) e1
        have hv := wp_result (tableSteps_ok liveExp_table (by decide) (by decide) (by decide) vD C.bound iD
          D.odd positive bD k (by omega_arith) t ht) f1
        have eq2 := tableStep_trace pg (by omega_arith) liveExp_table (by decide) (by decide) (by decide)
          hu vC C.bound iC positive bC hv vD C.bound iD positive bD e2 f2
        rw [eq1, eq2]

theorem table_relCT (pg : PubG g) :
    RelCT isa (fun s t => C.Mont s ∧ D.Mont t) VG.Impl.Rsa.X86.RecoverRt.table
      (fun s t => C.Table s ∧ D.Table t) := by
  have positive : 0 < m := by have := C.large; omega_arith
  obtain ⟨_, oC, bC, _⟩ := C.montFacts
  obtain ⟨_, oD, bD, _⟩ := D.montFacts
  refine stage_relCT (fun s t _ _ _ _ ⟨hs, ht⟩ es et => ?_)
    (fun s hs => candTable_ok hs C.value C.bound C.inverse C.odd C.one positive)
    (fun t ht => candTable_ok ht D.value D.bound D.inverse D.odd D.one positive)
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := pub_trace pg tableStartCheck hs ht e1 f1
      have hu := wp_result (tableInit_ok hs liveExp_table (by decide) (by decide) oC bC) e1
      have hv := wp_result (tableInit_ok ht liveExp_table (by decide) (by decide) oD bD) f1
      have eq2 := tableSteps_trace C D pg 14 (by decide) u v hu hv e2 f2
      exact ⟨by rw [eq1, eq2], trivial⟩

/-- The window loop's facts of a candidate. -/
theorem CandidateData.windowFacts :
    (∀ j < 16, tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16 j =
      (C.V sCand + 2) ^ j * 2 ^ (64 * g.n) % m) ∧
    tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16 mBase = m := by
  refine ⟨fun j hj => by simp only [tableA, hj, ↓reduceIte], ?_⟩
  simp only [tableA, show ¬ mBase < 16 by decide, ↓reduceIte, candMontA]
  rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact C.value

end

theorem windowBody_trace {g : Geo} (pg : PubG g) {s0 t0 s t : State} {T T' AW AW' V V' : Nat → Nat}
    {m b b' E E' c i : Nat}
    (h : WI g s0 T AW V m b E c i s) (tA : ∀ j < 16, T j = b ^ j * 2 ^ (64 * g.n) % m) (vA : T mBase = m)
    (iA : (m * V sInv + 1) % 2 ^ 32 = 0)
    (j : WI g t0 T' AW' V' m b' E' c i t) (tB : ∀ j < 16, T' j = b' ^ j * 2 ^ (64 * g.n) % m)
    (vB : T' mBase = m) (iB : (m * V' sInv + 1) % 2 ^ 32 = 0)
    (bound : m < 2 ^ (64 * g.n)) (odd : m % 2 = 1) (positive : 0 < m)
    {tr ur : List Leak} {sf tf : State}
    (es : Exec isa VG.Impl.Rsa.X86.RecoverRt.windowBody s tr sf)
    (et : Exec isa VG.Impl.Rsa.X86.RecoverRt.windowBody t ur tf) : tr = ur := by
  have hP : 0 < 2 ^ (32 * g.W) := Nat.two_pow_pos _
  have vbA : ∀ y, upd T mY y mBase = m := fun y => by rw [upd_ne _ _ (by decide)]; exact vA
  have vbB : ∀ y, upd T' mY y mBase = m := fun y => by rw [upd_ne _ _ (by decide)]; exact vB
  have viA : (m * upd V sCnt (c - i) sInv + 1) % 2 ^ 32 = 0 := by rw [upd_ne _ _ (by decide)]; exact iA
  have viB : (m * upd V' sCnt (c - i) sInv + 1) % 2 ^ 32 = 0 := by rw [upd_ne _ _ (by decide)]; exact iB
  unfold WI at h j
  have sq := fun {s' t' : State} {tr' ur' : List Leak} {sf' tf' : State} (p₁ : MulPre g mY mY mY s')
      (p₂ : MulPre g mY mY mY t') (e : Exec isa (VG.Impl.Rsa.X86.RecoverRt.mmul mY mY mY) s' tr' sf')
      (f : Exec isa (VG.Impl.Rsa.X86.RecoverRt.mmul mY mY mY) t' ur' tf') =>
    (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mY_mY_mYCheck
      ⟨_, clrTop_mYCheck⟩ _ _ _ _ _ _ ⟨p₁, p₂⟩ e f).1
  cases es with
  | @seq _ _ _ s1 _ _ _ e1 er =>
  cases et with
  | @seq _ _ _ t1 _ _ _ f1 fr =>
  have q1 := sq (h.mulYPre (by decide) (by decide) (by decide) (by decide) (vbA _) bound viA positive
    liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) (j.mulYPre (by decide) (by decide) (by decide) (by decide)
    (vbB _) bound viB positive liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) e1 f1
  have h1 := wp_result (h.squareY (by decide) (by decide) (by decide) (vbA _) bound viA odd positive
    liveWin_apart (upd_self _ _ _)) e1
  have j1 := wp_result (j.squareY (by decide) (by decide) (by decide) (vbB _) bound viB odd positive
    liveWin_apart (upd_self _ _ _)) f1
  simp only [upd_twice] at h1 j1
  cases er with
  | @seq _ _ _ s2 _ _ _ e2 er =>
  cases fr with
  | @seq _ _ _ t2 _ _ _ f2 fr =>
  have q2 := sq (h1.mulYPre (by decide) (by decide) (by decide) (by decide) (vbA _) bound viA positive
    liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) (j1.mulYPre (by decide) (by decide) (by decide) (by decide)
    (vbB _) bound viB positive liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) e2 f2
  have h2 := wp_result (h1.squareY (by decide) (by decide) (by decide) (vbA _) bound viA odd positive
    liveWin_apart (upd_self _ _ _)) e2
  have j2 := wp_result (j1.squareY (by decide) (by decide) (by decide) (vbB _) bound viB odd positive
    liveWin_apart (upd_self _ _ _)) f2
  simp only [upd_twice] at h2 j2
  cases er with
  | @seq _ _ _ s3 _ _ _ e3 er =>
  cases fr with
  | @seq _ _ _ t3 _ _ _ f3 fr =>
  have q3 := sq (h2.mulYPre (by decide) (by decide) (by decide) (by decide) (vbA _) bound viA positive
    liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) (j2.mulYPre (by decide) (by decide) (by decide) (by decide)
    (vbB _) bound viB positive liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) e3 f3
  have h3 := wp_result (h2.squareY (by decide) (by decide) (by decide) (vbA _) bound viA odd positive
    liveWin_apart (upd_self _ _ _)) e3
  have j3 := wp_result (j2.squareY (by decide) (by decide) (by decide) (vbB _) bound viB odd positive
    liveWin_apart (upd_self _ _ _)) f3
  simp only [upd_twice] at h3 j3
  cases er with
  | @seq _ _ _ s4 _ _ _ e4 er =>
  cases fr with
  | @seq _ _ _ t4 _ _ _ f4 fr =>
  have q4 := sq (h3.mulYPre (by decide) (by decide) (by decide) (by decide) (vbA _) bound viA positive
    liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) (j3.mulYPre (by decide) (by decide) (by decide) (by decide)
    (vbB _) bound viB positive liveWin_apart (upd_self _ _ _) (upd_self _ _ _)) e4 f4
  have h4 := wp_result (h3.squareY (by decide) (by decide) (by decide) (vbA _) bound viA odd positive
    liveWin_apart (upd_self _ _ _)) e4
  have j4 := wp_result (j3.squareY (by decide) (by decide) (by decide) (vbB _) bound viB odd positive
    liveWin_apart (upd_self _ _ _)) f4
  simp only [upd_twice] at h4 j4
  cases er with
  | @seq _ _ _ s5 _ _ _ e5 er =>
  cases fr with
  | @seq _ _ _ t5 _ _ _ f5 fr =>
  have q5 := pub_trace pg windowNextCheck h4 j4 e5 f5
  have h5 := wp_result (windowNext_ok h4 (by decide) (by decide) (Nat.mod_lt _ hP)) e5
  have j5 := wp_result (windowNext_ok j4 (by decide) (by decide) (Nat.mod_lt _ hP)) f5
  have smallA : E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W) < 16 := by
    rw [Nat.div_lt_iff_lt_mul hP]
    have := Nat.mod_lt (E * 16 ^ i) hP
    omega_arith
  have smallB : E' * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W) < 16 := by
    rw [Nat.div_lt_iff_lt_mul hP]
    have := Nat.mod_lt (E' * 16 ^ i) hP
    omega_arith
  cases er with
  | @seq _ _ _ s6 _ _ _ e6 e7 =>
  cases fr with
  | @seq _ _ _ t6 _ _ _ f6 f7 =>
  have entryA : upd T mY (((((b ^ (E * 16 ^ i / 2 ^ (32 * g.W))) ^ 2) ^ 2) ^ 2) ^ 2 * 2 ^ (64 * g.n) % m)
      (E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) =
      b ^ (E * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) * 2 ^ (64 * g.n) % m := by
    rw [upd_ne _ _ (by unfold mY; omega_arith)]
    exact tA _ smallA
  have entryB : upd T' mY (((((b' ^ (E' * 16 ^ i / 2 ^ (32 * g.W))) ^ 2) ^ 2) ^ 2) ^ 2 * 2 ^ (64 * g.n) % m)
      (E' * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) =
      b' ^ (E' * 16 ^ i % 2 ^ (32 * g.W) * 16 / 2 ^ (32 * g.W)) * 2 ^ (64 * g.n) % m := by
    rw [upd_ne _ _ (by unfold mY; omega_arith)]
    exact tB _ smallB
  have q6 := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mY_mY_mXmCheck
    ⟨_, clrTop_mYCheck⟩ _ _ _ _ _ _
    ⟨h5.mulYPre (b := mXm) (by decide) (by decide) (by decide) (by decide)
      (by rw [upd_ne _ _ (by decide)]; exact vbA _) bound (by rw [upd_ne _ _ (by decide)]; exact viA) positive
      (by decide) (by rw [upd_ne _ _ (by decide), upd_self]) (by rw [upd_self]; exact entryA),
     j5.mulYPre (b := mXm) (by decide) (by decide) (by decide) (by decide)
      (by rw [upd_ne _ _ (by decide)]; exact vbB _) bound (by rw [upd_ne _ _ (by decide)]; exact viB) positive
      (by decide) (by rw [upd_ne _ _ (by decide), upd_self]) (by rw [upd_self]; exact entryB)⟩ e6 f6).1
  have h6 := wp_result (h5.mulY (b := mXm) (by decide) (by decide) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide)]; exact vbA _) bound
    (by rw [upd_ne _ _ (by decide)]; exact viA) odd positive (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self]) (by rw [upd_self]; exact entryA)) e6
  have j6 := wp_result (j5.mulY (b := mXm) (by decide) (by decide) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide)]; exact vbB _) bound
    (by rw [upd_ne _ _ (by decide)]; exact viB) odd positive (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self]) (by rw [upd_self]; exact entryB)) f6
  have q7 := pub_trace pg cntNextCheck h6 j6 e7 f7
  rw [q1, q2, q3, q4, q5, q6, q7]

theorem candExp_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen) (pg : PubG g) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) VG.Impl.Rsa.X86.RecoverRt.candExp
      (fun s t => C.Exp s ∧ D.Exp t) := by
  have positive : 0 < m := by have := C.large; omega_arith
  have shifts : ∀ {s : State} {k : Nat}, C.Align k s → alignShifts g eLen dLen < 2 ^ 32 :=
    fun hs => by have := geo_wide g (KS.upper hs); unfold alignShifts; omega_arith
  have shifts' : ∀ {s : State} {k : Nat}, D.Align k s → alignShifts g eLen dLen < 2 ^ 32 :=
    fun hs => by have := geo_wide g (KS.upper hs); unfold alignShifts; omega_arith
  unfold VG.Impl.Rsa.X86.RecoverRt.candExp
  simp only [seqs]
  refine VG.RelCT.seq (R := fun s t => C.Align 0 s ∧ D.Align 0 t)
    (pub_relCT (P := C.Start) (Q := D.Start) (P' := C.Align 0) (Q' := D.Align 0) pg alignStartCheck
      (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht)
      (fun s hs => alignStart_ok hs C.zero C.candidate C.ae C.ad C.wide C.rb)
      (fun t ht => alignStart_ok ht D.zero D.candidate D.ae D.ad D.wide D.rb)) ?_
  refine VG.RelCT.seq (R := fun s t => C.Align (alignShifts g eLen dLen) s ∧
      D.Align (alignShifts g eLen dLen) t)
    (fixedLoop_relCT (body := VG.Impl.Rsa.X86.RecoverRt.alignBody) (fun k s => C.Align k s)
      (fun k t => D.Align k t) (by unfold alignShifts; have := C.wide; omega_arith)
      (fun _ _ _ _ _ _ _ _ ⟨hs, ht⟩ es et =>
        ⟨by unfold CandidateData.Align AI at hs ht; exact pub_trace pg alignBodyCheck hs ht es et, trivial⟩)
      (fun k s hk hs => alignBody_ok hs hk (shifts hs))
      (fun k t hk ht => alignBody_ok ht hk (shifts' ht))) ?_
  refine VG.RelCT.seq (R := fun s t => C.Mont s ∧ D.Mont t)
    (mmul_stage (P := C.Align (alignShifts g eLen dLen)) (Q := D.Align (alignShifts g eLen dLen))
      (P' := C.Mont) (Q' := D.Mont)
      pg (by decide) (by decide) (by decide) (by decide) mulArgs_mG_mG_mR2Check clrTop_mGCheck
      (fun s hs => candMont_pre C hs) (fun t ht => candMont_pre D ht)
      (fun s hs => candMont_ok hs C.value C.bound C.inverse C.odd C.r2 C.baseBound C.wide C.rb)
      (fun t ht => candMont_ok ht D.value D.bound D.inverse D.odd D.r2 D.baseBound D.wide D.rb)) ?_
  refine VG.RelCT.seq (R := fun s t => C.Table s ∧ D.Table t) (table_relCT C D pg) ?_
  refine VG.RelCT.seq (R := fun s t => C.Window 0 s ∧ D.Window 0 t)
    (pub_relCT (P := C.Table) (Q := D.Table) (P' := C.Window 0) (Q' := D.Window 0) pg windowCountCheck
      (fun _ hs => KS.stage hs) (fun _ ht => KS.stage ht)
      (fun s hs => tableStart_ok hs C.one C.ae C.ad C.wide C.rb)
      (fun t ht => tableStart_ok ht D.one D.ae D.ad D.wide D.rb)) ?_
  obtain ⟨tC, vC⟩ := C.windowFacts
  obtain ⟨tD, vD⟩ := D.windowFacts
  refine (fixedLoop_relCT (body := VG.Impl.Rsa.X86.RecoverRt.windowBody) (fun k s => C.Window k s)
      (fun k t => D.Window k t) (by have := C.count; omega_arith)
      (fun _ _ _ _ _ _ _ _ ⟨hs, ht⟩ es et =>
        ⟨windowBody_trace pg hs tC vC C.inverse ht tD vD D.inverse C.bound C.odd positive es et, trivial⟩)
      (fun k s hk hs => windowBody_ok hs tC vC C.bound C.inverse C.odd positive hk (by have := C.limit; omega_arith))
      (fun k t hk ht => windowBody_ok ht tD vD D.bound D.inverse D.odd positive hk
        (by have := D.limit; omega_arith))).mono
    (fun s t h => h) (fun s t ⟨hs, ht⟩ => ⟨windows_done hs C.wide, windows_done ht D.wide⟩)

end VG.Proof.Rsa.X86.Recover
