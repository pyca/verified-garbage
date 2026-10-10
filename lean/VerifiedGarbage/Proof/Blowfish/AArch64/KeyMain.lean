import VerifiedGarbage.Proof.Blowfish.AArch64.KeySetup
import VerifiedGarbage.Proof.Blowfish.AArch64.KeyLoop

/-!
# The key expansion function

`q8`–`q15` are saved in the working space, the constants set, the initial
S-boxes copied from the table, the P-array keyed, the 521 encryptions run
and `q8`–`q15` restored (`expandKey_correct`).
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

/-! ## The table -/

/-! ## Keeping `d8`–`d15` -/

/-- The low half of a vector register. -/
abbrev low (t : State) (r : VReg) : BitVec 64 := (t.v r).extractLsb' 0 64

theorem saveLow_eq : saveLow = [.umov .x .x0 .v8 0, .umov .x .x1 .v9 0, .umov .x .x3 .v10 0,
    .umov .x .x4 .v11 0, .umov .x .x11 .v12 0, .umov .x .x16 .v13 0, .umov .x .x17 .v14 0,
    .vop (.mov .v27 .v15)] := rfl

theorem restoreLow_eq : restoreLow = [.vop (.dup .d2 .v8 .x0), .vop (.dup .d2 .v9 .x1),
    .vop (.dup .d2 .v10 .x3), .vop (.dup .d2 .v11 .x4), .vop (.dup .d2 .v12 .x11),
    .vop (.dup .d2 .v13 .x16), .vop (.dup .d2 .v14 .x17), .vop (.mov .v15 .v27)] := rfl

theorem exec_umov_x0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .x d n 0) s = some (s.write .x d (low s n)) := rfl

theorem exec_dup_d2 (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem low_ofVDwords (x : BitVec 64) : (ofVDwords x x).extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

/-- The registers `saveLow` writes. -/
def keepGprs : List Reg := [.x0, .x1, .x3, .x4, .x11, .x16, .x17]

theorem saveLow_run (t : State) :
    ∃ t', runBlock isa saveLow t = some t' ∧
      t'.gpr .x0 = low t .v8 ∧ t'.gpr .x1 = low t .v9 ∧ t'.gpr .x3 = low t .v10 ∧
      t'.gpr .x4 = low t .v11 ∧ t'.gpr .x11 = low t .v12 ∧ t'.gpr .x16 = low t .v13 ∧
      t'.gpr .x17 = low t .v14 ∧ t'.v .v27 = t.v .v15 ∧
      (∀ r, r ∉ keepGprs → t'.gpr r = t.gpr r) ∧ (∀ r, r ≠ .v27 → t'.v r = t.v r) ∧
      t' = { t with gpr := t'.gpr, v := t'.v } := by
  let t₁ := t.write .x .x0 (low t .v8)
  let t₂ := t₁.write .x .x1 (low t₁ .v9)
  let t₃ := t₂.write .x .x3 (low t₂ .v10)
  let t₄ := t₃.write .x .x4 (low t₃ .v11)
  let t₅ := t₄.write .x .x11 (low t₄ .v12)
  let t₆ := t₅.write .x .x16 (low t₅ .v13)
  let t₇ := t₆.write .x .x17 (low t₆ .v14)
  let t₈ := t₇.setV .v27 (t₇.v .v15)
  refine ⟨t₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun r hr => ?_, fun r hr => ?_, rfl⟩
  · rw [saveLow_eq, runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_umov_x0, runStep_some,
      runBlock_cons, exec_umov_x0, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_nil]
  rotate_right 2
  · simp only [keepGprs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV, gpr_write, hr, ↓reduceIte]
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, v_setV, v_write, hr, ↓reduceIte]
  all_goals simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, gpr_setV, gpr_write, v_write, low,
    BitVec.setWidth_eq, reduceCtorEq, ↓reduceIte]

theorem restoreLow_run (t : State) :
    ∃ t', runBlock isa restoreLow t = some t' ∧
      low t' .v8 = t.gpr .x0 ∧ low t' .v9 = t.gpr .x1 ∧ low t' .v10 = t.gpr .x3 ∧
      low t' .v11 = t.gpr .x4 ∧ low t' .v12 = t.gpr .x11 ∧ low t' .v13 = t.gpr .x16 ∧
      low t' .v14 = t.gpr .x17 ∧ t'.v .v15 = t.v .v27 ∧ t' = { t with v := t'.v } := by
  let t₁ := t.setV .v8 (ofVDwords (t.gpr .x0) (t.gpr .x0))
  let t₂ := t₁.setV .v9 (ofVDwords (t₁.gpr .x1) (t₁.gpr .x1))
  let t₃ := t₂.setV .v10 (ofVDwords (t₂.gpr .x3) (t₂.gpr .x3))
  let t₄ := t₃.setV .v11 (ofVDwords (t₃.gpr .x4) (t₃.gpr .x4))
  let t₅ := t₄.setV .v12 (ofVDwords (t₄.gpr .x11) (t₄.gpr .x11))
  let t₆ := t₅.setV .v13 (ofVDwords (t₅.gpr .x16) (t₅.gpr .x16))
  let t₇ := t₆.setV .v14 (ofVDwords (t₆.gpr .x17) (t₆.gpr .x17))
  let t₈ := t₇.setV .v15 (t₇.v .v27)
  refine ⟨t₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [restoreLow_eq, runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_dup_d2, runStep_some,
      runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_vmov, runStep_some, runBlock_nil]
  rotate_right
  · simp only [t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, State.setV]
  all_goals simp only [low, t₈, t₇, t₆, t₅, t₄, t₃, t₂, t₁, v_setV, gpr_setV, low_ofVDwords, reduceCtorEq,
    ↓reduceIte]

/-! ## The function -/

/-- What the function may assume: the key and the table readable, the
schedule writable, all apart. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .x1).toNat
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.syms initSym, 4168⟩]
  wr : s.wr = [⟨s.gpr .x2, 4168⟩]
  keySch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩
  fitS : (s.gpr .x2).toNat + 4168 ≤ 2 ^ 64
  held : ∀ i < 521, s.mem.readW (s.syms initSym + BitVec.ofNat 64 (8 * i)) 64 =
    Impl.Blowfish.initWords.getD i 0
  fitT : (s.syms initSym).toNat + 4168 ≤ 2 ^ 64
  tSch : (⟨s.syms initSym, 4168⟩ : Region).Disjoint ⟨s.gpr .x2, 4168⟩

theorem expandKey_eq' : Impl.Blowfish.AArch64.expandKey =
    .seq (.block (constants ++ ([.adrSym .x9 initSym, .addImm .x .x12 .x2 0] : List Instr)))
      (.seq copyPlanes (.seq keyP (.seq (.block saveLow) (.seq encryptions (.block restoreLow))))) := rfl

theorem contains_self (a : Addr) (n : Nat) : (⟨a, n⟩ : Region).Contains a n := by
  simp [Region.Contains]

/-- The schedule becomes the key's expansion, and the low halves of
`v8`–`v15` are kept. -/
theorem expandKey_correct {s : State} (P : KeyPre s) :
    WP isa Impl.Blowfish.AArch64.expandKey s (fun s' =>
      scheduleAt s'.mem (s.gpr .x2) = Spec.Blowfish.expandKey (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) ∧
      ∀ r ∈ preservedV, low s' r = low s r) := by
  let K := s.gpr .x0
  let L := (s.gpr .x1).toNat
  let S := s.gpr .x2
  let T := s.syms initSym
  have hL := P.valid
  unfold validKey at hL
  have schW : (⟨S, 4168⟩ : Region) ∈ s.wr := by rw [P.wr]; exact List.mem_cons_self
  have keyR : (⟨K, L⟩ : Region) ∈ s.rd ++ s.wr := by rw [P.rd]; exact List.mem_append_left _ List.mem_cons_self
  have tabR : (⟨T, 4168⟩ : Region) ∈ s.rd ++ s.wr := by
    rw [P.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have kc : ∀ c < L, (⟨K, L⟩ : Region).Contains (K + BitVec.ofNat 64 c) 1 := fun c hc =>
    Offset.contains_base K (by omega) (by omega)
  -- the prologue
  obtain ⟨s₂, r₂, c₂, g₂, m₂, rd₂, wr₂, sp₂, o₂⟩ := constants_run s
  let s₃' := s₂.write .x .x9 (s₂.syms initSym)
  let s₃ := s₃'.write .x .x12 (s₃'.read .x .x2 + BitVec.ofNat _ 0)
  have r₃ : runBlock isa [.adrSym .x9 initSym, .addImm .x .x12 .x2 0] s₂ = some s₃ := by
    rw [runBlock_cons, exec_adrSym, runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some,
      runBlock_nil]
  have sy₂ : s₂.syms = s.syms := by rw [o₂.1]
  have g₃ : ∀ r, r ≠ .x6 → r ≠ .x9 → r ≠ .x12 → s₃.gpr r = s.gpr r := fun r h6 h9 h12 => by
    simp only [s₃, s₃', gpr_write_of_ne _ .x _ h12, gpr_write_of_ne _ .x _ h9, g₂ r h6]
  have m₃ : s₃.mem = s.mem := m₂
  have rd₃ : s₃.rd = s.rd := by rw [show s₃.rd = s₂.rd from rfl, rd₂]
  have wr₃ : s₃.wr = s.wr := by rw [show s₃.wr = s₂.wr from rfl, wr₂]
  have v₃ : ∀ r, r ≠ c64 → r ≠ c128 → s₃.v r = s.v r := fun r h1 h2 => by
    rw [show s₃.v = s₂.v from rfl, o₂.2 r (by simp [h1, h2])]
  have x9₃ : s₃.gpr .x9 = T := by
    simp only [s₃, s₃', gpr_write_of_ne _ .x _ (by decide : Reg.x9 ≠ .x12), gpr_write_self, sy₂]
    rfl
  have x12₃ : s₃.gpr .x12 = S := by
    simp only [s₃, s₃', gpr_write_self, State.read, BitVec.setWidth_eq, BitVec.add_zero,
      gpr_write_of_ne _ .x _ (by decide : Reg.x2 ≠ .x9), g₂ _ (by decide : Reg.x2 ≠ .x6)]
    rfl
  rw [expandKey_eq']
  apply WP.seq
  refine WP.of_runBlock ⟨s₃, cat_run r₂ r₃, ?_⟩
  -- the S-boxes
  have CE : CopyEnv T S s₃ := by
    refine ⟨by rw [rd₃, wr₃]; exact ⟨_, tabR, contains_self _ _⟩, by rw [wr₃]; exact ⟨_, schW, contains_self _ _⟩,
      P.tSch, P.fitT, P.fitS⟩
  apply WP.seq
  refine WP.mono (copyPlanes_run CE x9₃ x12₃) fun u ⟨u₀, hu₀, C⟩ => ?_
  have m₀ : u₀.mem = s.mem := by rw [hu₀]; exact m₃
  have gu : ∀ r, r ≠ .x6 → r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h6 h9 h11 h12 => by
    rw [C.gpr r h9 h11 h12, hu₀, gpr_write_of_ne _ .x _ h11, g₃ r h6 h9 h12]
  have rdu : u.rd = s.rd := by rw [C.rd, hu₀]; exact rd₃
  have wru : u.wr = s.wr := by rw [C.wr, hu₀]; exact wr₃
  have tu : ∀ o < 4168, u.mem (T + BitVec.ofNat 64 o) = s.mem (T + BitVec.ofNat 64 o) := fun o ho => by
    rw [C.frame _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.tSch _ (Offset.contains_base T (by omega) (by omega)) (Region.sub_prefix (by omega) _ hc),
      m₀]
  have ku : bytesAt u.mem K L = bytesAt s.mem K L := by
    rw [bytesAt_frame C.frame fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact P.keySch _ (kc c hc) (Region.sub_prefix (by omega) _ hcon), m₀]
  have su : ∀ o < 4096, u.mem (S + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [C.copied o (by omega), m₀, table_byte P.held (by omega)]
  have vu : ∀ r ∈ preservedV, u.v r = s.v r := fun r hr => by
    rw [C.v r (by simp [preservedV] at hr ⊢; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide),
      hu₀]
    exact v₃ r (by simp [preservedV] at hr; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide)
      (by simp [preservedV] at hr; rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> decide)
  -- the P-array
  have PE : KeyPEnv T S K L u := by
    refine ⟨by omega, by omega, fun c hc => ?_, gu _ (by decide) (by decide) (by decide) (by decide),
      ?_, ?_, ?_, ?_, ?_, P.tSch, fun c hc h => P.keySch _ (kc c hc) h⟩
    · rw [rdu, wru]; exact ⟨_, keyR, kc c hc⟩
    · rw [gu _ (by decide) (by decide) (by decide) (by decide)]; simp [L]
    · rw [C.x9]
    · rw [C.x12]
    · rw [rdu, wru]; exact ⟨_, tabR, contains_self _ _⟩
    · rw [wru]; exact ⟨_, schW, contains_self _ _⟩
  apply WP.seq
  refine WP.mono (keyP_run PE) fun u' KP => ?_
  have hK : scheduleAt u'.mem S = keyed (bytesAt u.mem K L) := by
    refine keyed_of_mem (fun o ho => ?_) (fun i hi => ?_)
    · rw [KP.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base S (d := 4096) (n := 4 * 18) (k := 4096) (by omega) (by omega) _ hc
          (Offset.contains_base S (by omega) (by omega)), su o ho]
    · rw [KP.done i hi, table_P (fun o ho => (tu o ho).trans (table_byte P.held ho)) hi]
  have ev : u'.v = u.v := by rw [KP.eq]
  have wru' : u'.wr = s.wr := by rw [KP.eq]; exact wru
  -- keeping `d8`–`d15`
  obtain ⟨w, rw', w0, w1, w3, w4, w11, w16, w17, w27, wg, wv, we⟩ := saveLow_run u'
  apply WP.seq
  refine WP.of_runBlock ⟨w, rw', ?_⟩
  -- the encryptions
  have EE : EncEnv S w := by
    refine ⟨?_, fun off n h => by rw [we, wru']; exact ⟨_, schW, Offset.contains_base S h (by omega)⟩, ?_⟩
    · rw [wg _ (by decide), KP.gpr _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide)]
    have cv : ∀ r, r = c64 ∨ r = c128 → w.v r = s₂.v r := fun r hr => by
      rw [wv r (by rcases hr with rfl | rfl <;> decide), ev,
        C.v r (by rcases hr with rfl | rfl <;> decide), hu₀]; rfl
    exact ⟨fun e he => by rw [cv _ (.inl rfl)]; exact c₂.1 e he,
      fun e he => by rw [cv _ (.inr rfl)]; exact c₂.2 e he⟩
  have hK' : scheduleAt w.mem S = keyed (bytesAt u.mem K L) := by rw [we]; exact hK
  apply WP.seq
  refine WP.mono (encryptions_run EE hK') fun u'' EI => ?_
  -- the epilogue
  obtain ⟨s', r', l8, l9, l10, l11, l12, l13, l14, l15, e'⟩ := restoreLow_run u''
  refine WP.of_runBlock ⟨s', r', ?_, ?_⟩
  · rw [show s'.mem = u''.mem by rw [e'], EI.sched, ← expandKey_eq, ku]
  · have kg : ∀ r, r ∉ encGprs → u''.gpr r = w.gpr r := EI.gpr
    have lv : ∀ r ∈ preservedV, low u' r = low s r := fun r hr => by
      simp only [low]; rw [ev, vu r hr]
    intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [l8, kg _ (by decide), w0]; exact lv .v8 (by decide)
    · rw [l9, kg _ (by decide), w1]; exact lv .v9 (by decide)
    · rw [l10, kg _ (by decide), w3]; exact lv .v10 (by decide)
    · rw [l11, kg _ (by decide), w4]; exact lv .v11 (by decide)
    · rw [l12, kg _ (by decide), w11]; exact lv .v12 (by decide)
    · rw [l13, kg _ (by decide), w16]; exact lv .v13 (by decide)
    · rw [l14, kg _ (by decide), w17]; exact lv .v14 (by decide)
    · simp only [low]
      rw [l15, EI.v _ (by decide), w27, ev, vu _ (by decide)]

end VG.Proof.Blowfish.AArch64
