import VerifiedGarbage.Proof.Blowfish.AArch64.Copy

/-!
# The batches of sixteen blocks

While at least sixteen blocks are left, a batch runs on the next sixteen
in place (`wide_ok`).
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the batches may assume of the state they start in: the schedule
readable, the `n` blocks of data and the working space writable, apart from
each other, and the constants in `c64` and `c128`. -/
structure Env (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 4168⟩]
  wr : s.wr = [⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 256⟩]
  keyData : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
  keyBuf : (⟨s.gpr .x0, 4168⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  dataBuf : (⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩
  fit : (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  consts : Consts s

/-- A region disjoint from a nonempty one does not cover the whole address space. -/
theorem len_lt_of_disjoint {r₁ r₂ : Region} (h : r₁.Disjoint r₂) (h2 : 0 < r₂.len) : r₁.len < 2 ^ 64 := by
  by_contra hc
  refine h r₂.base ?_ ?_
  · simp only [Region.Contains]; have := (r₂.base - r₁.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self]; simp; omega

theorem Env.len {s : State} (E : Env s) : 8 * (s.gpr .x2).toNat < 2 ^ 64 :=
  len_lt_of_disjoint E.dataBuf (by simp)

theorem Env.sched {s : State} (E : Env s) : SchedIn s .x0 := by
  intro off n h
  rw [E.rd]
  exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by omega)⟩

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

theorem blockAt_eq_of_readW {m m' : Mem} {p p' : Addr} (h : m'.readW p' 64 = m.readW p 64) :
    blockAt m' p' = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  rw [← Mem.extractLsb'_read m' p' (n := 8) hi, ← Mem.extractLsb'_read m p (n := 8) hi]
  have e : ∀ (m : Mem) (p : Addr), m.read p 8 = m.readW p 64 := fun m p => by
    simp only [Mem.readW]; rfl
  rw [e, e, h]

theorem eval_zero (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 m ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this
      simp at this; omega
    change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h0]

theorem lsr4 (m : Nat) (hm : 8 * m < 2 ^ 64) :
    BitVec.ofNat 64 m >>> 4 = BitVec.ofNat 64 (m / 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The batches of sixteen blocks -/

/-- The registers the batches change. -/
def WideRegs (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8

/-- `m` blocks left, a multiple of sixteen fewer than `n`, and at least sixteen. -/
structure WideInv (up : Bool) (s₀ : State) (n m : Nat) (s : State) : Prop where
  ge : 16 ≤ m
  le : m ≤ n
  mod : m % 16 = n % 16
  x2 : s.gpr .x2 = BitVec.ofNat 64 m
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - m)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : ∀ r, r ∉ roundRegs → s.v r = s₀.v r
  done : ∀ b < n - m, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - m)⟩] s₀.mem s.mem

structure WidePost (up : Bool) (s₀ : State) (n : Nat) (s : State) : Prop where
  x2 : s.gpr .x2 = BitVec.ofNat 64 (n % 16)
  x1 : s.gpr .x1 = wAt (s₀.gpr .x1) (n - n % 16)
  gpr : ∀ r, WideRegs r → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  v : ∀ r, r ∉ roundRegs → s.v r = s₀.v r
  done : ∀ b < n - n % 16, blockAt s.mem (wAt (s₀.gpr .x1) b) =
    blockOut (scheduleAt s₀.mem (s₀.gpr .x0)) up (blockAt s₀.mem (wAt (s₀.gpr .x1) b))
  frame : Frame [⟨s₀.gpr .x1, 8 * (n - n % 16)⟩] s₀.mem s.mem

theorem loop_ok (up : Bool) {s₀ : State} (E : Env s₀) {n : Nat}
    (hn : (s₀.gpr .x2).toNat = n) (m : Nat) (s : State) (hs : WideInv up s₀ n m s) :
    WP isa (.loop (.seq (.block [.addImm .x .x4 .x1 0]) (.seq (batch up)
        (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 16, wholeLeft])))
      (.nonzero .x .x8)) s (WidePost up s₀ n) := by
  refine WP.loop (M := isa) (WideInv up s₀ n) ?_ m s hs
  intro m s h
  have hl := E.len
  have hfit := E.fit
  rw [hn] at hl hfit
  have hge := h.ge
  have hle := h.le
  let D := s₀.gpr .x1
  let S := s₀.gpr .x0
  have g := h.gpr
  have hx0 : s.gpr .x0 = S := g _ (by simp [WideRegs])
  apply WP.seq
  let s₁ := s.write .x .x4 (s.read .x .x1 + BitVec.ofNat _ 0)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_addImm_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have g₁ : ∀ r, r ≠ .x4 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have x4₁ : s₁.gpr .x4 = wAt D (n - m) := by simp [s₁, State.write, State.read, h.x1]; rfl
  have dataR : (⟨D, 8 * n⟩ : Region) ∈ s₁.wr := by
    show _ ∈ s.wr; rw [h.wr, E.wr, hn]; exact List.mem_cons_self
  have hW₁ : ∀ k < 8, InRegions s₁.wr (s₁.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk =>
    ⟨_, dataR, by rw [x4₁, wAt, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have hS₁ : SchedIn s₁ .x0 := fun off n' h' => by
    rw [g₁ _ (by decide), hx0]
    show InRegions (s.rd ++ s.wr) _ n'
    rw [h.rd, h.wr]; exact E.sched off n' h'
  have hc₁ : Consts s₁ := ⟨fun e he => by rw [show s₁.v = s.v from rfl, h.v _ (by decide)]; exact E.consts.1 e he,
    fun e he => by rw [show s₁.v = s.v from rfl, h.v _ (by decide)]; exact E.consts.2 e he⟩
  apply WP.seq
  apply WP.mono (batch_ok up hS₁ hc₁ hW₁)
  intro s₂ q
  have g₂ : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x4 → s₂.gpr r = s.gpr r :=
    fun r a b c e => (q.gpr r a b c).trans (g₁ r e)
  let s₃ := s₂.write .x .x1 (s₂.read .x .x1 + BitVec.ofNat _ 128)
  let s₄ := s₃.write .x .x2 (s₃.read .x .x2 - BitVec.ofNat _ 16)
  let s₅ := s₄.write .x .x8 (s₄.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, wholeLeft, exec_lsr_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  have x2₅ : s₅.gpr .x2 = BitVec.ofNat 64 (m - 16) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.x2,
      show (BitVec.ofNat 64 16) = BitVec.ofNat 64 16 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) hge]
  have x1₅ : s₅.gpr .x1 = wAt D (n - (m - 16)) := by
    simp only [s₅, s₄, s₃, State.write, State.read, BitVec.setWidth_eq, reduceCtorEq, ite_false,
      ite_true]
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h.x1, wAt, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    exact congrArg (fun i => D + BitVec.ofNat 64 i) (by omega)
  have x8₅ : s₅.gpr .x8 = BitVec.ofNat 64 ((m - 16) / 16) := by
    simp only [s₅, State.write, State.read, BitVec.setWidth_eq, ite_true]
    have : s₄.gpr .x2 = s₅.gpr .x2 := by simp [s₅, State.write]
    rw [this, x2₅, lsr4 _ (by omega)]
  have g₅ : ∀ r, WideRegs r → s₅.gpr r = s₀.gpr r := by
    intro r ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩
    simp only [s₅, s₄, s₃, State.write, BitVec.setWidth_eq, a₇, a₂, a₁, ite_false]
    rw [g₂ r a₄ a₅ a₆ a₃, g r ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩]
  have mem₅ : s₅.mem = s₂.mem := rfl
  have frame' : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s₅.mem := by
    have f₁ : Frame [⟨D, 8 * (n - (m - 16))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
    have f₂ : Frame [⟨D, 8 * (n - (m - 16))⟩] s.mem s₂.mem := q.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, by
        show Region.Sub ⟨s₁.gpr .x4, 128⟩ _
        rw [x4₁]; exact Offset.sub_base _ (by omega)⟩
    rw [mem₅]; exact f₁.trans f₂
  have done' : ∀ b < n - (m - 16), blockAt s₅.mem (wAt D b) =
      blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b)) := by
    intro b hb
    rw [mem₅]
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame q.frame fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      show Region.Disjoint _ ⟨s₁.gpr .x4, 128⟩
      rw [x4₁]
      exact Offset.disjoint D (Or.inl (by omega)) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega⟩
      have e := q.out j (by omega)
      rw [x4₁] at e
      rw [show wAt D (n - m + j) = wAt D (n - m) + BitVec.ofNat 64 (8 * j) by rw [← wAt_wAt], e,
        g₁ _ (by decide), hx0]
      have hK : scheduleAt s.mem S = scheduleAt s₀.mem S :=
        scheduleAt_eq_of_frame S h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hn ▸ E.keyData).sub_right (Region.sub_prefix (by omega))
      have hB : blockAt s.mem (wAt D (n - m + j)) = blockAt s₀.mem (wAt D (n - m + j)) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (by omega) (by omega)
      show blockOut (scheduleAt s₁.mem S) up (blockAt s₁.mem _) = _
      rw [show s₁.mem = s.mem from rfl, hK, show wAt D (n - m) + BitVec.ofNat 64 (8 * j) = wAt D (n - m + j)
        by rw [← wAt_wAt], hB]
  have wr₅ : s₅.wr = s₀.wr := q.wr.trans h.wr
  have rd₅ : s₅.rd = s₀.rd := q.rd.trans h.rd
  have sp₅ : s₅.sp = s₀.sp := q.sp.trans h.sp
  have v₅ : ∀ r, r ∉ roundRegs → s₅.v r = s₀.v r := fun r hr => (q.v r hr).trans (h.v r hr)
  have flag := eval_nonzero s₅ .x8 x8₅ (by omega)
  by_cases hend : m - 16 < 16
  · left
    have e : m - 16 = n % 16 := by have := h.mod; omega
    refine ⟨by rw [flag]; simp; omega, by rw [x2₅, e], by rw [x1₅, e], g₅, rd₅, wr₅, sp₅, v₅,
      by rw [← e]; exact done', by rw [← e]; exact frame'⟩
  · right
    refine ⟨by rw [flag]; simp; omega, m - 16, by omega,
      ⟨by omega, by omega, by have := h.mod; omega, x2₅, x1₅, g₅, rd₅, wr₅, sp₅, v₅, done', frame'⟩⟩

theorem wide_ok (up : Bool) {s : State} (E : Env s) :
    WP isa (wide up) s (WidePost up s (s.gpr .x2).toNat) := by
  let n := (s.gpr .x2).toNat
  have hl := E.len
  rw [wide]
  apply WP.seq
  let s₁ := s.write .x .x8 (s.read .x .x2 >>> 4)
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, wholeLeft, exec_lsr_x (by decide), runStep_some,
    runBlock_nil], ?_⟩
  have x8₁ : s₁.gpr .x8 = BitVec.ofNat 64 (n / 16) := by
    simp only [s₁, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [show s.gpr .x2 = BitVec.ofNat 64 n by simp [n], lsr4 _ hl]
  have g₁ : ∀ r, r ≠ .x8 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  apply WP.ite _ (eval_zero s₁ .x8 x8₁ (by omega))
  · intro hz
    have hz' : n < 16 := by simp at hz; omega
    apply WP.block_nil
    have e : n % 16 = n := Nat.mod_eq_of_lt hz'
    refine ⟨?_, ?_, fun r hr => g₁ r hr.2.2.2.2.2.2, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega, ?_⟩
    · rw [g₁ _ (by decide), e]; simp [n]
    · rw [g₁ _ (by decide), e, Nat.sub_self]; simp [wAt]
    · rw [e, Nat.sub_self]; exact Frame.refl _ _
  · intro hnz
    have hge : 16 ≤ n := by simp at hnz; omega
    have E₁ : Env s₁ := by
      have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
      have h2 := g₁ .x2 (by decide); have h3 := g₁ .x3 (by decide)
      exact ⟨by rw [h0]; exact E.rd, by rw [h1, h2, h3]; exact E.wr,
        by rw [h0, h1, h2]; exact E.keyData, by rw [h0, h3]; exact E.keyBuf,
        by rw [h1, h2, h3]; exact E.dataBuf, by rw [h1, h2]; exact E.fit, E.consts⟩
    have hn₁ : (s₁.gpr .x2).toNat = n := by rw [g₁ _ (by decide)]
    have I : WideInv up s₁ n n s₁ := ⟨hge, Nat.le_refl _, rfl, by rw [g₁ _ (by decide)]; simp [n],
      by simp [wAt], fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => by omega,
      by rw [Nat.sub_self]; exact Frame.refl _ _⟩
    apply WP.mono (loop_ok up E₁ hn₁ n s₁ I)
    intro s₂ p
    have h0 := g₁ .x0 (by decide); have h1 := g₁ .x1 (by decide)
    refine ⟨p.x2, by rw [p.x1, h1], fun r hr => (p.gpr r hr).trans (g₁ r hr.2.2.2.2.2.2), p.rd, p.wr,
      p.sp, p.v, fun b hb => ?_, by rw [← h1]; exact p.frame⟩
    rw [← h1, p.done b hb, h0, h1]; rfl

end VG.Proof.Blowfish.AArch64
