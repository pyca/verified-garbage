import VerifiedGarbage.Proof.Seed.AArch64.Copy
import VerifiedGarbage.Proof.Seed.Memory

/-!
# A batch on AArch64

`batch_ok`: a batch encrypts or decrypts the first `min n 16` blocks at
`x1` in place (`n = x2`), with the keys at `x0` (`keysAt`), and moves `x1`
and `x2` past them.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

/-! ## The batch size -/

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.write .x d (s.gpr n)) := by
  rw [movR, exec_addImm_x (by decide), read_x]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.add_zero _)

theorem exec_sub (s : State) (sz : Size) (d n m : Reg) :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem sb_eq : sb = .x5 := rfl

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .x15 = BitVec.ofNat 64 (min (s.gpr .x2).toNat 16) ∧
      (∀ r, r ≠ .x15 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .x .x15 (s.gpr .x2 >>> 4)
  have e₁ : runBlock isa [lsrI .x15 .x2 4] s = some s₁ := by
    rw [runBlock_cons, lsrI, exec_lsr_x (by decide), runStep_some, runBlock_nil, read_x]
  have g₁ : ∀ r, r ≠ .x15 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have hc : isa.eval (.nonzero .x .x15) s₁ = some (decide (16 ≤ (s.gpr .x2).toNat)) := by
    show some (s₁.read .x .x15 != 0) = _
    rw [read_x, gpr_write_self, BitVec.setWidth_eq]
    congr 1
    by_cases h : 16 ≤ (s.gpr .x2).toNat
    · simp only [h, decide_true, bne_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ushiftRight] at this
      simp at this; omega
    · simp only [h, decide_false, bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight]; simp; omega
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite _ hc (fun hb => ?_) (fun hb => ?_)
  · have hge := of_decide_eq_true hb
    let s₂ := s₁.write .x .x15 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega)]; rfl
    · rw [gpr_write_of_ne _ _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    refine WP.of_runBlock ⟨s₁.write .x .x15 (s₁.gpr .x2), by rw [runBlock_cons, exec_movR, runStep_some,
      runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, BitVec.setWidth_eq, g₁ _ (by decide), Nat.min_eq_left (by omega),
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [gpr_write_of_ne _ _ _ hr, g₁ r hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .x3 = s.gpr .x1 ∧ t.gpr .x4 = s.gpr .x5 ∧
      (∀ r, r ≠ .x3 → r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp :=
  ⟨(s.write .x .x3 (s.gpr .x1)).write .x .x4 ((s.write .x .x3 (s.gpr .x1)).gpr .x5),
    by rw [copyStart, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil]; rfl,
    by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => by simp [gpr_write, h1, h2],
    rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

theorem roundsN_congr {k₁ k₂ : Nat → Spec.Seed.Word × Spec.Seed.Word} :
    ∀ (n : Nat) (q : Quad), (∀ j < n, k₁ j = k₂ j) → roundsN k₁ n q = roundsN k₂ n q
  | 0, _, _ => rfl
  | n + 1, q, h => by
    rw [roundsN_succ, roundsN_succ, h n (by omega), roundsN_congr n q fun j hj => h j (by omega)]

theorem crypt_congr {k₁ k₂ : Nat → Spec.Seed.Word × Spec.Seed.Word} (h : ∀ j < 16, k₁ j = k₂ j)
    (b : Spec.Seed.Block) : Spec.Seed.crypt k₁ b = Spec.Seed.crypt k₂ b := by
  rw [crypt_eq, crypt_eq, roundsN_congr 16 _ h]

theorem quad_of_lanes {t : State} {m : Mem} {p : Addr} {b : Nat}
    (h : ∀ w < 4, lv t (arrSlot w) b = bw m p b w) :
    quad t b = decodeQ (Spec.Seed.blockAt m (p + BitVec.ofNat 64 (16 * b))) := by
  rw [decodeQ_blockAt]
  simp only [quad, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), bw,
    Offset.add_ofNat_add_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]
  rfl

theorem encodeSwapped_get (t : State) (b : Nat) {i : Nat} (hi : i < 16) :
    (encodeSwapped (quad t b))[i] = outByte t b i := by
  have hk : ∀ w < 4, (#v[(quad t b).2.2.1, (quad t b).2.2.2, (quad t b).1, (quad t b).2.1] :
      Vector Spec.Seed.Word 4).getD w 0 = lv t (arrSlot ((w + 2) % 4)) b := by
    intro w hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  simp only [encodeSwapped, Vector.getElem_ofFn, outByte]
  rw [hk _ (by omega)]

theorem blockAt_of_bytes {m : Mem} {q : Addr} {v : Spec.Seed.Block}
    (h : ∀ i (hi : i < 16), m (q + BitVec.ofNat 64 i) = v[i]) : Spec.Seed.blockAt m q = v := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact h i hi

/-! ## The batch -/

/-- What a batch needs: the scratch buffer; the batch's blocks writable, and
they and the keys apart from the scratch buffer and each other. -/
structure BatchPre (d : Spec.Seed.Direction) (s : State) : Prop where
  room : Room s
  pos : 1 ≤ (s.gpr .x2).toNat
  data : ∀ b < min (s.gpr .x2).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .x0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .x0) j, 8⟩ ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .x2).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .x0))
        (Spec.Seed.blockAt s.mem (s.gpr .x1 + BitVec.ofNat 64 (16 * b)))
  rsi : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (16 * min (s.gpr .x2).toNat 16)
  rdx : s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (min (s.gpr .x2).toNat 16)
  regs : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .x1, 16 * min (s.gpr .x2).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .x5, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega)

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .x5, 8 * 112⟩
  exact Offset.sub_base _ (by omega)

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .x2).toNat
  let k := min n 16
  let p := s.gpr .x1
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hk16 : k ≤ 16 := by omega
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, x3₂, x4₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have G₂ : ∀ r, r ≠ .x15 → r ≠ .x3 → r ≠ .x4 → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  have x5₂ : s₂.gpr .x5 = s.gpr .x5 := G₂ _ (by decide) (by decide) (by decide)
  have scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, x5₂]
  have arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, x5₂]
  have room₂ : Room s₂ := room_congr h.room x5₂ (by rw [wr₂, wr₁])
  have pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega, ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [x3₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, x4₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  have x5₃ : s₃.gpr .x5 = s.gpr .x5 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans x5₂
  have G₃ : ∀ r ∈ [Reg.x0, .x1, .x2], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x14 ∧ r ≠ .x4 ∧ r ≠ .x15 ∧ r ≠ .x3 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  have rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  have sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  have room₃ : Room s₃ := room_congr h.room x5₃ wr₃
  have f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  have scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, x5₃]
  have keys₃ : KeysOk d s₃ (s₃.gpr .x0) := by
    rw [G₃ .x0 (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  have hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .x0) j = keysAt d s.mem (s.gpr .x0) j := by
    intro j hj
    rw [G₃ .x0 (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    have hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .x0) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hdis.sub_right (arraysR_sub_scratch s)
    simp only [keysAt]
    congr 1
    · exact f₃.readW (contains_prefix (by decide)) hd (by decide)
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
      exact f₃.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega) (by omega)) hd (by decide)
  -- the blocks, in the lanes
  have hq₃ : ∀ b < k, quad s₃ b = decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    refine quad_of_lanes fun w hw => ?_
    rw [i₃.lanes w hw b hb, m₂, m₁]
  -- the rounds
  apply WP.seq
  refine WP.mono (rounds_ok d room₃ keys₃) fun s₄ ⟨q₄, room₄, rd₄, wr₄, sp₄, g₄, f₄⟩ => ?_
  have G₄ : ∀ r ∈ [Reg.x0, .x1, .x2, .x5], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact x5₃
  have hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .x0)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, x3₆, x4₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  have G₆ : ∀ r, r ≠ .x15 → r ≠ .x3 → r ≠ .x4 → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  have x5₆ : s₆.gpr .x5 = s.gpr .x5 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  have x2₄ : s₄.gpr .x2 = s.gpr .x2 := G₄ _ (by simp)
  have x1₄ : s₄.gpr .x1 = p := G₄ _ (by simp)
  have rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  have arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, x5₆]
  have pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room x5₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [x3₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), x1₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, x4₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, x2₄]
  have quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, x5₆, G₄ .x5 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have G₇ : ∀ r, r ≠ .x14 → r ≠ .x4 → r ≠ .x15 → r ≠ .x3 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  have x2₇ : s₇.gpr .x2 = s.gpr .x2 := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans x2₄
  have c₈' : s₈.gpr .x15 = BitVec.ofNat 64 k := by rw [c₈, x2₇]
  have x3₈ : s₈.gpr .x3 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.x3]
  let s₉ := s₈.write .x .x1 (s₈.gpr .x3)
  let s' := s₉.write .x .x2 (s₉.read .x .x2 - s₉.read .x .x15)
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub,
    runStep_some, runBlock_nil], ?_⟩
  have g' : ∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  have x2₉ : s₉.gpr .x2 = s.gpr .x2 := by rw [gpr_write_of_ne _ _ _ (by decide), g₈ _ (by decide), x2₇]
  have x15₉ : s₉.gpr .x15 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ _ (by decide), c₈']
  have mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  have G' : ∀ r ∈ [Reg.x0, .x5], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x2 ∧ r ≠ .x1 ∧ r ≠ .x15 ∧ r ≠ .x14 ∧ r ≠ .x4 ∧ r ≠ .x3 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g' _ this.2.1 this.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl <;> simp)
  have x5' : s'.gpr .x5 = s.gpr .x5 := G' _ (by simp)
  -- the memory
  have f₇ : Frame [⟨p, 16 * k⟩] s₄.mem s₇.mem := by
    have := i₇.frame; rw [m₆, m₅] at this; exact this
  have frame : Frame [workR s, ⟨p, 16 * k⟩] s.mem s'.mem := by
    rw [mem']
    have a : Frame [workR s, ⟨p, 16 * k⟩] s.mem s₃.mem :=
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨workR s, List.mem_cons_self, arraysR_sub_work s⟩)
    have b : Frame [workR s, ⟨p, 16 * k⟩] s₃.mem s₄.mem :=
      f₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [workR, x5₃]; exact List.mem_cons_self
    have c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  refine ⟨fun b hb => ?_, ?_, ?_, G', ?_, by simp only [s', s₉, rd_write, rd₈, i₇.rd, rd₆],
    by simp only [s', s₉, wr_write, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · simp [s', s₉, gpr_write, x3₈]; rfl
  · simp only [s', gpr_write_self, BitVec.setWidth_eq, read_x, x2₉, x15₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.AArch64
