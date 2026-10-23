module

public import VerifiedGarbage.Proof.Seed.PPC64LE.Copy
public import VerifiedGarbage.Proof.Seed.PPC64LE.Rounds
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A batch on PPC64LE

`batch_ok`: a batch encrypts or decrypts the first `min n 16` blocks at
`r4` in place (`n = r5`), with the keys at `r3` (`keysAt`), and moves `r4`
and `r5` past them.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE
  VG.Proof.Seed

/-! ## The batch size -/

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.write d (s.gpr n)) :=
  exec_or_self

theorem sb_eq : sb = .r8 := rfl

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .r10 = BitVec.ofNat 64 (min (s.gpr .r5).toNat 16) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .r10 (s.gpr .r5 >>> 4)
  have e₁ : runBlock isa [shrI .r10 .r5 4] s = some s₁ := by
    rw [runBlock_cons, shrI, exec_lsr_d (by decide), runStep_some, runBlock_nil]
  have g₁ : ∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have hc : isa.eval (.nonzero .d .r10) s₁ = some (decide (16 ≤ (s.gpr .r5).toNat)) := by
    show some (s₁.read .d .r10 != 0) = _
    rw [show s₁.read .d .r10 = s₁.gpr .r10 from BitVec.setWidth_eq _, gpr_write_self]
    congr 1
    by_cases h : 16 ≤ (s.gpr .r5).toNat
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
    let s₂ := s₁.write .r10 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega)]; rfl
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    refine WP.of_runBlock ⟨s₁.write .r10 (s₁.gpr .r5), by rw [runBlock_cons, exec_movR, runStep_some,
      runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, g₁ _ (by decide), Nat.min_eq_left (by omega),
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .r6 = s.gpr .r4 ∧ t.gpr .r7 = s.gpr .r8 ∧
      (∀ r, r ≠ .r6 → r ≠ .r7 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp :=
  ⟨(s.write .r6 (s.gpr .r4)).write .r7 ((s.write .r6 (s.gpr .r4)).gpr .r8),
    by rw [copyStart, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil]; rfl,
    by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => by simp [gpr_write, h1, h2],
    rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

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
  pos : 1 ≤ (s.gpr .r5).toNat
  data : ∀ b < min (s.gpr .r5).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .r4, 16 * min (s.gpr .r5).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .r3)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .r3) j, 8⟩ ⟨s.gpr .r4, 16 * min (s.gpr .r5).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .r5).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .r4 + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .r3))
        (Spec.Seed.blockAt s.mem (s.gpr .r4 + BitVec.ofNat 64 (16 * b)))
  rsi : s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 64 (16 * min (s.gpr .r5).toNat 16)
  rdx : s'.gpr .r5 = s.gpr .r5 - BitVec.ofNat 64 (min (s.gpr .r5).toNat 16)
  regs : ∀ r ∈ [Reg.r3, .r8], s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .r4, 16 * min (s.gpr .r5).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .r8, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega)

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .r8, 8 * 112⟩
  exact Offset.sub_base _ (by omega)

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .r5).toNat
  let k := min n 16
  let p := s.gpr .r4
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hk16 : k ≤ 16 := by omega
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, r6₂, r7₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have G₂ : ∀ r, r ≠ .r10 → r ≠ .r6 → r ≠ .r7 → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  have r8₂ : s₂.gpr .r8 = s.gpr .r8 := G₂ _ (by decide) (by decide) (by decide)
  have scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, r8₂]
  have arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, r8₂]
  have room₂ : Room s₂ := room_congr h.room r8₂ (by rw [wr₂, wr₁])
  have pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega, ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [r6₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, r7₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  have r8₃ : s₃.gpr .r8 = s.gpr .r8 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans r8₂
  have G₃ : ∀ r ∈ [Reg.r3, .r4, .r5], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r6 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  have rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  have sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  have room₃ : Room s₃ := room_congr h.room r8₃ wr₃
  have f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  have scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, r8₃]
  have keys₃ : KeysOk d s₃ (s₃.gpr .r3) := by
    rw [G₃ .r3 (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  have hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .r3) j = keysAt d s.mem (s.gpr .r3) j := by
    intro j hj
    rw [G₃ .r3 (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    have hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .r3) j, 8⟩ r := by
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
  have G₄ : ∀ r ∈ [Reg.r3, .r4, .r5, .r8], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact r8₃
  have hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .r3)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, r6₆, r7₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  have G₆ : ∀ r, r ≠ .r10 → r ≠ .r6 → r ≠ .r7 → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  have r8₆ : s₆.gpr .r8 = s.gpr .r8 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  have r5₄ : s₄.gpr .r5 = s.gpr .r5 := G₄ _ (by simp)
  have r4₄ : s₄.gpr .r4 = p := G₄ _ (by simp)
  have rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  have arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, r8₆]
  have pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room r8₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [r6₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), r4₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, r7₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, r5₄]
  have quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, r8₆, G₄ .r8 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have G₇ : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  have r5₇ : s₇.gpr .r5 = s.gpr .r5 := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans r5₄
  have c₈' : s₈.gpr .r10 = BitVec.ofNat 64 k := by rw [c₈, r5₇]
  have r6₈ : s₈.gpr .r6 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.r6]
  let s₉ := s₈.write .r4 (s₈.gpr .r6)
  let s' := s₉.write .r5 (s₉.gpr .r5 - s₉.gpr .r10)
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub,
    runStep_some, runBlock_nil], ?_⟩
  have g' : ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  have r5₉ : s₉.gpr .r5 = s.gpr .r5 := by rw [gpr_write_of_ne _ _ (by decide), g₈ _ (by decide), r5₇]
  have r10₉ : s₉.gpr .r10 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ (by decide), c₈']
  have mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  have G' : ∀ r ∈ [Reg.r3, .r8], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r5 ∧ r ≠ .r4 ∧ r ≠ .r10 ∧ r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r6 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g' _ this.2.1 this.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl <;> simp)
  have r8' : s'.gpr .r8 = s.gpr .r8 := G' _ (by simp)
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
        simp only [workR, r8₃]; exact List.mem_cons_self
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
  · simp [s', s₉, gpr_write, r6₈]; rfl
  · simp only [s', gpr_write_self, r5₉, r10₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.PPC64LE
