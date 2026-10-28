module

public import VerifiedGarbage.Proof.Seed.RISCV64.Copy
public import VerifiedGarbage.Proof.Seed.RISCV64.Rounds
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A batch on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Batch.lean`): `batch_ok`: a batch
encrypts or decrypts the first `min n 16` blocks at `a1` in place
(`n = a2`), with the keys at `a0` (`keysAt`), and moves `a1` and `a2` past
them. It keeps `g16`'s masks (`Masks`), writing only the working area and
the blocks.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb movR shrI)

/-! ## The batch size -/

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.write d (s.gpr n)) := by
  rw [movR, exec_addi (by decide)]
  simp

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .t2 = BitVec.ofNat 64 (min (s.gpr .a2).toNat 16) ∧
      (∀ r, r ≠ .t2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .t2 (s.gpr .a2 >>> 4)
  have e₁ : runBlock isa [shrI .t2 .a2 4] s = some s₁ := by
    rw [runBlock_cons, shrI, exec_shift_d (by decide), runStep_some, runBlock_nil]
  have g₁ : ∀ r, r ≠ .t2 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have hc : isa.eval (.nonzero .t2) s₁ = some (decide (16 ≤ (s.gpr .a2).toNat)) := by
    rw [RISCV64.Steps.eval_nonzero, gpr_write_self]
    congr 1
    by_cases h : 16 ≤ (s.gpr .a2).toNat
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
    have e : runBlock isa [.li .t2 16] s₁ = some (s₁.write .t2 (BitVec.ofInt 64 16)) := by
      rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
    refine WP.of_runBlock ⟨_, e, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega)]; rfl
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    have e : runBlock isa [movR .t2 .a2] s₁ = some (s₁.write .t2 (s₁.gpr .a2)) := by
      rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
    refine WP.of_runBlock ⟨_, e, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, g₁ _ (by decide), Nat.min_eq_left (by omega),
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]

/-! ## Small steps -/

theorem copyStart_ok (s : State) :
    ∃ t, runBlock isa copyStart s = some t ∧ t.gpr .t3 = s.gpr .a1 ∧ t.gpr .t4 = s.gpr sb ∧
      (∀ r, r ≠ .t3 → r ≠ .t4 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp :=
  ⟨(s.write .t3 (s.gpr .a1)).write .t4 ((s.write .t3 (s.gpr .a1)).gpr sb),
    by rw [copyStart, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_nil],
    by simp [gpr_write], by simp [gpr_write, show ¬ sb = Reg.t3 by decide],
    fun r h1 h2 => by simp [gpr_write, h1, h2],
    rfl, rfl, rfl, rfl⟩

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## Blocks and lanes -/

theorem quad_of_lanes {t : State} {m : Mem} {p : Addr} {b : Nat}
    (h : ∀ w < 4, lv t (arrSlot w) b = bw m p b w) :
    quad t b = decodeQ (Spec.Seed.blockAt m (p + BitVec.ofNat 64 (16 * b))) := by
  rw [decodeQ_blockAt]
  simp only [quad, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), bw,
    Offset.add_ofNat_add_ofNat, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul]

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
  masks : Masks s
  pos : 1 ≤ (s.gpr .a2).toNat
  data : ∀ b < min (s.gpr .a2).toNat 16, ∀ w < 4,
    InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  dataSep : Region.Disjoint ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩ (scratchR s)
  keys : KeysOk d s (s.gpr .a0)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s.gpr .a0) j, 8⟩ ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩

structure BatchPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  done : ∀ b < min (s.gpr .a2).toNat 16,
    Spec.Seed.blockAt s'.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s.mem (s.gpr .a0))
        (Spec.Seed.blockAt s.mem (s.gpr .a1 + BitVec.ofNat 64 (16 * b)))
  a1 : s'.gpr .a1 = s.gpr .a1 + BitVec.ofNat 64 (16 * min (s.gpr .a2).toNat 16)
  a2 : s'.gpr .a2 = s.gpr .a2 - BitVec.ofNat 64 (min (s.gpr .a2).toNat 16)
  regs : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s.gpr r
  masks : Masks s'
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workR s, ⟨s.gpr .a1, 16 * min (s.gpr .a2).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := arraysR_sub s

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 (8 * 40), 8 * 64⟩ ⟨s.gpr sb, 8 * 104⟩
  exact Offset.sub_base _ (by omega)

theorem cr_ra : CopyRegs .ra := by unfold CopyRegs; decide
theorem cr_a0 : CopyRegs .a0 := by unfold CopyRegs; decide
theorem cr_a1 : CopyRegs .a1 := by unfold CopyRegs; decide
theorem cr_a2 : CopyRegs .a2 := by unfold CopyRegs; decide
theorem cr_a3 : CopyRegs .a3 := by unfold CopyRegs; decide

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .a2).toNat
  let k := min n 16
  let p := s.gpr .a1
  have hk1 : 1 ≤ k := by have := h.pos; omega
  have hk16 : k ≤ 16 := by omega
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, t3₂, t4₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  have G₂ : ∀ r, CopyRegs r → s₂.gpr r = s.gpr r := fun r hr =>
    (g₂ r hr.2.2.2.1 hr.2.2.2.2).trans (g₁ r hr.2.2.1)
  have sb₂ : s₂.gpr sb = s.gpr sb := G₂ _ sb_copyRegs
  have arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, sb₂]
  have room₂ : Room s₂ := room_congr h.room sb₂ (by rw [wr₂, wr₁])
  have pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega, ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [t3₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, t4₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  have G₃ : ∀ r, CopyRegs r → s₃.gpr r = s.gpr r := fun r hr => (i₃.regs r hr).trans (G₂ r hr)
  have sb₃ : s₃.gpr sb = s.gpr sb := G₃ _ sb_copyRegs
  have rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  have wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  have sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  have room₃ : Room s₃ := room_congr h.room sb₃ wr₃
  have f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  have masks₃ : Masks s₃ := h.masks.frame sb₃ (G₃ _ cr_a3) (scratch_of_arrays f₃)
  have scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, sb₃]
  have keys₃ : KeysOk d s₃ (s₃.gpr .a0) := by
    rw [G₃ .a0 cr_a0]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  have hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .a0) j = keysAt d s.mem (s.gpr .a0) j := by
    intro j hj
    rw [G₃ .a0 cr_a0]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    have hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .a0) j, 8⟩ r := by
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
  refine WP.mono (rounds_ok d room₃ masks₃ keys₃) fun s₄ ⟨q₄, room₄, masks₄, rd₄, wr₄, sp₄, g₄, f₄⟩ => ?_
  have G₄ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r hr, G₃ r (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> (unfold CopyRegs; decide))]
  have sb₄ : s₄.gpr sb = s.gpr sb := G₄ _ (by simp [sb])
  have hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .a0)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, t3₆, t4₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  have G₆ : ∀ r, CopyRegs r → s₆.gpr r = s₄.gpr r := fun r hr =>
    (g₆ r hr.2.2.2.1 hr.2.2.2.2).trans (g₅ r hr.2.2.1)
  have sb₆ : s₆.gpr sb = s.gpr sb := (G₆ _ sb_copyRegs).trans sb₄
  have a2₄ : s₄.gpr .a2 = s.gpr .a2 := G₄ _ (by simp)
  have a1₄ : s₄.gpr .a1 = p := G₄ _ (by simp)
  have rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  have arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, sb₆]
  have pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room sb₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  have inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [t3₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), a1₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, t4₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, a2₄]
  have quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, sb₆, sb₄]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  have G₇ : ∀ r, CopyRegs r → s₇.gpr r = s₄.gpr r := fun r hr => (i₇.regs r hr).trans (G₆ r hr)
  have a2₇ : s₇.gpr .a2 = s.gpr .a2 := (G₇ _ cr_a2).trans a2₄
  have c₈' : s₈.gpr .t2 = BitVec.ofNat 64 k := by rw [c₈, a2₇]
  have t3₈ : s₈.gpr .t3 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.t3]
  let s₉ := s₈.write .a1 (s₈.gpr .t3)
  let s' := s₉.write .a2 (s₉.gpr .a2 - s₉.gpr .t2)
  have e' : runBlock isa [movR .a1 .t3, .sub .a2 .a2 .t2] s₈ = some s' := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s', e', ?_⟩
  have g' : ∀ r, r ≠ .a1 → r ≠ .a2 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  have a2₉ : s₉.gpr .a2 = s.gpr .a2 := by rw [gpr_write_of_ne _ _ (by decide), g₈ _ (by decide), a2₇]
  have t2₉ : s₉.gpr .t2 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ (by decide), c₈']
  have mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  have G' : ∀ r ∈ [Reg.ra, .a0, .a3, .a5], s'.gpr r = s.gpr r := by
    intro r hr
    have hc : CopyRegs r ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .t2 ∧ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨by unfold CopyRegs; decide, by decide, by decide,
        by decide, by simp⟩
    rw [g' _ hc.2.1 hc.2.2.1, g₈ _ hc.2.2.2.1, G₇ _ hc.1, G₄ _ hc.2.2.2.2]
  have sb' : s'.gpr sb = s.gpr sb := G' _ (by simp [sb])
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
        simp only [workR, sb₃]; exact List.mem_cons_self
    have c : Frame [workR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  have masks' : Masks s' := by
    refine masks₄.frame' (by rw [sb', sb₄])
      (show s'.gpr .a3 = s₄.gpr .a3 by rw [G' _ (by simp), G₄ _ (by simp)])
      (by rw [mem']; exact f₇) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    have hm : masksR s₄ = masksR s := by simp only [masksR, sb₄]
    rw [hm]
    exact (h.dataSep.sub_right (masksR_sub s)).symm
  refine ⟨fun b hb => ?_, ?_, ?_, G', masks', ?_, by simp only [s', s₉, rd_write, rd₈, i₇.rd, rd₆],
    by simp only [s', s₉, wr_write, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · simp [s', s₉, gpr_write, t3₈]; rfl
  · simp only [s', gpr_write_self, a2₉, t2₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.RISCV64
