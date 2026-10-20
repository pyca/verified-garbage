module

public import VerifiedGarbage.Proof.Seed.X86_64.KeyStore
public import VerifiedGarbage.Proof.Seed.X86_64.G16
public import VerifiedGarbage.Proof.Seed.X86_64.KeyRounds
import VerifiedGarbage.Proof.Seed.X86_64.Batch
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The key schedule's computation on x86-64

`keyBody_ok`: from `r10 = Key0 || Key1` and `r11 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Proof.Seed
open VG.Impl.Aes.X86_64 (movR)

/-- The rounds and the schedule's end, between loading the key and the loop. -/
def keyPre : List Instr :=
  (List.range 16).flatMap keyRound ++ [movR .rdx .rsi, .alu .add .rdx (.imm 128)]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

theorem schedR_sep {s : State} {k : Nat} (hk : k + 64 ≤ 128)
    (h : (⟨s.gpr .rsi, 128⟩ : Region).Disjoint (scratchR s)) : (outR s (k / 4)).Disjoint (scratchR s) := by
  refine h.sub_left ?_
  exact Offset.sub_base _ (by omega)

theorem lane_sub_work {s : State} {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    Region.Sub ⟨laneA s k b, 4⟩ (workR s) := by
  have := arrays_bound k hk
  exact Offset.sub_base _ (by omega)

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hr9 : s'.gpr .r9 = s.gpr .r9) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hr9]
  refine hf.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega))).symm

theorem arraysR_sub_work' (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * 61), 8 * 64⟩ ⟨s.gpr .r9, 8 * 125⟩
  exact Offset.sub_base _ (by omega)

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hm : MasksIn s)
    (h10 : s.gpr .r10 = kx (keyWords key 0)) (h11 : s.gpr .r11 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧ MasksIn s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .rdx = s.gpr .rsi + BitVec.ofNat 64 128 ∧ (∀ r ∈ [Reg.r9, .rsi, .rsp], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h10 h11 16 (Nat.le_refl _)
  let s2 := s1.setReg .rdx (s1.gpr .rsi)
  let s3 := (arithFlags s2 (s2.gpr .rdx + (128 : BitVec 32).signExtend 64)
    (2 ^ 64 ≤ (s2.gpr .rdx).toNat + ((128 : BitVec 32).signExtend 64).toNat)
    (addOverflow (s2.gpr .rdx) ((128 : BitVec 32).signExtend 64)
      (s2.gpr .rdx + (128 : BitVec 32).signExtend 64))).setReg .rdx (s2.gpr .rdx + (128 : BitVec 32).signExtend 64)
  have e3 : runBlock isa [movR .rdx .rsi, .alu .add .rdx (.imm 128)] s1 = some s3 := rfl
  have g3 : ∀ r, r ≠ .rdx → s3.gpr r = s1.gpr r := fun r hr => by
    simp only [s3, s2, gpr_setReg, hr, ↓reduceIte, gpr_arithFlags]
  have m3 : s3.mem = s1.mem := rfl
  have r9_1 : s1.gpr .r9 = s.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  have r9_3 : s3.gpr .r9 = s.gpr .r9 := (g3 _ (by decide)).trans r9_1
  have lv3 : ∀ k b, lv s3 k b = lv s1 k b := fun k b => by simp only [lv, laneA, m3, g3 _ (show Reg.r9 ≠ .rdx by decide)]
  refine ⟨s3, runBlock_trans e1 e3, room_congr h r9_3 inv.wr,
    masks_of_arrays hm r9_3 (by rw [m3]; exact inv.frame), fun w hw => ?_, fun w hw => ?_, ?_, fun r hr => ?_,
    inv.rd, inv.wr, by rw [m3]; exact inv.frame⟩
  · rw [lv3, ← inv.lanes w (by omega), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv3, ← inv.lanes (16 + w) (by omega), gSlot_hi hw, show (16 + w) % 16 = w by omega]
  · simp only [s3, s2, gpr_setReg_self]
    rw [inv.regs .rsi (by decide) (by decide) (by decide) (by decide)]
    rfl
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [g3 _ (by decide), inv.regs _ (by decide) (by decide) (by decide) (by decide)]

theorem endTest (S : Addr) : ∀ k ≤ 2,
    (S + BitVec.ofNat 64 (64 * k) - (S + BitVec.ofNat 64 128) == 0) = decide (k = 2)
  | 0, _ | 1, _ | 2, _ => by rw [Offset.add_sub_add_left]; decide

theorem eval_ne' (t : State) : isa.eval .ne t = t.zf.map (!·) := rfl

/-- `cmp rsi, rdx`. -/
theorem cmp_ok (t : State) :
    ∃ t', runBlock isa [.alu .cmp .rsi (.reg .rdx)] t = some t' ∧ t'.gpr = t.gpr ∧
      t'.zf = some (t.gpr .rsi - t.gpr .rdx == 0) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  ⟨_, rfl, by funext r; simp only [gpr_arithFlags], rfl, rfl, rfl, rfl⟩

/-- `add rsi, 64; cmp rsi, rdx`. -/
theorem addCmp_ok (t : State) :
    ∃ t', runBlock isa [.alu .add .rsi (.imm 64), .alu .cmp .rsi (.reg .rdx)] t = some t' ∧
      t'.gpr .rsi = t.gpr .rsi + BitVec.ofNat 64 64 ∧ (∀ r, r ≠ .rsi → t'.gpr r = t.gpr r) ∧
      t'.zf = some (t.gpr .rsi + BitVec.ofNat 64 64 - t.gpr .rdx == 0) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  let t1 := (arithFlags t (t.gpr .rsi + (64 : BitVec 32).signExtend 64)
    (2 ^ 64 ≤ (t.gpr .rsi).toNat + ((64 : BitVec 32).signExtend 64).toNat)
    (addOverflow (t.gpr .rsi) ((64 : BitVec 32).signExtend 64)
      (t.gpr .rsi + (64 : BitVec 32).signExtend 64))).setReg .rsi (t.gpr .rsi + (64 : BitVec 32).signExtend 64)
  have e1 : runBlock isa [.alu .add .rsi (.imm 64)] t = some t1 := rfl
  have r1 : t1.gpr .rsi = t.gpr .rsi + BitVec.ofNat 64 64 := by simp only [t1, gpr_setReg_self]; rfl
  have g1 : ∀ r, r ≠ .rsi → t1.gpr r = t.gpr r := fun r hr => by
    simp only [t1, gpr_setReg, hr, ↓reduceIte, gpr_arithFlags]
  obtain ⟨t2, e2, g2, z2, m2, rd2, wr2⟩ := cmp_ok t1
  refine ⟨t2, runBlock_trans e1 e2, by rw [g2, r1], fun r hr => by rw [g2, g1 r hr], ?_, m2, rd2, wr2⟩
  rw [z2, r1, g1 _ (by decide)]

/-- After `c` of the two halves: `rsi` at the schedule's word `16 c`, `G`'s
words holding the next sixteen inputs, the schedule's words before `16 c`
done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  masks : MasksIn t
  r9 : t.gpr .r9 = s.gpr .r9
  rsp : t.gpr .rsp = s.gpr .rsp
  rsi : t.gpr .rsi = S + BitVec.ofNat 64 (64 * c)
  rdx : t.gpr .rdx = S + BitVec.ofNat 64 128
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      t.gpr .r9 = s.gpr .r9 → t.gpr .rsp = s.gpr .rsp → t.rd = s.rd → t.wr = s.wr →
      Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf .ne) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  have scrS : ∀ t : State, t.gpr .r9 = s.gpr .r9 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  have workS : ∀ t : State, t.gpr .r9 = s.gpr .r9 → workR t = workR s := fun t h => by simp only [workR, h]
  have schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, masks2, room2, rd2, wr2, regs2, f2⟩ := g16_lanes hi.room hi.masks
  have r9_2 : t2.gpr .r9 = s.gpr .r9 := (regs2 _ (by decide)).trans hi.r9
  have rsi_2 : t2.gpr .rsi = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.rsi
  have out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 r9_2]; simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
    exact hsep.sub_left (Offset.sub_base _ (by omega))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 room2
    (fun w hw => by
      rw [rsi_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩) out2 (by decide) 16 (Nat.le_refl _)
  have r9_3 : t3.gpr .r9 = s.gpr .r9 := (g3 _ (by decide)).trans r9_2
  have masks3 : MasksIn t3 := masks_of_frame masks2 (g3 _ (by decide)) f3 out2
  obtain ⟨t4, e4, rsi4, g4, z4, m4, rd4, wr4⟩ := addCmp_ok t3
  have r9_4 : t4.gpr .r9 = s.gpr .r9 := (g4 _ (by decide)).trans r9_3
  have rsi_4 : t4.gpr .rsi = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [rsi4, g3 _ (by decide), rsi_2, Offset.add_add]; congr 2
  have rdx_4 : t4.gpr .rdx = S + BitVec.ofNat 64 128 := by
    rw [g4 _ (by decide), g3 _ (by decide), regs2 _ (by decide), hi.rdx]
  have zf4 : t4.zf = some (decide (c = 1)) := by
    rw [z4, ← g4 _ (show Reg.rdx ≠ .rsi by decide), ← rsi4, rsi_4, rdx_4, endTest S (c + 1) (by omega)]
    congr 1
  -- the schedule's words so far
  have lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  have done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
          exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.r9]
          exact schedWork.sub_left (Offset.sub_base _ (by omega))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega⟩
      have := v3 w (by omega)
      rw [rsi_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega] at this
      rw [this, g2 w (by omega), hi.cur w (by omega)]
  have frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.r9]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, rsi_2, Nat.mul_zero, ofNat_zero_add]
      exact Offset.sub_base _ (by omega)
  have room4 : Room t4 := room_congr hi.room (r9_4.trans hi.r9.symm) (by rw [wr4, wr3, wr2, hi.wr])
  have masks4 : MasksIn t4 := fun kv hkv => by
    rw [← masks3 kv hkv]
    show t4.mem.readW (Straight.wordAddr (t4.gpr .r9) kv.1) 64 = t3.mem.readW (Straight.wordAddr (t3.gpr .r9) kv.1) 64
    rw [m4, g4 _ (by decide)]
  have rsp4 : t4.gpr .rsp = s.gpr .rsp := by
    rw [g4 _ (by decide), g3 _ (by decide), regs2 _ (by decide), hi.rsp]
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (!decide (c = 1)) (by rw [eval_ne', zf4]; rfl) (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    have hc0 : c = 0 := by simp at hb; omega
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    obtain ⟨t6, e6, gg6, z6, m6, rd6, wr6⟩ := cmp_ok t5
    have g6 : ∀ r, r ≠ .rax → r ≠ .rcx → t6.gpr r = t4.gpr r := fun r h1 h2 => by rw [gg6, g5 r h1 h2]
    refine WP.of_runBlock ⟨t6, runBlock_trans e5 e6, .inr ⟨?_, 1, by omega, 1, by omega, rfl, ?_⟩⟩
    · rw [eval_ne', z6, ← gg6, g6 _ (by decide) (by decide), g6 _ (by decide) (by decide), rsi_4, rdx_4,
        endTest S (0 + 1) (by omega)]
      rfl
    have r9_6 : t6.gpr .r9 = s.gpr .r9 := (g6 _ (by decide) (by decide)).trans r9_4
    have workF : Frame [workR s] t4.mem t6.mem := by
      rw [m6]
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 r9_4]; exact arraysR_sub_work' t4⟩
    refine ⟨room_congr room4 (r9_6.trans r9_4.symm) (by rw [wr6, wr5]), ?_,
      r9_6, by rw [g6 _ (by decide) (by decide), rsp4], by rw [g6 _ (by decide) (by decide), rsi_4],
      by rw [g6 _ (by decide) (by decide), rdx_4], fun w hw => ?_, fun h => absurd h (by decide),
      fun i hi' => ?_, by rw [rd6, rd5, rd4, rd3, rd2, hi.rd], by rw [wr6, wr5, wr4, wr3, wr2, hi.wr],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · exact masks_of_arrays masks4 (g6 _ (by decide) (by decide)) (by rw [m6]; exact f5)
    · rw [show lv t6 (tSlot 0) w = lv t5 (tSlot 0) w by simp only [lv, laneA, m6, gg6],
        v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by simp only [lv, laneA, m4, g4 _ (show Reg.r9 ≠ .rsi by decide)],
        lv_frame (g3 _ (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t6 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega)))]
      exact done4 i hi'
  · -- the end
    have hc1 : c = 1 := by simp at hb; omega
    subst hc1
    refine WP.block_nil (.inl ⟨by rw [eval_ne', zf4]; rfl, hQ t4 done4 r9_4 rsp4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)

end VG.Proof.Seed.X86_64
