module

import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Seed.PPC64LE.Steps
public import VerifiedGarbage.Proof.Seed.Rounds
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.ReadHalves

/-! ### `Seed.PPC64LE.Batch`, which this module and modules that import it used -/

section

/-! ### `Seed.PPC64LE.Round`, which this module and modules that import it used -/

section

/-! ### `Seed.PPC64LE.Swap`, which only this module used -/

section

/-!
# Lanes and slots; exchanging the halves

A lane is half of a 64-bit slot (`lv_slot`), so `g16`'s words are lanes of
`tSlot 0` (`wordQ_lv`). `swap_ok`: `swapHalves` exchanges the arrays of
`L` (`arrSlot 0`, `arrSlot 1`) with those of `R` (`arrSlot 2`, `arrSlot 3`),
checked by evaluating its moves over named words (`Bitslice.names`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Seed.PPC64LE

theorem lv_slot (s : State) (k b : Nat) :
    lv s k b = ((slotW s (k + b / 2)) >>> (32 * (b % 2))).setWidth 32 := by
  obtain ha : laneA s k b = wordAddr (s.gpr .r8) (k + b / 2) + BitVec.ofNat 64 (4 * (b % 2)) := by
    simp only [laneA, wordAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; omega_using []
  rcases Nat.mod_two_eq_zero_or_one b with h | h
  · rw [lv, ha, h, show wordAddr (s.gpr .r8) (k + b / 2) + BitVec.ofNat 64 (4 * 0) =
      wordAddr (s.gpr .r8) (k + b / 2) by simp, Mem.readW_lo32 (a := wordAddr (s.gpr .r8) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    simp
  · rw [lv, ha, h, show 4 * 1 = 4 from rfl, Mem.readW_hi32 (a := wordAddr (s.gpr .r8) (k + b / 2)) (v := slotW s (k + b / 2)) rfl]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]

theorem wordQ_lv (s : State) (w : Nat) :
    Proof.Seed.wordQ (fun i => slotW s (tSlot i)) w = lv s (tSlot 0) w := by
  rw [lv_slot]; rfl

/-- The slots `swapHalves` moves, and those below them. -/
def swapCfg : Cfg := { base := .r8, slots := 112, ext := .r8, exts := 0 }

def swapEnv : Env Nat := { reg := fun _ => none, slot := fun k => if k < 112 then some k else none }

def swapPost (e : Env Nat) : Bool :=
  (List.range 16).all (fun k => e.slot (80 + k) == some (96 + k) && e.slot (96 + k) == some (80 + k)) &&
    (List.range 80).all fun j => e.slot j == some j

theorem swap_check : check (names 64) swapCfg (fun _ => none) swapHalves swapEnv swapPost = true := by
  decide +kernel

theorem ok_of_room {s : State} (h : Room s) {c : Cfg} (hb : c.base = .r8) (hs : c.slots ≤ 122)
    (he : c.exts = 0) : Ok c s :=
  ⟨fun k hk => h.wr (by
      rw [hb]; exact Offset.contains_base _ (by unfold scratchSlots; omega_using [hs, hk]) (by omega_using [hs, hk])),
    fun k hk => by omega, by omega_using [hs], fun _ _ j hj => by omega⟩

theorem swap_writes (r : Reg) (h1 : r ≠ .r9) (h2 : r ≠ .r10) :
    (swapHalves.all fun i => dstOf i != some r) = true := by
  cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | decide

theorem swap_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      (∀ w < 4, ∀ b < 16, lv s' (arrSlot w) b = lv s (arrSlot ((w + 2) % 4)) b) ∧
      (∀ j < 80, slotW s' j = slotW s j) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain hok : Ok swapCfg s := ok_of_room h rfl (by decide) rfl
  obtain hrel : Rel (NameRel (fun k => slotW s k)) swapCfg (fun _ => none) swapEnv s := by
    refine ⟨fun _ _ h => (by cases h), fun k a hk h => ?_, fun _ _ hk => (by cases hk), fun _ _ h => (by cases h)⟩
    simp only [swapEnv, show k < 112 from hk, ite_true, Option.some.injEq] at h
    subst h; rfl
  obtain ⟨e, he, hp⟩ := of_check _ _ _ swap_check
  obtain ⟨s', hs', p⟩ := run (names_sound _) hok hrel he
  simp only [swapPost, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hp
  obtain hsl : ∀ k a, k < 112 → e.slot k = some a → slotW s' k = slotW s a := by
    intro k a hk hka
    exact p.rel.slot k a hk hka
  refine ⟨s', hs', fun w hw b hb => ?_, fun j hj => hsl j j (by omega_using [hj]) (hp.2 j hj), p.rd, p.wr, p.sp,
    fun r h1 h2 => p.other r ?_, ?_⟩
  · rw [lv_slot, lv_slot]
    congr 2
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl
    · exact hsl _ _ (by simp [arrSlot]; omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 1 + b / 2 = 80 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((1 + 2) % 4) + b / 2 = 96 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).1)
    · rw [show arrSlot 2 + b / 2 = 96 + b / 2 by simp [arrSlot],
        show arrSlot ((2 + 2) % 4) + b / 2 = 80 + b / 2 by simp [arrSlot]]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (b / 2) (by omega_using [hb])).2)
    · rw [show arrSlot 3 + b / 2 = 96 + (8 + b / 2) by simp [arrSlot]; omega_using [],
        show arrSlot ((3 + 2) % 4) + b / 2 = 80 + (8 + b / 2) by simp [arrSlot]; omega_using []]
      exact hsl _ _ (by omega_using [hb]) ((hp.1 (8 + b / 2) (by omega_using [hb])).2)
  · rw [swap_writes r h1 h2]; decide
  · have := p.frame
    refine this.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [swapCfg])⟩

end VG.Proof.Seed.PPC64LE

end

end


/-!
# A round on PPC64LE

`g16_lanes` restates `g16_ok` on the lanes of the arrays, and `round_ok`
puts the steps of a round together: on every lane, the round's code does
RFC 4269 §2's round (`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`,
`R1`, with the round key at `r3`.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s := ok_of_room h rfl (by decide) rfl

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g16_ok (room_ok_gCfg h)
  obtain hr9 : s'.gpr .r8 = s.gpr .r8 := hregs _ (by decide)
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, room_congr h hr9 hwr, hrd, hwr, hsp,
    hregs, ?_⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    obtain hk56 : 56 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hr9]
    refine hfr.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr .r8) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 56)
      (by omega_using [hk56]) (by omega_using [hb, hb'])
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg])⟩

/-! ## The round -/

/-- Lane `b` of the blocks' state: `(L0, L1, R0, R1)`. -/
def quad (s : State) (b : Nat) : Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word :=
  (lv s (arrSlot 0) b, lv s (arrSlot 1) b, lv s (arrSlot 2) b, lv s (arrSlot 3) b)

theorem reads1 (k0 k1 : BitVec 32) : ReadsArrays (sp1 k0 k1) := by
  intro kv hkv x y h
  simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_R0, h _ mem_R1]

theorem reads2 : ReadsArrays sp2 := by
  intro kv hkv x y h
  simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_aA]

theorem reads3 : ReadsArrays sp3 := by
  intro kv hkv x y h
  simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_cA]

theorem reads4 : ReadsArrays sp4 := by
  intro kv hkv x y h
  simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_dA, h _ mem_L0, h _ mem_L1]

theorem dests1 (k0 k1 : BitVec 32) : ∀ kv ∈ sp1 k0 k1, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact mem_aA
  · exact mem_tA
theorem dests2 : ∀ kv ∈ sp2, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests3 : ∀ kv ∈ sp3, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests4 : ∀ kv ∈ sp4, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide

/-- A step on all sixteen lanes, from a state where the scratch buffer is writable. -/
theorem lanes16_room {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) (hf : ∀ b < 16, ∀ s, Room s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s : State} (h : Room s) :
    ∃ s', runBlock isa (lanes16 f) s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal sp k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => room_congr hP (hok.regs _ (by decide) (by decide)) hok.wr) hf h 16 (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

theorem scratch_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [])⟩

/-- The step of the key pointer. -/
def stepW : Spec.Seed.Direction → BitVec 64
  | .encrypt => 8
  | .decrypt => -8

theorem exec_keyNext (d : Spec.Seed.Direction) (s : State) :
    exec (keyNext d) s = some (s.write .r3 (s.gpr .r3 + stepW d)) := by
  cases d
  · rw [keyNext, exec_addi' (n := .r3) (by decide)]; rfl
  · rw [keyNext, exec_subi' (n := .r3) (by decide), BitVec.sub_eq_add_neg]; rfl

theorem exec_dec (s : State) (r : Reg) (hr : r ≠ .r0 := by decide) :
    exec (.subi r r 1) s = some (s.write r (s.gpr r - 1)) := by
  rw [exec_subi' (by decide) hr]; rfl

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem keepRegs : ∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r7, .r8],
    r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem notG16 : ∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r7, .r8], r ∉ g16Writes := by decide

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .r3) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .r3 + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .r3) 32, s.mem.readW (s.gpr .r3 + 4) 32) (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .r3 = s.gpr .r3 + stepW d ∧ s'.gpr .r7 = s.gpr .r7 - 1 ∧
      s'.gpr .r4 = s.gpr .r4 ∧ s'.gpr .r5 = s.gpr .r5 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r6 = s.gpr .r6 ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .r3) 32
  let K1 := s.mem.readW (s.gpr .r3 + 4) 32
  -- The round key.
  obtain e1 : exec (.load .w .r11 .r3 0) s = some (s.write .r11 (K0.setWidth 64)) := by
    rw [exec_load_w (by decide) (by decide) (by simpa using hk0)]; simp [K0]
  obtain e2 : exec (.load .w .r12 .r3 4) (s.write .r11 (K0.setWidth 64)) =
      some ((s.write .r11 (K0.setWidth 64)).write .r12 (K1.setWidth 64)) := by
    rw [exec_load_w (by decide) (by decide)
      (by rw [rd_write, wr_write, gpr_write_of_ne _ _ (by decide)]; exact hk1)]
    rw [gpr_write_of_ne _ _ (by decide), mem_write]; rfl
  let s2 := (s.write .r11 (K0.setWidth 64)).write .r12 (K1.setWidth 64)
  obtain hrun2 : runBlock isa [.load .w .r11 .r3 0, .load .w .r12 .r3 4] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  obtain hkeys : KeysIn K0 K1 s2 := by
    refine ⟨room_congr h rfl rfl, ?_, ?_⟩ <;>
      simp [s2, gpr_write]
  obtain lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [s2, lv_write _ _ (show ¬ Reg.r8 = .r12 by decide),
      lv_write _ _ (show ¬ Reg.r8 = .r11 by decide)]
  obtain g2 : ∀ r, r ≠ .r11 → r ≠ .r12 → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp [s2, gpr_write, h1, h2]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, spp4, rg4, fr4⟩ := g16_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ := lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, spp6, rg6, fr6⟩ := g16_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ := lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, spp8, rg8, fr8⟩ := g16_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ := lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, spp10, rg10, fr10⟩ := swap_ok h9
  let s11 := s10.write .r3 (s10.gpr .r3 + stepW d)
  let s12 := s11.write .r7 (s11.gpr .r7 - 1)
  obtain hrun : runBlock isa [keyNext d, .subi .r7 .r7 1] s10 = some s12 := by
    rw [runBlock_cons, exec_keyNext, runStep_some, runBlock_cons, exec_dec _ .r7, runStep_some, runBlock_nil]
  -- Registers through the steps.
  obtain keep : ∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r7, .r8], s10.gpr r = s.gpr r := by
    intro r hr
    obtain hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h3 h4]
  obtain r9_10 : s10.gpr .r8 = s.gpr .r8 := keep _ (by decide)
  obtain g12 : ∀ r, r ≠ .r3 → r ≠ .r7 → s12.gpr r = s10.gpr r := fun r a b => by
    simp [s12, s11, gpr_write, a, b]
  obtain r9_12 : s12.gpr .r8 = s.gpr .r8 := by rw [g12 _ (by decide) (by decide), r9_10]
  obtain lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, s12, s11, mem_write, r9_12, r9_10]
  refine ⟨s12, ?_, fun b hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6)
      hs7) hs8) hs9) hs10) hrun
  · -- The values, stage by stage.
    obtain ar : ∀ k ∈ arrays, k ∈ arrays := fun _ h => h
    obtain t3 : lv s3 (tSlot 0) b = (lv s (arrSlot 2) b ^^^ K0) ^^^ (lv s (arrSlot 3) b ^^^ K1) := by
      rw [hv3 _ mem_tA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot, BitVec.xor_assoc]
    obtain a3 : lv s3 aSlot b = lv s (arrSlot 2) b ^^^ K0 := by
      rw [hv3 _ mem_aA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    obtain o3 : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3], lv s3 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [hv3 _ hk' b hb, ite_eq_left hb]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    -- c
    obtain t4 : lv s4 (tSlot 0) b = Spec.Seed.g (lv s3 (tSlot 0) b) := hg4 b hb
    obtain k4 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s4 k b = lv s3 k b := fun k hk hkt => hk4 k hk hkt b hb
    obtain t5 : lv s5 (tSlot 0) b = lv s4 (tSlot 0) b + lv s4 aSlot b := by
      rw [hv5 _ mem_tA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    obtain c5 : lv s5 cSlot b = lv s4 (tSlot 0) b := by
      rw [hv5 _ mem_cA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    obtain o5 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ cSlot → lv s5 k b = lv s4 k b := by
      intro k hk h1 h2; rw [hv5 _ hk b hb]; simp [newVal, sp2, Ne.symm h1, Ne.symm h2]
    -- d
    obtain t6 : lv s6 (tSlot 0) b = Spec.Seed.g (lv s5 (tSlot 0) b) := hg6 b hb
    obtain k6 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s6 k b = lv s5 k b := fun k hk hkt => hk6 k hk hkt b hb
    obtain t7 : lv s7 (tSlot 0) b = lv s6 (tSlot 0) b + lv s6 cSlot b := by
      rw [hv7 _ mem_tA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    obtain d7 : lv s7 dSlot b = lv s6 (tSlot 0) b := by
      rw [hv7 _ mem_dA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    obtain o7 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ dSlot → lv s7 k b = lv s6 k b := by
      intro k hk h1 h2; rw [hv7 _ hk b hb]; simp [newVal, sp3, Ne.symm h1, Ne.symm h2]
    -- e
    obtain t8 : lv s8 (tSlot 0) b = Spec.Seed.g (lv s7 (tSlot 0) b) := hg8 b hb
    obtain k8 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s8 k b = lv s7 k b := fun k hk hkt => hk8 k hk hkt b hb
    obtain l0_9 : lv s9 (arrSlot 0) b = (lv s8 (tSlot 0) b + lv s8 dSlot b) ^^^ lv s8 (arrSlot 0) b := by
      rw [hv9 _ mem_L0 b hb]; simp [newVal, sp4, arrSlot]
    obtain l1_9 : lv s9 (arrSlot 1) b = lv s8 (arrSlot 1) b ^^^ lv s8 (tSlot 0) b := by
      rw [hv9 _ mem_L1 b hb]; simp [newVal, sp4, arrSlot]
    obtain r0_9 : lv s9 (arrSlot 2) b = lv s8 (arrSlot 2) b := by
      rw [hv9 _ mem_R0 b hb]; simp [newVal, sp4, arrSlot]
    obtain r1_9 : lv s9 (arrSlot 3) b = lv s8 (arrSlot 3) b := by
      rw [hv9 _ mem_R1 b hb]; simp [newVal, sp4, arrSlot]
    -- The arrays other than `G`'s words, through the `G`s and the steps that do not write them.
    obtain xs : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3],
        lv s8 k b = lv s k b := by
      intro k hk
      obtain hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkt : k ≠ tSlot 0 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkc : k ≠ cSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      obtain hkd : k ≠ dSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [k8 k hk' hkt, o7 k hk' hkt hkd, k6 k hk' hkt, o5 k hk' hkt hkc, k4 k hk' hkt, o3 k hk]
    obtain a4 : lv s4 aSlot b = lv s3 aSlot b := k4 _ mem_aA (by decide)
    obtain c6 : lv s6 cSlot b = lv s5 cSlot b := k6 _ mem_cA (by decide)
    obtain d8 : lv s8 dSlot b = lv s7 dSlot b := k8 _ mem_dA (by decide)
    simp only [quad, lv12, hsw 0 (by decide) b hb, hsw 1 (by decide) b hb, hsw 2 (by decide) b hb,
      hsw 3 (by decide) b hb]
    simp only [show (0 + 2) % 4 = 2 from rfl, show (1 + 2) % 4 = 3 from rfl,
      show (2 + 2) % 4 = 0 from rfl, show (3 + 2) % 4 = 1 from rfl]
    simp only [r0_9, r1_9, l0_9, l1_9]
    simp only [xs (arrSlot 0) (by simp), xs (arrSlot 1) (by simp), xs (arrSlot 2) (by simp),
      xs (arrSlot 3) (by simp), d8, d7, t8, t7, c6, c5, t6, t5, t4, a4, a3, t3]
    simp only [Spec.Seed.round, Spec.Seed.f, K0, K1, BitVec.xor_comm (lv s (arrSlot 0) b),
      BitVec.xor_comm (lv s (arrSlot 1) b)]
  · exact room_congr h r9_12 (by simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl)
  · simp only [s12, s11, rd_write, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · simp only [s12, s11, sp_write, spp10]
    rw [runBlock_sp hs9, spp8, runBlock_sp hs7, spp6, runBlock_sp hs5, spp4, runBlock_sp hs3,
      runBlock_sp hrun2]
  · simp [s12, s11, gpr_write, keep _ (show Reg.r3 ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r7, .r8] by decide)]
  · simp [s12, s11, gpr_write, keep _ (show Reg.r7 ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r7, .r8] by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · exact r9_12
  · -- The frames, all in the scratch buffer.
    obtain fc : ∀ {t : State} {m m' : Mem}, t.gpr .r8 = s.gpr .r8 → Frame [workR t] m m' →
        Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
    simp only [s12, s11, mem_write]
    refine (fc rfl (scratch_of_arrays fr3)).trans ?_
    refine (fc (rg3 _ (by decide) (by decide)) fr4).trans ?_
    refine (fc ?_ (scratch_of_arrays fr5)).trans ?_
    · rw [rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr6).trans ?_
    · rw [rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr7)).trans ?_
    · rw [rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
        rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr8).trans ?_
    · rw [rg7 _ (by decide) (by decide), rg6 _ (by decide), rg5 _ (by decide) (by decide),
        rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr9)).trans ?_
    · rw [rg8 _ (by decide), rg7 _ (by decide) (by decide), rg6 _ (by decide),
        rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine fc ?_ fr10
    rw [rg9 _ (by decide) (by decide), rg8 _ (by decide), rg7 _ (by decide) (by decide),
      rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
      rg3 _ (by decide) (by decide)]; rfl

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.Setup`, which this module and modules that import it used -/

section

/-!
# Storing to and loading from scratch slots

`stores_ok`: stores of registers to distinct slots, writing only the
scratch buffer; `loads_ok`: loads of distinct registers, other than `r8`,
from slots.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE

theorem slot_in_scratch (s : State) {j : Nat} (hj : j < scratchSlots) :
    (scratchR s).Contains (wordAddr (s.gpr .r8) j) (64 / 8) :=
  slot_contains (s.gpr .r8) (n := scratchSlots) hj (by unfold scratchSlots; decide)

theorem slot_off {j : Nat} (hj : j < scratchSlots) : 8 * j % 8 = 0 ∧ 8 * j < 32768 := by
  unfold scratchSlots at hj; omega_using [hj]

/-- The memory after storing `v` in slot `k`. -/
def stMem (s : State) (k : Nat) (v : BitVec 64) : Mem := s.mem.writeW (wordAddr (s.gpr .r8) k) v

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (stS k r) s = some (setMem s (stMem s k (s.gpr r))) :=
  VG.PPC64LE.exec_std (slot_off hk) (h.wr (slot_in_scratch s hk))

theorem exec_ld {s : State} (h : Room s) {k : Nat} (hk : k < scratchSlots) (r : Reg) :
    exec (ldS r k) s = some (s.write r (slotW s k)) :=
  VG.PPC64LE.exec_ld (slot_off hk) (h.rw (slot_in_scratch s hk))

theorem slotW_stMem (s : State) {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) {j : Nat}
    (hj : j < scratchSlots) : slotW (setMem s (stMem s k v)) j = if j = k then v else slotW s j := by
  unfold scratchSlots at hk hj
  show (stMem s k v).readW (wordAddr (s.gpr .r8) j) 64 = _
  simp only [stMem]
  split
  · subst j; exact Mem.readW_writeW_self64 _ _ _
  · rename_i hne
    rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) hne) (by decide)]
    rfl

theorem stMem_frame {s : State} {k : Nat} (hk : k < scratchSlots) (v : BitVec 64) :
    Frame [scratchR s] s.mem (stMem s k v) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in_scratch s hk)

theorem slotW_write (s : State) {r : Reg} (hr : r ≠ .r8) (v : BitVec 64) (j : Nat) :
    slotW (s.write r v) j = slotW s j := by
  show s.mem.readW (wordAddr ((s.write r v).gpr .r8) j) 64 = s.mem.readW (wordAddr (s.gpr .r8) j) 64
  rw [gpr_write_of_ne _ _ (Ne.symm hr)]

/-- A block of stores of registers to distinct scratch slots. -/
theorem stores_ok {s : State} (h : Room s) (l : List (Nat × Reg)) (hl : ∀ p ∈ l, p.1 < scratchSlots)
    (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => stS p.1 p.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [scratchR s] s.mem s'.mem ∧
      (∀ p ∈ l, slotW s' p.1 = s.gpr p.2) ∧
      (∀ x < scratchSlots, (∀ p ∈ l, p.1 ≠ x) → slotW s' x = slotW s x) := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, Frame.refl _ _, (fun _ h => by cases h),
      fun _ _ _ => rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_st (r := p.2) h hp
    let s₁ : State := setMem s (stMem s p.1 (s.gpr p.2))
    have h₁ : Room s₁ := h
    have hd' : (l.map (·.1)).Nodup := (List.nodup_cons.mp hd).2
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', g', rd', wr', sp', f', set', keep'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hd'
    refine ⟨s', ?_, g', rd', wr', sp', (stMem_frame hp _).trans f', fun q hq => ?_,
      fun x hx hne => ?_⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ hp (fun r hr he => hn (he ▸ List.mem_map_of_mem hr)), slotW_stMem s hp _ hp]
        simp
      · exact set' q hq
    · rw [keep' x hx (fun q hq => hne q (List.mem_cons_of_mem _ hq)), slotW_stMem s hp _ hx]
      simp [Ne.symm (hne p List.mem_cons_self)]

/-- A block of loads of distinct registers, other than `r8`, from scratch slots. -/
theorem loads_ok {s : State} (h : Room s) (l : List (Reg × Nat))
    (hl : ∀ p ∈ l, p.2 < scratchSlots ∧ p.1 ≠ .r8) (hd : (l.map (·.1)).Nodup) :
    ∃ s', runBlock isa (l.map fun p => ldS p.1 p.2) s = some s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ p ∈ l, s'.gpr p.1 = slotW s p.2) ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction l generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, (fun _ h => by cases h), fun _ _ => rfl, rfl, rfl⟩
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    have e := exec_ld h hp.1 p.1
    let s₁ := s.write p.1 (slotW s p.2)
    have c₁ : s₁.gpr .r8 = s.gpr .r8 := gpr_write_of_ne _ _ (Ne.symm hp.2)
    have h₁ : Room s₁ := room_congr h c₁ rfl
    have hn : p.1 ∉ l.map (·.1) := (List.nodup_cons.mp hd).1
    obtain ⟨s', run', m', sp', set', keep', rd', wr'⟩ :=
      ih h₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.mp hd).2
    have sl₁ : ∀ j, slotW s₁ j = slotW s j := slotW_write s hp.2 _
    refine ⟨s', ?_, by rw [m']; rfl, by rw [sp']; rfl, fun q hq => ?_, fun r hr => ?_, by rw [rd']; rfl,
      by rw [wr']; rfl⟩
    · rw [List.map_cons, runBlock_cons, e, runStep_some]; exact run'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [keep' _ (fun r hr he => hn (by rw [← he]; exact List.mem_map_of_mem hr))]
        simp [s₁, gpr_write]
      · rw [set' q hq, sl₁]
    · rw [keep' r (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      simp only [s₁]
      rw [gpr_write_of_ne _ _ (Ne.symm (hr p List.mem_cons_self))]

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.Rounds`, which only this module used -/

section

/-!
# Sixteen rounds on PPC64LE

`rounds_ok`: `rounds d` does sixteen rounds on every lane, with round
`j + 1`'s key at `r3 + j * step` (`kp`), and moves `r3` back.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- Where round `j + 1`'s key is, from `p`. -/
def kp (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : Addr := p + BitVec.ofNat 64 j * stepW d

theorem kp_succ (d : Spec.Seed.Direction) (p : Addr) (j : Nat) : kp d p j + stepW d = kp d p (j + 1) := by
  simp only [kp, BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]

theorem exec_keyBack (d : Spec.Seed.Direction) (s : State) :
    exec (keyBack d) s = some (s.write .r3 (s.gpr .r3 - BitVec.ofNat 64 16 * stepW d)) := by
  cases d
  · rw [keyBack, exec_subi' (n := .r3) (by decide)]; rfl
  · rw [keyBack, exec_addi' (n := .r3) (by decide), show BitVec.ofNat 64 16 * stepW .decrypt =
      -BitVec.ofNat 64 128 by decide, BitVec.sub_neg]

theorem kp_back (d : Spec.Seed.Direction) (p : Addr) : kp d p 16 - BitVec.ofNat 64 16 * stepW d = p := by
  rw [kp, BitVec.add_sub_cancel]

/-- The round keys, read from memory `m`. -/
def keysAt (d : Spec.Seed.Direction) (m : Mem) (p : Addr) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word :=
  (m.readW (kp d p j) 32, m.readW (kp d p j + 4) 32)

/-- The keys can be read and are outside the scratch buffer. -/
def KeysOk (d : Spec.Seed.Direction) (s : State) (p : Addr) : Prop :=
  ∀ j < 16, InRegions (s.rd ++ s.wr) (kp d p j) 4 ∧ InRegions (s.rd ++ s.wr) (kp d p j + 4) 4 ∧
    Region.Disjoint ⟨kp d p j, 8⟩ (scratchR s)

/-- After `16 - m` rounds, with `m` left. -/
structure RoundsInv (d : Spec.Seed.Direction) (s₀ : State) (m : Nat) (s : State) : Prop where
  le : 1 ≤ m ∧ m ≤ 16
  quads : ∀ b < 16, quad s b = roundsN (keysAt d s₀.mem (s₀.gpr .r3)) (16 - m) (quad s₀ b)
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r3 : s.gpr .r3 = kp d (s₀.gpr .r3) (16 - m)
  r7 : s.gpr .r7 = BitVec.ofNat 64 m
  regs : ∀ r ∈ [Reg.r2, .r4, .r5, .r6, .r8], s.gpr r = s₀.gpr r
  frame : Frame [workR s₀] s₀.mem s.mem

theorem contains_prefix {a : Addr} {k n : Nat} (h : k ≤ n) : (⟨a, n⟩ : Region).Contains a k := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem r7_sub (m : Nat) (h : 1 ≤ m) (h' : m ≤ 16) :
    BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

theorem rounds_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hk : KeysOk d s (s.gpr .r3)) :
    WP isa (rounds d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .r3)) 16 (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r8], s'.gpr r = s.gpr r) ∧
      Frame [workR s] s.mem s'.mem) := by
  let s1 := s.write .r7 (BitVec.ofNat 64 16)
  have e1 : runBlock isa [.li .r7 16] s = some s1 := by
    simp only [runBlock_cons, exec_li (show 16 < 2 ^ 15 by decide), runStep_some, runBlock_nil, s1]
  have q1 : ∀ b, quad s1 b = quad s b := fun b => by
    simp only [quad, s1, lv_write _ _ (show ¬ Reg.r8 = .r7 by decide)]
  refine WP.seq (WP.of_runBlock ⟨s1, e1, ?_⟩)
  refine WP.seq (WP.loop (M := isa) (fun m t => RoundsInv d s m t) ?_ 16 s1 ?_)
  · intro m t inv
    have hi : 16 - m < 16 := by have := inv.le; omega_arith
    obtain ⟨hk0, hk1, hdis⟩ := hk (16 - m) hi
    have hk0' : InRegions (t.rd ++ t.wr) (t.gpr .r3) 4 := by rw [inv.rd, inv.wr, inv.r3]; exact hk0
    have hk1' : InRegions (t.rd ++ t.wr) (t.gpr .r3 + 4) 4 := by rw [inv.rd, inv.wr, inv.r3]; exact hk1
    obtain ⟨t', ht', hq, hroom, hrd, hwr, hsp, hr3, hr7, hx1, hx2, hx0, hx6, hx5, hfr⟩ :=
      round_ok d inv.room hk0' hk1'
    -- The key, from the original memory.
    have hkey : (t.mem.readW (t.gpr .r3) 32, t.mem.readW (t.gpr .r3 + 4) 32) =
        keysAt d s.mem (s.gpr .r3) (16 - m) := by
      simp only [keysAt, inv.r3]
      have hd : ∀ r ∈ [workR s], Region.Disjoint ⟨kp d (s.gpr .r3) (16 - m), 8⟩ r := by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact hdis.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
      refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
      · exact inv.frame.readW (contains_prefix (by decide)) hd (by decide)
      · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
        exact inv.frame.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith))
          hd (by decide)
    refine WP.of_runBlock ⟨t', ht', ?_⟩
    have hquads : ∀ b < 16, quad t' b = roundsN (keysAt d s.mem (s.gpr .r3)) (16 - (m - 1)) (quad s b) := by
      intro b hb
      rw [hq b hb, hkey, inv.quads b hb, show 16 - (m - 1) = 16 - m + 1 by have := inv.le; omega_arith,
        roundsN_succ]
    have hr7' : t'.gpr .r7 = BitVec.ofNat 64 (m - 1) := by
      rw [hr7, inv.r7, r7_sub m inv.le.1 inv.le.2]
    have hregs : ∀ r ∈ [Reg.r2, .r4, .r5, .r6, .r8], t'.gpr r = s.gpr r := by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hx0]; exact inv.regs _ (by simp)
      · rw [hx1]; exact inv.regs _ (by simp)
      · rw [hx2]; exact inv.regs _ (by simp)
      · rw [hx6]; exact inv.regs _ (by simp)
      · rw [hx5]; exact inv.regs _ (by simp)
    have hframe : Frame [workR s] s.mem t'.mem := by
      refine inv.frame.trans ?_
      simpa [workR, inv.regs .r8 (by simp)] using hfr
    have hc : isa.eval (.nonzero .d .r7) t' = some (BitVec.ofNat 64 (m - 1) != 0) := by
      show some (t'.read .d .r7 != 0) = _
      rw [show t'.read .d .r7 = t'.gpr .r7 from BitVec.setWidth_eq _, hr7']
    by_cases hm1 : m = 1
    · subst hm1
      left
      refine ⟨by rw [hc]; rfl, ?_⟩
      let u := t'.write .r3 (t'.gpr .r3 - BitVec.ofNat 64 16 * stepW d)
      refine WP.of_runBlock ⟨u, by rw [runBlock_cons, exec_keyBack, runStep_some, runBlock_nil], ?_⟩
      have hu5 : u.gpr .r8 = t'.gpr .r8 := gpr_write_of_ne _ _ (by decide)
      refine ⟨fun b hb => ?_, room_congr hroom hu5 rfl, by rw [rd_write, hrd, inv.rd],
        by rw [wr_write, hwr, inv.wr], by rw [sp_write, hsp, inv.sp], fun r hr => ?_, by rw [mem_write]; exact hframe⟩
      · have : quad u b = quad t' b := by simp only [quad, u, lv_write _ _ (show ¬ Reg.r8 = .r3 by decide)]
        rw [this, hquads b hb]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | hr
        · rw [gpr_write_of_ne _ _ (by decide)]; exact hregs _ (by simp)
        · rw [gpr_write_self, hr3, inv.r3, kp_succ, kp_back]
        · rw [gpr_write_of_ne _ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
          exact hregs _ (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; exact .inr hr)
    · right
      refine ⟨?_, m - 1, by omega_arith, ⟨by have := inv.le; omega_arith, hquads, hroom, by rw [hrd, inv.rd],
        by rw [hwr, inv.wr], by rw [hsp, inv.sp], ?_, hr7', hregs, hframe⟩⟩
      · rw [hc]
        have : (BitVec.ofNat 64 (m - 1) != 0) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h0
          have hm2 : 2 ≤ m := by have := inv.le; omega_arith
          have hm16 := inv.le.2
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (by omega_arith)] at this
          omega_arith
        rw [this]
      · rw [hr3, inv.r3, kp_succ, show 16 - m + 1 = 16 - (m - 1) by have := inv.le; omega_arith]
  · refine ⟨by omega_arith, fun b _ => by rw [q1]; rfl, room_congr h rfl rfl, rfl, rfl, rfl,
      by simp [s1, kp, gpr_write], rfl, fun r hr => ?_, Frame.refl _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.Copy`, which only this module used -/

section

/-!
# Copying blocks into the arrays and back

As on x86-64: `copyIn_loop`: the loop of `copyInBody` copies `m` blocks from
`p` into lanes `0 … m - 1` of the arrays, each word byte-reversed (`bw`, a
block's big-endian word). `copyOut_loop`: the loop of `copyOutBody` copies
them back, `R` first.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  rev32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

theorem mem_arrA_of {w : Nat} (hw : w < 4) : arrSlot w ∈ arrays := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- What the copy into the arrays needs. -/
structure CopyPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  read : ∀ b < m, ∀ w < 4, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy in. -/
structure CopyInInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  r6 : s.gpr .r6 = p + BitVec.ofNat 64 (16 * j)
  r7 : s.gpr .r7 = s₀.gpr .r8 + BitVec.ofNat 64 (4 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  [.li .r9 (4 * w), .loadRev .w .r9 .r6 .r9, .store .w .r9 .r7 (8 * arrSlot w)]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)))) := rfl

theorem arr_off (w j : Nat) (b : Addr) :
    b + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (8 * arrSlot w) = b + BitVec.ofNat 64 (8 * arrSlot w + 4 * j) := by
  rw [Offset.add_add, Nat.add_comm]

theorem arr_ok {w : Nat} (hw : w < 4) : 8 * arrSlot w % 4 = 0 ∧ 8 * arrSlot w < 16384 := by
  unfold arrSlot; omega_arith

/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (rev32 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) := by
  obtain hL : arrSlot w ∈ arrays := mem_arrA_of hw
  obtain hla : s.gpr .r7 + BitVec.ofNat 64 (8 * arrSlot w) = laneA s (arrSlot w) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold inWord
  let v := s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32
  let s1 := s.write .r9 (BitVec.ofNat 64 (4 * w))
  let s2 := s1.write .r9 ((rev32 v).setWidth 64)
  obtain h6 : s1.gpr .r6 = s.gpr .r6 := gpr_write_of_ne _ _ (by decide)
  obtain h9 : s1.gpr .r9 = BitVec.ofNat 64 (4 * w) := gpr_write_self _ _ _
  obtain e1 : exec (.li .r9 (4 * w)) s = some s1 := exec_li (by omega_arith)
  obtain e2 : exec (.loadRev .w .r9 .r6 .r9) s1 = some s2 := by
    rw [exec_loadRev_w (by decide) (by rw [h6, h9]; exact hr), h6, h9]; rfl
  obtain h4 : s2.gpr .r7 = s.gpr .r7 := by simp [s2, s1, gpr_write]
  obtain e3 := exec_store_w (s := s2) (t := .r9) (n := .r7) (off := 8 * arrSlot w) (by decide)
    (by have := arr_ok hw; omega_arith) (by rw [h4, hla]; simp only [s2, s1, wr_write]; exact lane_wr h hL hj)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h4, hla]
    simp [s2, s1, gpr_write, mem_write, setWidth_setWidth_32, v]
  · simp [s2, s1, gpr_write, hr]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => rev32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .r6)) j ∧
      s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r7 = s.gpr .r7 + 4 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  obtain hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  obtain h1 : Room s1 := room_congr h (g1 _ (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), g1 _ (by decide), hrb]) (by rw [rd1, wr1, g1 _ (by decide)]; exact hr 1 (by decide))
  obtain h2 : Room s2 := room_congr h1 (g2 _ (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g2 _ (by decide), g1 _ (by decide), g1 _ (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide), g1 _ (by decide)]; exact hr 2 (by decide))
  obtain h3 : Room s3 := room_congr h2 (g3 _ (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g3 _ (by decide), g2 _ (by decide), g2 _ (by decide), g1 _ (by decide),
      g1 _ (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)];
        exact hr 3 (by decide))
  let s5 := s4.write .r6 (s4.gpr .r6 + BitVec.ofNat _ 16)
  let s6 := s5.write .r7 (s5.gpr .r7 + BitVec.ofNat _ 4)
  let s7 := s6.write .r10 (s6.gpr .r10 - BitVec.ofNat _ 1)
  obtain hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, exec_addi' (n := .r6) (by decide),
      runStep_some, runBlock_cons, exec_addi' (n := .r7) (by decide), runStep_some, runBlock_cons,
      exec_subi' (n := .r10) (by decide), runStep_some, runBlock_nil]
  -- Registers through the words.
  obtain r9s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r8 = s.gpr .r8 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r6 = s.gpr .r6 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain lA : ∀ t ∈ [s1, s2, s3, s4], ∀ k, laneA t k j = laneA s k j := by
    intro t ht k; simp only [laneA, r9s t ht]
  -- Memory.
  let v (w : Nat) := rev32 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32)
  obtain f1 : Frame [arraysR s] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f2 : Frame [arraysR s] s.mem s2.mem := by
    rw [m2, lA s1 (by simp)]; exact f1.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain f3 : Frame [arraysR s] s.mem s3.mem := by
    rw [m3, lA s2 (by simp)]; exact f2.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  obtain mm : s4.mem = (((s.mem.writeW (laneA s (arrSlot 0) j) (v 0)).writeW (laneA s (arrSlot 1) j) (v 1)).writeW
      (laneA s (arrSlot 2) j) (v 2)).writeW (laneA s (arrSlot 3) j) (v 3) := by
    rw [m4, lA s3 (by simp), r10s s3 (by simp), hkeep s3 f3 3 (by decide), m3, lA s2 (by simp),
      r10s s2 (by simp), hkeep s2 f2 2 (by decide), m2, lA s1 (by simp), r10s s1 (by simp),
      hkeep s1 f1 1 (by decide), m1]
  obtain r10_4 := r10s s4 (by simp)
  obtain rbx_4 : s4.gpr .r7 = s.gpr .r7 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .r10 = s.gpr .r10 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · simp [s7, s6, s5, gpr_write, r10_4]
  · simp [s7, s6, s5, gpr_write, rbx_4]
  · simp [s7, s6, s5, gpr_write, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 != 0) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith)] at this
  omega_arith

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  r7_sub k h1 h2

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) (.nonzero .d .r10)) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .r7 = t.gpr .r8 + BitVec.ofNat 64 (4 * j) := by rw [inv.r7, hr9]
  obtain hdata : ∀ w < 4, t.gpr .r6 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.r6, Offset.add_add]
  obtain hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .r6 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr, hsp, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  obtain hr9' : t'.gpr .r8 = t.gpr .r8 := hregs _ (by decide) (by decide) (by decide) (by decide)
  obtain inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.r7, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.r10, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .r6)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hr9']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega_arith) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        obtain hkeep : t.mem.readW (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega_arith)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .r6)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .d .r10 != 0) = some false
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show some (t'.read .d .r10 != 0) = some true
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]

/-! ## Copying out -/

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem rev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (rev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  obtain e : ((rev32 x).extractLsb' (8 * j) 8).getLsbD i = (rev32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold rev32
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.2]; simp [BitVec.getLsbD_extractLsb', hi]

/-- A byte of the 4 bytes a 32-bit write writes. -/
theorem writeW32_at (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h1 : d ≤ i) (h2 : i < d + 4)
    (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * (i - d)) 8 := by
  simp only [Mem.writeW, Mem.write, Offset.sub_toNat a h1 hi, show i - d < 32 / 8 by omega_arith, ite_true,
    BitVec.setWidth_eq]

/-- A byte outside the 4 bytes a 32-bit write writes. -/
theorem writeW32_off (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h : i < d ∨ d + 4 ≤ i)
    (hd : d + 4 ≤ 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i) := by
  apply Mem.write_apply
  have := Offset.sep a (d := i) (n := 1) (e := d) (k := 4) (by omega_arith) (by omega_arith) hd
  exact this _ (by simp)

/-- The four byte-swapped words `y` written from `a` are the block of their big-endian bytes. -/
theorem block_writes (m : Mem) (a : Addr) (y : Nat → BitVec 32) {i : Nat} (hi : i < 16) :
    ((((m.writeW (a + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (a + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (a + BitVec.ofNat 64 12) (rev32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega_arith) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
      rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith
  · rw [writeW32_at _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), rev32_byte _ (by omega_arith), h]
    congr 3; omega_arith

/-- The copy of word `w` of a block out: the lane loaded byte-reversed, and
stored. -/
def outWord (w : Nat) : List Instr :=
  [.li .r9 (8 * arrSlot ((w + 2) % 4)), .loadRev .w .r9 .r7 .r9, .store .w .r9 .r6 (4 * w)]

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)))) := rfl

theorem copyOutWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 (4 * w))
        (rev32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) := by
  obtain hw' : (w + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of hw'
  obtain hla : s.gpr .r7 + BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold outWord
  let s1 := s.write .r9 (BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)))
  let s2 := s1.write .r9 ((rev32 (lv s (arrSlot ((w + 2) % 4)) j)).setWidth 64)
  obtain h7 : s1.gpr .r7 = s.gpr .r7 := gpr_write_of_ne _ _ (by decide)
  obtain h9 : s1.gpr .r9 = BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) := gpr_write_self _ _ _
  obtain e1 : exec (.li .r9 (8 * arrSlot ((w + 2) % 4))) s = some s1 :=
    exec_li (by have := arr_ok hw'; omega_arith)
  obtain e2 : exec (.loadRev .w .r9 .r7 .r9) s1 = some s2 := by
    rw [exec_loadRev_w (by decide) (by rw [h7, h9, hla]; exact lane_rw h hL hj), h7, h9, hla]; rfl
  obtain h3 : s2.gpr .r6 = s.gpr .r6 := by simp [s2, s1, gpr_write]
  obtain e3 := exec_store_w (s := s2) (t := .r9) (n := .r6) (off := 4 * w) (by decide) (by omega_arith)
    (by rw [h3]; simp only [s2, s1, wr_write]; exact hwr)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h3]
    simp [s2, s1, gpr_write, mem_write, setWidth_setWidth_32]
  · simp [s2, s1, gpr_write, hr]

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (q + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (q + BitVec.ofNat 64 12) (rev32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .r6, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .r6) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r7 = s.gpr .r7 + 4 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  obtain hkeep : ∀ (t : State), t.gpr .r8 = s.gpr .r8 → Frame [⟨s.gpr .r6, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyOutWord_ok (w := 0) (by decide) hj s h hrb (hwr 0 (by decide))
  obtain r9_1 : s1.gpr .r8 = s.gpr .r8 := g1 _ (by decide)
  obtain h1 : Room s1 := room_congr h r9_1 wr1
  obtain hin : ∀ w < 4, (⟨s.gpr .r6, 16⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain f1 : Frame [⟨s.gpr .r6, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyOutWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), r9_1, hrb]) (by rw [wr1, g1 _ (by decide)]; exact hwr 1 (by decide))
  obtain r9_2 : s2.gpr .r8 = s.gpr .r8 := by rw [g2 _ (by decide), r9_1]
  obtain h2 : Room s2 := room_congr h r9_2 (by rw [wr2, wr1])
  obtain r10_1 : s1.gpr .r6 = s.gpr .r6 := g1 _ (by decide)
  obtain f2 : Frame [⟨s.gpr .r6, 16⟩] s.mem s2.mem := by
    rw [m2, r10_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyOutWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g1 _ (by decide), r9_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide), r10_1]; exact hwr 2 (by decide))
  obtain r9_3 : s3.gpr .r8 = s.gpr .r8 := by rw [g3 _ (by decide), r9_2]
  obtain h3 : Room s3 := room_congr h r9_3 (by rw [wr3, wr2, wr1])
  obtain r10_2 : s2.gpr .r6 = s.gpr .r6 := by rw [g2 _ (by decide), r10_1]
  obtain f3 : Frame [⟨s.gpr .r6, 16⟩] s.mem s3.mem := by
    rw [m3, r10_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyOutWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r9_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide), r10_2]; exact hwr 3 (by decide))
  obtain r10_3 : s3.gpr .r6 = s.gpr .r6 := by rw [g3 _ (by decide), r10_2]
  let s5 := s4.write .r6 (s4.gpr .r6 + BitVec.ofNat _ 16)
  let s6 := s5.write .r7 (s5.gpr .r7 + BitVec.ofNat _ 4)
  let s7 := s6.write .r10 (s6.gpr .r10 - BitVec.ofNat _ 1)
  obtain hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons,
      exec_addi' (n := .r6) (by decide), runStep_some, runBlock_cons, exec_addi' (n := .r7) (by decide), runStep_some,
      runBlock_cons, exec_subi' (n := .r10) (by decide), runStep_some, runBlock_nil]
  obtain rbx_4 : s4.gpr .r7 = s.gpr .r7 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain rcx_4 : s4.gpr .r10 = s.gpr .r10 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  obtain r10_4 : s4.gpr .r6 = s.gpr .r6 := by rw [g4 _ (by decide), r10_3]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [m4, r10_3, hkeep s3 r9_3 f3 3 (by decide), m3, r10_2,
      hkeep s2 r9_2 f2 2 (by decide), m2, r10_1, hkeep s1 r9_1 f1 1 (by decide), m1, outWrites]
  · simp [s7, s6, s5, gpr_write, r10_4]
  · simp [s7, s6, s5, gpr_write, rbx_4]
  · simp [s7, s6, s5, gpr_write, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem outWrites_off (m : Mem) (q : Addr) (y : Nat → BitVec 32) {x : Addr}
    (h : ¬ (x - q).toNat < 16) : outWrites m q y x = m x := by
  obtain hx : x = q + BitVec.ofNat 64 (x - q).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  obtain hlt := (x - q).isLt
  obtain hoff : ∀ c : Nat, c ≤ 12 → ¬ (x - (q + BitVec.ofNat 64 c)).toNat < 32 / 8 := by
    intro c hc
    have := Offset.sep q (d := (x - q).toNat) (n := 1) (e := c) (k := 4) (by omega_arith) (by omega_arith) (by omega_arith)
    refine this x ?_
    rw [← hx, BitVec.sub_self]; decide
  simp only [outWrites, Mem.writeW]
  rw [Mem.write_apply (hoff 12 (by decide)), Mem.write_apply (hoff 8 (by decide)),
    Mem.write_apply (hoff 4 (by decide)), Mem.write_apply (hoff 0 (by decide))]

theorem outWrites_frame {m₀ m : Mem} {p : Addr} {n j : Nat} (h : Frame [⟨p, n⟩] m₀ m) (hj : 16 * j + 16 ≤ n)
    (hn : n < 2 ^ 64) (y : Nat → BitVec 32) :
    Frame [⟨p, n⟩] m₀ (outWrites m (p + BitVec.ofNat 64 (16 * j)) y) := by
  obtain hc : ∀ c, c ≤ 12 → (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 c) (32 / 8) := by
    intro c hc; rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  exact (((h.writeW List.mem_cons_self _ (hc 0 (by decide))).writeW List.mem_cons_self _ (hc 4 (by decide))).writeW
    List.mem_cons_self _ (hc 8 (by decide))).writeW List.mem_cons_self _ (hc 12 (by decide))

/-- Byte `i` of block `b` copied out: byte `3 - i % 4` of word `(i / 4 + 2) % 4` of lane `b`. -/
def outByte (s : State) (b i : Nat) : Byte := (lv s (arrSlot ((i / 4 + 2) % 4)) b >>> (8 * (3 - i % 4))).setWidth 8

/-- What the copy out of the arrays needs. -/
structure CopyOutPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  write : ∀ b < m, ∀ w < 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy out. -/
structure CopyOutInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  r6 : s.gpr .r6 = p + BitVec.ofNat 64 (16 * j)
  r7 : s.gpr .r7 = s₀.gpr .r8 + BitVec.ofNat 64 (4 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) (.nonzero .d .r10)) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  obtain hj : j < 16 := by omega_arith
  obtain hr9 : t.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  obtain hroom : Room t := room_congr hpre.room hr9 inv.wr
  obtain hrb : t.gpr .r7 = t.gpr .r8 + BitVec.ofNat 64 (4 * j) := by rw [inv.r7, hr9]
  obtain hwr : ∀ w < 4, InRegions t.wr (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.r6, Offset.add_add, inv.wr]; exact hpre.write j (by omega_arith) w hw
  obtain harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  obtain hsep : Region.Disjoint ⟨t.gpr .r6, 16⟩ (arraysR t) := by
    rw [inv.r6, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega_arith))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr', hsp, hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  obtain hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hr9]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  obtain inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega_arith, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.r7, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.r10, show m - j = k by omega_arith, cnt_sub1 hk1 (by omega_arith)]; congr 1; omega_arith
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .r6 + BitVec.ofNat 64 i by
          rw [inv.r6, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega_arith)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega_arith) i hi
        · rw [inv.r6, Offset.sub_toNat' p (by omega_arith) (by omega_arith)]
          split <;> omega_arith
    · rw [hmem, inv.r6]
      exact outWrites_frame inv.frame (by omega_arith) (by omega_arith) _
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    obtain hjm : j + 1 = m := by omega_arith
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .d .r10 != 0) = some false
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - 1) = 1 by omega_arith]; rfl
  · right
    refine ⟨?_, k - 1, by omega_arith, ⟨by simpa [show j + 1 = m - (k - 1) by omega_arith] using inv', by omega_arith, by omega_arith⟩⟩
    show some (t'.read .d .r10 != 0) = some true
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - k) = k by omega_arith, cnt_ne_zero (by omega_arith) (by omega_arith)]

end VG.Proof.Seed.PPC64LE

end

end


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

theorem batchSize_ok (s : State) :
    WP isa batchSize s (fun s' => s'.gpr .r10 = BitVec.ofNat 64 (min (s.gpr .r5).toNat 16) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp) := by
  let s₁ := s.write .r10 (s.gpr .r5 >>> 4)
  obtain e₁ : runBlock isa [shrI .r10 .r5 4] s = some s₁ := by
    rw [runBlock_cons, shrI, exec_lsr_d (by decide), runStep_some, runBlock_nil]
  obtain g₁ : ∀ r, r ≠ .r10 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  obtain hc : isa.eval (.nonzero .d .r10) s₁ = some (decide (16 ≤ (s.gpr .r5).toNat)) := by
    show some (s₁.read .d .r10 != 0) = _
    rw [show s₁.read .d .r10 = s₁.gpr .r10 from BitVec.setWidth_eq _, gpr_write_self]
    congr 1
    by_cases h : 16 ≤ (s.gpr .r5).toNat
    · simp only [h, decide_true, bne_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ushiftRight] at this
      simp at this; omega_using [h, this]
    · simp only [h, decide_false, bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight]; simp; omega
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite _ hc (fun hb => ?_) (fun hb => ?_)
  · have hge := of_decide_eq_true hb
    let s₂ := s₁.write .r10 ((16 : BitVec 16).setWidth 64 <<< (16 * 0))
    refine WP.of_runBlock ⟨s₂, rfl, ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, Nat.min_eq_right (by omega_using [hge])]; rfl
    · rw [gpr_write_of_ne _ _ hr, g₁ r hr]
  · have hlt := of_decide_eq_false hb
    refine WP.of_runBlock ⟨s₁.write .r10 (s₁.gpr .r5), by rw [runBlock_cons, exec_movR, runStep_some,
      runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, g₁ _ (by decide), Nat.min_eq_left (by omega_using [hlt]),
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
  obtain hk : ∀ w < 4, (#v[(quad t b).2.2.1, (quad t b).2.2.2, (quad t b).1, (quad t b).2.1] :
      Vector Spec.Seed.Word 4).getD w 0 = lv t (arrSlot ((w + 2) % 4)) b := by
    intro w hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_using [hw]) with rfl | rfl | rfl | rfl <;> rfl
  simp only [encodeSwapped, Vector.getElem_ofFn, outByte]
  rw [hk _ (by omega_using [hi])]

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
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [scratchR s, ⟨s.gpr .r4, 16 * min (s.gpr .r5).toNat 16⟩] s.mem s'.mem

theorem arraysR_sub_scratch (s : State) : Region.Sub (arraysR s) (scratchR s) := by
  show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .r8, 8 * scratchSlots⟩
  exact Offset.sub_base _ (by unfold scratchSlots; omega_using [])

theorem arraysR_sub_work (s : State) : Region.Sub (arraysR s) (workR s) := by
  show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * 48), 8 * 64⟩ ⟨s.gpr .r8, 8 * 112⟩
  exact Offset.sub_base _ (by omega_using [])

/-! ## The rounds, between the registers saved and restored -/

/-- The saved registers' slots, 112 to 129. -/
def savedR (s : State) : Region := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * 112), 8 * 18⟩

/-- Stores to the saved registers' slots change nothing else. -/
theorem stores_frame (l : List (Nat × Reg)) (hl : ∀ p ∈ l, 112 ≤ p.1 ∧ p.1 < scratchSlots) {s s' : State}
    (h : Room s) (e : runBlock isa (l.map fun p => stS p.1 p.2) s = some s') :
    Frame [savedR s] s.mem s'.mem := by
  induction l generalizing s with
  | nil =>
    rw [List.map_nil, runBlock_nil] at e
    cases e; exact Frame.refl _ _
  | cons p l ih =>
    obtain hp := hl p List.mem_cons_self
    rw [List.map_cons, runBlock_cons, exec_st h hp.2 p.2, runStep_some] at e
    obtain f := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (s := setMem s (stMem s p.1 (s.gpr p.2))) h e
    have hs : scratchSlots = 130 := rfl
    obtain f₀ : Frame [savedR s] s.mem (stMem s p.1 (s.gpr p.2)) :=
      (Frame.refl _ _).writeW List.mem_cons_self _
        (show (savedR s).Contains (s.gpr .r8 + BitVec.ofNat 64 (8 * p.1)) (64 / 8) from
          Offset.contains _ (by omega_using [hp]) (by omega_using [hp, hs]) (by omega_using []))
    exact f₀.trans f

theorem saveRegs_eq : Impl.Seed.PPC64LE.saveRegs = (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)).map
    (fun p => stS p.1 p.2) := rfl

theorem restore_eq : restore = Impl.Seed.PPC64LE.savedRegs.map (fun p => ldS p.1 p.2) := rfl

theorem savedRegs_ok : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, p.2 < scratchSlots ∧ p.1 ≠ .r8 ∧ 112 ≤ p.2 := by
  decide

/-- The registers saved, the rounds, and the registers restored: the rounds'
effect on the lanes, and the saved registers as they were. -/
theorem rounds_saved_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hk : KeysOk d s (s.gpr .r3)) :
    WP isa (roundsSaved d) s (fun s' =>
      (∀ b < 16, quad s' b = roundsN (keysAt d s.mem (s.gpr .r3)) 16 (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r8], s'.gpr r = s.gpr r) ∧
      (∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧
      Frame [scratchR s] s.mem s'.mem) := by
  have hs : scratchSlots = 130 := rfl
  obtain ⟨s₁, e₁, g₁, rd₁, wr₁, sp₁, f₁, set₁, -⟩ := stores_ok h
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  obtain fs₁ : Frame [savedR s] s.mem s₁.mem := stores_frame _ (by decide) h e₁
  refine WP.seq (WP.of_runBlock ⟨s₁, by rw [saveRegs_eq]; exact e₁, ?_⟩)
  obtain r8₁ : s₁.gpr .r8 = s.gpr .r8 := by rw [g₁]
  obtain room₁ : Room s₁ := room_congr h r8₁ wr₁
  obtain scr₁ : scratchR s₁ = scratchR s := by simp only [scratchR, r8₁]
  obtain keys₁ : KeysOk d s₁ (s₁.gpr .r3) := by
    rw [g₁]
    intro j hj
    obtain ⟨a, b, c⟩ := hk j hj
    exact ⟨by rw [rd₁, wr₁]; exact a, by rw [rd₁, wr₁]; exact b, by rw [scr₁]; exact c⟩
  obtain hkeys : ∀ j < 16, keysAt d s₁.mem (s₁.gpr .r3) j = keysAt d s.mem (s.gpr .r3) j := by
    intro j hj
    rw [g₁]
    obtain ⟨-, -, hdis⟩ := hk j hj
    obtain hd : ∀ r ∈ [scratchR s], Region.Disjoint ⟨kp d (s.gpr .r3) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hdis
    simp only [keysAt]
    refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
    · exact f₁.readW (contains_prefix (by decide)) hd (by decide)
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
      exact f₁.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_using []) (by omega_using [])) hd (by decide)
  obtain lv₁ : ∀ w < 4, ∀ b < 16, lv s₁ (arrSlot w) b = lv s (arrSlot w) b := by
    intro w hw b hb
    simp only [lv, laneA, r8₁]
    refine fs₁.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (Or.inl (by simp only [arrSlot]; omega_using [hw, hb])) (by simp only [arrSlot]; omega_using [hw, hb]) (by omega_using [])
  obtain quad₁ : ∀ b < 16, quad s₁ b = quad s b := fun b hb => by
    simp only [quad, lv₁ 0 (by decide) b hb, lv₁ 1 (by decide) b hb, lv₁ 2 (by decide) b hb,
      lv₁ 3 (by decide) b hb]
  refine WP.seq (WP.mono (rounds_ok d room₁ keys₁) fun s₂ ⟨q₂, room₂, rd₂, wr₂, sp₂, g₂, f₂⟩ => ?_)
  obtain r8₂ : s₂.gpr .r8 = s.gpr .r8 := (g₂ _ (by simp)).trans r8₁
  obtain ⟨s', run', m', sp', set', keep', rd', wr'⟩ := loads_ok room₂ Impl.Seed.PPC64LE.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact run', ?_⟩
  obtain notSaved : ∀ r ∈ [Reg.r2, .r3, .r4, .r5, .r6, .r8], ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, p.1 ≠ r := by
    decide
  obtain r8' : s'.gpr .r8 = s.gpr .r8 := (keep' _ (notSaved .r8 (by simp))).trans r8₂
  refine ⟨fun b hb => ?_, room_congr room₂ (r8'.trans r8₂.symm) wr', by rw [rd', rd₂, rd₁],
    by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], fun r hr => ?_, fun p hp => ?_, ?_⟩
  · rw [show quad s' b = quad s₂ b by simp only [quad, lv, laneA, m', r8', r8₂], q₂ b hb,
      roundsN_congr 16 _ hkeys, quad₁ b hb]
  · rw [keep' r (notSaved r hr), g₂ r hr, g₁]
  · have hp' := savedRegs_ok p hp
    rw [set' p hp, ← set₁ (p.2, p.1) (List.mem_map_of_mem hp)]
    show s₂.mem.readW (StraightK.wordAddr (s₂.gpr .r8) p.2) 64 =
      s₁.mem.readW (StraightK.wordAddr (s₁.gpr .r8) p.2) 64
    rw [r8₂, ← r8₁]
    refine f₂.readW (r := ⟨StraightK.wordAddr (s₁.gpr .r8) p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    simp only [workR]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [m']
    refine f₁.trans (f₂.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨scratchR s, List.mem_cons_self, ?_⟩
    simp only [workR, scratchR, r8₁]; exact Region.sub_prefix (by omega_using [hs])

theorem batch_ok (d : Spec.Seed.Direction) {s : State} (h : BatchPre d s) :
    WP isa (batch d) s (BatchPost d s) := by
  let n := (s.gpr .r5).toNat
  let k := min n 16
  let p := s.gpr .r4
  obtain hk1 : 1 ≤ k := by have := h.pos; omega
  obtain hk16 : k ≤ 16 := by omega_using []
  have hpos := h.pos
  -- the copy in
  apply WP.seq
  apply WP.seq
  refine WP.mono (batchSize_ok s) fun s₁ ⟨c₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  apply WP.seq
  obtain ⟨s₂, e₂, r6₂, r7₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := copyStart_ok s₁
  refine WP.of_runBlock ⟨s₂, e₂, ?_⟩
  obtain G₂ : ∀ r, r ≠ .r10 → r ≠ .r6 → r ≠ .r7 → s₂.gpr r = s.gpr r := fun r a b c =>
    (g₂ r b c).trans (g₁ r a)
  obtain r8₂ : s₂.gpr .r8 = s.gpr .r8 := G₂ _ (by decide) (by decide) (by decide)
  obtain scr₂ : scratchR s₂ = scratchR s := by simp only [scratchR, r8₂]
  obtain arr₂ : arraysR s₂ = arraysR s := by simp only [arraysR, r8₂]
  obtain room₂ : Room s₂ := room_congr h.room r8₂ (by rw [wr₂, wr₁])
  obtain pre₂ : CopyPre s₂ p k := by
    refine ⟨room₂, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · obtain ⟨r, hr, hc⟩ := h.data b hb w hw
      exact ⟨r, by rw [rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_right _ hr, hc⟩
    · rw [arr₂]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₂ : CopyInInv s₂ p k (k - k) s₂ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun w _ b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [r6₂, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₁ _ (by decide)]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, r7₂, g₂ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₂ _ (by decide) (by decide), c₁]
  refine WP.mono (copyIn_loop pre₂ k s₂ inv₂ hk1 (Nat.le_refl _)) fun s₃ i₃ => ?_
  obtain r8₃ : s₃.gpr .r8 = s.gpr .r8 := (i₃.regs _ (by decide) (by decide) (by decide) (by decide)).trans r8₂
  obtain G₃ : ∀ r ∈ [Reg.r3, .r4, .r5], s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r10 ∧ r ≠ .r6 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    rw [i₃.regs _ this.1 this.2.1 this.2.2.1 this.2.2.2]
    exact G₂ _ this.2.2.1 this.2.2.2 this.2.1
  obtain rd₃ : s₃.rd = s.rd := by rw [i₃.rd, rd₂, rd₁]
  obtain wr₃ : s₃.wr = s.wr := by rw [i₃.wr, wr₂, wr₁]
  obtain sp₃ : s₃.sp = s.sp := by rw [i₃.sp, sp₂, sp₁]
  obtain room₃ : Room s₃ := room_congr h.room r8₃ wr₃
  obtain f₃ : Frame [arraysR s] s.mem s₃.mem := by
    have := i₃.frame; rw [arr₂, m₂, m₁] at this; exact this
  obtain scr₃ : scratchR s₃ = scratchR s := by simp only [scratchR, r8₃]
  obtain keys₃ : KeysOk d s₃ (s₃.gpr .r3) := by
    rw [G₃ .r3 (by simp)]
    intro j hj
    obtain ⟨a, b, c⟩ := h.keys j hj
    exact ⟨by rw [rd₃, wr₃]; exact a, by rw [rd₃, wr₃]; exact b, by rw [scr₃]; exact c⟩
  -- the keys are as on entry
  obtain hkeys : ∀ j < 16, keysAt d s₃.mem (s₃.gpr .r3) j = keysAt d s.mem (s.gpr .r3) j := by
    intro j hj
    rw [G₃ .r3 (by simp)]
    obtain ⟨-, -, hdis⟩ := h.keys j hj
    obtain hd : ∀ r ∈ [arraysR s], Region.Disjoint ⟨kp d (s.gpr .r3) j, 8⟩ r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact hdis.sub_right (arraysR_sub_scratch s)
    simp only [keysAt]
    refine Eq.mpr (Prod.mk.injEq _ _ _ _) ⟨?_, ?_⟩
    · exact f₃.readW (contains_prefix (by decide)) hd (by decide)
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
      exact f₃.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_using []) (by omega_using [])) hd (by decide)
  -- the blocks, in the lanes
  obtain hq₃ : ∀ b < k, quad s₃ b = decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    refine quad_of_lanes fun w hw => ?_
    rw [i₃.lanes w hw b hb, m₂, m₁]
  -- the rounds
  apply WP.seq
  refine WP.mono (rounds_saved_ok d room₃ keys₃) fun s₄ ⟨q₄, room₄, rd₄, wr₄, sp₄, g₄, sv₄, f₄⟩ => ?_
  obtain G₄ : ∀ r ∈ [Reg.r3, .r4, .r5, .r8], s₄.gpr r = s.gpr r := by
    intro r hr
    rw [g₄ r (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp)]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact G₃ _ (by simp)
    · exact r8₃
  obtain hq₄ : ∀ b < k, quad s₄ b = roundsN (keysAt d s.mem (s.gpr .r3)) 16
      (decodeQ (Spec.Seed.blockAt s.mem (p + BitVec.ofNat 64 (16 * b)))) := by
    intro b hb
    rw [q₄ b (by omega_using [hb]), hq₃ b hb]
    exact roundsN_congr 16 _ hkeys
  -- the copy out
  apply WP.seq
  refine WP.mono (batchSize_ok s₄) fun s₅ ⟨c₅, g₅, m₅, rd₅, wr₅, sp₅⟩ => ?_
  apply WP.seq
  obtain ⟨s₆, e₆, r6₆, r7₆, g₆, m₆, rd₆, wr₆, sp₆⟩ := copyStart_ok s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain G₆ : ∀ r, r ≠ .r10 → r ≠ .r6 → r ≠ .r7 → s₆.gpr r = s₄.gpr r := fun r a b c =>
    (g₆ r b c).trans (g₅ r a)
  obtain r8₆ : s₆.gpr .r8 = s.gpr .r8 := (G₆ _ (by decide) (by decide) (by decide)).trans (G₄ _ (by simp))
  obtain r5₄ : s₄.gpr .r5 = s.gpr .r5 := G₄ _ (by simp)
  obtain r4₄ : s₄.gpr .r4 = p := G₄ _ (by simp)
  obtain rd₆ : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  obtain wr₆ : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  obtain sp₆ : s₆.sp = s.sp := by rw [sp₆, sp₅, sp₄, sp₃]
  obtain arr₆ : arraysR s₆ = arraysR s := by simp only [arraysR, r8₆]
  obtain pre₆ : CopyOutPre s₆ p k := by
    refine ⟨room_congr h.room r8₆ wr₆, ⟨hk1, hk16⟩, fun b hb w hw => ?_, ?_⟩
    · rw [wr₆]; exact h.data b hb w hw
    · rw [arr₆]; exact h.dataSep.sub_right (arraysR_sub_scratch s)
  obtain inv₆ : CopyOutInv s₆ p k (k - k) s₆ := by
    refine ⟨by omega_using [], ?_, ?_, ?_, fun b hb => by omega, Frame.refl _ _, fun _ _ _ _ _ => rfl, rfl, rfl,
      rfl⟩
    · rw [r6₆, Nat.sub_self, Nat.mul_zero, ofNat_zero_add, g₅ _ (by decide), r4₄]
    · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add, r7₆, g₆ _ (by decide) (by decide)]
    · rw [Nat.sub_self, Nat.sub_zero, g₆ _ (by decide) (by decide), c₅, r5₄]
  obtain quad₆ : ∀ b, quad s₆ b = quad s₄ b := fun b => by
    simp only [quad, lv, laneA, m₆, m₅, r8₆, G₄ .r8 (by simp)]
  apply WP.seq
  refine WP.mono (copyOut_loop pre₆ k s₆ inv₆ hk1 (Nat.le_refl _)) fun s₇ i₇ => ?_
  apply WP.seq
  refine WP.mono (batchSize_ok s₇) fun s₈ ⟨c₈, g₈, m₈, rd₈, wr₈, sp₈⟩ => ?_
  obtain G₇ : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s₇.gpr r = s₄.gpr r :=
    fun r a b c e => (i₇.regs r a b c e).trans (G₆ r c e b)
  obtain r5₇ : s₇.gpr .r5 = s.gpr .r5 := (G₇ _ (by decide) (by decide) (by decide) (by decide)).trans r5₄
  obtain c₈' : s₈.gpr .r10 = BitVec.ofNat 64 k := by rw [c₈, r5₇]
  obtain r6₈ : s₈.gpr .r6 = p + BitVec.ofNat 64 (16 * k) := by rw [g₈ _ (by decide), i₇.r6]
  let s₉ := s₈.write .r4 (s₈.gpr .r6)
  let s' := s₉.write .r5 (s₉.gpr .r5 - s₉.gpr .r10)
  refine WP.of_runBlock ⟨s', by rw [runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_sub,
    runStep_some, runBlock_nil], ?_⟩
  obtain g' : ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s₈.gpr r := fun r a b => by
    simp [s', s₉, gpr_write, a, b]
  obtain r5₉ : s₉.gpr .r5 = s.gpr .r5 := by rw [gpr_write_of_ne _ _ (by decide), g₈ _ (by decide), r5₇]
  obtain r10₉ : s₉.gpr .r10 = BitVec.ofNat 64 k := by rw [gpr_write_of_ne _ _ (by decide), c₈']
  obtain mem' : s'.mem = s₇.mem := by simp only [s', s₉, mem_write, m₈]
  obtain G' : ∀ r ∈ [Reg.r3, .r8], s'.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .r5 ∧ r ≠ .r4 ∧ r ≠ .r10 ∧ r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r6 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g' _ this.2.1 this.1, g₈ _ this.2.2.1, G₇ _ this.2.2.2.1 this.2.2.2.2.1 this.2.2.1 this.2.2.2.2.2]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    exact G₄ _ (by rcases hr with rfl | rfl <;> simp)
  obtain r8' : s'.gpr .r8 = s.gpr .r8 := G' _ (by simp)
  -- the memory
  obtain f₇ : Frame [⟨p, 16 * k⟩] s₄.mem s₇.mem := by
    have := i₇.frame; rw [m₆, m₅] at this; exact this
  obtain frame : Frame [scratchR s, ⟨p, 16 * k⟩] s.mem s'.mem := by
    rw [mem']
    obtain a : Frame [scratchR s, ⟨p, 16 * k⟩] s.mem s₃.mem :=
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scratchR s, List.mem_cons_self, arraysR_sub_scratch s⟩)
    obtain b : Frame [scratchR s, ⟨p, 16 * k⟩] s₃.mem s₄.mem :=
      f₄.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [scratchR, r8₃]; exact List.mem_cons_self
    obtain c : Frame [scratchR s, ⟨p, 16 * k⟩] s₄.mem s₇.mem :=
      f₇.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ List.mem_cons_self
    exact (a.trans b).trans c
  obtain saved' : ∀ q ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr q.1 = s.gpr q.1 := by
    intro q hq
    obtain hne : ∀ q ∈ Impl.Seed.PPC64LE.savedRegs, q.1 ≠ .r4 ∧ q.1 ≠ .r5 ∧ q.1 ≠ .r6 ∧ q.1 ≠ .r7 ∧
        q.1 ≠ .r9 ∧ q.1 ≠ .r10 := by decide
    obtain ⟨h4, h5, h6, h7, h9, h10⟩ := hne q hq
    rw [g' _ h4 h5, g₈ _ h10, G₇ _ h9 h7 h10 h6, sv₄ q hq, i₃.regs _ h9 h7 h10 h6, G₂ _ h10 h6 h7]
  refine ⟨fun b hb => ?_, ?_, ?_, G', saved', ?_, by simp only [s', s₉, rd_write, rd₈, i₇.rd, rd₆],
    by simp only [s', s₉, wr_write, wr₈, i₇.wr, wr₆], frame⟩
  · rw [crypt_eq, ← hq₄ b hb, ← quad₆ b, mem']
    refine blockAt_of_bytes fun i hi => ?_
    rw [Offset.add_ofNat_add_ofNat, i₇.done b hb i hi, encodeSwapped_get _ _ hi]
  · simp [s', s₉, gpr_write, r6₈]; rfl
  · simp only [s', gpr_write_self, r5₉, r10₉]; rfl
  · simp only [s', s₉, sp_write, sp₈, i₇.sp, sp₆]

end VG.Proof.Seed.PPC64LE

end

end

/-!
# The function on PPC64LE

After moving the scratch buffer to `r8` and saving the callee-saved
registers in it, the function runs batches of up to 16 blocks until none are
left (`loop_ok`), then restores the registers (`ecb_ok`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE
  VG.Proof.Seed

theorem toNat_ofNat_le {m n : Nat} (hm : m ≤ n) (hn : 16 * n ≤ 2 ^ 64) : (BitVec.ofNat 64 m).toNat = m := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Seed.blockAt m' p = Spec.Seed.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; decide) hi

/-- The keys are as in `m` wherever the frame's regions leave them. -/
theorem keysAt_frame {d : Spec.Seed.Direction} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    {j : Nat} (hd : ∀ r ∈ rs, (⟨kp d p j, 8⟩ : Region).Disjoint r) : keysAt d m' p j = keysAt d m p j := by
  simp only [keysAt]
  congr 1
  · exact hf.readW (contains_prefix (by decide)) hd (by decide)
  · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl]
    exact hf.readW (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The loop of batches -/

/-- What the loop may assume throughout, of the state it starts in. -/
structure BatchesEnv (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) : Prop where
  room : Room s₀
  dataIn : (⟨s₀.gpr .r4, 16 * n⟩ : Region) ∈ s₀.wr
  dataSep : Region.Disjoint ⟨s₀.gpr .r4, 16 * n⟩ (scratchR s₀)
  fit : 16 * n ≤ 2 ^ 64
  keys : KeysOk d s₀ (s₀.gpr .r3)
  keyData : ∀ j < 16, Region.Disjoint ⟨kp d (s₀.gpr .r3) j, 8⟩ ⟨s₀.gpr .r4, 16 * n⟩

/-- `m` blocks left, the first `n - m` done. -/
structure BatchesInv (d : Spec.Seed.Direction) (s₀ : State) (n m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ n
  r5 : s.gpr .r5 = BitVec.ofNat 64 m
  r4 : s.gpr .r4 = s₀.gpr .r4 + BitVec.ofNat 64 (16 * (n - m))
  regs : ∀ r ∈ [Reg.r3, .r8], s.gpr r = s₀.gpr r
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s.gpr p.1 = s₀.gpr p.1
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n - m, Spec.Seed.blockAt s.mem (s₀.gpr .r4 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .r3))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [scratchR s₀, ⟨s₀.gpr .r4, 16 * (n - m)⟩] s₀.mem s.mem

structure BatchesPost (d : Spec.Seed.Direction) (s₀ : State) (n : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [Reg.r3, .r8], s.gpr r = s₀.gpr r
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s.gpr p.1 = s₀.gpr p.1
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  done : ∀ b < n, Spec.Seed.blockAt s.mem (s₀.gpr .r4 + BitVec.ofNat 64 (16 * b)) =
    Spec.Seed.crypt (keysAt d s₀.mem (s₀.gpr .r3))
      (Spec.Seed.blockAt s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [scratchR s₀, ⟨s₀.gpr .r4, 16 * n⟩] s₀.mem s.mem

theorem BatchesInv.batchPre {d : Spec.Seed.Direction} {s₀ : State} {n m : Nat} (E : BatchesEnv d s₀ n)
    {s : State} (h : BatchesInv d s₀ n m s) : BatchPre d s := by
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  have hm : (s.gpr .r5).toNat = m := by rw [h.r5]; exact toNat_ofNat_le h.le E.fit
  have r9 : s.gpr .r8 = s₀.gpr .r8 := h.regs _ (by simp)
  have rdi : s.gpr .r3 = s₀.gpr .r3 := h.regs _ (by simp)
  have scr : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  let D := s₀.gpr .r4
  have hsub : Region.Sub ⟨s.gpr .r4, 16 * min (s.gpr .r5).toNat 16⟩ ⟨D, 16 * n⟩ := by
    rw [h.r4, hm]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨room_congr E.room r9 h.wr, by omega_arith, fun b hb w hw => ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [h.wr, h.r4, Offset.add_ofNat_add_ofNat]
    rw [hm] at hb
    exact ⟨_, E.dataIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [scr]; exact E.dataSep.sub_left hsub
  · rw [rdi]
    intro j hj
    obtain ⟨a, b, c⟩ := E.keys j hj
    exact ⟨by rw [h.rd, h.wr]; exact a, by rw [h.rd, h.wr]; exact b, by rw [scr]; exact c⟩
  · rw [rdi]; exact (E.keyData j hj).sub_right hsub

theorem loop_ok (d : Spec.Seed.Direction) {s₀ : State} {n : Nat} (E : BatchesEnv d s₀ n) (m : Nat) (s : State)
    (hs : BatchesInv d s₀ n m s) : WP isa (.loop (batch d) (.nonzero .d .r5)) s (BatchesPost d s₀ n) := by
  refine WP.loop (M := isa) (BatchesInv d s₀ n) ?_ m s hs
  intro m s h
  have hp := h.pos
  have hl := h.le
  have hfit := E.fit
  apply WP.mono (batch_ok d (h.batchPre E))
  intro s' q
  have hm : (s.gpr .r5).toNat = m := by rw [h.r5]; exact toNat_ofNat_le h.le E.fit
  obtain ⟨qdone, qrsi, qrdx, qregs, qsaved, qsp, qrd, qwr, qframe⟩ := q
  rw [hm] at qdone qrsi qrdx qframe
  generalize hk : min m 16 = k at qdone qrsi qrdx qframe
  have hk1 : 1 ≤ k := by omega_arith
  have hkm : k ≤ m := by omega_arith
  let D := s₀.gpr .r4
  let S := s₀.gpr .r3
  have r9 : s.gpr .r8 = s₀.gpr .r8 := h.regs _ (by simp)
  have rdi : s.gpr .r3 = S := h.regs _ (by simp)
  have scratchR_eq : scratchR s = scratchR s₀ := by simp only [scratchR, r9]
  rw [h.r4, scratchR_eq] at qframe
  rw [h.r4] at qrsi qdone
  rw [rdi] at qdone
  -- the memory written so far
  have frame' : Frame [scratchR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s'.mem := by
    have f₁ : Frame [scratchR s₀, ⟨D, 16 * (n - (m - k))⟩] s₀.mem s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Region.sub_prefix (by omega_arith)⟩
    have f₂ : Frame [scratchR s₀, ⟨D, 16 * (n - (m - k))⟩] s.mem s'.mem := qframe.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scratchR s₀, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨⟨D, 16 * (n - (m - k))⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          Offset.sub_base _ (by omega_arith)⟩
    exact f₁.trans f₂
  have workSep : ∀ b, b < n → (⟨D + BitVec.ofNat 64 (16 * b), 16⟩ : Region).Disjoint (scratchR s₀) :=
    fun b hb => E.dataSep.sub_left (Offset.sub_base _ (by omega_arith))
  have done' : ∀ b < n - (m - k), Spec.Seed.blockAt s'.mem (D + BitVec.ofNat 64 (16 * b)) =
      Spec.Seed.crypt (keysAt d s₀.mem S) (Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * b))) := by
    intro b hb
    by_cases hb' : b < n - m
    · rw [← h.done b hb']
      refine blockAt_frame qframe fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact workSep b (by omega_arith)
      · exact Offset.disjoint D (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · obtain ⟨j, rfl⟩ : ∃ j, b = n - m + j := ⟨b - (n - m), by omega_arith⟩
      have e := qdone j (by omega_arith)
      rw [Offset.add_ofNat_add_ofNat, show 16 * (n - m) + 16 * j = 16 * (n - m + j) by omega_arith] at e
      rw [e]
      have hK : ∀ i < 16, keysAt d s.mem S i = keysAt d s₀.mem S i := fun i hi =>
        keysAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          obtain ⟨-, -, hdis⟩ := E.keys i hi
          rcases hr with rfl | rfl
          · exact hdis
          · exact (E.keyData i hi).sub_right (Region.sub_prefix (by omega_arith))
      have hB : Spec.Seed.blockAt s.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) =
          Spec.Seed.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (n - m + j))) :=
        blockAt_frame h.frame fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact workSep _ (by omega_arith)
          · exact Offset.disjoint_base D (by omega_arith) (by omega_arith)
      rw [hB]
      exact crypt_congr hK _
  have rdx' : s'.gpr .r5 = BitVec.ofNat 64 (m - k) := by
    rw [qrdx, h.r5, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) hkm]
  have zf' : isa.eval (.nonzero .d .r5) s' = some (BitVec.ofNat 64 (m - k) != 0) := by
    show some (s'.read .d .r5 != 0) = _
    rw [show s'.read .d .r5 = s'.gpr .r5 from BitVec.setWidth_eq _, rdx']
  have regs' : ∀ r ∈ [Reg.r3, .r8], s'.gpr r = s₀.gpr r := fun r hr =>
    (qregs r hr).trans (h.regs r hr)
  have saved' : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s₀.gpr p.1 := fun p hp =>
    (qsaved p hp).trans (h.saved p hp)
  have sp' : s'.sp = s₀.sp := qsp.trans h.sp
  have rd' := qrd.trans h.rd
  have wr' := qwr.trans h.wr
  by_cases hend : m ≤ 16
  · have hkm' : k = m := by omega_arith
    left
    refine ⟨?_, regs', saved', sp', rd', wr', ?_, ?_⟩
    · rw [zf', hkm', Nat.sub_self]; rfl
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at done'; exact done'
    · rw [hkm', Nat.sub_self, Nat.sub_zero] at frame'; exact frame'
  · have hk16 : k = 16 := by omega_arith
    right
    refine ⟨?_, m - k, by omega_arith, ⟨by omega_arith, by omega_arith, rdx', ?_, regs', saved', sp', rd', wr', done', frame'⟩⟩
    · rw [zf']
      have : (BitVec.ofNat 64 (m - k) != 0) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [toNat_ofNat_le (show m - k ≤ n by omega_arith) E.fit] at this
        have z : (0 : BitVec 64).toNat = 0 := rfl
        omega_arith
      rw [this]
    · rw [qrsi, Offset.add_ofNat_add_ofNat]; congr 2; omega_arith

/-! ## The keys -/

/-- Where round `j + 1`'s key is in the schedule. -/
def keyOff : Spec.Seed.Direction → Nat → Nat
  | .encrypt, j => 8 * j
  | .decrypt, j => 8 * (15 - j)

theorem keyOff_le (d : Spec.Seed.Direction) {j : Nat} (hj : j < 16) : keyOff d j + 8 ≤ 128 := by
  cases d <;> simp only [keyOff] <;> omega_arith

theorem kp_start_const (d : Spec.Seed.Direction) :
    ∀ j < 16, BitVec.ofNat 64 (keyStart d) + BitVec.ofNat 64 j * stepW d = BitVec.ofNat 64 (keyOff d j) := by
  cases d <;> decide

theorem kp_start (d : Spec.Seed.Direction) (S : Addr) {j : Nat} (hj : j < 16) :
    kp d (S + BitVec.ofNat 64 (keyStart d)) j = S + BitVec.ofNat 64 (keyOff d j) := by
  rw [kp, BitVec.add_assoc, kp_start_const d j hj]

/-- The block function in the direction `d`. -/
def cipher (d : Spec.Seed.Direction) (K : Spec.Seed.Schedule) (b : Spec.Seed.Block) : Spec.Seed.Block :=
  match d with
  | .encrypt => Spec.Seed.encryptBlock K b
  | .decrypt => Spec.Seed.decryptBlock K b

theorem crypt_keysAt (d : Spec.Seed.Direction) (m : Mem) (S : Addr) (b : Spec.Seed.Block) :
    Spec.Seed.crypt (keysAt d m (S + BitVec.ofNat 64 (keyStart d))) b = cipher d (Spec.Seed.scheduleAt m S) b := by
  cases d
  · show _ = Spec.Seed.crypt (Spec.Seed.roundKey (Spec.Seed.scheduleAt m S)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ hj]
    simp only [keyOff]
  · show _ = Spec.Seed.crypt (fun j => Spec.Seed.roundKey (Spec.Seed.scheduleAt m S) (15 - j)) b
    refine crypt_congr (fun j hj => ?_) b
    rw [keysAt, kp_start _ _ hj, roundKey_readW _ _ (by omega_arith)]
    simp only [keyOff]

theorem ecb_blocks (K : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.Seed.blockAt m' (D + BitVec.ofNat 64 (16 * b)) =
      cipher d K (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * b)))) :
    Spec.Seed.blocksAt m' D n = Spec.Seed.ecb K d (Spec.Seed.blocksAt m D n) := by
  cases d <;>
  · simp only [Spec.Seed.blocksAt, Spec.Seed.ecb, List.map_map]
    apply List.map_congr_left
    intro b hb
    rw [Function.comp_apply]
    exact h b (List.mem_range.mp hb)

/-! ## The function -/

/-- What the function needs: the scratch buffer and the data writable, the
schedule readable, apart from each other. -/
structure EcbPre (s : State) : Prop where
  scratch : ∃ n, 8 * scratchSlots ≤ n ∧ (⟨s.gpr .r6, n⟩ : Region) ∈ s.wr
  dataIn : (⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .r3, 128⟩ : Region) ∈ s.rd
  keyData : (⟨s.gpr .r3, 128⟩ : Region).Disjoint ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩
  keyBuf : (⟨s.gpr .r3, 128⟩ : Region).Disjoint ⟨s.gpr .r6, 8 * scratchSlots⟩
  dataBuf : (⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 8 * scratchSlots⟩
  fit : 16 * (s.gpr .r5).toNat ≤ 2 ^ 64

/-- What the function does: every block of the data becomes its encryption or
decryption, the callee-saved registers it uses are restored, the scratch
buffer's address is in `r8` and the key pointer at the first round's key,
and only the scratch buffer and the data change. -/
structure EcbPost (d : Spec.Seed.Direction) (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1
  r8 : s'.gpr .r8 = s.gpr .r6
  r3 : s'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (keyStart d)
  done : ∀ b < (s.gpr .r5).toNat, Spec.Seed.blockAt s'.mem (s.gpr .r4 + BitVec.ofNat 64 (16 * b)) =
    cipher d (Spec.Seed.scheduleAt s.mem (s.gpr .r3))
      (Spec.Seed.blockAt s.mem (s.gpr .r4 + BitVec.ofNat 64 (16 * b)))
  frame : Frame [⟨s.gpr .r6, 8 * scratchSlots⟩, ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩] s.mem s'.mem

theorem keyStart_lt (d : Spec.Seed.Direction) : keyStart d < 32768 := by cases d <;> decide

theorem ecb_ok (d : Spec.Seed.Direction) {s : State} (h : EcbPre s) : WP isa (ecb d) s (EcbPost d s) := by
  let n := (s.gpr .r5).toNat
  let D := s.gpr .r4
  let S := s.gpr .r3
  have hn := h.fit
  rw [ecb]
  -- `r8 := r6`, and the key pointer
  let s₁ := s.write .r8 (s.gpr .r6)
  let s₅ := s₁.write .r3 (s₁.gpr .r3 + BitVec.ofNat _ (keyStart d))
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [setup, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_addi' (keyStart_lt d), runStep_some,
      runBlock_nil]; rfl, ?_⟩)
  have G₅ : ∀ r, r ≠ .r8 → r ≠ .r3 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [gpr_write_of_ne _ _ b, gpr_write_of_ne _ _ a]
  have r9₅ : s₅.gpr .r8 = s.gpr .r6 := by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self]
  have rdi₅ : s₅.gpr .r3 = S + BitVec.ofNat 64 (keyStart d) := by
    rw [gpr_write_self, gpr_write_of_ne _ _ (by decide)]
  have rd₅ : s₅.rd = s.rd := rfl
  have wr₅ : s₅.wr = s.wr := rfl
  have mem₅ : s₅.mem = s.mem := rfl
  have scr₅ : scratchR s₅ = ⟨s.gpr .r6, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅]
  have room₅ : Room s₅ := by
    obtain ⟨n, hn, hm⟩ := h.scratch; exact ⟨n, hn, by rw [r9₅, wr₅]; exact hm⟩
  have zf₅ : isa.eval (.zero .d .r5) s₅ = some (s.gpr .r5 == 0) := by
    show some (s₅.read .d .r5 == 0) = _
    rw [show s₅.read .d .r5 = s₅.gpr .r5 from BitVec.setWidth_eq _, G₅ _ (by decide) (by decide)]
  have rsi₅ : s₅.gpr .r4 = D := G₅ _ (by decide) (by decide)
  have rdx₅ : s₅.gpr .r5 = s.gpr .r5 := G₅ _ (by decide) (by decide)
  -- after the loop (or none)
  have finish : ∀ s₆ : State, BatchesPost d s₅ n s₆ → EcbPost d s s₆ := by
    intro s₆ p
    have pf := p.frame
    rw [rsi₅, scr₅, mem₅] at pf
    refine ⟨fun q hq => ?_, ?_, ?_, fun b hb => ?_, pf⟩
    · have hne : ∀ q ∈ Impl.Seed.PPC64LE.savedRegs, q.1 ≠ .r8 ∧ q.1 ≠ .r3 := by decide
      rw [p.saved q hq, G₅ _ (hne q hq).1 (hne q hq).2]
    · rw [p.regs _ (by simp), r9₅]
    · rw [p.regs _ (by simp), rdi₅]
    · have e := p.done b hb
      rw [rsi₅, rdi₅, mem₅] at e
      rw [e, crypt_keysAt]
  apply WP.ite (s.gpr .r5 == 0) zf₅
  · intro hz
    apply WP.block_nil
    have hn0 : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    refine finish s₅ ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith, ?_⟩
    rw [hn0]; exact Frame.refl _ _
  · intro hz
    have hn1 : 1 ≤ n := by
      have : s.gpr .r5 ≠ 0 := by simpa using hz
      have : (s.gpr .r5).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega_arith
    have E : BatchesEnv d s₅ n := by
      refine ⟨room₅, by rw [rsi₅, wr₅]; exact h.dataIn, by rw [rsi₅, scr₅]; exact h.dataBuf, hn,
        fun j hj => ?_, fun j hj => ?_⟩
      · rw [rdi₅, kp_start _ _ hj, rd₅, wr₅, scr₅]
        have hle := keyOff_le d hj
        refine ⟨⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, ?_,
          h.keyBuf.sub_left (Offset.sub_base _ hle)⟩
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_add_ofNat]
        exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
      · rw [rdi₅, kp_start _ _ hj, rsi₅]
        exact h.keyData.sub_left (Offset.sub_base _ (keyOff_le d hj))
    have I : BatchesInv d s₅ n n s₅ := by
      refine ⟨hn1, Nat.le_refl _, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun b hb => by omega_arith,
        by rw [Nat.sub_self]; exact Frame.refl _ _⟩
      · rw [rdx₅]; exact BitVec.eq_of_toNat_eq (by simp [n])
      · rw [Nat.sub_self, Nat.mul_zero, ofNat_zero_add]
    exact WP.mono (loop_ok d E n s₅ I) finish

end VG.Proof.Seed.PPC64LE
