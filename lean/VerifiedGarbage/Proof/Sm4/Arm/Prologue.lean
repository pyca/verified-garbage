import VerifiedGarbage.Proof.Sm4.Arm.Copy

/-!
# Slots, and saving and restoring registers, on ARMv7

Loads and stores of the scratch buffer's slots through a base register
(`ldW_ok`, `stW_ok`, and lists of them), and the prologue and epilogue's
saving and restoring of the callee-saved registers (`save_ok`,
`restore_ok`) in the slots from `savedSlot`.
-/

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb t0 t1 kp)

theorem savedSlot_eq : savedSlot = 352 := rfl
theorem dSlot_eq : dSlot = 361 := rfl
theorem nSlot_eq : nSlot = 362 := rfl

/-- The scratch buffer at `b`, in the writable regions. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨State.addr b, 4 * slots⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 := slot_in h.mem h.fit hk

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := by
  rw [slot_addr (by omega)]
  exact VG.Offset.sub_base _ (by omega)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)

/-- `ldr d, [n, #4 k]`, `n` holding `b`. -/
theorem ldW_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr b k) 4) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), by
    rw [runBlock_cons, exec_ldr hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `str t, [n, #4 k]`, `n` holding `b`. -/
theorem stW_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions s.wr (wordAddr b k) 4) :
    runBlock isa [.str t n (4 * k)] s = some { s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) } := by
  rw [runBlock_cons, exec_str hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil]

/-- A store to a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.str t n (4 * k)] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem :=
  ⟨_, stW_ok s t n hn (by rw [slots_eq] at hk; omega) (hw.slot hk), rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩

/-- A load of a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ldW_ok s d n hn (by rw [slots_eq] at hk; omega) (inRd (hw.slot hk))

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .str x.2 n (4 * x.1)) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_,
      fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .ldr x.1 n (4 * x.2)) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r4

theorem savedRegs_eq : savedRegs = (List.range 9).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {base : Reg} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr base = b) :
    ∃ s', runBlock isa (saveRegs base) s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  let L : List (Nat × Reg) := (List.range 9).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs base = L.map fun x => .str x.2 base (4 * x.1) := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 9).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ := stW_list_ok base L s hb hw (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', sp', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; rw [slots_eq]; omega)⟩
  · exact v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega

theorem sreg_ne_r12 : ∀ i < 9, sreg i ≠ .r12 := by decide

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .r12 = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 9, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let L : List (Reg × Nat) := (List.range 9).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs .r12 = L.map fun x => .ldr x.1 .r12 (4 * x.2) := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 9).map sreg := by simp only [L, List.map_map]; rfl
  obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok .r12 L s hb hw
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_r12 i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr', sp'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

end VG.Proof.Sm4.Arm
