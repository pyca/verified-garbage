module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Camellia.X86.Core
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Slots, and saving and restoring registers, on x86 (32-bit)

As SM4's (`Proof/Sm4/X86/Prologue.lean`, whose code is the same): loads and stores of the
scratch buffer's slots through a base register (`ldSlot_ok`, `stSlot_ok`,
and lists of them), and the prologue and epilogue's saving and restoring
of the callee-saved registers in the slots from `j` (`saveAt_ok`,
`restoreAt_ok`; ECB's and the key expansion's from `savedSlot`, `save_ok`,
`restore_ok`), and the slots that frames keep (`slot_keep`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb slotAt movS st movR argOp at_)

/-- Argument `i`'s address, while `esp` is as on entry. -/
theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- `mov d, [esp + 4 + 4 i]`: argument `i`. -/
theorem ldArg_ok (s : State) (d : Reg) (i : Nat) (h : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov d (.mem (argOp i))] s = some s' ∧ s'.gpr d = s.mem.readW (s.ea (argOp i)) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.ea (argOp i)) 32), by
    rw [runBlock_cons, show exec (.mov d (.mem (argOp i))) s = some (s.setReg d (s.mem.readW (s.ea (argOp i)) 32)) by
      simp [exec, readSrc, State.load32, h], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
  rw [slot_addr (by omega)]
  exact VG.Offset.sub_base _ (by omega)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)

/-- What `crypt8` writes is in the scratch buffer. -/
theorem ctx_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions b, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq]; omega)
  · exact slot_sub hfit (by rw [grpSlot_eq, slots_eq]; decide)

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_arith)]
  exact hf.readW (VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

/-- What `crypt8` writes (`ctx_sub`) is apart from the table, the saved registers, and the data pointer and count. -/
theorem ctx_disj {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions b, (slotsRegion b keySlot grpSlot).Disjoint r := fun r hr => by
  rw [slots_eq] at hfit
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by omega_arith) (by rw [keySlot_eq, grpSlot_eq]; omega_arith)
  · rw [slot_addr (by rw [grpSlot_eq]; omega_arith)]
    exact VG.Offset.disjoint _ (by rw [keySlot_eq, grpSlot_eq]; omega_arith) (by rw [keySlot_eq, grpSlot_eq]; omega_arith)
      (by rw [grpSlot_eq]; omega_arith)

/-- … and from the slots after the group's end. -/
theorem ctx_disj_hi {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions b, (slotsRegion b (grpSlot + 1) slots).Disjoint r := fun r hr => by
  rw [slots_eq] at hfit
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq, grpSlot_eq]; omega_arith) (by rw [grpSlot_eq, slots_eq]; omega_arith)
  · rw [slot_addr (by rw [grpSlot_eq]; omega_arith)]
    exact VG.Offset.disjoint _ (.inr (by decide)) (by decide)
      (by rw [grpSlot_eq]; omega_arith)

/-- `mov d, [n + 4 k]`, `n` holding `b`, a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (hw.slot hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, `n` holding `b`, a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, hw.slot hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .store (slotAt n x.1) x.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_, fun y hy => ?_⟩
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
    ∃ s', runBlock isa (L.map fun x => .mov x.1 (.mem (slotAt n x.2))) s = some s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .ebx

theorem savedRegsAt_eq (j : Nat) : savedRegsAt j = (List.range 4).map fun i => (sreg i, j + i) := rfl

/-- The saved registers are in their slots, from `j`. -/
def SavedAt (j : Nat) (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (j + i)) 32 = s₀.gpr (sreg i)

/-- … from `savedSlot`. -/
abbrev Saved : State → BitVec 32 → Mem → Prop := SavedAt savedSlot

theorem saveAt_ok {s : State} {b : BitVec 32} {j k : Nat} (hj : j + 4 ≤ slots) (hw : ScrIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegsAt j k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ SavedAt j s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      ∀ i, i < slots → (i < j ∨ j + 4 ≤ i) → s'.mem.readW (wordAddr b i) 32 = s.mem.readW (wordAddr b i) 32 := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax k ha
  rw [hb] at v₁
  let L : List (Nat × Reg) := (List.range 4).map fun i => (j + i, sreg i)
  have hL : (savedRegsAt j).map (fun (r, i) => Instr.store (slotAt .eax i) r) =
      L.map fun x => .store (slotAt .eax x.1) x.2 := by
    rw [savedRegsAt_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 4).map fun i => j + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, o₂, v₂⟩ := stW_list_ok .eax L s₁ v₁ (by rw [wr₁]; exact hw)
    (by rw [hslots]; exact List.pairwise_map.mpr (List.nodup_range.imp fun h e => h (Nat.add_left_cancel e)))
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      omega)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, -, -⟩ := movR_ok s₂ .edi .eax
  refine ⟨s₃, ?_, by rw [r₃, g₂, v₁], fun r h0 h7 => by rw [o₃ r h7, g₂, o₁ r h0], fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, ← m₁]; exact f₂, fun i hi hji => ?_⟩
  · rw [saveRegsAt, runBlock_app, runBlock_app, e₁, Option.bind_some, hL, e₂, Option.bind_some, e₃]
  · rw [m₃, v₂ (j + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩),
      o₁ _ (show sreg i ≠ .eax by revert i; decide)]
  · rw [m₃, o₂ i ?_ hi, m₁]
    rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i' hi' h; omega

theorem save_ok {s : State} {b : BitVec 32} {k : Nat} (hw : ScrIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegs k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Saved s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
  let ⟨s', e, b', g, sv, rd, wr, f, kp⟩ := saveAt_ok (j := savedSlot) (by decide) hw ha hb
  ⟨s', e, b', g, sv, rd, wr, f, fun i hi => kp i (by rw [slots_eq]; rw [savedSlot_eq] at hi; omega) (.inl hi)⟩

theorem restoreAt_ok {s₀ s : State} {b : BitVec 32} {j : Nat} (hj : j + 4 ≤ slots) (hw : ScrIn s.wr b)
    (hb : s.gpr .edi = b) (hs : SavedAt j s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegsAt j) s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.ebx, j), (.esi, j + 1), (.ebp, j + 3)]
  have hLr : L.map (·.1) = [.ebx, .esi, .ebp] := rfl
  obtain ⟨s₁, e₁, m₁, rd₁, wr₁, o₁, v₁⟩ := ldW_list_ok .edi L s hb hw
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only <;> decide) (by rw [hLr]; decide)
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only <;> omega)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok s₁ .edi .edi (k := j + 2)
    (by rw [o₁ _ (by rw [hLr]; decide), hb]) (by omega) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show restoreRegsAt j = (L.map fun x => .mov x.1 (.mem (slotAt .edi x.2))) ++
        [.mov .edi (.mem (slotAt .edi (j + 2)))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · show s₂.gpr .ebx = _
      rw [o₂ _ (by decide), v₁ (.ebx, j) (by simp [L])]; exact hs 0 (by decide)
    · show s₂.gpr .esi = _
      rw [o₂ _ (by decide), v₁ (.esi, j + 1) (by simp [L])]; exact hs 1 (by decide)
    · rw [show sreg 2 = .edi from rfl, v₂, m₁]; exact hs 2 (by decide)
    · show s₂.gpr .ebp = _
      rw [o₂ _ (by decide), v₁ (.ebp, j + 3) (by simp [L])]; exact hs 3 (by decide)
  · rw [o₂ r (hr 2 (by decide)), o₁ r (by
      simp only [hLr, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 3 (by decide)⟩)]

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .edi = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  restoreAt_ok (by decide) hw hb hs

end VG.Proof.Camellia.X86
