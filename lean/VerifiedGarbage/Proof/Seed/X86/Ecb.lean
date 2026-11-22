module

public import VerifiedGarbage.Proof.Seed.X86.Prologue
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Seed.X86.Group`, which only this module used -/

section

/-!
# A group of blocks of SEED ECB on x86 (32-bit)

`dataGroup_wp`, one iteration of the data loop, copies the group's blocks
(eight, or the last one to seven) from `ebx` to the tail buffer, saves the
caller's `esi` and `ebp` and the group's data pointer in their slots
(`stash`), transforms the tail buffer (`crypt8_wp`), takes them back
(`unstash`), copies the blocks back and tests whether any are left. The
blocks of a group are computed from `ebx` and the stack arguments
(`countR_wp`), and the caller's `esi` and `ebp` are in their registers
whenever the code copies blocks.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI argOp)

/-! ## Small blocks -/

/-- `ecx := min(edx, 8)`. -/
theorem countR_wp {s : State} {v : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .ecx .edx
  let s₂ := arithFlags s₁ (s₁.gpr .edx - 8) ((s₁.gpr .edx).toNat < (8 : BitVec 32).toNat)
    (subOverflow (s₁.gpr .edx) 8 (s₁.gpr .edx - 8))
  obtain e₂ : runBlock isa [movR .ecx .edx, .alu .cmp .edx (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .edx, .alu .cmp .edx (.imm 8)] : List Instr) =
      [movR .ecx .edx] ++ [.alu .cmp .edx (.imm 8)] from rfl, runBlock_append, e₁, Option.bind_some]
    rfl
  obtain cf₂ : s₂.cf = some (decide (v < 8)) := by
    rw [RegUpd.cf_arithFlags, o₁ _ (by decide), hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl
  obtain o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr]
  obtain m₂ : s₂.mem = s.mem := by rw [RegUpd.mem_arithFlags, m₁]
  obtain rd₂ : s₂.rd = s.rd := by rw [RegUpd.rd_arithFlags, rd₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [RegUpd.wr_arithFlags, wr₁]
  unfold countR
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  refine WP.ite (decide (v < 8)) ((eval_b s₂).trans cf₂) (fun h => ?_) (fun h => ?_)
  · refine WP.block_nil ⟨?_, o₂, m₂, rd₂, wr₂⟩
    rw [RegUpd.gpr_arithFlags, r₁, hn, Nat.min_eq_left (by simp at h; omega_arith)]
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ecx 8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => by rw [o₃ r hr, o₂ r hr], by rw [m₃, m₂],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rw [r₃, Nat.min_eq_right (by simp at h; omega_arith)]; rfl

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : d < 2 ^ 32), Nat.mod_eq_of_lt h]

theorem setWidth_add {D : BitVec 32} {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-! ## The scratch buffer's contents -/

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

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers, in the slots from `tableSlot` to `ptrSlot`. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (E : Nat → Spec.Seed.Word) (m : Mem) : Prop where
  keys : ∀ e < 32, m.readW (wordAddr b (tableSlot + e)) 32 = E e
  saved : Saved s₀ b m

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {E : Nat → Spec.Seed.Word} {m m' : Mem}
    (h : ScrOk s₀ b E m) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b tableSlot ptrSlot).Disjoint r) : ScrOk s₀ b E m' := by
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · rw [← h.keys e he]
    exact slot_keep hfit (by decide) hf hd (by omega_arith) (by rw [ptrSlot_eq, tableSlot_eq]; omega_arith)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega_arith)
      (by rw [savedSlot_eq, ptrSlot_eq]; omega_arith)

/-! ## The data loop -/

/-- Round `j + 1`'s key, from the table's words `E`. -/
def keyPairs (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Word × Spec.Seed.Word := (E (2 * j), E (2 * j + 1))

/-- Each block, transformed: `crypt` with the table's round keys `E`. -/
def outF (m₀ : Mem) (D : Addr) (E : Nat → Spec.Seed.Word) (j : Nat) : Spec.Seed.Block :=
  Spec.Seed.crypt (keyPairs E) (Spec.Seed.blockAt m₀ (D + BitVec.ofNat 64 (16 * j)))

theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Seed.blockAt, Vector.getD, hi]

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`: its data pointer in `ebx`, the blocks
left in `edx`, the caller's `esi` and `ebp` in theirs. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  ptr : s.gpr .ebx = D + BitVec.ofNat 32 (128 * k)
  cnt : s.gpr .edx = BitVec.ofNat 32 (n - 8 * k)
  esi : s.gpr .esi = s₀.gpr .esi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  lt : 8 * k < n
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n (8 * k) (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (s : State) : Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  esi : s.gpr .esi = s₀.gpr .esi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The slots `stash` writes. -/
def stashRegions (b : BitVec 32) : List Region :=
  [⟨wordAddr b (savedSlot + 1), 4⟩, ⟨wordAddr b (savedSlot + 3), 4⟩, ⟨wordAddr b ptrSlot, 4⟩,
   ⟨wordAddr b cntSlot, 4⟩]

theorem stash_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ stashRegions b, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [stashRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact slot_sub hfit (by decide)

/-- `stash`: the caller's `esi` and `ebp` (which the saved slots hold
already), the data pointer and the blocks left to their slots. -/
theorem stash_ok {s₀ s : State} {b : BitVec 32} {E : Nat → Spec.Seed.Word} (hw : ScrIn s.wr b)
    (hb : s.gpr .edi = b) (hsc : ScrOk s₀ b E s.mem) (hesi : s.gpr .esi = s₀.gpr .esi)
    (hebp : s.gpr .ebp = s₀.gpr .ebp) :
    ∃ s', runBlock isa stash s = some s' ∧ s'.mem.readW (wordAddr b ptrSlot) 32 = s.gpr .ebx ∧
      s'.mem.readW (wordAddr b cntSlot) 32 = s.gpr .edx ∧ ScrOk s₀ b E s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame (stashRegions b) s.mem s'.mem := by
  have hfit : b.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  let L : List (Nat × Reg) := [(savedSlot + 1, .esi), (savedSlot + 3, .ebp), (ptrSlot, .ebx), (cntSlot, .edx)]
  obtain ⟨s', e', g', rd', wr', -, o', v'⟩ := stW_list_ok .edi L s hb hw (by decide) (by decide)
  obtain fr : Frame (stashRegions b) s.mem s'.mem := by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s .esi .edi (k := savedSlot + 1) hb (by decide) hw
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .ebp .edi (k := savedSlot + 3) (by rw [g₁, hb])
      (by decide) (by rw [wr₁]; exact hw)
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .ebx .edi (k := ptrSlot) (by rw [g₂, g₁, hb])
      (by decide) (by rw [wr₂, wr₁]; exact hw)
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, -, -, f₄⟩ := stSlot_ok s₃ .edx .edi (k := cntSlot) (by rw [g₃, g₂, g₁, hb])
      (by decide) (by rw [wr₃, wr₂, wr₁]; exact hw)
    obtain e : runBlock isa stash s = some s₄ := by
      rw [stash, show ([st (savedSlot + 1) .esi, st (savedSlot + 3) .ebp, st ptrSlot .ebx, st cntSlot .edx] :
          List Instr) = [.store (slotAt .edi (savedSlot + 1)) .esi] ++ ([.store (slotAt .edi (savedSlot + 3)) .ebp] ++
          ([.store (slotAt .edi ptrSlot) .ebx] ++ [.store (slotAt .edi cntSlot) .edx])) from rfl,
        runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
        Option.bind_some, e₄]
    obtain he : s' = s₄ := by
      have e'' : runBlock isa stash s = some s' := e'
      rw [e] at e''; exact (Option.some.inj e'').symm
    subst he
    refine (f₁.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans ((f₂.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans
      ((f₃.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans (f₄.sub fun r hr => ⟨r, ?_, fun _ h => h⟩))) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;> simp [stashRegions]
  refine ⟨s', e', v' (ptrSlot, .ebx) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    v' (cntSlot, .edx) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    ⟨fun e he => ?_, fun i hi => ?_⟩, g', rd', wr', fr⟩
  · rw [o' _ (by simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        savedSlot_eq, ptrSlot_eq, cntSlot_eq, tableSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith)]
    exact hsc.keys e he
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [o' _ (by decide) (by decide)]; exact hsc.saved 0 (by decide)
    · rw [v' (savedSlot + 1, .esi) List.mem_cons_self]; exact hesi
    · rw [o' _ (by decide) (by decide)]; exact hsc.saved 2 (by decide)
    · rw [v' (savedSlot + 3, .ebp) (List.mem_cons_of_mem _ List.mem_cons_self)]; exact hebp

/-- `unstash`: the caller's `esi` and `ebp`, the data pointer and the blocks
left back. -/
theorem unstash_ok {s₀ s : State} {b P N : BitVec 32} {E : Nat → Spec.Seed.Word} (hw : ScrIn s.wr b)
    (hb : s.gpr .edi = b) (hsc : ScrOk s₀ b E s.mem) (hP : s.mem.readW (wordAddr b ptrSlot) 32 = P)
    (hN : s.mem.readW (wordAddr b cntSlot) 32 = N) :
    ∃ s', runBlock isa unstash s = some s' ∧ s'.gpr .esi = s₀.gpr .esi ∧ s'.gpr .ebp = s₀.gpr .ebp ∧
      s'.gpr .ebx = P ∧ s'.gpr .edx = N ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ebx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.esi, savedSlot + 1), (.ebp, savedSlot + 3), (.ebx, ptrSlot), (.edx, cntSlot)]
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok .edi L s hb hw (by decide) (by decide) (by decide)
  refine ⟨s', e', ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => o' r (by simp [L, h1, h2, h3, h4]), m', rd', wr'⟩
  · rw [v' (.esi, savedSlot + 1) (by simp [L])]; exact hsc.saved 1 (by decide)
  · rw [v' (.ebp, savedSlot + 3) (by simp [L])]; exact hsc.saved 3 (by decide)
  · rw [v' (.ebx, ptrSlot) (by simp [L])]; exact hP
  · rw [v' (.edx, cntSlot) (by simp [L])]; exact hN

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := toNat_addr b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  obtain z0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  obtain hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega_arith)
  obtain hAk : A.toNat = D.toNat + 128 * k := toNat_add32 _ (by omega_arith)
  let T64 := b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot)
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    obtain ⟨n', hn', hf', hr'⟩ := hwS.mem
    refine ⟨_, hr', ?_⟩
    rw [VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq] at hn'; rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨T64, 16 * c⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  obtain dT : (slotsRegion b tableSlot slots).Disjoint ⟨T64, 16 * c⟩ :=
    VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain dA : (slotsRegion b tableSlot slots).Disjoint ⟨A.setWidth 64, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  obtain dTab : (slotsRegion b tableSlot slots).Disjoint ⟨b.setWidth 64, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  obtain subTab : (slotsRegion b tableSlot ptrSlot).Sub (slotsRegion b tableSlot slots) :=
    VG.Offset.sub _ (by decide) (by decide)
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain hsub := stash_sub hfit'
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (countR_wp hi.cnt hv) fun s₁ ⟨ecx₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  refine WP.mono (guardedFrom_wp (s₀ := s₁) (sr := .ebx) (dr := .edi) (X := A) (Y := b) (so := 0)
    (dd := 4 * tailSlot) (c := c) (by decide) (by decide) (by decide) (by decide) (by omega_arith)
    (by omega_arith) (by rw [tailSlot_eq]; omega_arith) (by rw [z0]; exact sepAT)
    (fun t ht h4 => by rw [z0, rd₁, wr₁]; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₁]; exact inT t ht h4) 8 0 s₁ (by decide) rfl rfl
    (by rw [o₁ _ (by decide), hi.ptr]) (by rw [o₁ _ (by decide), hi.base]) ecx₁ (fun _ _ => rfl)
    ⟨fun t ht => by omega_arith, Frame.refl _ _⟩) fun s₃ ⟨cp₃, g₃', rd₃', wr₃'⟩ => ?_
  rw [z0, show min (0 + 8) c = c by omega_arith] at cp₃
  obtain f₃ : Frame [⟨T64, 16 * c⟩] s.mem s₃.mem := by rw [← m₁]; exact cp₃.frame
  obtain g₃ : ∀ r, r ≠ .ecx → r ≠ .eax → s₃.gpr r = s.gpr r :=
    fun r h2 h3 => by rw [g₃' r h3, o₁ r h2]
  obtain base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  obtain wr₃ : s₃.wr = s.wr := by rw [wr₃', wr₁]
  obtain rd₃ : s₃.rd = s.rd := by rw [rd₃', rd₁]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The caller's `esi` and `ebp`, the data pointer and the blocks left to their slots.
  obtain ⟨s₄, e₄, dp₄, np₄, sc₄, g₄, rd₄, wr₄, fs⟩ := stash_ok hwS₃ base₃ sc₃
    (by rw [g₃ _ (by decide) (by decide), hi.esi]) (by rw [g₃ _ (by decide) (by decide), hi.ebp])
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  obtain base₄ : s₄.gpr sb = b := by rw [g₄]; exact base₃
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks.
  obtain hR₄ : Room s₄ := ⟨by rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
  refine WP.seq (WP.mono (crypt8_wp hR₄) fun s₅ ⟨b₅, _, rd₅', wr₅', sb₅, esp₅, sl₅, f₅'⟩ => ?_)
  obtain base₅ : s₅.gpr .edi = b := sb₅.trans base₄
  obtain f₅ : Frame [⟨b.setWidth 64, 4 * tableSlot⟩] s₄.mem s₅.mem := by rw [base₄] at f₅'; exact f₅'
  obtain keep₅ : ∀ j, tableSlot ≤ j → j < slots →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by have := sl₅ j h1 h2; simp only [slotW, sb₅, base₄] at this; exact this
  obtain sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  obtain hk₄ : ∀ j < 16, tableKeys s₄ j = keyPairs E j := fun j hj => by
    simp only [tableKeys, keyPairs, slotW, base₄]
    rw [sc₄.keys _ (by omega_arith), show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega_arith,
      sc₄.keys _ (by omega_arith)]
  obtain wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  obtain esp₅' : s₅.gpr .esp = s₀.gpr .esp := by
    rw [esp₅, g₄, g₃ _ (by decide) (by decide), hi.esp]
  -- The caller's registers, the data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, esi₆, ebp₆, ebx₆, edx₆, o₆a, m₆a, rd₆a, wr₆a⟩ := unstash_ok hwS₅ base₅ sc₅
    ((keep₅ ptrSlot (by decide) (by decide)).trans dp₄) ((keep₅ cntSlot (by decide) (by decide)).trans np₄)
  rw [g₃ _ (by decide) (by decide), hi.ptr] at ebx₆
  rw [g₃ _ (by decide) (by decide), hi.cnt] at edx₆
  unfold copyOut
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₆a, e₆a, ?_⟩))
  refine WP.seq (WP.mono (countR_wp edx₆ hv) fun s₆ ⟨ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_)
  obtain base₆ : s₆.gpr .edi = b := by
    rw [o₆ _ (by decide), o₆a _ (by decide) (by decide) (by decide) (by decide), base₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  refine WP.mono (guardedFrom_wp (s₀ := s₆) (sr := .edi) (dr := .ebx) (X := b) (Y := A) (so := 4 * tailSlot)
    (dd := 0) (c := c) (by decide) (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by rw [z0]; exact sepAT.symm)
    (fun t ht h4 => by rw [rd₆', wr₆']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [z0, wr₆']; exact inA t ht h4) 8 0 s₆ (by decide) rfl rfl base₆
    (by rw [o₆ _ (by decide), ebx₆]) ecx₆ (fun _ _ => rfl) ⟨fun t ht => by omega_arith, Frame.refl _ _⟩)
    fun s₈ ⟨cp₈, g₈', rd₈', wr₈'⟩ => ?_
  rw [z0, show min (0 + 8) c = c by omega_arith] at cp₈
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  obtain f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₆]; exact cp₈.frame
  obtain g₈ : ∀ r, r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆a.gpr r :=
    fun r h2 h3 => by rw [g₈' r h3, o₆ r h2]
  obtain sc₈ : ScrOk s₀ b E s₈.mem := sc₅.frame hfit' f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  obtain wr₈ : s₈.wr = s.wr := by rw [wr₈', wr₆']
  obtain rd₈ : s₈.rd = s.rd := by rw [rd₈', rd₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Seed.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Seed.blockAt, Vector.getElem_ofFn]
    have := cp₃.copied (16 * j + u) (by omega_arith)
    rw [VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ stashRegions b,
        ¬ r.Contains (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [stashRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [slot_addr (by (try simp only [savedSlot_eq, ptrSlot_eq, cntSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, savedSlot_eq, ptrSlot_eq, cntSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith)
          (by (try simp only [savedSlot_eq, ptrSlot_eq, cntSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, m₁, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₈.copied _ (by omega_arith), mem₆, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T64 + BitVec.ofNat 64 (i - 128 * k) =
          (s₅.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [show s₅.gpr sb = b from base₅, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj, Proof.Seed.crypt_congr hk₄]
      rfl
    · have hout : ∀ r ∈ [(⟨A.setWidth 64, 16 * c⟩ : Region)],
          ¬ r.Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hA]
        exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₈ _ hout,
        f₅.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  -- On to the next group.
  obtain fr : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₈.mem := by
    refine hi.frame.trans ((f₃.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₈.sub fun r hr => ⟨⟨D.setWidth 64, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  obtain ⟨s₉, e₉, r₉, -, o₉, m₉, rd₉, wr₉⟩ := addI_ok s₈ .ebx 128
  obtain ⟨s₁₀, e₁₀, r₁₀, z₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subI_ok s₉ .edx (s₉.gpr .ecx)
  refine WP.of_runBlock ⟨s₁₀, by
    rw [advance, show ([addI .ebx 128, subR .edx .ecx] : List Instr) = [addI .ebx 128] ++ [subR .edx .ecx] from rfl,
      runBlock_append, e₉, Option.bind_some,
      show runBlock isa [subR .edx .ecx] s₉ = runBlock isa [subI .edx (s₉.gpr .ecx)] s₉ from rfl, e₁₀], ?_⟩
  obtain g₁₀ : ∀ r, r ≠ .ebx → r ≠ .edx → r ≠ .ecx → r ≠ .eax → s₁₀.gpr r = s₆a.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₁₀ r h2, o₉ r h1, g₈ r h3 h4]
  obtain keepA : ∀ r, r ≠ .ebx → r ≠ .edx → r ≠ .ecx → r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₁₀.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₁₀ r h1 h2 h3 h4, o₆a r h5 h6 h1 h2]
  obtain base₁₀ : s₁₀.gpr .edi = b := by
    rw [keepA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by
    rw [keepA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₅']
  obtain esi₁₀ : s₁₀.gpr .esi = s₀.gpr .esi := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  obtain ebp₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, hi.rd]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, hi.wr]
  obtain mem₁₀ : s₁₀.mem = s₈.mem := by rw [m₁₀, m₉]
  rw [← mem₁₀] at sc₈ hdata fr
  obtain ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 c := by
    rw [o₉ _ (by decide), g₈' _ (by decide)]; exact ecx₆
  obtain edx₉ : s₉.gpr .edx = BitVec.ofNat 32 v := by
    rw [o₉ _ (by decide), g₈ _ (by decide) (by decide), edx₆]
  obtain zz : s₁₀.zf = some (decide (v = c)) := by
    rw [z₁₀, edx₉, ecx₉, ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, esi₁₀, ebp₁₀, sc₈,
      by have := hdata; rw [hn] at this; exact this, fr, rd₁₀', wr₁₀'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₀, esp₁₀, ?_, ?_, esi₁₀, ebp₁₀, by omega_arith, sc₈,
      by rw [show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₀', wr₁₀'⟩
    · rw [o₁₀ _ (by decide), r₉, g₈ _ (by decide) (by decide), ebx₆]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₀, edx₉, ecx₉, VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]

/-- The data loop. -/
theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_arith, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

end VG.Proof.Seed.X86

end

end


/-!
# SEED ECB on x86 (32-bit): the whole function

`ecb_wp`: with the working space as an argument (`ecbX86W w`, of any `w`
slots that hold the code's `slots`; `ecbX86`, the `wsSlots` slots of the
blocks function), `blocks`, called with the flag of the direction `d` in
the working space's slot `dirSlot`, saves the callee-saved registers,
copies the round keys to the table in the order the rounds of `d` use them
(`keyTable_ok`), the branch on the flag, transforms the blocks a group at a time
(`dataLoop_wp`), from the data pointer in `ebx`, and restores `ebx` and
`edi` (the groups keep `esi` and `ebp`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG VG.X86 VG.Impl.Seed.X86

/-- ECB on x86 with its working space, of `w` slots, as the fourth argument. -/
def ecbX86W (w : Nat) (d : Spec.Seed.Direction) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * w⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * w ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    s.mem.readW (VG.X86.Straight.wordAddr (arg s 3) Impl.Seed.X86.dirSlot) 32 =
      BitVec.ofNat 32 (Impl.Seed.X86.dirFlag d)
  post s s' :=
    Spec.Seed.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) d
        (Spec.Seed.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- ECB on x86 with its working space, the `wsSlots` slots of the blocks
functions, as the fourth argument. -/
def ecbX86 (d : Spec.Seed.Direction) : Contract X86.isa := ecbX86W wsSlots d

end VG.Proof.Seed

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt st argOp at_ movS)
open VG.Proof.Seed (ecbX86W ecbX86 crypt_congr)

/-! ## The arguments -/

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := toNat_addr (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

/-! ## The table of round keys -/

/-- `mov eax, [ecx + 4 a]; mov [edi + 4 d], eax` for each `(a, d)`. -/
def loadsCode (L : List (Nat × Nat)) : List Instr :=
  L.flatMap fun p => [.mov .eax (.mem (at_ .ecx (4 * p.1))), st p.2 .eax]

/-- The schedule at `sched` and the scratch buffer at `b`. -/
structure SchedPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  ecx : s.gpr .ecx = sched
  sch : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩

/-- Word `i` of the schedule. -/
def schW (m : Mem) (sched : BitVec 32) (i : Nat) : BitVec 32 := m.readW (wordAddr sched i) 32

theorem loads_ok {b sched : BitVec 32} :
    ∀ (L : List (Nat × Nat)) (s : State), SchedPre s b sched → (∀ p ∈ L, p.1 < 32 ∧ p.2 < slots) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (loadsCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (wordAddr b p.2) 32 = schW s.mem sched p.1) ∧
        (∀ j < slots, j ∉ L.map (·.2) → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    obtain hp := hL p List.mem_cons_self
    have hfK := hs.schFit
    obtain hea : s.ea (at_ .ecx (4 * p.1)) = wordAddr sched p.1 := by
      show addr (s.gpr .ecx) (4 * p.1) = _; rw [hs.ecx]
    obtain hin : InRegions (s.rd ++ s.wr) (wordAddr sched p.1) 4 :=
      ⟨_, hs.sch, by
        rw [slot_addr (by omega_arith)]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    let v := schW s.mem sched p.1
    let s₁ := s.setReg .eax v
    obtain e₀ : exec (.mov .eax (.mem (at_ .ecx (4 * p.1)))) s = some s₁ := by
      simp only [exec, readSrc, hea, State.load32, hin, ↓reduceIte, Option.map_some]; rfl
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax sb (k := p.2)
      (by rw [show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base]) hp.2
      (by rw [show s₁.wr = s.wr from rfl]; exact hs.scr)
    obtain e₁ : runBlock isa [.mov .eax (.mem (at_ .ecx (4 * p.1))), st p.2 .eax] s = some s₂ := by
      rw [runBlock_cons, e₀, runStep_some]; exact e₂
    obtain hs₂ : SchedPre s₂ b sched :=
      ⟨by rw [g₂, show s₁.gpr sb = s.gpr sb from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.base],
        by rw [wr₂]; exact hs.scr,
        by rw [g₂, show s₁.gpr .ecx = s.gpr .ecx from RegUpd.gpr_setReg_of_ne _ _ (by decide), hs.ecx],
        by rw [rd₂, wr₂]; exact hs.sch, hfK, hs.sep⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := loads_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    have hfit := hs.scr.fit
    obtain hsch : ∀ i < 32, schW s₂.mem sched i = schW s.mem sched i := by
      intro i hi
      simp only [schW]
      rw [slot_addr (by omega_arith)]
      refine f₂.readW (r := ⟨sched.setWidth 64, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (slot_sub hfit hp.2)
    obtain m₂' : s₂.mem = s.mem.writeW (wordAddr b p.2) v := by
      rw [m₂, show s₁.mem = s.mem from rfl, show s₁.gpr .eax = v from RegUpd.gpr_setReg_self _ _ _]
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd', rd₂]; rfl,
      by rw [wr', wr₂]; rfl, ?_⟩
    · rw [loadsCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, m₂', readW_slot_write hfit _ hp.2 hp.2, ite_eq_left rfl]
      · rw [v' q hq, hsch _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, m₂', readW_slot_write hfit _ hj hp.2, ite_eq_right hjL.1]
    · rw [g' r hr, g₂, RegUpd.gpr_setReg_of_ne _ _ hr]
    · exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hp.2⟩).trans f'

def tableMoves (d : Spec.Seed.Direction) : List (Nat × Nat) := (List.range 32).map fun i => (keySrc d i, tableSlot + i)

theorem keyTable_eq (d : Spec.Seed.Direction) :
    keyTable d = .mov .ecx (.mem (argOp 0)) :: loadsCode (tableMoves d) := by
  cases d <;> decide +kernel

theorem keySrc_lt (d : Spec.Seed.Direction) {i : Nat} (hi : i < 32) : keySrc d i < 32 := by
  cases d <;> simp [keySrc] <;> omega_arith

/-- The table, after `ecx` is loaded: word `i` is the schedule's word `keySrc d i`. -/
theorem table_ok (d : Spec.Seed.Direction) {s : State} {b sched : BitVec 32} (hs : SchedPre s b sched) :
    ∃ s', runBlock isa (loadsCode (tableMoves d)) s = some s' ∧
      (∀ i < 32, s'.mem.readW (wordAddr b (tableSlot + i)) 32 = schW s.mem sched (keySrc d i)) ∧
      (∀ j < slots, (j < tableSlot ∨ tableEnd ≤ j) →
        s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := loads_ok (tableMoves d) s hs
    (by intro p hp
        simp only [tableMoves, List.mem_map, List.mem_range] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact ⟨keySrc_lt d hi, by rw [slots_eq, tableSlot_eq]; omega_arith⟩)
    (by cases d <;> decide +kernel)
  refine ⟨s', e', fun i hi => v' (keySrc d i, tableSlot + i) ?_,
    fun j hj hj' => o' j hj ?_, g', rd', wr', f'⟩
  · simp only [tableMoves, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩
  · simp only [tableMoves, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro i hi he; rw [tableSlot_eq, tableEnd_eq] at *; omega_arith

/-! ## The block function -/

/-- The block function of each direction. -/
def blockFn (sch : Spec.Seed.Schedule) : Spec.Seed.Direction → Spec.Seed.Block → Spec.Seed.Block
  | .encrypt => Spec.Seed.encryptBlock sch
  | .decrypt => Spec.Seed.decryptBlock sch

theorem ecb_eq (sch : Spec.Seed.Schedule) (d : Spec.Seed.Direction) (l : List Spec.Seed.Block) :
    Spec.Seed.ecb sch d l = l.map (blockFn sch d) := by
  cases d <;> rfl

/-- The table's round keys are the schedule's, in the order of `d`. -/
theorem keyPairs_eq (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    {j : Nat} (hj : j < 16) :
    keyPairs (fun i => schW m sched (keySrc d i)) j =
      Spec.Seed.roundKey (Spec.Seed.scheduleAt m (sched.setWidth 64))
        (match d with | .encrypt => j | .decrypt => 15 - j) := by
  obtain hw : ∀ i < 32, schW m sched i = m.readW (sched.setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 := fun i hi => by
    simp only [schW]; rw [slot_addr (by omega_arith)]
  cases d
  · rw [Proof.Seed.roundKey_readW _ _ hj]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega_arith), hw _ (by omega_arith), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * j) = 8 * j by omega_arith, show 4 * (2 * j + 1) = 8 * j + 4 by omega_arith]
  · show keyPairs _ j = Spec.Seed.roundKey _ (15 - j)
    rw [Proof.Seed.roundKey_readW _ _ (by omega_arith)]
    simp only [keyPairs, keySrc]
    rw [hw _ (by omega_arith), hw _ (by omega_arith), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add,
      show 4 * (2 * (15 - 2 * j / 2) + 2 * j % 2) = 8 * (15 - j) by omega_arith,
      show 4 * (2 * (15 - (2 * j + 1) / 2) + (2 * j + 1) % 2) = 8 * (15 - j) + 4 by omega_arith]

theorem outF_spec (d : Spec.Seed.Direction) (m : Mem) {sched : BitVec 32} (hfit : sched.toNat + 128 ≤ 2 ^ 32)
    (D : Addr) (j : Nat) :
    outF m D (fun i => schW m sched (keySrc d i)) j =
      blockFn (Spec.Seed.scheduleAt m (sched.setWidth 64)) d
        (Spec.Seed.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  simp only [outF]
  cases d
  · exact crypt_congr (fun i hi => keyPairs_eq .encrypt m hfit hi) _
  · exact crypt_congr (fun i hi => keyPairs_eq .decrypt m hfit hi) _

/-! ## The function -/

theorem ecb_wpW (dir : Spec.Seed.Direction) {w : Nat} (hw : slots ≤ w) {s₀ : State}
    (hp : (ecbX86W w dir).pre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86W w dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, dAD, dAS, dRD, dRS, fitK, fitD, fitB, fitE, hflag⟩ := hp
  let sched := arg s₀ 0
  let D := arg s₀ 1
  let n := (arg s₀ 2).toNat
  let b := arg s₀ 3
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by
    have : b.toNat + 4 * w ≤ 2 ^ 32 := fitB
    omega_using [this, hw]
  obtain hwS : ScrIn s₀.wr b := ⟨⟨w, hw, fitB, by rw [hwr]; simp [b]⟩, hfit'⟩
  obtain subWs : Region.Sub ⟨b.setWidth 64, 4 * slots⟩ ⟨b.setWidth 64, 4 * w⟩ :=
    Region.sub_prefix (Nat.mul_le_mul_left 4 hw)
  obtain dDS' : Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ ⟨b.setWidth 64, 4 * slots⟩ := dDS.sub_right subWs
  obtain dAS' : Region.Disjoint ⟨argAddr s₀ 0, 16⟩ ⟨b.setWidth 64, 4 * slots⟩ := dAS.sub_right subWs
  obtain dKS' : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩ := dKS.sub_right subWs
  obtain hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS') (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains s₀ fitE hi⟩
  obtain subS : ∀ k < slots, Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    fun k hk => slot_sub hfit' hk
  unfold blocks
  -- The prologue, and the direction's flag.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, ks₁⟩ := save_ok (k := 3) hwS (argIn rfl rfl rfl 3 (by decide))
    (by rw [ea_arg rfl]; rfl)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain ⟨s₁f, e₁f, v₁f, o₁f, m₁f, rd₁f, wr₁f, -, -⟩ := lptrSlot_ok s₁ .eax .edi (k := dirSlot) b₁
    (by decide) (by rw [wr₁]; exact hwS)
  let s₁t := arithFlags s₁f (s₁f.gpr .eax &&& s₁f.gpr .eax) false false
  obtain e₁t : runBlock isa entry s₀ = some s₁t := by
    rw [entry, runBlock_append, e₁, Option.bind_some,
      show ([movS .eax dirSlot, .alu .test .eax (.reg .eax)] : List Instr) =
        [movS .eax dirSlot] ++ [.alu .test .eax (.reg .eax)] from rfl, runBlock_append]
    change (runBlock isa [.mov .eax (.mem (slotAt .edi dirSlot))] s₁).bind _ = _
    rw [e₁f, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₁t, e₁t, ?_⟩)
  obtain fl₁ : s₁f.gpr .eax = BitVec.ofNat 32 (dirFlag dir) := by
    rw [v₁f, ks₁ _ (.inr (by decide)) (by decide)]
    exact hflag
  obtain hz₁ : s₁t.zf = some (decide (dirFlag dir = 0)) := by
    rw [RegUpd.zf_arithFlags, fl₁, BitVec.and_self]
    cases dir <;> rfl
  obtain o₁t : ∀ r, r ≠ .eax → s₁t.gpr r = s₁.gpr r := fun r hr => by
    show s₁f.gpr r = _; exact o₁f r hr
  obtain m₁t : s₁t.mem = s₁.mem := by show s₁f.mem = _; exact m₁f
  obtain rd₁t : s₁t.rd = s₀.rd := by show s₁f.rd = _; rw [rd₁f, rd₁]
  obtain wr₁t : s₁t.wr = s₀.wr := by show s₁f.wr = _; rw [wr₁f, wr₁]
  obtain esp₁t : s₁t.gpr .esp = s₀.gpr .esp := by rw [o₁t _ (by decide), esp₁]
  -- The table, in the order of the direction.
  refine WP.seq ?_
  obtain ⟨s₁', e₁', c₁', o₁', m₁'', rd₁', wr₁'⟩ := ldArg_ok s₁t .ecx 0 (argIn rd₁t wr₁t esp₁t 0 (by decide))
  obtain m₁' : s₁'.mem = s₁.mem := m₁''.trans m₁t
  obtain ecx₁ : s₁'.gpr .ecx = sched := by rw [c₁', ea_arg esp₁t, m₁t]; exact argR f₁ 0 (by decide)
  obtain hk₁ : SchedPre s₁' b sched :=
    ⟨by rw [o₁' _ (by decide), o₁t _ (by decide)]; exact b₁, by rw [wr₁', wr₁t]; exact hwS, ecx₁,
      List.mem_append_left _ (by rw [rd₁', rd₁t]; exact hrK), fitK, dKS'⟩
  obtain ⟨s₂, e₂, t₂, k₂, g₂, rd₂', wr₂', f₂⟩ := table_ok dir hk₁
  obtain e₁₂ : runBlock isa (keyTable dir) s₁t = some s₂ := by
    rw [keyTable_eq, show Instr.mov .ecx (.mem (argOp 0)) :: loadsCode (tableMoves dir) =
        [.mov .ecx (.mem (argOp 0))] ++ loadsCode (tableMoves dir) from rfl,
      runBlock_append, e₁', Option.bind_some, e₂]
  suffices hK : WP isa (.block (keyTable dir)) s₁t
      (fun s => WP isa groups s fun s' => abiPreserved s₀ s' ∧ (ecbX86W w dir).post s₀ s') by
    cases dir
    · exact WP.ite true ((eval_e s₁t).trans hz₁) (fun _ => hK) (fun h => absurd h (by decide))
    · exact WP.ite false ((eval_e s₁t).trans hz₁) (fun h => absurd h (by decide)) (fun _ => hK)
  refine WP.of_runBlock ⟨s₂, e₁₂, ?_⟩
  unfold groups
  let E : Nat → Spec.Seed.Word := fun i => schW s₀.mem sched (keySrc dir i)
  have hfK : sched.toNat + 128 ≤ 2 ^ 32 := fitK
  obtain hsch : ∀ i < 32, schW s₁'.mem sched i = schW s₀.mem sched i := by
    intro i hi
    simp only [schW]
    rw [m₁', slot_addr (by omega_arith)]
    refine f₁.readW (r := ⟨sched.setWidth 64, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact dKS'
  obtain f₀₂ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₂.mem := f₁.trans (by rw [← m₁']; exact f₂)
  obtain g₁₂ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → s₂.gpr r = s₀.gpr r := fun r h1 h2 h3 => by
    rw [g₂ r h1, o₁' r h2, o₁t r h1, g₁ r h1 h3]
  obtain base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide), o₁' _ (by decide), o₁t _ (by decide)]; exact b₁
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := g₁₂ _ (by decide) (by decide) (by decide)
  obtain sc₂ : ScrOk s₀ b E s₂.mem := by
    refine ⟨fun e he => ?_, fun i hi => ?_⟩
    · rw [t₂ e he, hsch _ (keySrc_lt dir he)]
    · rw [← sv₁ i hi, ← m₁']
      exact k₂ _ (by rw [savedSlot_eq, slots_eq]; omega_arith) (.inr (by rw [savedSlot_eq, tableEnd_eq]; omega_arith))
  obtain rd₂ : s₂.rd = s₀.rd := by rw [rd₂', rd₁', rd₁t]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [wr₂', wr₁', wr₁t]
  -- The data pointer to `ebx`, and whether there are any blocks.
  obtain ⟨s₃a, e₃a, a₃a, o₃a, m₃a, rd₃a, wr₃a⟩ := ldArg_ok s₂ .ebx 1 (argIn rd₂ wr₂ esp₂ 1 (by decide))
  obtain esp₃a : s₃a.gpr .esp = s₀.gpr .esp := by rw [o₃a _ (by decide), esp₂]
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := ldArg_ok s₃a .edx 2
    (argIn (by rw [rd₃a, rd₂]) (by rw [wr₃a, wr₂]) esp₃a 2 (by decide))
  let s₃ := arithFlags s₃b (s₃b.gpr .edx &&& s₃b.gpr .edx) false false
  obtain e₃ : runBlock isa [.mov .ebx (.mem (argOp 1)), .mov .edx (.mem (argOp 2)), .alu .test .edx (.reg .edx)] s₂ =
      some s₃ := by
    rw [show ([.mov .ebx (.mem (argOp 1)), .mov .edx (.mem (argOp 2)), .alu .test .edx (.reg .edx)] : List Instr) =
      [.mov .ebx (.mem (argOp 1))] ++ ([.mov .edx (.mem (argOp 2))] ++ [.alu .test .edx (.reg .edx)]) from rfl,
      runBlock_append, e₃a, Option.bind_some, runBlock_append, e₃b, Option.bind_some]
    rfl
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  obtain m₃ : s₃.mem = s₂.mem := by show s₃b.mem = _; rw [m₃b, m₃a]
  obtain eax₃ : s₃b.gpr .edx = arg s₀ 2 := by
    rw [a₃b, ea_arg esp₃a, m₃a]; exact argR f₀₂ 2 (by decide)
  obtain ebx₃ : s₃.gpr .ebx = D := by
    show s₃b.gpr .ebx = _
    rw [o₃b _ (by decide), a₃a, ea_arg esp₂]; exact argR f₀₂ 1 (by decide)
  obtain sc₃ : ScrOk s₀ b E s₃.mem := by rw [m₃]; exact sc₂
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem := by rw [m₃]; exact f₀₂
  obtain data₃ : ∀ i < 16 * n, s₃.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => f₀₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS') (by simp only; omega_arith) hi
  obtain fr₃ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₃.mem :=
    f₀₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain g₃ : ∀ r, r ≠ .edx → r ≠ .ebx → s₃.gpr r = s₂.gpr r := fun r h1 h2 => by
    show s₃b.gpr r = _; rw [o₃b r h1, o₃a r h2]
  obtain base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide) (by decide)]; exact base₂
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide) (by decide), esp₂]
  obtain rd₃ : s₃.rd = s₀.rd := by show s₃b.rd = _; rw [rd₃b, rd₃a, rd₂]
  obtain wr₃ : s₃.wr = s₀.wr := by show s₃b.wr = _; rw [wr₃b, wr₃a, wr₂]
  obtain hz₃ : s₃.zf = some (decide (n = 0)) := by
    rw [RegUpd.zf_arithFlags, eax₃, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [n, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  -- The groups.
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n E)
    (WP.ite (decide (n = 0)) ((eval_e s₃).trans hz₃) (fun h0 => ?_) (fun h0 => ?_)) fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₃, esp₃, by rw [g₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide) (by decide)],
      by rw [g₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide) (by decide)], sc₃,
      fun i hi => by omega_arith, fr₃, rd₃, wr₃⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS', fitD⟩ ⟨base₃, esp₃, by rw [ebx₃]; simp,
      by show s₃b.gpr .edx = _; rw [eax₃]; simp [n],
      by rw [g₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide) (by decide)],
      by rw [g₃ _ (by decide) (by decide), g₁₂ _ (by decide) (by decide) (by decide)], by omega_arith, sc₃,
      fun i hi => ?_, fr₃, rd₃, wr₃⟩
    rw [data₃ i hi, ite_eq_right (by omega_arith)]
  -- The epilogue.
  obtain ⟨s₆, e₆, bx₆, di₆, o₆, m₆, -, -⟩ := restoreBE_ok (s₀ := s₀) (b := b) (by rw [d₅.wr]; exact hwS) d₅.base
    d₅.scr.saved
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact bx₆
    · rw [o₆ _ (by decide) (by decide)]; exact d₅.esi
    · exact di₆
    · rw [o₆ _ (by decide) (by decide)]; exact d₅.ebp
    · rw [o₆ _ (by decide) (by decide), d₅.esp]
  · rw [m₆]
    exact d₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRS.sub_right subWs
      · exact dRD) (by decide)
  · have hd₆ : DInv s₀.mem s₆.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E) := fun i hi => by
      rw [m₆]; exact d₅.data i hi
    show Spec.Seed.blocksAt s₆.mem (D.setWidth 64) n = _
    rw [blocksAt_of_dinv hd₆, ecb_eq]
    simp only [Spec.Seed.blocksAt, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    exact outF_spec dir s₀.mem hfK _ j

theorem ecb_wp (dir : Spec.Seed.Direction) {s₀ : State} (hp : (ecbX86 dir).pre s₀) :
    WP isa blocks s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 dir).post s₀ s' :=
  ecb_wpW dir (by decide) hp

end VG.Proof.Seed.X86
