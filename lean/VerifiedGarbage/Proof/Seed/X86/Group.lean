module

public import VerifiedGarbage.Proof.Seed.X86.Prologue
import VerifiedGarbage.Proof.Seed.X86.Crypt8
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have e₂ : runBlock isa [movR .ecx .edx, .alu .cmp .edx (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .edx, .alu .cmp .edx (.imm 8)] : List Instr) =
      [movR .ecx .edx] ++ [.alu .cmp .edx (.imm 8)] from rfl, runBlock_append, e₁, Option.bind_some]
    rfl
  have cf₂ : s₂.cf = some (decide (v < 8)) := by
    rw [RegUpd.cf_arithFlags, o₁ _ (by decide), hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl
  have o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr]
  have m₂ : s₂.mem = s.mem := by rw [RegUpd.mem_arithFlags, m₁]
  have rd₂ : s₂.rd = s.rd := by rw [RegUpd.rd_arithFlags, rd₁]
  have wr₂ : s₂.wr = s.wr := by rw [RegUpd.wr_arithFlags, wr₁]
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

/-- The registers other than the ones the steps of a group write. -/
theorem keep_regs (r : Reg) (h1 : r ≠ .esi) (h2 : r ≠ .ebp) (h3 : r ≠ .ecx) (h4 : r ≠ .edx) (h5 : r ≠ .ebx)
    (h6 : r ≠ .eax) : r = .esp ∨ r = .edi := by
  cases r <;> simp_all

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
  have fr : Frame (stashRegions b) s.mem s'.mem := by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s .esi .edi (k := savedSlot + 1) hb (by decide) hw
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .ebp .edi (k := savedSlot + 3) (by rw [g₁, hb])
      (by decide) (by rw [wr₁]; exact hw)
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .ebx .edi (k := ptrSlot) (by rw [g₂, g₁, hb])
      (by decide) (by rw [wr₂, wr₁]; exact hw)
    obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, -, -, f₄⟩ := stSlot_ok s₃ .edx .edi (k := cntSlot) (by rw [g₃, g₂, g₁, hb])
      (by decide) (by rw [wr₃, wr₂, wr₁]; exact hw)
    have e : runBlock isa stash s = some s₄ := by
      rw [stash, show ([st (savedSlot + 1) .esi, st (savedSlot + 3) .ebp, st ptrSlot .ebx, st cntSlot .edx] :
          List Instr) = [.store (slotAt .edi (savedSlot + 1)) .esi] ++ ([.store (slotAt .edi (savedSlot + 3)) .ebp] ++
          ([.store (slotAt .edi ptrSlot) .ebx] ++ [.store (slotAt .edi cntSlot) .edx])) from rfl,
        runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
        Option.bind_some, e₄]
    have he : s' = s₄ := by
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
  have hb := toNat_addr b
  rw [slots_eq] at hfit
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  have z0 : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 32 := by omega_arith
  have hc0 : 0 < c := by omega_arith
  have hc8 : c ≤ 8 := by omega_arith
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  have hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega_arith)
  have hAk : A.toNat = D.toNat + 128 * k := toNat_add32 _ (by omega_arith)
  let T64 := b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot)
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    obtain ⟨n', hn', hf', hr'⟩ := hwS.mem
    refine ⟨_, hr', ?_⟩
    rw [VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq] at hn'; rw [tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  have subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  have subT : Region.Sub ⟨T64, 16 * c⟩ ⟨b.setWidth 64, 4 * slots⟩ :=
    VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  have sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  have dT : (slotsRegion b tableSlot slots).Disjoint ⟨T64, 16 * c⟩ :=
    VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega_arith)
      (by rw [tableSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  have dA : (slotsRegion b tableSlot slots).Disjoint ⟨A.setWidth 64, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  have dTab : (slotsRegion b tableSlot slots).Disjoint ⟨b.setWidth 64, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega_arith) (by rw [tableSlot_eq, slots_eq]; omega_arith)
  have subTab : (slotsRegion b tableSlot ptrSlot).Sub (slotsRegion b tableSlot slots) :=
    VG.Offset.sub _ (by decide) (by decide)
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have hsub := stash_sub hfit'
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
  have f₃ : Frame [⟨T64, 16 * c⟩] s.mem s₃.mem := by rw [← m₁]; exact cp₃.frame
  have g₃ : ∀ r, r ≠ .ecx → r ≠ .eax → s₃.gpr r = s.gpr r :=
    fun r h2 h3 => by rw [g₃' r h3, o₁ r h2]
  have base₃ : s₃.gpr .edi = b := by rw [g₃ _ (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  have wr₃ : s₃.wr = s.wr := by rw [wr₃', wr₁]
  have rd₃ : s₃.rd = s.rd := by rw [rd₃', rd₁]
  have hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The caller's `esi` and `ebp`, the data pointer and the blocks left to their slots.
  obtain ⟨s₄, e₄, dp₄, np₄, sc₄, g₄, rd₄, wr₄, fs⟩ := stash_ok hwS₃ base₃ sc₃
    (by rw [g₃ _ (by decide) (by decide), hi.esi]) (by rw [g₃ _ (by decide) (by decide), hi.ebp])
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have base₄ : s₄.gpr sb = b := by rw [g₄]; exact base₃
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks.
  have hR₄ : Room s₄ := ⟨by rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
  refine WP.seq (WP.mono (crypt8_wp hR₄) fun s₅ ⟨b₅, _, rd₅', wr₅', sb₅, esp₅, sl₅, f₅'⟩ => ?_)
  have base₅ : s₅.gpr .edi = b := sb₅.trans base₄
  have f₅ : Frame [⟨b.setWidth 64, 4 * tableSlot⟩] s₄.mem s₅.mem := by rw [base₄] at f₅'; exact f₅'
  have keep₅ : ∀ j, tableSlot ≤ j → j < slots →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by have := sl₅ j h1 h2; simp only [slotW, sb₅, base₄] at this; exact this
  have sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  have hk₄ : ∀ j < 16, tableKeys s₄ j = keyPairs E j := fun j hj => by
    simp only [tableKeys, keyPairs, slotW, base₄]
    rw [sc₄.keys _ (by omega_arith), show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega_arith,
      sc₄.keys _ (by omega_arith)]
  have wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  have rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₃]
  have hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  have esp₅' : s₅.gpr .esp = s₀.gpr .esp := by
    rw [esp₅, g₄, g₃ _ (by decide) (by decide), hi.esp]
  -- The caller's registers, the data pointer and the blocks left back.
  obtain ⟨s₆a, e₆a, esi₆, ebp₆, ebx₆, edx₆, o₆a, m₆a, rd₆a, wr₆a⟩ := unstash_ok hwS₅ base₅ sc₅
    ((keep₅ ptrSlot (by decide) (by decide)).trans dp₄) ((keep₅ cntSlot (by decide) (by decide)).trans np₄)
  rw [g₃ _ (by decide) (by decide), hi.ptr] at ebx₆
  rw [g₃ _ (by decide) (by decide), hi.cnt] at edx₆
  unfold copyOut
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₆a, e₆a, ?_⟩))
  refine WP.seq (WP.mono (countR_wp edx₆ hv) fun s₆ ⟨ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_)
  have base₆ : s₆.gpr .edi = b := by
    rw [o₆ _ (by decide), o₆a _ (by decide) (by decide) (by decide) (by decide), base₅]
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆a, rd₅]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆a, wr₅]
  refine WP.mono (guardedFrom_wp (s₀ := s₆) (sr := .edi) (dr := .ebx) (X := b) (Y := A) (so := 4 * tailSlot)
    (dd := 0) (c := c) (by decide) (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by rw [z0]; exact sepAT.symm)
    (fun t ht h4 => by rw [rd₆', wr₆']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [z0, wr₆']; exact inA t ht h4) 8 0 s₆ (by decide) rfl rfl base₆
    (by rw [o₆ _ (by decide), ebx₆]) ecx₆ (fun _ _ => rfl) ⟨fun t ht => by omega_arith, Frame.refl _ _⟩)
    fun s₈ ⟨cp₈, g₈', rd₈', wr₈'⟩ => ?_
  rw [z0, show min (0 + 8) c = c by omega_arith] at cp₈
  have mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆a]
  have f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₆]; exact cp₈.frame
  have g₈ : ∀ r, r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆a.gpr r :=
    fun r h2 h3 => by rw [g₈' r h3, o₆ r h2]
  have sc₈ : ScrOk s₀ b E s₈.mem := sc₅.frame hfit' f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  have wr₈ : s₈.wr = s.wr := by rw [wr₈', wr₆']
  have rd₈ : s₈.rd = s.rd := by rw [rd₈', rd₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Seed.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Seed.blockAt, Vector.getElem_ofFn]
    have := cp₃.copied (16 * j + u) (by omega_arith)
    rw [VG.Offset.add_add, hA, VG.Offset.add_add] at this
    have hout : ∀ r ∈ stashRegions b,
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
  have hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₈.copied _ (by omega_arith), mem₆, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      have hj : (i - 128 * k) / 16 < c := by omega_arith
      have eT : T64 + BitVec.ofNat 64 (i - 128 * k) =
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
  have fr : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₈.mem := by
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
  have g₁₀ : ∀ r, r ≠ .ebx → r ≠ .edx → r ≠ .ecx → r ≠ .eax → s₁₀.gpr r = s₆a.gpr r :=
    fun r h1 h2 h3 h4 => by rw [o₁₀ r h2, o₉ r h1, g₈ r h3 h4]
  have keepA : ∀ r, r ≠ .ebx → r ≠ .edx → r ≠ .ecx → r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₁₀.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₁₀ r h1 h2 h3 h4, o₆a r h5 h6 h1 h2]
  have base₁₀ : s₁₀.gpr .edi = b := by
    rw [keepA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  have esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by
    rw [keepA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), esp₅']
  have esi₁₀ : s₁₀.gpr .esi = s₀.gpr .esi := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  have ebp₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, hi.rd]
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, hi.wr]
  have mem₁₀ : s₁₀.mem = s₈.mem := by rw [m₁₀, m₉]
  rw [← mem₁₀] at sc₈ hdata fr
  have ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 c := by
    rw [o₉ _ (by decide), g₈' _ (by decide)]; exact ecx₆
  have edx₉ : s₉.gpr .edx = BitVec.ofNat 32 v := by
    rw [o₉ _ (by decide), g₈ _ (by decide) (by decide), edx₆]
  have zz : s₁₀.zf = some (decide (v = c)) := by
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
