import VerifiedGarbage.Proof.Seed.X86.Prologue

/-!
# A group of blocks of SEED ECB on x86 (32-bit)

As for SM4 (`Proof/Sm4/X86/Group.lean`): `dataGroup_wp`, one iteration of
the data loop, copies the group's blocks (eight, or the last one to seven)
to the tail buffer, transforms it (`crypt8_wp`), copies the blocks back and
steps to the next group. The data pointer and the blocks left live in their
slots (`ptrSlot`, `cntSlot`) between the steps, which use every other register.
-/

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Seed.X86
open VG.Impl.Aes.X86 (sb slotAt movS st movR addI subI subR movI)

/-! ## Small blocks -/

/-- `ecx := min(ebp, 8)`. -/
theorem countR_wp {s : State} {v : Nat} (hn : s.gpr .ebp = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .ecx .ebp
  let s₂ := arithFlags s₁ (s₁.gpr .ebp - 8) ((s₁.gpr .ebp).toNat < (8 : BitVec 32).toNat)
    (subOverflow (s₁.gpr .ebp) 8 (s₁.gpr .ebp - 8))
  have e₂ : runBlock isa [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] s = some s₂ := by
    rw [show ([movR .ecx .ebp, .alu .cmp .ebp (.imm 8)] : List Instr) =
      [movR .ecx .ebp] ++ [.alu .cmp .ebp (.imm 8)] from rfl, runBlock_append, e₁, Option.bind_some]
    rfl
  have ebp₂ : s₂.gpr .ebp = BitVec.ofNat 32 v := by rw [RegUpd.gpr_arithFlags, o₁ _ (by decide), hn]
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
    rw [RegUpd.gpr_arithFlags, r₁, hn, Nat.min_eq_left (by simp at h; omega)]
  · obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s₂ .ecx 8
    refine WP.of_runBlock ⟨s₃, e₃, ?_, fun r hr => by rw [o₃ r hr, o₂ r hr], by rw [m₃, m₂],
      by rw [rd₃, rd₂], by rw [wr₃, wr₂]⟩
    rw [r₃, Nat.min_eq_right (by simp at h; omega)]; rfl

/-- The data pointer and the blocks left from their slots to `esi` and
`ebp`, and `ecx := min(ebp, 8)`. -/
theorem groupCount_wp {s : State} {b A : BitVec 32} {v : Nat} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b)
    (hd : s.mem.readW (wordAddr b ptrSlot) 32 = A) (hn : s.mem.readW (wordAddr b cntSlot) 32 = BitVec.ofNat 32 v)
    (hv : v < 2 ^ 32) :
    WP isa groupCount s fun s' => s'.gpr .esi = A ∧ s'.gpr .ebp = BitVec.ofNat 32 v ∧
      s'.gpr .ecx = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := lptrSlot_ok s .esi .edi (k := ptrSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, -, -⟩ := lptrSlot_ok s₁ .ebp .edi (k := cntSlot)
    (by rw [o₁ _ (by decide), hb]) (by decide) (by rw [wr₁]; exact hw)
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, WP.mono (countR_wp (by rw [r₂, m₁, hn]) hv)
    fun s₃ ⟨c₃, o₃, m₃, rd₃, wr₃⟩ => ?_⟩)
  · rw [show ([movS .esi ptrSlot, movS .ebp cntSlot] : List Instr) =
      [.mov .esi (.mem (slotAt .edi ptrSlot))] ++ [.mov .ebp (.mem (slotAt .edi cntSlot))] from rfl,
      runBlock_append, e₁, Option.bind_some, e₂]
  · exact ⟨by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hd], by rw [o₃ _ (by decide), r₂, m₁, hn], c₃,
      fun r h1 h2 h3 => by rw [o₃ r h3, o₂ r h2, o₁ r h1], by rw [m₃, m₂, m₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩

/-- `st ptrSlot, esi; st cntSlot, ebp`. -/
theorem stDN_ok (s : State) {b : BitVec 32} (hb : s.gpr .edi = b) (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [st ptrSlot .esi, st cntSlot .ebp] s = some s' ∧
      s'.mem.readW (wordAddr b ptrSlot) 32 = s.gpr .esi ∧ s'.mem.readW (wordAddr b cntSlot) 32 = s.gpr .ebp ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      Frame [⟨wordAddr b ptrSlot, 4⟩, ⟨wordAddr b cntSlot, 4⟩] s.mem s'.mem := by
  have hfit : b.toNat + 4 * slots ≤ 2 ^ 32 := hw.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, z₁, -, f₁⟩ := stSlot_ok s .esi .edi (k := ptrSlot) hb (by decide) hw
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, z₂, -, f₂⟩ := stSlot_ok s₁ .ebp .edi (k := cntSlot) (by rw [g₁, hb])
    (by decide) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [z₂, z₁],
    (f₁.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
  · rw [show ([st ptrSlot .esi, st cntSlot .ebp] : List Instr) =
      [.store (slotAt .edi ptrSlot) .esi] ++ [.store (slotAt .edi cntSlot) .ebp] from rfl, runBlock_append, e₁,
      Option.bind_some, e₂]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_right (by decide), m₁,
      readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl]
  · rw [m₂, readW_slot_write hfit _ (by decide) (by decide), ite_eq_left rfl, g₁]

theorem toNat_add32 (D : BitVec 32) {d : Nat} (h : D.toNat + d < 2 ^ 32) :
    (D + BitVec.ofNat 32 d).toNat = D.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt h]

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
  rw [slot_addr (by omega)]
  exact hf.readW (VG.Offset.contains _ (by omega) (by omega) (by omega)) hd (by decide)

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
    exact slot_keep hfit (by decide) hf hd (by omega) (by rw [ptrSlot_eq, tableSlot_eq]; omega)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf hd (by rw [savedSlot_eq, tableSlot_eq]; omega)
      (by rw [savedSlot_eq, ptrSlot_eq]; omega)

/-- The slots of the data pointer and the count are in the scratch buffer. -/
theorem dn_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      Region.Sub r ⟨b.setWidth 64, 4 * slots⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slot_sub hfit (by decide)
  · exact slot_sub hfit (by decide)

/-- … and apart from the table and the saved registers. -/
theorem dn_disj {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
      (slotsRegion b tableSlot ptrSlot).Disjoint r := fun r hr => by
  rw [slots_eq] at hfit
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)] <;>
    exact VG.Offset.disjoint _ (by (try simp only [tableSlot_eq, ptrSlot_eq, cntSlot_eq]); omega)
      (by (try simp only [tableSlot_eq, ptrSlot_eq]); omega) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)

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

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (E : Nat → Spec.Seed.Word) (k : Nat) (s : State) :
    Prop where
  base : s.gpr .edi = b
  esp : s.gpr .esp = s₀.gpr .esp
  dp : s.mem.readW (wordAddr b ptrSlot) 32 = D + BitVec.ofNat 32 (128 * k)
  np : s.mem.readW (wordAddr b cntSlot) 32 = BitVec.ofNat 32 (n - 8 * k)
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
  scr : ScrOk s₀ b E s.mem
  data : DInv s₀.mem s.mem (D.setWidth 64) n n (outF s₀.mem (D.setWidth 64) E)
  frame : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {k : Nat} {s : State} (hi : GInv s₀ b D n E k s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone s₀ b D n E s') ∨
      (s'.zf = some false ∧ GInv s₀ b D n E (k + 1) s') := by
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  have hb := toNat_addr b
  rw [slots_eq] at hfit
  have hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega
  let v := n - 8 * k
  let c := min v 8
  have hv : v < 2 ^ 32 := by omega
  have hc0 : 0 < c := by omega
  have hc8 : c ≤ 8 := by omega
  have hkc : 128 * k + 16 * c ≤ 16 * n := by omega
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  have hA : A.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (128 * k) := setWidth_add (by omega)
  have hT : T.setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot) :=
    setWidth_add (by rw [tailSlot_eq]; omega)
  have hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega)]; omega
  have hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega), tailSlot_eq]; omega
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  have hwD : (⟨D.setWidth 64, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (T.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)
  have inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (A.setWidth 64 + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega) (by omega)
  have subA : Region.Sub ⟨A.setWidth 64, 16 * c⟩ ⟨D.setWidth 64, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega)
  have subT : Region.Sub ⟨T.setWidth 64, 16 * c⟩ ⟨b.setWidth 64, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega)
  have sepAT : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨T.setWidth 64, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  -- The regions the steps write keep the slots from `tableSlot`.
  have dT : (slotsRegion b tableSlot slots).Disjoint ⟨T.setWidth 64, 16 * c⟩ := by
    rw [hT]; exact VG.Offset.disjoint _ (by rw [tableSlot_eq, tailSlot_eq]; omega)
      (by rw [tableSlot_eq, slots_eq]; omega) (by rw [tailSlot_eq]; omega)
  have dA : (slotsRegion b tableSlot slots).Disjoint ⟨A.setWidth 64, 16 * c⟩ :=
    ((hp.sep.sub_left subA).sub_right (VG.Offset.sub_base _ (by rw [tableSlot_eq, slots_eq]))).symm
  have dTab : (slotsRegion b tableSlot slots).Disjoint ⟨b.setWidth 64, 4 * tableSlot⟩ :=
    VG.Offset.disjoint_base _ (by omega) (by rw [tableSlot_eq, slots_eq]; omega)
  have subTab : (slotsRegion b tableSlot ptrSlot).Sub (slotsRegion b tableSlot slots) :=
    VG.Offset.sub _ (by decide) (by decide)
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨D.setWidth 64, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  have hsub := dn_sub hfit'
  have dsTab := dn_disj hfit'
  unfold group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.base hwS hi.dp hi.np hv)
    fun s₁ ⟨esi₁, ebp₁, ecx₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, -, -⟩ := movR_ok s₁ .edx .esi
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b, -, -⟩ := movR_ok s₂a .ebx .edi
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₂b .ebx (BitVec.ofNat 32 (4 * tailSlot))
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [tailAddr, show ([movR .edx .esi] ++ [movR .ebx .edi, addI .ebx (BitVec.ofNat 32 (4 * tailSlot))] :
        List Instr) = [movR .edx .esi] ++ ([movR .ebx .edi] ++ [addI .ebx (BitVec.ofNat 32 (4 * tailSlot))])
        from rfl, runBlock_append, e₂a, Option.bind_some, runBlock_append, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, esi₁]; simp [A],
      by rw [r₂, r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂b _ (by decide), o₂a _ (by decide), ecx₁, Nat.sub_zero],
      ⟨fun t ht => by omega, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ h₃ => ?_)
  have f₃ : Frame [⟨T.setWidth 64, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  have g₃ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₃.gpr r = s₁.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₃.regs r h0 h1 h2 h3, o₂ r h1, o₂b r h1, o₂a r h0]
  have base₃ : s₃.gpr .edi = b := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide) (by decide), hi.base]
  have sc₃ : ScrOk s₀ b E s₃.mem := hi.scr.frame hfit' f₃ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dT.sub_left subTab
  have wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  have rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  have hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer and the blocks left back to their slots.
  obtain ⟨s₄, e₄, dp₄, np₄, g₄, rd₄, wr₄, -, fs⟩ := stDN_ok s₃ base₃ hwS₃
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  have esi₃ : s₃.gpr .esi = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), esi₁]
  have ebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), ebp₁]
  rw [esi₃] at dp₄
  rw [ebp₃] at np₄
  have sc₄ : ScrOk s₀ b E s₄.mem := sc₃.frame hfit' fs dsTab
  have base₄ : s₄.gpr sb = b := by rw [g₄]; exact base₃
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃]
  -- The eight blocks.
  have hR₄ : Room s₄ := ⟨by unfold scratchR; rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
  refine WP.seq (WP.mono (crypt8_wp hR₄) fun s₅ ⟨b₅, _, rd₅', wr₅', sb₅, esp₅, sl₅, f₅'⟩ => ?_)
  have base₅ : s₅.gpr .edi = b := sb₅.trans base₄
  have keepr₅ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .eax → s₅.gpr r = s₄.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rcases keep_regs r h1 h2 h3 h4 h5 h6 with rfl | rfl
      · exact esp₅
      · exact sb₅
  have f₅ : Frame [⟨b.setWidth 64, 4 * tableSlot⟩] s₄.mem s₅.mem := by rw [base₄] at f₅'; exact f₅'
  have keep₅ : ∀ j, tableSlot ≤ j → j < slots →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j h1 h2 => by have := sl₅ j h1 h2; simp only [slotW, sb₅, base₄] at this; exact this
  have sc₅ : ScrOk s₀ b E s₅.mem := sc₄.frame hfit' f₅ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dTab.sub_left subTab
  have hk₄ : ∀ j < 16, tableKeys s₄ j = keyPairs E j := fun j hj => by
    simp only [tableKeys, keyPairs, slotW, base₄]
    rw [sc₄.keys _ (by omega), show tableSlot + 2 * j + 1 = tableSlot + (2 * j + 1) by omega,
      sc₄.keys _ (by omega)]
  have wr₅ : s₅.wr = s.wr := by rw [wr₅', wr₄']
  have rd₅ : s₅.rd = s.rd := by rw [rd₅', rd₄, rd₃]
  have hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp (A := A) base₅ hwS₅
    (by rw [keep₅ _ (by decide) (by decide)]; exact dp₄) (by rw [keep₅ _ (by decide) (by decide)]; exact np₄) hv)
    fun s₆ ⟨esi₆, ebp₆, ecx₆, o₆, m₆, rd₆, wr₆⟩ => ?_))
  obtain ⟨s₇a, e₇a, r₇a, o₇a, m₇a, rd₇a, wr₇a, -, -⟩ := movR_ok s₆ .edx .edi
  obtain ⟨s₇b, e₇b, r₇b, -, o₇b, m₇b, rd₇b, wr₇b⟩ := addI_ok s₇a .edx (BitVec.ofNat 32 (4 * tailSlot))
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, -, -⟩ := movR_ok s₇b .ebx .esi
  have mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₇b, m₇a, m₆]
  have rd₇' : s₇.rd = s.rd := by rw [rd₇, rd₇b, rd₇a, rd₆, rd₅]
  have wr₇' : s₇.wr = s.wr := by rw [wr₇, wr₇b, wr₇a, wr₆, wr₅]
  refine WP.seq (WP.of_runBlock ⟨s₇, by
    rw [tailAddr, show ([movR .edx .edi, addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi] :
        List Instr) = [movR .edx .edi] ++ ([addI .edx (BitVec.ofNat 32 (4 * tailSlot))] ++ [movR .ebx .esi])
        from rfl, runBlock_append, e₇a, Option.bind_some, runBlock_append, e₇b, Option.bind_some, e₇], ?_⟩)
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₇', wr₇']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₇']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₇ _ (by decide), r₇b, r₇a, o₆ _ (by decide) (by decide) (by decide), base₅]; simp [T],
      by rw [r₇, o₇b _ (by decide), o₇a _ (by decide), esi₆]; simp [A],
      by rw [o₇ _ (by decide), o₇b _ (by decide), o₇a _ (by decide), ecx₆, Nat.sub_zero],
      ⟨fun t ht => by omega, Frame.refl _ _⟩, fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₈ h₈ => ?_
  have f₈ : Frame [⟨A.setWidth 64, 16 * c⟩] s₅.mem s₈.mem := by rw [← mem₇]; exact h₈.cp.frame
  have g₈ : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s₈.gpr r = s₆.gpr r :=
    fun r h0 h1 h2 h3 => by rw [h₈.regs r h0 h1 h2 h3, o₇ r h1, o₇b r h0, o₇a r h0]
  have sc₈ : ScrOk s₀ b E s₈.mem := sc₅.frame hfit' f₈ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dA.sub_left subTab
  have wr₈ : s₈.wr = s.wr := by rw [h₈.wr, wr₇']
  have rd₈ : s₈.rd = s.rd := by rw [h₈.rd, rd₇']
  -- The blocks the eight-block code read are the group's, as on entry.
  have hblk : ∀ j < c, tailBlock s₄ j =
      Spec.Seed.blockAt s₀.mem (D.setWidth 64 + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [tailBlock, Spec.Seed.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    have hout : ∀ r ∈ [(⟨wordAddr b ptrSlot, 4⟩ : Region), ⟨wordAddr b cntSlot, 4⟩],
        ¬ r.Contains (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rw [slot_addr (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, ptrSlot_eq, cntSlot_eq]); omega)
          (by rw [tailSlot_eq]; omega) (by omega) (by (try simp only [ptrSlot_eq, cntSlot_eq]); omega)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega,
      fs _ hout, this, mem₂, hi.data _ (by omega), ite_eq_right (by omega), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega]
  have hdata : DInv s₀.mem s₈.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D.setWidth 64 + BitVec.ofNat 64 i = A.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega]
      rw [e1, h₈.cp.copied _ (by omega), mem₇, ite_eq_left (show i < 16 * (8 * k + c) by omega),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega, show i % 16 = (i - 128 * k) % 16 by omega]
      have hj : (i - 128 * k) / 16 < c := by omega
      have eT : T.setWidth 64 + BitVec.ofNat 64 (i - 128 * k) =
          (s₅.gpr sb).setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [show s₅.gpr sb = b from base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (tailBlock s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega), hblk _ hj, Proof.Seed.crypt_congr hk₄]
      rfl
    · have hout : ∀ r ∈ [(⟨A.setWidth 64, 16 * c⟩ : Region)],
          ¬ r.Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hA]
        exact not_contains_off _ (by omega) (by omega) (by omega) (by omega)
      rw [f₈ _ hout,
        f₅.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)) (by simp only; omega) hin,
        fs.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega) hin,
        f₃.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega), ite_eq_left (show i < 16 * (8 * k + c) by omega)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega)]
  -- On to the next group.
  have esi₈ : s₈.gpr .esi = A := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), esi₆]
  have ebp₈ : s₈.gpr .ebp = BitVec.ofNat 32 v := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  unfold advance
  refine WP.seq (WP.mono (countR_wp ebp₈ hv) fun s₉ ⟨ecx₉, o₉, m₉, rd₉, wr₉⟩ => ?_)
  obtain ⟨s₁₀a, e₁₀a, r₁₀a, -, o₁₀a, m₁₀a, rd₁₀a, wr₁₀a⟩ := addI_ok s₉ .esi 128
  obtain ⟨s₁₀b, e₁₀b, r₁₀b, z₁₀b, o₁₀b, m₁₀b, rd₁₀b, wr₁₀b⟩ := subI_ok s₁₀a .ebp (s₁₀a.gpr .ecx)
  have base₁₀b : s₁₀b.gpr .edi = b := by
    rw [o₁₀b _ (by decide), o₁₀a _ (by decide), o₉ _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide), o₆ _ (by decide) (by decide) (by decide), base₅]
  have wr₁₀b' : s₁₀b.wr = s.wr := by rw [wr₁₀b, wr₁₀a, wr₉, wr₈]
  obtain ⟨s₁₀, e₁₀, dp₁₀, np₁₀, g₁₀, rd₁₀, wr₁₀, z₁₀, fa⟩ := stDN_ok s₁₀b base₁₀b (by rw [wr₁₀b']; exact hwS)
  refine WP.of_runBlock ⟨s₁₀, by
    rw [show ([addI .esi 128, subR .ebp .ecx, st ptrSlot .esi, st cntSlot .ebp] : List Instr) =
      [addI .esi 128] ++ ([subR .ebp .ecx] ++ [st ptrSlot .esi, st cntSlot .ebp]) from rfl,
      runBlock_append, e₁₀a, Option.bind_some, runBlock_append,
      show runBlock isa [subR .ebp .ecx] s₁₀a = runBlock isa [subI .ebp (s₁₀a.gpr .ecx)] s₁₀a from rfl,
      e₁₀b, Option.bind_some, e₁₀], ?_⟩
  have ecx₁₀a : s₁₀a.gpr .ecx = BitVec.ofNat 32 c := by rw [o₁₀a _ (by decide), ecx₉]
  have ebp₁₀a : s₁₀a.gpr .ebp = BitVec.ofNat 32 v := by rw [o₁₀a _ (by decide), o₉ _ (by decide), ebp₈]
  have zz : s₁₀.zf = some (decide (v = c)) := by
    rw [z₁₀, z₁₀b, ebp₁₀a, ecx₁₀a, ofNat32_sub_beq (by omega) (by omega)]
  have hmem : ∀ i < 16 * n, s₁₀.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s₈.mem (D.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi' => by
      rw [fa.bytes (R := ⟨D.setWidth 64, 16 * n⟩) (dD hsub) (by simp only; omega) hi', m₁₀b, m₁₀a, m₉]
  have hdata' : DInv s₀.mem s₁₀.mem (D.setWidth 64) n (8 * k + c) (outF s₀.mem (D.setWidth 64) E) :=
    fun i hi' => by rw [hmem i hi']; exact hdata i hi'
  have mem₉' : s₁₀b.mem = s₈.mem := by rw [m₁₀b, m₁₀a, m₉]
  have sc₁₀ : ScrOk s₀ b E s₁₀.mem := (mem₉' ▸ sc₈).frame hfit' fa dsTab
  have g₁₀' : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .ecx → r ≠ .edx → r ≠ .ebx → r ≠ .eax → s₁₀.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [g₁₀, o₁₀b r h2, o₁₀a r h1, o₉ r h3, g₈ r h4 h5 h3 h6, o₆ r h1 h2 h3, keepr₅ r h1 h2 h3 h4 h5 h6, g₄, g₃ r h4 h5 h3 h6, o₁ r h1 h2 h3]
  have base₁₀ : s₁₀.gpr .edi = b := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  have esp₁₀ : s₁₀.gpr .esp = s₀.gpr .esp := by
    rw [g₁₀' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.esp]
  have rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₁₀b, rd₁₀a, rd₉, rd₈, hi.rd]
  have wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₁₀b', hi.wr]
  have fr : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨D.setWidth 64, 16 * n⟩] s₀.mem s₁₀.mem := by
    refine hi.frame.trans ((f₃.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₈.sub fun r hr => ⟨⟨D.setWidth 64, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (mem₉' ▸ fa.sub fun r hr => ⟨⟨b.setWidth 64, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩)))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [slots_eq, tableSlot_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega
    refine .inl ⟨by rw [zz]; simp; omega, base₁₀, esp₁₀, sc₁₀, by have := hdata'; rw [hn] at this; exact this, fr, rd₁₀', wr₁₀'⟩
  · have hc : c = 8 := by omega
    refine .inr ⟨by rw [zz]; simp; omega, base₁₀, esp₁₀, ?_, ?_, by omega, sc₁₀,
      by rw [show 8 * (k + 1) = 8 * k + c by omega]; exact hdata', fr, rd₁₀', wr₁₀'⟩
    · rw [dp₁₀, o₁₀b _ (by decide), r₁₀a, o₉ _ (by decide), esi₈]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega]
    · rw [np₁₀, r₁₀b, ebp₁₀a, ecx₁₀a, VG.Offset.ofNat_sub_ofNat (by omega), show v - c = n - 8 * (k + 1) by omega]

/-- The data loop. -/
theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {E : Nat → Spec.Seed.Word} (hp : GPre s₀ b D n)
    {s : State} (hi : GInv s₀ b D n E 0 s) :
    WP isa (.loop group .ne) s (GDone s₀ b D n E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n E k s) (fun m s hs => ?_) n s
    ⟨0, by omega, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega, k + 1, rfl, d⟩

end VG.Proof.Seed.X86
