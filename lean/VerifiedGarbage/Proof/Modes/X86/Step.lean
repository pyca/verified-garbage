import VerifiedGarbage.Proof.Modes.X86.Core

/-!
# One step of a mode on x86 (32-bit)

`body_wp`: one run of the loop's body (`Core.body`) takes the invariant
(`Inv`) from `j` steps done to `j + 1`, and sets ZF when no step is left.
After `j` steps, the data are the outputs of the mode's step function `F`
on the first `j` input steps followed by the other inputs, the chaining
value is `F`'s after them, the data pointer and the steps left are in their
slots, and the key is ready. The step's three areas (`areas`) are the
data's step `j`, the chaining value's slots and the core's first block;
`pre` and `post` are `opsCode_wp`, the block cipher `crypt_wp`, and
`Computes M L ciph F` relates them to `F`.
-/

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The areas' lengths: a step's data, and blocks of `4 bw` bytes. -/
def lens (c : Core) (st : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => 4 * c.bw

/-- The areas' addresses, for step `j` of the data at `D`. -/
def areas (c : Core) (B D : BitVec 32) (st j : Nat) : Loc → Addr
  | .dat => D.setWidth 64 + BitVec.ofNat 64 (st * j)
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

/-- The mode's slots of the data pointer, the steps left and the chaining
value. -/
abbrev dnRegion (c : Core) (B : BitVec 32) : Region := ⟨slotA B c.dSlot, 4 * (2 + c.bw)⟩

/-- The data. -/
abbrev dataRegion (D : BitVec 32) (st n : Nat) : Region := ⟨D.setWidth 64, st * n⟩

/-- What a run keeps fixed: the scratch buffer at `B`, the data at `D` of `n`
steps of `st` bytes, the stack the core uses below `esp`, and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : BitVec 32) (n st : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : dataRegion D st n ∈ s₀.wr
  dataFit : D.toNat + st * n ≤ 2 ^ 32
  dataScr : Region.Disjoint (dataRegion D st n) ⟨B.setWidth 64, 4 * c.total⟩
  stkData : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) (dataRegion D st n)
  stkMode : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) ⟨slotA B c.slots, 40⟩
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  step : 0 < st ∧ st ≤ 4 * c.bw
  layout : Layout c

/-- The invariant after `j` of the `n` steps from the inputs `xs` and the
chaining value `c0`. -/
structure Inv (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (n st : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j)
  np : s.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (n - j)
  ready : cs.Ready s B k
  data : chunksAt st s.mem (D.setWidth 64) n = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame [coreRegion c B, dnRegion c B, dataRegion D st n, stkRegion (s₀.gpr .esp) c.stack] s₀.mem s.mem

/-! ## Areas -/

theorem rd_cont (A : Loc → Addr) (m : Mem) (l : Loc) (n : Nat) : rd (cont A m) l n = bytesAt m (A l) n := rfl

theorem rd_agree {len : Loc → Nat} {a a' : Areas} (h : Agree len a a') {l : Loc} {n : Nat} (hn : n ≤ len l) :
    rd a l n = rd a' l n :=
  List.map_congr_left fun i hi => h l i (by have := List.mem_range.mp hi; omega)

theorem cryptBuf_agree {len : Loc → Nat} {n : Nat} (hn : n ≤ len .buf) (ciph : Spec.Cbc.Cipher) {a a' : Areas}
    (h : Agree len a a') : Agree len (cryptBuf n ciph a) (cryptBuf n ciph a') := by
  intro l i hi
  simp only [cryptBuf]
  split
  · rename_i hl; subst hl; rw [rd_agree h hn]
  · exact h l i hi

/-- Slot `k` plus `off`, as the code addresses it. -/
theorem addr_slot {B : BitVec 32} {k off total : Nat} (hfit : B.toNat + 4 * total ≤ 2 ^ 32)
    (h : 4 * k + off < 4 * total) : addr B (4 * k + off) = slotA B k + BitVec.ofNat 64 off := by
  rw [addr_eq (by omega), VG.Offset.add_add]

theorem slot_contains {B : BitVec 32} {total d n : Nat} (hfit : B.toNat + 4 * total ≤ 2 ^ 32)
    (h : d + n ≤ 4 * total) :
    (⟨B.setWidth 64, 4 * total⟩ : Region).Contains (B.setWidth 64 + BitVec.ofNat 64 d) n :=
  VG.Offset.contains_base _ h (by omega)

theorem slot_sub {B : BitVec 32} {total d n : Nat} (h : d + n ≤ 4 * total) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ ⟨B.setWidth 64, 4 * total⟩ :=
  VG.Offset.sub_base _ h

/-- Every byte of the areas at step `j`, as the code addresses them. -/
theorem areasOk {s₀ s : State} {B D : BitVec 32} {n st j : Nat} (hF : Fixed c s₀ B D n st) (hj : j < n)
    (hb : s.gpr sb = B) (hesi : s.gpr .esi = D + BitVec.ofNat 32 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st) (areas c B D st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  have hst := hF.step
  have hD := hF.dataFit
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hW : ∀ l off w, off + w ≤ lens c st l → InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.dataW, ?_⟩
      rw [VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega) (by omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by simp only [Core.chnSlot]; omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by omega)
  refine ⟨fun l off ho => ?_, fun l off w ho => ?_, fun l _ off w ho => hW l off w ho, fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hesi, Nat.zero_add, addr, VG.Offset.add_add, ← addr, addr_eq (by omega), VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by simp only [Core.chnSlot]; omega)
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by omega)
  · obtain ⟨r, hr, hc⟩ := hW l off w ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 4 * c.total →
        Region.Disjoint ⟨D.setWidth 64 + BitVec.ofNat 64 (st * j), st⟩ ⟨B.setWidth 64 + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by simp only [Core.chnSlot]; omega)) (by simp only [Core.chnSlot]; omega)
        (by omega)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by simp only [Core.chnSlot]; omega)
    · exact dD _ _ (by omega)
    · exact (dD _ _ (by simp only [Core.chnSlot]; omega)).symm
    · exact dCB
    · exact (dD _ _ (by omega)).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega

/-! ## The slots -/

theorem slot_in {s : State} {B : BitVec 32} {total k : Nat} (hS : ScrIn s B total) (hk : k < total) :
    InRegions (s.rd ++ s.wr) (addr B (4 * k)) 4 := by
  have := hS.fit
  refine ⟨_, List.mem_append_right _ hS.wr, ?_⟩
  rw [addr_eq (by omega)]; exact slot_contains hS.fit (by omega)

theorem slot_inW {s : State} {B : BitVec 32} {total k : Nat} (hS : ScrIn s B total) (hk : k < total) :
    InRegions s.wr (addr B (4 * k)) 4 := by
  have := hS.fit
  refine ⟨_, hS.wr, ?_⟩
  rw [addr_eq (by omega)]; exact slot_contains hS.fit (by omega)

theorem addr_slotA {B : BitVec 32} {total k : Nat} (hfit : B.toNat + 4 * total ≤ 2 ^ 32) (hk : k < total) :
    addr B (4 * k) = slotA B k := addr_eq (by omega)

/-- The data pointer and the steps left to `esi` and `ebp`. -/
theorem load_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .esi = s.mem.readW (slotA B c.dSlot) 32 → s'.gpr .ebp = s.mem.readW (slotA B c.nSlot) 32 →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (c.load ++ is)) s Q := by
  have := hL.room
  have hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega
  have hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega
  simp only [Core.load, slotAt, at_, List.cons_append, List.nil_append]
  refine wp_ldm hb (slot_in hS hd) fun s₁ u₁ => ?_
  refine wp_ldm (B := B) (by rw [u₁.other _ (by decide)]; exact hb) (by rw [u₁.rd, u₁.wr]; exact slot_in hS hn)
    fun s₂ u₂ => ?_
  refine k s₂ (by rw [u₂.other _ (by decide), u₁.gpr, addr_slotA hS.fit hd])
    (by rw [u₂.gpr, u₁.mem, addr_slotA hS.fit hn]) (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

/-- On by `st` bytes, one step fewer, both stored back. -/
theorem advance_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    (st : Nat) {Q : State → Prop}
    (k : ∀ s', s'.zf = some (s.gpr .ebp - 1 == 0) → (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (slotA B c.dSlot) (s.gpr .esi + BitVec.ofNat 32 st)).writeW (slotA B c.nSlot)
        (s.gpr .ebp - 1) → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block (c.advance st)) s Q := by
  have := hL.room
  have hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega
  have hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega
  simp only [Core.advance, slotAt, at_]
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ z₂ => ?_
  have b₂ : s₂.gpr sb = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  refine wp_stm b₂ (by rw [u₂.wr, u₁.wr]; exact slot_inW hS hd) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.gpr]; exact b₂) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hn)
    fun s₄ u₄ => WP.block_nil ?_
  refine k s₄ (by rw [u₄.zf, u₃.zf, z₂, u₁.other _ (by decide)]) (fun r h1 h2 => by
      rw [u₄.gpr, u₃.gpr, u₂.other r h2, u₁.other r h1]) ?_ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide),
    addr_slotA hS.fit hd, addr_slotA hS.fit hn]

theorem Agree.trans {len : Loc → Nat} {a b c : Areas} (h₁ : Agree len a b) (h₂ : Agree len b c) :
    Agree len a c := fun l i hi => (h₁ l i hi).trans (h₂ l i hi)

theorem readW_write_sep {m : Mem} {a b : Addr} {v : BitVec 32} (h : Region.Disjoint ⟨a, 4⟩ ⟨b, 4⟩) :
    (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega)
    (by simp only [Region.Contains]; omega)) (by decide)

/-! ## The regions of a step -/

/-- The data of step `j`. -/
abbrev datRegion (D : BitVec 32) (st j : Nat) : Region := ⟨D.setWidth 64 + BitVec.ofNat 64 (st * j), st⟩

/-- The chaining value's slots. -/
abbrev chnRegion (c : Core) (B : BitVec 32) : Region := ⟨slotA B c.chnSlot, 4 * c.bw⟩

/-- The regions a step's operations and core change: the data of the step,
the core's slots, the chaining value, and the core's stack. -/
abbrev fine (c : Core) (B D : BitVec 32) (st j : Nat) (E : BitVec 32) : List Region :=
  [datRegion D st j, coreRegion c B, chnRegion c B, stkRegion E c.stack]

/-- The slots of the data pointer and the count. -/
abbrev dnSlots (c : Core) (B : BitVec 32) : List Region := [⟨slotA B c.dSlot, 4⟩, ⟨slotA B c.nSlot, 4⟩]

/-- The regions a run changes. -/
abbrev big (c : Core) (B D : BitVec 32) (n st : Nat) (E : BitVec 32) : List Region :=
  [coreRegion c B, dnRegion c B, dataRegion D st n, stkRegion E c.stack]

/-- What a step needs of the regions. -/
structure Regs (c : Core) (B D : BitVec 32) (n st j : Nat) (E : BitVec 32) : Prop where
  areasFine : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j E, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs, ∃ r' ∈ [dataRegion D st n, ⟨B.setWidth 64, 4 * c.total⟩],
    Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  slotsW : ∀ r ∈ dnSlots c B, ∃ r' ∈ [dataRegion D st n, ⟨B.setWidth 64, 4 * c.total⟩], Region.Sub r r'
  slotsCore : ∀ r ∈ dnSlots c B, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  dKeep : ∀ r ∈ fine c B D st j E, Region.Disjoint ⟨slotA B c.dSlot, 4⟩ r
  nKeep : ∀ r ∈ fine c B D st j E, Region.Disjoint ⟨slotA B c.nSlot, 4⟩ r
  dn : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ ⟨slotA B c.nSlot, 4⟩
  dChn : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ (chnRegion c B)
  nChn : Region.Disjoint ⟨slotA B c.nSlot, 4⟩ (chnRegion c B)
  chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B)
  chnStk : Region.Disjoint (chnRegion c B) (stkRegion E c.stack)
  datCore : Region.Disjoint (datRegion D st j) (coreRegion c B)
  datStk : Region.Disjoint (datRegion D st j) (stkRegion E c.stack)
  dataOut : ∀ r ∈ [coreRegion c B, chnRegion c B, stkRegion E c.stack, ⟨slotA B c.dSlot, 4⟩,
    ⟨slotA B c.nSlot, 4⟩], Region.Disjoint (dataRegion D st n) r
  datData : Region.Sub (datRegion D st j) (dataRegion D st n)
  toBig : ∀ r ∈ fine c B D st j E ++ dnSlots c B, ∃ r' ∈ big c B D n st E, Region.Sub r r'

/-- `omega`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot]); omega))

theorem regs {s₀ : State} {B D : BitVec 32} {n st j : Nat} (hF : Fixed c s₀ B D n st) (hj : j < n) :
    Regs c B D n st j (s₀.gpr .esp) := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hDf := hF.dataFit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  have subChn : Region.Sub (chnRegion c B) (dnRegion c B) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  have subBuf : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (coreRegion c B) := VG.Offset.sub_base _ (by slot_omega)
  have subBlk : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (blkRegion c B) :=
    Region.sub_prefix (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hbG)
  have subD4 : Region.Sub ⟨slotA B c.dSlot, 4⟩ (dnRegion c B) := Region.sub_prefix (by slot_omega)
  have subN4 : Region.Sub ⟨slotA B c.nSlot, 4⟩ (dnRegion c B) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  have dnScr : Region.Sub (dnRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ := VG.Offset.sub_base _ (by slot_omega)
  have coreScr : Region.Sub (coreRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ := Region.sub_prefix (by slot_omega)
  have dnCore : Region.Disjoint (dnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
  have datCore : Region.Disjoint (datRegion D st j) (coreRegion c B) :=
    (hF.dataScr.sub_left subDat).sub_right coreScr
  have stkDn : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) (dnRegion c B) :=
    hF.stkMode.sub_right (VG.Offset.sub _ (by slot_omega) (by slot_omega))
  have dataDn : Region.Disjoint (dataRegion D st n) (dnRegion c B) := hF.dataScr.sub_right dnScr
  have datStk : Region.Disjoint (datRegion D st j) (stkRegion (s₀.gpr .esp) c.stack) :=
    hF.stkData.symm.sub_left subDat
  have d4n4 : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ ⟨slotA B c.nSlot, 4⟩ :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  have d4chn : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ (chnRegion c B) :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  have n4chn : Region.Disjoint ⟨slotA B c.nSlot, 4⟩ (chnRegion c B) :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  have scrSub : ∀ {r : Region}, Region.Sub r (dnRegion c B) → Region.Sub r ⟨B.setWidth 64, 4 * c.total⟩ :=
    fun h x hx => dnScr x (h x hx)
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m3 : ∀ {a b c' d : Region} {l : List Region}, d ∈ a :: b :: c' :: d :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => ?_, d4n4, d4chn, n4chn, dnCore.sub_left subChn, stkDn.symm.sub_left subChn, datCore, datStk,
    fun r hr => ?_, subDat, fun r hr => ?_⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, subBuf⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subDat⟩
    · exact ⟨_, m1, scrSub subChn⟩
    · exact ⟨_, m1, fun x hx => coreScr x (subBuf x hx)⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl datCore.symm
    · exact .inl (dnCore.sub_left subChn).symm
    · exact .inr subBlk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, m1, scrSub subD4⟩
    · exact ⟨_, m1, scrSub subN4⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (dnCore.sub_left subD4).symm
    · exact .inl (dnCore.sub_left subN4).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dataDn.sub_left subDat).symm.sub_left subD4
    · exact dnCore.sub_left subD4
    · exact d4chn
    · exact stkDn.symm.sub_left subD4
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (dataDn.sub_left subDat).symm.sub_left subN4
    · exact dnCore.sub_left subN4
    · exact n4chn
    · exact stkDn.symm.sub_left subN4
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hF.dataScr.sub_right coreScr
    · exact dataDn.sub_right subChn
    · exact hF.stkData.symm
    · exact dataDn.sub_right subD4
    · exact dataDn.sub_right subN4
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, m2, subDat⟩
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m1, subChn⟩
    · exact ⟨_, m3, fun _ h => h⟩
    · exact ⟨_, m1, subD4⟩
    · exact ⟨_, m1, subN4⟩

/-! ## The stages of a step -/

/-- In the middle of a step from `s`: the areas agree with `a`, the key is
ready, and memory has changed only in `fine` since `s`. -/
structure Mid (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (st j : Nat) (k : cs.Key) (s : State) (a : Areas)
    (s' : State) : Prop where
  b : s'.gpr sb = B
  esp : s'.gpr .esp = s₀.gpr .esp
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B k
  agree : Agree (lens c st) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j (s₀.gpr .esp)) s.mem s'.mem

theorem toWr {s₀ t : State} {B D : BitVec 32} {n st : Nat} (hF : Fixed c s₀ B D n st) (hw : t.wr = s₀.wr)
    {rs : List Region} (h : ∀ r ∈ rs, ∃ r' ∈ [dataRegion D st n, ⟨B.setWidth 64, 4 * c.total⟩], Region.Sub r r') :
    ∀ r ∈ rs, ∃ r' ∈ t.wr, Region.Sub r r' := fun r hr => by
  obtain ⟨r', hr', hs⟩ := h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hw]
  rcases hr' with rfl | rfl
  · exact ⟨_, hF.dataW, hs⟩
  · exact ⟨_, hF.scr.wr, hs⟩

theorem pre_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs j s) :
    WP isa (.block (c.load ++ c.opsCode M.pre)) s
      (Mid cs s₀ B D st j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  have hR := regs hF hj
  refine load_wp hI.b ⟨by rw [hI.wr]; exact hF.scr.wr, hF.scr.fit⟩ hF.layout fun s₁ esi₁ _ g₁ m₁ rd₁ wr₁ => ?_
  rw [← List.append_nil (c.opsCode M.pre)]
  have b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide) (by decide)]; exact hI.b
  have hA : AreasOk c s₁ (lens c st) (areas c B D st j) allLocs :=
    areasOk hF hj b₁ (by rw [esi₁, hI.dp]) (by rw [wr₁, hI.wr])
  refine opsCode_wp c (fun o ho => ⟨hpre o ho, mem_allLocs _⟩) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => WP.block_nil ?_
  rw [m₁] at a₂ f₂
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hI.esp]
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact b₁, esp₂, by rw [rd₂, rd₁, hI.rd], by rw [wr₂, wr₁, hI.wr],
    cs.ready_frame hI.ready (by rw [esp₂, hI.esp]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) f₂
      (toWr hF hI.wr hR.areasW) hR.areasCore, a₂, f₂.sub hR.areasFine⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem blkAddr_zero (c : Core) (B : BitVec 32) : blkAddr c B 0 = slotA B c.buf := by
  simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]

theorem crypt_step (cs : CoreSpec c) {s₀ : State} {B D : BitVec 32} {n st : Nat} {k : cs.Key}
    (hF : Fixed c s₀ B D n st) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : Mid cs s₀ B D st j k s a s₂) :
    WP isa c.crypt s₂ (Mid cs s₀ B D st j k s (cryptBuf (4 * c.bw) (cs.cipher k) a)) := by
  have hR := regs hF hj
  have hst := hF.step
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready
    (by rw [hm.esp]; exact hF.stack)) fun s₃ ⟨b₃, esp₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  rw [hm.esp] at f₃
  refine ⟨b₃, by rw [esp₃, hm.esp], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf (4 * c.bw) (cs.cipher k) (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.datCore
      · exact hR.datStk) (by show st ≤ 2 ^ 64; have := hF.layout.bw; omega) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.chnCore
      · exact hR.chnStk) (by show 4 * c.bw ≤ 2 ^ 64; have := hF.layout.bw; omega) hi
  · simp only [lens] at hi
    have e := enc₃ 0 hF.layout.G_pos
    rw [blkAddr_zero] at e
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

theorem chunksAt_getElem {L : Nat} {m : Mem} {p : Addr} {n j : Nat} (hj : j < n) :
    (chunksAt L m p n)[j]'(by rw [chunksAt_length]; exact hj) = bytesAt m (p + BitVec.ofNat 64 (L * j)) L := by
  simp [chunksAt]

/-- Input step `j`, from the invariant. -/
theorem Inv.input {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {n st : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State} (hI : Inv cs s₀ B D n st k F c0 xs j s)
    (hxs : xs.length = n) (hj : j < n) :
    bytesAt s.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega) := by
  have hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega
  have e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

theorem post_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st) (hM : M.step = st)
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st)) (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s s₃ : State} (hI : Inv cs s₀ B D n st k F c0 xs j s)
    (hm : Mid cs s₀ B D st j k s (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.load ++ c.opsCode M.post ++ c.advance M.step)) s₃
      fun s' => Inv cs s₀ B D n st k F c0 xs (j + 1) s' ∧ s'.zf = some (decide (j + 1 = n)) := by
  have hR := regs hF hj
  have hL := hF.layout
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hst := hF.step
  have hDf := hF.dataFit
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hS : ∀ {t : State}, t.wr = s₀.wr → ScrIn t B c.total := fun h => ⟨by rw [h]; exact hF.scr.wr, hF.scr.fit⟩
  have dp₃ : s₃.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.dKeep (by decide), hI.dp]
  have np₃ : s₃.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (n - j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.nKeep (by decide), hI.np]
  rw [List.append_assoc]
  refine load_wp hm.b (hS hm.wr) hL fun s₄ esi₄ ebp₄ g₄ m₄ rd₄ wr₄ => ?_
  have b₄ : s₄.gpr sb = B := by rw [g₄ _ (by decide) (by decide)]; exact hm.b
  have hA : AreasOk c s₄ (lens c st) (areas c B D st j) allLocs :=
    areasOk hF hj b₄ (by rw [esi₄, dp₃]) (by rw [wr₄, hm.wr])
  refine opsCode_wp c (fun o ho => ⟨hpost o ho, mem_allLocs _⟩) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_
  rw [m₄] at a₅ f₅
  have b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide) (by decide)]; exact b₄
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, hm.wr]
  refine advance_wp b₅ (hS wr₅') hL M.step fun s₆ z₆ g₆ m₆ rd₆ wr₆ => ?_
  have esi₅ : s₅.gpr .esi = D + BitVec.ofNat 32 (st * j) := by rw [g₅ _ (by decide) (by decide), esi₄, dp₃]
  have ebp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (n - j) := by rw [g₅ _ (by decide) (by decide), ebp₄, np₃]
  rw [esi₅, ebp₅, hM] at m₆
  rw [ebp₅] at z₆
  -- The step's outputs.
  let A := areas c B D st j
  have hstep : Agree (lens c st) (cont A s₅.mem) (stepA M (4 * c.bw) (cs.cipher k) (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  have xj : rd (cont A s.mem) .dat st = xs[j]'(by omega) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  have out₅ : bytesAt s₅.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  have chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) = (F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  -- The stores of the data pointer and the count.
  have hd4 : (⟨slotA B c.dSlot, 4⟩ : Region).Contains (slotA B c.dSlot) (32 / 8) := Region.contains_self _ _
  have f₆ : Frame (dnSlots c B) s₅.mem s₆.mem := by
    rw [m₆]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ hd4).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _
      (Region.contains_self _ _)
  have all : Frame (fine c B D st j (s₀.gpr .esp) ++ dnSlots c B) s.mem s₆.mem :=
    ((hm.frame.mono fun r hr => List.mem_append_left _ hr).trans
      ((f₅.sub hR.areasFine).mono fun r hr => List.mem_append_left _ hr)).trans
      (f₆.mono fun r hr => List.mem_append_right _ hr)
  have keep6 : ∀ {R : Region}, (∀ r ∈ dnSlots c B, R.Disjoint r) → R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len →
      s₆.mem (R.base + BitVec.ofNat 64 i) = s₅.mem (R.base + BitVec.ofNat 64 i) := fun hd hl _ hi =>
    f₆.bytes hd hl hi
  have dDat : ∀ r ∈ dnSlots c B, Region.Disjoint (datRegion D st j) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
  have dChn : ∀ r ∈ dnSlots c B, Region.Disjoint (chnRegion c B) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hR.dChn.symm
    · exact hR.nChn.symm
  have out₆ : bytesAt s₆.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).1 := by
    rw [← out₅]
    exact List.map_congr_left fun i hi => keep6 dDat (by show st ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  have chn₆ : bytesAt s₆.mem (slotA B c.chnSlot) (4 * c.bw) = (F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).2 := by
    rw [← chn₅]
    exact List.map_congr_left fun i hi => keep6 dChn (by show 4 * c.bw ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  have hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++ [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, run_snoc]
  have gg : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆ r h1 h2, g₅ r h3 h4, g₄ r h1 h2]
  show Inv cs s₀ B D n st k F c0 xs (j + 1) s₆ ∧ s₆.zf = some (decide (j + 1 = n))
  refine ⟨⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.esp,
    by rw [rd₆, rd₅, rd₄, hm.rd], by rw [wr₆, wr₅'], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m₆, readW_write_sep hR.dn, Mem.readW_writeW_self32, VG.Offset.add_add, Nat.mul_succ]
  · rw [m₆, Mem.readW_writeW_self32, Wp.ofNat_pred (by omega)]
    congr 1
  · exact cs.ready_frame hm.ready (by rw [gg _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄])
      ((f₅.mono fun r hr => List.mem_append_left _ hr).trans (f₆.mono fun r hr => List.mem_append_right _ hr))
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact toWr hF hm.wr hR.areasW r h
        · exact toWr hF hm.wr hR.slotsW r h)
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact hR.areasCore r h
        · exact hR.slotsCore r h)
  · rw [chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₆, run_set F c0 (by omega)]
    refine all _ fun r hr hcon => ?_
    rcases List.mem_append.mp hr with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · simp only [Region.Contains] at hcon
        have e := (VG.Offset.lt_iff (D.setWidth 64 + BitVec.ofNat 64 i) (D.setWidth 64) (d := st * j) (n := st)
          (by omega)).mp (by omega)
        rw [sub_self_add _ (by omega)] at e
        omega
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega)) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega)) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega)) hcon
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega)) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega)) hcon
  · rw [chn₆, hrun]
  · exact hI.frame.trans (all.sub hR.toBig)
  · have : n ≤ 2 ^ 32 := Nat.le_trans (Nat.le_mul_of_pos_left n hst.1) (by omega)
    rw [z₆, Wp.ofNat_pred (by omega), Wp.ofNat_beq_zero (by omega)]
    congr 1; exact decide_eq_decide.mpr (by omega)

/-! ## The step and the loop -/

theorem body_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs j s) :
    WP isa (c.body M) s fun s' => Inv cs s₀ B D n st k F c0 xs (j + 1) s' ∧ s'.zf = some (decide (j + 1 = n)) := by
  unfold Core.body
  exact WP.seq (WP.mono (pre_wp cs hF hpre hj hI) fun _ h₂ =>
    WP.seq (WP.mono (crypt_step cs hF hj h₂) fun _ h₃ => post_wp cs hF hM hpost hcomp hxs hj hI h₃))

theorem loop_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs 0 s) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (c.body M) .ne)) s (Inv cs s₀ B D n st k F c0 xs n) := by
  by_cases hn : n = 0
  · subst hn
    exact WP.ite true (by show VG.X86.eval .e s = _; simp [VG.X86.eval, hz]) (fun _ => WP.block_nil hI)
      (fun h => by cases h)
  refine WP.ite false (by show VG.X86.eval .e s = _; simp [VG.X86.eval, hz, hn]) (fun h => by cases h)
    fun _ => ?_
  refine WP.loop (M := isa) (body := c.body M) (c := .ne) (Q := Inv cs s₀ B D n st k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st k F c0 xs j t)
    ?_ n s ⟨0, by omega, by omega, hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hM hpre hpost hcomp hxs hj h) fun t' ⟨h', hz'⟩ => ?_
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := by
    show VG.X86.eval .ne t' = _; simp [VG.X86.eval, hz']
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [ev]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [ev]; simp [he], n - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

end VG.Proof.Modes.X86
