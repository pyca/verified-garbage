module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Modes.X86.Core
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Modes.X86.Ops
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Modes.Ops
import VerifiedGarbage.Proof.AesCtr.Inc
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Modes.X86.Counter
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.TCB.Mem
public import Init.Data.BitVec.Basic
public import Init.Data.List.BasicAux
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target

/-! ### `Modes.X86.Step`, which only this module used -/

section

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

@[expose] public section

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
steps of `st` bytes (within a writable region, at `e` bytes from its base),
the stack the core uses below `esp`, and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : BitVec 32) (n st : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : ∃ (R : Addr) (e ℓ : Nat), (⟨R, ℓ⟩ : Region) ∈ s₀.wr ∧ D.setWidth 64 = R + BitVec.ofNat 64 e ∧
    e + st * n ≤ ℓ ∧ ℓ < 2 ^ 64
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

theorem rd_agree {len : Loc → Nat} {a a' : Areas} (h : Agree len a a') {l : Loc} {n : Nat} (hn : n ≤ len l) :
    rd a l n = rd a' l n :=
  List.map_congr_left fun i hi => h l i (by have := List.mem_range.mp hi; omega_using [hn, this])

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
  rw [addr_eq (by omega_using [hfit, h]), VG.Offset.add_add]

theorem slot_contains {B : BitVec 32} {total d n : Nat} (hfit : B.toNat + 4 * total ≤ 2 ^ 32)
    (h : d + n ≤ 4 * total) :
    (⟨B.setWidth 64, 4 * total⟩ : Region).Contains (B.setWidth 64 + BitVec.ofNat 64 d) n :=
  VG.Offset.contains_base _ h (by omega_using [hfit, h])

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
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hW : ∀ l off w, off + w ≤ lens c st l → InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      obtain ⟨R, e, ℓ, hR, hDR, heℓ, hℓ⟩ := hF.dataW
      refine ⟨_, hR, ?_⟩
      rw [VG.Offset.add_add, hDR, VG.Offset.add_add]
      exact VG.Offset.contains_base _ (by omega_using [hjn, ho, heℓ]) (by omega_using [hjn, ho, heℓ, hℓ])
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by simp only [Core.chnSlot]; omega_using [hroom, hbw, ho])
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by omega_using [hroom, hbuf, hbw, ho])
  refine ⟨fun l off ho => ?_, fun l off w ho => ?_, fun l _ off w ho => hW l off w ho, fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hesi, Nat.zero_add, addr, VG.Offset.add_add, ← addr, addr_eq (by omega_using [hD, hjn, ho]), VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by simp only [Core.chnSlot]; omega_using [hroom, hbw, ho])
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by omega_using [hroom, hbuf, hbw, ho])
  · obtain ⟨r, hr, hc⟩ := hW l off w ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 4 * c.total →
        Region.Disjoint ⟨D.setWidth 64 + BitVec.ofNat 64 (st * j), st⟩ ⟨B.setWidth 64 + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    obtain dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by simp only [Core.chnSlot]; omega_using [hbuf, hbw])) (by simp only [Core.chnSlot]; omega_using [hfit, hroom, hbw])
        (by omega_using [hfit, hroom, hbuf, hbw])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by simp only [Core.chnSlot]; omega_using [hroom, hbw])
    · exact dD _ _ (by omega_using [hroom, hbuf, hbw])
    · exact (dD _ _ (by simp only [Core.chnSlot]; omega_using [hroom, hbw])).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hbuf, hbw])).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw]

/-! ## The slots -/

theorem slot_in {s : State} {B : BitVec 32} {total k : Nat} (hS : ScrIn s B total) (hk : k < total) :
    InRegions (s.rd ++ s.wr) (addr B (4 * k)) 4 := by
  have := hS.fit
  refine ⟨_, List.mem_append_right _ hS.wr, ?_⟩
  rw [addr_eq (by omega_using [hk, this])]; exact slot_contains hS.fit (by omega_using [hk])

theorem slot_inW {s : State} {B : BitVec 32} {total k : Nat} (hS : ScrIn s B total) (hk : k < total) :
    InRegions s.wr (addr B (4 * k)) 4 := by
  have := hS.fit
  refine ⟨_, hS.wr, ?_⟩
  rw [addr_eq (by omega_using [hk, this])]; exact slot_contains hS.fit (by omega_using [hk])

theorem addr_slotA {B : BitVec 32} {total k : Nat} (hfit : B.toNat + 4 * total ≤ 2 ^ 32) (hk : k < total) :
    addr B (4 * k) = slotA B k := addr_eq (by omega_using [hfit, hk])

/-- The data pointer and the steps left to `esi` and `ebp`. -/
theorem load_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .esi = s.mem.readW (slotA B c.dSlot) 32 → s'.gpr .ebp = s.mem.readW (slotA B c.nSlot) 32 →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block is) s' Q) :
    WP isa (.block (c.load ++ is)) s Q := by
  have := hL.room
  obtain hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega_using [this]
  obtain hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega_using [this]
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
  obtain hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega_using [this]
  obtain hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega_using [this]
  simp only [Core.advance, slotAt, at_]
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ z₂ => ?_
  obtain b₂ : s₂.gpr sb = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
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
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

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

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot]); omega_arith))

theorem regs {s₀ : State} {B D : BitVec 32} {n st j : Nat} (hF : Fixed c s₀ B D n st) (hj : j < n) :
    Regs c B D n st j (s₀.gpr .esp) := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hDf := hF.dataFit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  obtain subChn : Region.Sub (chnRegion c B) (dnRegion c B) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  obtain subBuf : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (coreRegion c B) := VG.Offset.sub_base _ (by slot_omega)
  obtain subBlk : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (blkRegion c B) :=
    Region.sub_prefix (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hbG)
  obtain subD4 : Region.Sub ⟨slotA B c.dSlot, 4⟩ (dnRegion c B) := Region.sub_prefix (by slot_omega)
  obtain subN4 : Region.Sub ⟨slotA B c.nSlot, 4⟩ (dnRegion c B) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  obtain dnScr : Region.Sub (dnRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ := VG.Offset.sub_base _ (by slot_omega)
  obtain coreScr : Region.Sub (coreRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ := Region.sub_prefix (by slot_omega)
  obtain dnCore : Region.Disjoint (dnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
  obtain datCore : Region.Disjoint (datRegion D st j) (coreRegion c B) :=
    (hF.dataScr.sub_left subDat).sub_right coreScr
  obtain stkDn : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) (dnRegion c B) :=
    hF.stkMode.sub_right (VG.Offset.sub _ (by slot_omega) (by slot_omega))
  obtain dataDn : Region.Disjoint (dataRegion D st n) (dnRegion c B) := hF.dataScr.sub_right dnScr
  obtain datStk : Region.Disjoint (datRegion D st j) (stkRegion (s₀.gpr .esp) c.stack) :=
    hF.stkData.symm.sub_left subDat
  obtain d4n4 : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ ⟨slotA B c.nSlot, 4⟩ :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  obtain d4chn : Region.Disjoint ⟨slotA B c.dSlot, 4⟩ (chnRegion c B) :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  obtain n4chn : Region.Disjoint ⟨slotA B c.nSlot, 4⟩ (chnRegion c B) :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  obtain scrSub : ∀ {r : Region}, Region.Sub r (dnRegion c B) → Region.Sub r ⟨B.setWidth 64, 4 * c.total⟩ :=
    fun h x hx => dnScr x (h x hx)
  obtain m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  obtain m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain m3 : ∀ {a b c' d : Region} {l : List Region}, d ∈ a :: b :: c' :: d :: l :=
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
  · obtain ⟨R, e, ℓ, hR, hDR, heℓ, -⟩ := hF.dataW
    refine ⟨_, hR, fun a ha => ?_⟩
    have := VG.Offset.sub_base R (n := st * n) heℓ
    rw [← hDR] at this
    exact this a (hs a ha)
  · exact ⟨_, hF.scr.wr, hs⟩

theorem pre_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs j s) :
    WP isa (.block (c.load ++ c.opsCode M.pre)) s
      (Mid cs s₀ B D st j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  obtain hR := regs hF hj
  refine WP.syms_intro ?_
  refine load_wp hI.b ⟨by rw [hI.wr]; exact hF.scr.wr, hF.scr.fit⟩ hF.layout fun s₁ esi₁ _ g₁ m₁ rd₁ wr₁ => ?_
  rw [← List.append_nil (c.opsCode M.pre)]
  obtain b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide) (by decide)]; exact hI.b
  obtain hA : AreasOk c s₁ (lens c st) (areas c B D st j) allLocs :=
    areasOk hF hj b₁ (by rw [esi₁, hI.dp]) (by rw [wr₁, hI.wr])
  refine opsCode_wp c (fun o ho => ⟨hpre o ho, mem_allLocs _⟩) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => WP.block_nil fun sy₂ => ?_
  rw [m₁] at a₂ f₂
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hI.esp]
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact b₁, esp₂, by rw [rd₂, rd₁, hI.rd], by rw [wr₂, wr₁, hI.wr],
    cs.ready_frame hI.ready (by rw [esp₂, hI.esp]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) sy₂ f₂
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
  obtain hR := regs hF hj
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
      · exact hR.datStk) (by show st ≤ 2 ^ 64; have := hF.layout.bw; omega_using [hst, this]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.chnCore
      · exact hR.chnStk) (by show 4 * c.bw ≤ 2 ^ 64; have := hF.layout.bw; omega_using [this]) hi
  · simp only [lens] at hi
    obtain e := enc₃ 0 hF.layout.G_pos
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
    bytesAt s.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega_using [hxs, hj]) := by
  obtain hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  obtain e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
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
  obtain hR := regs hF hj
  have hL := hF.layout
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hst := hF.step
  have hDf := hF.dataFit
  obtain hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hS : ∀ {t : State}, t.wr = s₀.wr → ScrIn t B c.total := fun h => ⟨by rw [h]; exact hF.scr.wr, hF.scr.fit⟩
  obtain dp₃ : s₃.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.dKeep (by decide), hI.dp]
  obtain np₃ : s₃.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (n - j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.nKeep (by decide), hI.np]
  rw [List.append_assoc]
  refine WP.syms_intro ?_
  refine load_wp hm.b (hS hm.wr) hL fun s₄ esi₄ ebp₄ g₄ m₄ rd₄ wr₄ => ?_
  obtain b₄ : s₄.gpr sb = B := by rw [g₄ _ (by decide) (by decide)]; exact hm.b
  obtain hA : AreasOk c s₄ (lens c st) (areas c B D st j) allLocs :=
    areasOk hF hj b₄ (by rw [esi₄, dp₃]) (by rw [wr₄, hm.wr])
  refine opsCode_wp c (fun o ho => ⟨hpost o ho, mem_allLocs _⟩) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_
  rw [m₄] at a₅ f₅
  obtain b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide) (by decide)]; exact b₄
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, hm.wr]
  refine advance_wp b₅ (hS wr₅') hL M.step fun s₆ z₆ g₆ m₆ rd₆ wr₆ => ?_
  intro sy₆
  obtain esi₅ : s₅.gpr .esi = D + BitVec.ofNat 32 (st * j) := by rw [g₅ _ (by decide) (by decide), esi₄, dp₃]
  obtain ebp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (n - j) := by rw [g₅ _ (by decide) (by decide), ebp₄, np₃]
  rw [esi₅, ebp₅, hM] at m₆
  rw [ebp₅] at z₆
  -- The step's outputs.
  let A := areas c B D st j
  obtain hstep : Agree (lens c st) (cont A s₅.mem) (stepA M (4 * c.bw) (cs.cipher k) (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  obtain xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  obtain out₅ : bytesAt s₅.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  obtain chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) = (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  -- The stores of the data pointer and the count.
  obtain hd4 : (⟨slotA B c.dSlot, 4⟩ : Region).Contains (slotA B c.dSlot) (32 / 8) := Region.contains_self _ _
  obtain f₆ : Frame (dnSlots c B) s₅.mem s₆.mem := by
    rw [m₆]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ hd4).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _
      (Region.contains_self _ _)
  obtain all : Frame (fine c B D st j (s₀.gpr .esp) ++ dnSlots c B) s.mem s₆.mem :=
    ((hm.frame.mono fun r hr => List.mem_append_left _ hr).trans
      ((f₅.sub hR.areasFine).mono fun r hr => List.mem_append_left _ hr)).trans
      (f₆.mono fun r hr => List.mem_append_right _ hr)
  obtain keep6 : ∀ {R : Region}, (∀ r ∈ dnSlots c B, R.Disjoint r) → R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len →
      s₆.mem (R.base + BitVec.ofNat 64 i) = s₅.mem (R.base + BitVec.ofNat 64 i) := fun hd hl _ hi =>
    f₆.bytes hd hl hi
  obtain dDat : ∀ r ∈ dnSlots c B, Region.Disjoint (datRegion D st j) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
    · exact (hR.dataOut _ (by simp)).sub_left hR.datData
  obtain dChn : ∀ r ∈ dnSlots c B, Region.Disjoint (chnRegion c B) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hR.dChn.symm
    · exact hR.nChn.symm
  obtain out₆ : bytesAt s₆.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← out₅]
    exact List.map_congr_left fun i hi => keep6 dDat (by show st ≤ 2 ^ 64; omega_using [hDf, hjn]) (List.mem_range.mp hi)
  obtain chn₆ : bytesAt s₆.mem (slotA B c.chnSlot) (4 * c.bw) = (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← chn₅]
    exact List.map_congr_left fun i hi => keep6 dChn (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) (List.mem_range.mp hi)
  obtain hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++ [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  obtain gg : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆ r h1 h2, g₅ r h3 h4, g₄ r h1 h2]
  show Inv cs s₀ B D n st k F c0 xs (j + 1) s₆ ∧ s₆.zf = some (decide (j + 1 = n))
  refine ⟨⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.esp,
    by rw [rd₆, rd₅, rd₄, hm.rd], by rw [wr₆, wr₅'], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m₆, readW_write_sep hR.dn, Mem.readW_writeW_self32, VG.Offset.add_add, Nat.mul_succ]
  · rw [m₆, Mem.readW_writeW_self32, Wp.ofNat_pred (by omega_using [hj])]
    congr 1
  · exact cs.ready_frame hm.ready (by rw [gg _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) sy₆
      ((f₅.mono fun r hr => List.mem_append_left _ hr).trans (f₆.mono fun r hr => List.mem_append_right _ hr))
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact toWr hF hm.wr hR.areasW r h
        · exact toWr hF hm.wr hR.slotsW r h)
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact hR.areasCore r h
        · exact hR.slotsCore r h)
  · rw [chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₆, run_set F c0 (by omega_using [hxs, hj])]
    refine all _ fun r hr hcon => ?_
    rcases List.mem_append.mp hr with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · simp only [Region.Contains] at hcon
        obtain e := (VG.Offset.lt_iff (D.setWidth 64 + BitVec.ofNat 64 i) (D.setWidth 64) (d := st * j) (n := st)
          (by omega_using [hDf, hjn])).mp (by omega_using [hcon])
        rw [sub_self_add _ (by omega_using [hDf, hi])] at e
        omega_using [hout, e]
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf])) hcon
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf])) hcon
      · exact hR.dataOut _ (by simp) _ (contains_area hi (by omega_using [hDf])) hcon
  · rw [chn₆, hrun]
  · exact hI.frame.trans (all.sub hR.toBig)
  · have : n ≤ 2 ^ 32 := Nat.le_trans (Nat.le_mul_of_pos_left n hst.1) (by omega_using [hDf])
    rw [z₆, Wp.ofNat_pred (by omega_using [hj]), Wp.ofNat_beq_zero (by omega_using [this])]
    congr 1; exact decide_eq_decide.mpr (by omega_using [hj])

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
    ?_ n s ⟨0, by omega_using [], by omega_using [hn], hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hM hpre hpost hcomp hxs hj h) fun t' ⟨h', hz'⟩ => ?_
  obtain ev : isa.eval .ne t' = some !decide (j + 1 = n) := by
    show VG.X86.eval .ne t' = _; simp [VG.X86.eval, hz']
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [ev]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [ev]; simp [he], n - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], h'⟩

end VG.Proof.Modes.X86

end

end


/-!
# A mode on x86 (32-bit), for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments
on the stack (`f(key, iv, data, n, scratch)`, the key `c.ka` arguments), replaces the `n` steps of
data at `data` with the outputs of `F` from the IV, and (if `M.ivOut`) the
IV with the last chaining value; it keeps the callee-saved registers and
the return address. Each mode's and cipher's contract follows from it.
-/

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev P (c : Core) : BitVec 32 := arg s₀ c.ka
abbrev Dp (c : Core) : BitVec 32 := arg s₀ (c.ka + 1)
abbrev N (c : Core) : Nat := (arg s₀ (c.ka + 2)).toNat
abbrev S (c : Core) : BitVec 32 := arg s₀ (c.ka + 3)

abbrev argsR (c : Core) : Region := ⟨argAddr s₀ 0, 4 * (c.ka + 4)⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
abbrev ivR (c : Core) : Region := ⟨(P s₀ c).setWidth 64, 4 * c.bw⟩
abbrev scrR (c : Core) : Region := ⟨(S s₀ c).setWidth 64, 4 * c.total⟩

end

/-- What the function needs on entry: the arguments readable, the IV
readable (and writable, apart from the data and the return address, if the
mode writes it back), the data and the scratch buffer writable, none wrapping
around, and apart from each other, the arguments, the return address and the
core's stack. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  args : argsR s₀ c ∈ s₀.rd ++ s₀.wr
  espFit : (s₀.gpr .esp).toNat + 4 * (c.ka + 5) ≤ 2 ^ 32
  scr : ScrIn s₀ (S s₀ c) c.total
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀ c).toNat + 4 * c.bw ≤ 2 ^ 32
  dataW : dataRegion (Dp s₀ c) M.step (N s₀ c) ∈ s₀.wr
  dataFit : (Dp s₀ c).toNat + M.step * N s₀ c ≤ 2 ^ 32
  dataScr : Region.Disjoint (dataRegion (Dp s₀ c) M.step (N s₀ c)) (scrR s₀ c)
  ivScr : Region.Disjoint (ivR s₀ c) (scrR s₀ c)
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀ c) M.step (N s₀ c))
  argsScr : Region.Disjoint (argsR s₀ c) (scrR s₀ c)
  argsData : Region.Disjoint (argsR s₀ c) (dataRegion (Dp s₀ c) M.step (N s₀ c))
  retScr : Region.Disjoint (retR s₀) (scrR s₀ c)
  retData : Region.Disjoint (retR s₀) (dataRegion (Dp s₀ c) M.step (N s₀ c))
  retIv : M.ivOut = true → Region.Disjoint (retR s₀) (ivR s₀ c)
  stkData : Region.Disjoint (stkRegion (E s₀) c.stack) (dataRegion (Dp s₀ c) M.step (N s₀ c))
  stkMode : Region.Disjoint (stkRegion (E s₀) c.stack) ⟨slotA (S s₀ c) c.slots, 40⟩
  stkArgs : Region.Disjoint (stkRegion (E s₀) c.stack) (argsR s₀ c)
  stkRet : Region.Disjoint (stkRegion (E s₀) c.stack) (retR s₀)
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-! ## The arguments -/

theorem argAddr_eq (s₀ : State) {n : Nat} (hfit : (s₀.gpr .esp).toNat + 4 * (n + 1) ≤ 2 ^ 32) {i : Nat} (hi : i < n) :
    argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega_arith), addr_eq (by omega_arith), VG.Offset.add_add]

theorem arg_contains (s₀ : State) (hfit : (s₀.gpr .esp).toNat + 4 * (c.ka + 5) ≤ 2 ^ 32) {i : Nat}
    (hi : i < c.ka + 4) : (argsR s₀ c).Contains (argAddr s₀ i) 4 := by
  rw [argAddr_eq s₀ (n := c.ka + 4) hfit hi]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- `mov r, [esp + 4 + 4 i]`: argument `i`, while the arguments are unchanged. -/
theorem wp_arg {s₀ s : State} (hp : SeqPre c M s₀) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) (hm : ∀ i < c.ka + 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) {d : Reg}
    {i : Nat} (hi : i < c.ka + 4) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (argOp i)) :: is)) s Q := by
  obtain e : addr (s.gpr .esp) (4 + 4 * i) = argAddr s₀ i := by rw [hesp]; rfl
  refine wp_ldm (B := s.gpr .esp) rfl (by rw [e, hrw]; exact ⟨_, hp.args, arg_contains s₀ hp.espFit hi⟩) fun s' u => ?_
  rw [e, hm i hi] at u
  exact k s' u

/-! ## The entry -/

/-- The mode's slots. -/
abbrev modeR (c : Core) (B : BitVec 32) : Region := ⟨slotA B c.slots, 40⟩

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot, Core.savedSlot]); omega_arith))

theorem range4_map {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : BitVec 32) : Loc → Addr
  | .dat => P.setWidth 64
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

theorem ivAreasOk {s₀ s : State} (hp : SeqPre c M s₀) (hb : s.gpr sb = S s₀ c) (hesi : s.gpr .esi = P s₀ c)
    (hrw : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s₀.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀ c) (S s₀ c)) ws := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  have hP := hp.ivFit
  obtain inScr : ∀ d w, d + w ≤ 4 * c.total → InRegions s.wr ((S s₀ c).setWidth 64 + BitVec.ofNat 64 d) w :=
    fun d w h => ⟨_, by rw [hw]; exact hp.scr.wr, slot_contains hfit h⟩
  refine ⟨fun l off ho => ?_, fun l off w ho => ?_, fun l hl off w ho => ?_, fun l l' hne => ?_, fun _ => by omega_arith⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hesi, Nat.zero_add, addr_eq (by omega_arith)]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb]; exact addr_slot hfit (by slot_omega)
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb]; exact addr_slot hfit (by omega_arith)
  · rw [hrw, hw]
    cases l
    · exact ⟨_, hp.ivRd, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (4 * c.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ (by rw [← hw]; exact hr), ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (4 * c.buf + off) w (by omega_arith)
      refine ⟨r, List.mem_append_right _ (by rw [← hw]; exact hr), ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · cases l
    · rw [hw]; exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega_arith)
  · have dIv : ∀ d, d + 4 * c.bw ≤ 4 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨(S s₀ c).setWidth 64 + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    obtain dCB : Region.Disjoint ⟨slotA (S s₀ c) c.chnSlot, 4 * c.bw⟩ ⟨slotA (S s₀ c) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_arith)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by slot_omega)
    · exact dIv _ (by omega_arith)
    · exact (dIv _ (by slot_omega)).symm
    · exact dCB
    · exact (dIv _ (by omega_arith)).symm
    · exact dCB.symm

/-- After the entry: the scratch buffer at `sb`, the callee-saved registers in
their slots, the IV in the chaining value's. -/
structure Entered (c : Core) (s₀ s : State) : Prop where
  b : s.gpr sb = S s₀ c
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  chn : bytesAt s.mem (slotA (S s₀ c) c.chnSlot) (4 * c.bw) = bytesAt s₀.mem ((P s₀ c).setWidth 64) (4 * c.bw)
  frame : Frame [modeR c (S s₀ c)] s₀.mem s.mem

theorem entry_wp {s₀ : State} (hp : SeqPre c M s₀) :
    WP isa (.block (c.entry ++ c.ivIn)) s₀ (Entered c s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  obtain slotW : ∀ k, k < c.total → InRegions s₀.wr (addr (S s₀ c) (4 * k)) 4 := fun k hk =>
    ⟨_, hp.scr.wr, by rw [addr_eq (by omega_arith)]; exact slot_contains hfit (by omega_arith)⟩
  obtain inMode : ∀ i < 4, (modeR c (S s₀ c)).Contains (slotA (S s₀ c) (c.savedSlot i)) (32 / 8) := fun i hi =>
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain sep : ∀ i < 4, ∀ j < 4, i ≠ j →
      Region.Disjoint ⟨slotA (S s₀ c) (c.savedSlot i), 4⟩ ⟨slotA (S s₀ c) (c.savedSlot j), 4⟩ := fun i hi j hj hij =>
    VG.Offset.disjoint _ (by slot_omega) (by slot_omega) (by slot_omega)
  obtain aS : ∀ i < 4, addr (S s₀ c) (4 * c.savedSlot i) = slotA (S s₀ c) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.entry, Core.ivIn, range4_map, List.cons_append,
    List.nil_append, at_]
  refine wp_arg hp rfl rfl (fun _ _ => rfl) (by omega_arith) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .eax = (S s₀ c) := u₁.gpr
  refine wp_stm b₁ (by rw [u₁.wr]; exact slotW _ (by slot_omega)) fun s₂ u₂ => ?_
  refine wp_stm (B := S s₀ c) (by rw [u₂.gpr]; exact b₁) (by rw [u₂.wr, u₁.wr]; exact slotW _ (by slot_omega))
    fun s₃ u₃ => ?_
  refine wp_stm (B := S s₀ c) (by rw [u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₄ u₄ => ?_
  refine wp_stm (B := S s₀ c) (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  obtain g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  obtain vals : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  obtain m₅ : s₅.mem = (((s₀.mem.writeW (slotA (S s₀ c) (c.savedSlot 0)) (s₀.gpr .ebx)).writeW (slotA (S s₀ c) (c.savedSlot 1))
      (s₀.gpr .esi)).writeW (slotA (S s₀ c) (c.savedSlot 2)) (s₀.gpr .edi)).writeW (slotA (S s₀ c) (c.savedSlot 3))
      (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, aS 0 (by decide), aS 1 (by decide),
      aS 2 (by decide), aS 3 (by decide)]
    simp only [Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ]
    rw [vals _ (by decide), vals _ (by decide), vals _ (by decide), vals _ (by decide)]
  obtain f₅ : Frame [modeR c (S s₀ c)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (inMode 0 (by decide))).writeW List.mem_cons_self _
      (inMode 1 (by decide))).writeW List.mem_cons_self _ (inMode 2 (by decide))).writeW List.mem_cons_self _
      (inMode 3 (by decide))
  obtain sv₅ : ∀ i < 4, s₅.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) := by
    intro i hi
    rw [m₅]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [readW_write_sep (sep 0 (by decide) 3 (by decide) (by decide)),
        readW_write_sep (sep 0 (by decide) 2 (by decide) (by decide)),
        readW_write_sep (sep 0 (by decide) 1 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [readW_write_sep (sep 1 (by decide) 3 (by decide) (by decide)),
        readW_write_sep (sep 1 (by decide) 2 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [readW_write_sep (sep 2 (by decide) 3 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [Mem.readW_writeW_self32]; rfl
  obtain argsK : ∀ i < c.ka + 4, s₆.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [u₆.mem]
    exact f₅.readW (arg_contains s₀ hp.espFit hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.argsScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by decide)
  obtain esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [u₆.other _ (by decide), g₅, vals _ (by decide)]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_arg hp esp₆ (by rw [rd₆, wr₆]) argsK (by omega_arith) fun s₇ u₇ => ?_
  obtain b₇ : s₇.gpr sb = (S s₀ c) := by rw [u₇.other _ (by decide), u₆.gpr, g₅]; exact b₁
  rw [← List.append_nil (c.opsCode _)]
  refine opsCode_wp c (ws := [.chn]) (fun o ho => ?_) (ivAreasOk hp b₇ u₇.gpr (by rw [u₇.rd, rd₆])
    (by rw [u₇.wr, wr₆]) (fun l hl e => by simp at hl; subst hl; cases e)) fun s₈ a₈ f₈ g₈ rd₈ wr₈ => ?_
  · simp only [copyBlk, List.mem_map, List.mem_range] at ho
    obtain ⟨w, hw, rfl⟩ := ho
    exact ⟨⟨by simp [Op.width]; omega_arith, by simp [Op.width]; omega_arith, fun _ _ h => by cases h⟩, List.mem_singleton_self _⟩
  refine WP.block_nil ⟨by rw [g₈ _ (by decide) (by decide)]; exact b₇,
    by rw [g₈ _ (by decide) (by decide), u₇.other _ (by decide), esp₆], by rw [rd₈, u₇.rd, rd₆],
    by rw [wr₈, u₇.wr, wr₆], fun i hi => ?_, ?_, ?_⟩
  · rw [← sv₅ i hi, ← u₆.mem, ← u₇.mem]
    exact f₈.readW (Region.contains_self _ _) (fun r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    obtain hi := List.mem_range.mp hi
    obtain e := a₈ .chn i hi
    simp only [cont, ivAreas] at e
    rw [e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, u₇.mem, u₆.mem]
    exact f₅.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi
  · refine f₅.trans ?_
    rw [← u₆.mem, ← u₇.mem]
    refine f₈.sub fun r hr => ?_
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ t : State} (hp : SeqPre c M s₀) (hb : t.gpr sb = S s₀ c)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (hsv : ∀ i < 4, t.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, r ≠ .esp → t'.gpr r = s₀.gpr r) → t'.gpr .esp = t.gpr .esp → t'.mem = t.mem →
      Q t') :
    WP isa (.block c.restore) t Q := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  obtain slotR : ∀ i < 4, InRegions (t.rd ++ t.wr) (addr (S s₀ c) (4 * c.savedSlot i)) 4 := fun i hi =>
    ⟨_, by rw [hrw]; exact List.mem_append_right _ hp.scr.wr, by
      rw [addr_eq (by slot_omega)]; exact slot_contains hfit (by slot_omega)⟩
  obtain aS : ∀ i < 4, addr (S s₀ c) (4 * c.savedSlot i) = slotA (S s₀ c) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.restore, slotAt, at_]
  refine wp_ldm hb (slotR 0 (by decide)) fun t₁ u₁ => ?_
  refine wp_ldm (B := S s₀ c) (by rw [u₁.other _ (by decide)]; exact hb) (by rw [u₁.rd, u₁.wr]; exact slotR 1 (by decide))
    fun t₂ u₂ => ?_
  refine wp_ldm (B := S s₀ c) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_ldm (B := S s₀ c) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 2 (by decide)) fun t₄ u₄ => WP.block_nil ?_
  obtain mm : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine k t₄ (fun r hr hne => ?_) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₄.mem, mm])
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, aS 0 (by decide),
      hsv 0 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, aS 1 (by decide), hsv 1 (by decide)]; rfl
  · rw [show sb = .edi from rfl] at u₄
    rw [u₄.gpr, mm, aS 2 (by decide), hsv 2 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, aS 3 (by decide), hsv 3 (by decide)]; rfl
  · exact absurd rfl hne

/-! ## The setup -/

theorem chunksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : BitVec 32} {st n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (dataRegion D st n) r) (hn : st * n ≤ 2 ^ 64) :
    chunksAt st m' (D.setWidth 64) n = chunksAt st m (D.setWidth 64) n := by
  refine List.map_congr_left fun j hj => List.map_congr_left fun u hu => ?_
  obtain hj := List.mem_range.mp hj
  obtain hu := List.mem_range.mp hu
  have : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  rw [VG.Offset.add_add]
  exact hf.bytes (R := dataRegion D st n) hd hn (by show st * j + u < st * n; omega_arith)

/-- The inputs: the data's steps and the IV, on entry. -/
abbrev xs0 (c : Core) (M : Mode) (s₀ : State) : List (List Byte) := chunksAt M.step s₀.mem ((Dp s₀ c).setWidth 64) (N s₀ c)
abbrev iv0 (c : Core) (s₀ : State) : List Byte := bytesAt s₀.mem ((P s₀ c).setWidth 64) (4 * c.bw)

/-- After the setup, at the loop. -/
structure SetUp (cs : CoreSpec c) (M : Mode) (F : StepFn) (k : cs.Key) (s₀ s : State) : Prop where
  fixed : Fixed c s (S s₀ c) (Dp s₀ c) (N s₀ c) M.step
  inv : Inv cs s (S s₀ c) (Dp s₀ c) (N s₀ c) M.step k F (iv0 c s₀) (xs0 c M s₀) 0 s
  zf : s.zf = some (decide (N s₀ c = 0))
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  frame : Frame [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] s₀.mem s.mem

theorem setup_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (.seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare (.block c.args))) s₀ (SetUp cs M F k s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  obtain modeScr : Region.Sub (modeR c (S s₀ c)) (scrR s₀ c) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (S s₀ c)) (scrR s₀ c) := Region.sub_prefix (by omega_arith)
  refine WP.seq (WP.mono_syms (entry_wp hp) fun s₁ h₁ sy₁ => ?_)
  obtain hS₁ : ScrIn s₁ (S s₀ c) c.total := ⟨by rw [h₁.wr]; exact hp.scr.wr, hfit⟩
  refine WP.seq (WP.mono (cs.prepare_wp h₁.b hS₁ List.mem_cons_self
    (cs.keyArgs_congr hk h₁.esp h₁.rd h₁.wr sy₁ (h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, modeScr⟩))
    (by rw [h₁.esp]; exact hp.stack)) fun s₂ ⟨ready₂, b₂, esp₂, f₂, rd₂, wr₂⟩ => ?_)
  refine WP.syms_intro ?_
  rw [h₁.esp] at f₂
  obtain esp₂' : s₂.gpr .esp = s₀.gpr .esp := by rw [esp₂, h₁.esp]
  obtain f₀₂ : Frame [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  obtain argsOut : ∀ r ∈ [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack], Region.Disjoint (argsR s₀ c) r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.argsScr.sub_right modeScr
      · exact hp.argsScr.sub_right coreScr
      · exact hp.stkArgs.symm
  obtain argsK : ∀ {m : Mem}, Frame [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] s₀.mem m →
      ∀ i < c.ka + 4, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun h i hi =>
    h.readW (arg_contains s₀ hp.espFit hi) argsOut (by decide)
  obtain hd : c.dSlot < c.total := by slot_omega
  obtain hn : c.nSlot < c.total := by slot_omega
  obtain dIn : (modeR c (S s₀ c)).Contains (slotA (S s₀ c) c.dSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain nIn : (modeR c (S s₀ c)).Contains (slotA (S s₀ c) c.nSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega_arith)
  obtain rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, h₁.rd, h₁.wr]
  obtain hS₂ : ScrIn s₂ (S s₀ c) c.total := ⟨by rw [wr₂]; exact hS₁.wr, hfit⟩
  simp only [Core.args, slotAt, at_]
  refine wp_arg hp esp₂' rw₂ (argsK f₀₂) (by omega_arith) fun s₃ u₃ => ?_
  refine wp_stm (B := S s₀ c) (by rw [u₃.other _ (by decide)]; exact b₂)
    (by rw [u₃.wr]; exact slot_inW hS₂ hd) fun s₄ u₄ => ?_
  obtain m₄ : s₄.mem = s₂.mem.writeW (slotA (S s₀ c) c.dSlot) (arg s₀ (c.ka + 1)) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, addr_slotA hfit hd]
  obtain f₀₄ : Frame [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₄.mem := by
    rw [m₄]; exact f₀₂.writeW List.mem_cons_self _ dIn
  refine wp_arg hp (by rw [u₄.gpr, u₃.other _ (by decide), esp₂']) (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂])
    (argsK f₀₄) (by omega_arith) fun s₅ u₅ => ?_
  refine wp_stm (B := S s₀ c) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact b₂)
    (by rw [u₅.wr, u₄.wr, u₃.wr]; exact slot_inW hS₂ hn) fun s₆ u₆ => ?_
  refine wp_test fun s₇ f₇ z₇ => WP.block_nil fun sy₇ => ?_
  obtain m₇ : s₇.mem = (s₂.mem.writeW (slotA (S s₀ c) c.dSlot) (arg s₀ (c.ka + 1))).writeW (slotA (S s₀ c) c.nSlot) (arg s₀ (c.ka + 2)) := by
    rw [f₇.mem, u₆.mem, u₅.mem, u₅.gpr, addr_slotA hfit hn, m₄]
  obtain g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₂.gpr r := fun r h => by
    rw [f₇.gpr, u₆.gpr, u₅.other r h, u₄.gpr, u₃.other r h]
  obtain eax₇ : s₇.gpr .eax = arg s₀ (c.ka + 2) := by rw [f₇.gpr, u₆.gpr, u₅.gpr]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, h₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, h₁.wr]
  obtain esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [g₇ _ (by decide), esp₂']
  obtain b₇ : s₇.gpr sb = S s₀ c := by rw [g₇ _ (by decide)]; exact b₂
  obtain fdn : Frame (dnSlots c (S s₀ c)) s₂.mem s₇.mem := by
    rw [m₇]
    obtain h1 : (⟨slotA (S s₀ c) c.dSlot, 4⟩ : Region).Contains (slotA (S s₀ c) c.dSlot) (32 / 8) :=
      Region.contains_self _ _
    obtain h2 : (⟨slotA (S s₀ c) c.nSlot, 4⟩ : Region).Contains (slotA (S s₀ c) c.nSlot) (32 / 8) :=
      Region.contains_self _ _
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ h1).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ h2
  obtain f₀₇ : Frame [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] s₀.mem s₇.mem := by
    rw [m₇]; exact f₀₄.writeW List.mem_cons_self _ nIn |> fun h => by rw [← m₄]; exact h
  obtain hF : Fixed c s₇ (S s₀ c) (Dp s₀ c) (N s₀ c) M.step :=
    ⟨⟨by rw [wr₇]; exact hp.scr.wr, hfit⟩, ⟨_, 0, _, by rw [wr₇]; exact hp.dataW, (BitVec.add_zero _).symm,
      by omega_arith, by have := hp.dataFit; omega_arith⟩, hp.dataFit, hp.dataScr,
      by rw [esp₇]; exact hp.stkData, by rw [esp₇]; exact hp.stkMode, by rw [esp₇]; exact hp.stack, hp.step, hL⟩
  obtain sChn : Region.Sub (chnRegion c (S s₀ c)) (modeR c (S s₀ c)) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  obtain dn : Region.Disjoint ⟨slotA (S s₀ c) c.dSlot, 4⟩ ⟨slotA (S s₀ c) c.nSlot, 4⟩ :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  obtain dnOut : ∀ r ∈ dnSlots c (S s₀ c), Region.Disjoint (coreRegion c (S s₀ c)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
  -- A slot of the mode outside the slots of the data pointer and the count.
  obtain keepSlot : ∀ {R : Region}, Region.Sub R (modeR c (S s₀ c)) → (∀ r ∈ dnSlots c (S s₀ c), R.Disjoint r) →
      R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len → s₇.mem (R.base + BitVec.ofNat 64 i) = s₁.mem (R.base + BitVec.ofNat 64 i) :=
    fun hsub hd hl _ hi => by
      rw [fdn.bytes hd hl hi]
      refine f₂.bytes (fun r hr => ?_) hl hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
      · exact (hp.stkMode.symm.sub_left hsub)
  refine ⟨hF, ⟨b₇, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, Frame.refl _ _⟩, ?_, esp₇, rd₇, wr₇, fun i hi => ?_, f₀₇⟩
  · rw [m₇, readW_write_sep dn, Mem.readW_writeW_self32, Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [m₇, Mem.readW_writeW_self32, Nat.sub_zero]
    simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact cs.ready_frame ready₂ (by rw [esp₇, esp₂']) (by rw [rd₇, rd₂, h₁.rd]) (by rw [wr₇, wr₂, h₁.wr]) sy₇ fdn
      (fun r hr => ⟨_, by rw [wr₂, h₁.wr]; exact hp.scr.wr, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.sub_base _ (by slot_omega)
        · exact VG.Offset.sub_base _ (by slot_omega)⟩)
      (fun r hr => .inl (dnOut r hr))
  · rw [chunksAt_frame f₀₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.dataScr.sub_right modeScr
      · exact hp.dataScr.sub_right coreScr
      · exact hp.stkData.symm) (by have := hp.dataFit; omega_arith)]
    simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  · simp only [List.take_zero, run]
    rw [iv0, ← h₁.chn]
    refine List.map_congr_left fun i hi => keepSlot sChn (fun r hr => ?_) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith)
      (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by slot_omega)
    · exact VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by slot_omega)
  · rw [z₇, u₆.gpr, u₅.gpr, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [N, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  · rw [← h₁.saved i hi]
    exact Mem.readW_congr fun u hu => keepSlot (R := ⟨slotA (S s₀ c) (c.savedSlot i), 4⟩)
      (VG.Offset.sub _ (by slot_omega) (by slot_omega)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))
      (by show 4 ≤ 2 ^ 64; omega_arith) (by simpa using hu)

/-! ## The function -/

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) = (run F (iv0 c s₀) (xs0 c M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = (run F (iv0 c s₀) (xs0 c M s₀)).2) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_arith
  obtain hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  obtain modeScr : Region.Sub (modeR c (S s₀ c)) (scrR s₀ c) := VG.Offset.sub_base _ (by omega_arith)
  obtain coreScr : Region.Sub (coreRegion c (S s₀ c)) (scrR s₀ c) := Region.sub_prefix (by omega_arith)
  obtain dnScr : Region.Sub (dnRegion c (S s₀ c)) (scrR s₀ c) := VG.Offset.sub_base _ (by slot_omega)
  obtain hlen : (xs0 c M s₀).length = N s₀ c := chunksAt_length _ _ _ _
  obtain hsu := setup_wp cs (F := F) hp hk
  rw [WP.seq_iff] at hsu
  unfold Core.seq
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  rw [WP.seq_iff] at h₁
  refine WP.seq (WP.mono h₁ fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  refine WP.seq (WP.mono (loop_wp cs h₃.fixed rfl hpre hpost hcomp hlen h₃.inv h₃.zf) fun s₄ h₄ => ?_)
  -- What the run so far changed.
  obtain big₀ : ∀ {R : Region}, (∀ r ∈ [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] ++
      big c (S s₀ c) (Dp s₀ c) (N s₀ c) M.step (E s₀), R.Disjoint r) → R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len →
      s₄.mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) := fun hd hl _ hi => by
    have f := h₄.frame
    rw [h₃.esp] at f
    rw [f.bytes (fun r hr => hd r (List.mem_append_right _ hr)) hl hi]
    exact h₃.frame.bytes (fun r hr => hd r (List.mem_append_left _ hr)) hl hi
  obtain bigScr : ∀ {R : Region}, R.Disjoint (scrR s₀ c) → R.Disjoint (stkRegion (E s₀) c.stack) →
      R.Disjoint (dataRegion (Dp s₀ c) M.step (N s₀ c)) →
      ∀ r ∈ [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack] ++
        big c (S s₀ c) (Dp s₀ c) (N s₀ c) M.step (E s₀), R.Disjoint r := fun h1 h2 h3 r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.sub_right modeScr
    · exact h1.sub_right coreScr
    · exact h2
    · exact h1.sub_right coreScr
    · exact h1.sub_right dnScr
    · exact h3
    · exact h2
  have b₄ : s₄.gpr sb = S s₀ c := h₄.b
  obtain esp₄ : s₄.gpr .esp = s₀.gpr .esp := by rw [h₄.esp, h₃.esp]
  obtain rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr]
  obtain sv₄ : ∀ i < 4, s₄.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) :=
    fun i hi => by
      rw [← h₃.saved i hi]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
      · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
      · exact (hp.dataScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm
      · rw [h₃.esp]; exact (hp.stkMode.sub_right (VG.Offset.sub _ (by slot_omega) (by slot_omega))).symm
  obtain ret₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
    Mem.readW_congr fun u hu => big₀ (R := retR s₀) (bigScr hp.retScr hp.stkRet.symm hp.retData)
      (by show 4 ≤ 2 ^ 64; omega_arith) (by simpa using hu)
  obtain data₄ : chunksAt M.step s₄.mem ((Dp s₀ c).setWidth 64) (N s₀ c) = (run F (iv0 c s₀) (xs0 c M s₀)).1 := by
    rw [h₄.data, List.take_of_length_le (by omega_arith), List.drop_of_length_le (by omega_arith), List.append_nil]
  obtain abi : ∀ t : State, (∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = s₀.gpr r) → t.gpr .esp = s₀.gpr .esp →
      t.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 →
      abiPreserved s₀ t := fun t hg he hm => ⟨fun r hr => by
        by_cases h : r = .esp
        · subst h; exact he
        · exact hg r hr h, hm⟩
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) ++ c.restore = c.restore by simp]
    refine restore_wp hp b₄ rw₄ sv₄ fun t g e m => ⟨abi t g (by rw [e, esp₄]) (by rw [m, ret₄]), by rw [m, data₄],
      fun h => by cases h⟩
  · rw [show (if true = true then c.ivBack else []) ++ c.restore =
      .mov .esi (.mem (argOp c.ka)) :: (c.opsCode (copyBlk c.bw .dat .chn) ++ c.restore) by simp [Core.ivBack]]
    obtain argsOut : ∀ r ∈ big c (S s₀ c) (Dp s₀ c) (N s₀ c) M.step (E s₀), Region.Disjoint (argsR s₀ c) r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.argsScr.sub_right coreScr
      · exact hp.argsScr.sub_right dnScr
      · exact hp.argsData
      · exact hp.stkArgs.symm
    obtain argsOut₀ : ∀ r ∈ [modeR c (S s₀ c), coreRegion c (S s₀ c), stkRegion (E s₀) c.stack],
        Region.Disjoint (argsR s₀ c) r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.argsScr.sub_right modeScr
      · exact hp.argsScr.sub_right coreScr
      · exact hp.stkArgs.symm
    obtain argsK : ∀ i < c.ka + 4, s₄.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
      have f := h₄.frame
      rw [h₃.esp] at f
      rw [f.readW (arg_contains s₀ hp.espFit hi) argsOut (by decide),
        h₃.frame.readW (arg_contains s₀ hp.espFit hi) argsOut₀ (by decide)]
      rfl
    refine wp_arg hp esp₄ rw₄ argsK (by omega_arith) fun s₅ u₅ => ?_
    obtain b₅ : s₅.gpr sb = S s₀ c := by rw [u₅.other _ (by decide)]; exact b₄
    refine opsCode_wp c (ws := [.dat]) (fun o ho => ?_) (ivAreasOk hp b₅ u₅.gpr (by rw [u₅.rd, h₄.rd, h₃.rd])
      (by rw [u₅.wr, h₄.wr, h₃.wr]) (fun _ _ _ => hp.ivWr hiv)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    · simp only [copyBlk, List.mem_map, List.mem_range] at ho
      obtain ⟨w, hw, rfl⟩ := ho
      exact ⟨⟨by simp [Op.width]; omega_arith, by simp [Op.width]; omega_arith, fun _ _ h => by cases h⟩,
        List.mem_singleton_self _⟩
    rw [u₅.mem] at a₆ f₆
    obtain ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀ c) (S s₀ c)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    obtain sv₆ : ∀ i < 4, s₆.mem.readW (slotA (S s₀ c) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) :=
      fun i hi => by
        rw [← sv₄ i hi]
        exact f₆.readW (Region.contains_self _ _)
          (ivOnly (hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm) (by decide)
    refine restore_wp hp (by rw [g₆ _ (by decide) (by decide)]; exact b₅)
      (by rw [rd₆, wr₆, u₅.rd, u₅.wr, rw₄]) sv₆ fun t g e m => ⟨abi t g ?_ ?_, ?_, fun _ => ?_⟩
    · rw [e, g₆ _ (by decide) (by decide), u₅.other _ (by decide), esp₄]
    · rw [m, f₆.readW (Region.contains_self _ _) (ivOnly (hp.retIv hiv)) (by decide), ret₄]
    · rw [m, chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega_arith), data₄]
    · rw [m]
      have hc := h₄.chn
      rw [List.take_of_length_le (by omega_arith)] at hc
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      obtain e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl

end VG.Proof.Modes.X86
