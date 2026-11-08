module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Proof.Modes.PPC64LE.Ops
public import VerifiedGarbage.Impl.Modes.PPC64LE.Wide
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# One step of a mode on PPC64LE

`body_wp`: one run of the loop's body (`Core.body`) takes the invariant
(`Inv`) from `j` steps done to `j + 1`. After `j` steps, the data are the
outputs of the mode's step function `F` on the first `j` input steps
followed by the other inputs, the chaining value is `F`'s after them, the
data pointer and the steps left are in `r31` and `r30`, and the key is
ready. The step's three areas (`areas`) are the data's step `j`, the
chaining value's slots and the first `bl` bytes of the core's buffer;
`pre` and `post` are `opsCode_wp`, the block cipher `crypt_wp`, which
enciphers the buffer's bytes as `ciphB` (`BufCipher`), and
`ComputesB M L bl ciphB F` relates them to `F`.

A step takes `d` from `r30`, which holds `n₀ - d j` after `j` steps: one
block a step (`body_wp`, `loop_wp`: `bl = 4 bw`, `d = 1`, `n₀ = n`), or a
group of `2 ^ lg` blocks (`loopWide_wp`: `bl = 4 bw 2 ^ lg`, `d = 2 ^ lg`,
`n = n₀ / d`), the loop going on while `r8 = r30 >> lg` is not zero, as on
RISC-V (`Proof/Modes/RISCV64/Step.lean`). The key is ready for the regions
`W`, which hold the data and the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The areas' lengths: a step's data, a block of `4 bw` bytes, and the
buffer's first `bl` bytes. -/
def lens (c : Core) (st bl : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => bl

/-- The areas' addresses, for step `j` of the data at `D`. -/
def areas (c : Core) (B D : Addr) (st j : Nat) : Loc → Addr
  | .dat => D + BitVec.ofNat 64 (st * j)
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

/-- The data. -/
abbrev dataRegion (D : Addr) (st n : Nat) : Region := ⟨D, st * n⟩

/-- The data of step `j`. -/
abbrev datRegion (D : Addr) (st j : Nat) : Region := ⟨D + BitVec.ofNat 64 (st * j), st⟩

/-- The chaining value's slots. -/
abbrev chnRegion (c : Core) (B : Addr) : Region := ⟨slotA B c.chnSlot, 4 * c.bw⟩

/-- The whole scratch buffer. -/
abbrev scrRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.total⟩

/-- What a run keeps fixed: the scratch buffer at `B`, the data at `D` of `n`
steps of `st` bytes, the buffer's `bl` bytes a step uses, the regions `W`
the key is ready for, the count `n₀ - d j` in `r30`, and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : Addr) (n st bl : Nat) (W : List Region) (n₀ d : Nat) :
    Prop where
  scr : ScrIn s₀ B c.total
  dataW : ∀ o w, 0 < w → o + w ≤ st * n → InRegions s₀.wr (D + BitVec.ofNat 64 o) w
  dataFit : D.toNat + st * n ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D st n) (scrRegion c B)
  nFit : n₀ < 2 ^ 64
  cnt : d * n ≤ n₀
  dec : d ≤ 2 ^ 15
  step : 0 < st ∧ st < 2 ^ 15
  buf : 0 < bl ∧ bl ≤ 4 * c.bw * c.G
  dataIn : ∃ r ∈ W, Region.Sub (dataRegion D st n) r
  scrIn : scrRegion c B ∈ W
  layout : Layout c

/-- Every access within a writable region of the data is permitted. -/
theorem dataW_of_mem {wr : List Region} {D : Addr} {len : Nat} (hm : (⟨D, len⟩ : Region) ∈ wr)
    (hD : D.toNat + len ≤ 2 ^ 64) {o w : Nat} (hw : 0 < w) (ho : o + w ≤ len) :
    InRegions wr (D + BitVec.ofNat 64 o) w :=
  ⟨_, hm, VG.Offset.contains_base _ (by omega_using [ho]) (by omega_using [hD, ho, hw])⟩

/-- The regions a mode writes: the data and the scratch buffer. -/
abbrev wrs (c : Core) (B D : Addr) (n st : Nat) : List Region := [dataRegion D st n, scrRegion c B]

/-- The regions a run changes. -/
abbrev big (c : Core) (B D : Addr) (n st : Nat) : List Region :=
  [coreRegion c B, chnRegion c B, dataRegion D st n]

/-- The invariant after `j` of the `n` steps from the inputs `xs` and the
chaining value `c0`. -/
structure Inv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n st : Nat) (W : List Region) (n₀ d : Nat)
    (k : cs.Key) (F : StepFn) (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.gpr .r31 = D + BitVec.ofNat 64 (st * j)
  np : s.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j)
  ready : cs.Ready s B W k
  data : chunksAt st s.mem D n = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (big c B D n st) s₀.mem s.mem

/-- After all `n` steps from the state `s₂`, by whatever loops: the data are
`F`'s outputs on the inputs `xs` from `c0`, the chaining value `F`'s last,
the scratch buffer's base and the registers the caller expects kept, and
memory changed only in `big`. -/
structure Done (s₂ : State) (B D : Addr) (n st : Nat) (F : StepFn) (c0 : List Byte) (xs : List (List Byte))
    (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .r30 → r ≠ .r31 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  data : chunksAt st s.mem D n = (run F c0 xs).1
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 xs).2
  frame : Frame (big c B D n st) s₂.mem s.mem

theorem Inv.done {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs n s) (hxs : xs.length = n) : Done (c := c) s₀ B D n st F c0 xs s := by
  refine ⟨hI.b, hI.keep, hI.rd, hI.wr, ?_, ?_, hI.frame⟩
  · rw [hI.data, List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]
  · rw [hI.chn, List.take_of_length_le (by omega)]

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

theorem Agree.trans {len : Loc → Nat} {a b c : Areas} (h₁ : Agree len a b) (h₂ : Agree len b c) :
    Agree len a c := fun l i hi => (h₁ l i hi).trans (h₂ l i hi)

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

theorem slot_contains {B : Addr} {total d n : Nat} (ht : 8 * total < 2 ^ 15)
    (h : d + n ≤ 8 * total) :
    (⟨B, 8 * total⟩ : Region).Contains (B + BitVec.ofNat 64 d) n :=
  VG.Offset.contains_base _ h (by omega_using [ht, h])

theorem slot_sub {B : Addr} {total d n : Nat} (h : d + n ≤ 8 * total) :
    Region.Sub ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B, 8 * total⟩ :=
  VG.Offset.sub_base _ h

/-- The buffer's bytes a step uses, within the core's slots. -/
theorem Fixed.buf_le {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) : 8 * c.buf + bl ≤ 8 * c.slots :=
  Nat.le_trans (Nat.add_le_add_left hF.buf.2 _) hF.layout.buf_le

/-- Every byte of the areas at step `j`, as the code addresses them. -/
theorem areasOk {s₀ s : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n)
    (hb : s.gpr sb = B) (hdp : s.gpr .r31 = D + BitVec.ofNat 64 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st bl) (areas c B D st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + bl ≤ 8 * c.slots := hF.buf_le
  have hW : ∀ l off w, 0 < w → off + w ≤ lens c st bl l →
      InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w hw0 ho
    rw [hwr]
    cases l
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.dataW _ _ hw0 (by omega_using [hjn, ho])
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by slot_omega)
    · simp only [lens, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hdisp (by omega_using [hroom, hb4, ho])
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l _ off w hw0 ho => hW l off w hw0 ho,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hroom, hdisp]
  · obtain ⟨r, hr, hc⟩ := hW l off w hw0 ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨D + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, bl⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_using [hdisp, hroom, hb4])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by slot_omega)
    · exact dD _ _ (by omega_using [hroom, hb4])
    · exact (dD _ _ (by slot_omega)).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hb4])).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw, hb4, hdisp, hroom]

/-! ## The regions of a step -/

/-- The regions a step's operations and core change: the data of the step,
the core's slots and the chaining value. -/
abbrev fine (c : Core) (B D : Addr) (st j : Nat) : List Region :=
  [datRegion D st j, coreRegion c B, chnRegion c B]

/-- What a step needs of the regions. -/
structure Regs (c : Core) (B D : Addr) (n st bl : Nat) (W : List Region) (j : Nat) : Prop where
  areasFine : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs, ∃ r' ∈ W, Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lens c st bl) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B)
  datCore : Region.Disjoint (datRegion D st j) (coreRegion c B)
  datData : Region.Sub (datRegion D st j) (dataRegion D st n)
  dataCore : Region.Disjoint (dataRegion D st n) (coreRegion c B)
  dataChn : Region.Disjoint (dataRegion D st n) (chnRegion c B)
  toBig : ∀ r ∈ fine c B D st j, ∃ r' ∈ big c B D n st, Region.Sub r r'

theorem regs {s₀ : State} {B D : Addr} {n st bl : Nat} {W : List Region} {n₀ d j : Nat}
    (hF : Fixed c s₀ B D n st bl W n₀ d) (hj : j < n) :
    Regs c B D n st bl W j := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  have hb4 : 8 * c.buf + bl ≤ 8 * c.slots := hF.buf_le
  have subBuf : Region.Sub ⟨slotA B c.buf, bl⟩ (coreRegion c B) :=
    VG.Offset.sub_base _ hb4
  have subBlk : Region.Sub ⟨slotA B c.buf, bl⟩ (blkRegion c B) := Region.sub_prefix hF.buf.2
  have chnScr : Region.Sub (chnRegion c B) (scrRegion c B) := VG.Offset.sub_base _ (by slot_omega)
  have coreScr : Region.Sub (coreRegion c B) (scrRegion c B) := Region.sub_prefix (by slot_omega)
  have chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
  have datCore : Region.Disjoint (datRegion D st j) (coreRegion c B) :=
    (hF.dataScr.sub_left subDat).sub_right coreScr
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  have m2 : ∀ {a b c' : Region} {l : List Region}, c' ∈ a :: b :: c' :: l :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, chnCore, datCore, subDat,
    hF.dataScr.sub_right coreScr, hF.dataScr.sub_right chnScr, fun r hr => ?_⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, subBuf⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨rD, hrD, sD⟩ := hF.dataIn
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, hrD, fun x hx => sD x (subDat x hx)⟩
    · exact ⟨_, hF.scrIn, chnScr⟩
    · exact ⟨_, hF.scrIn, fun x hx => coreScr x (subBuf x hx)⟩
  · simp only [areaRegions, allLocs, List.map, areas, lens, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl datCore.symm
    · exact .inl chnCore.symm
    · exact .inr subBlk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, m2, subDat⟩
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m1, fun _ h => h⟩

/-! ## The stages of a step -/

/-- In the middle of a step from `s`: the areas agree with `a`, the key is
ready, the mode's registers are kept, and memory has changed only in `fine`
since `s`. -/
structure Mid (cs : CoreSpec c) (s₀ : State) (B D : Addr) (st bl : Nat) (W : List Region) (j : Nat)
    (k : cs.Key) (s : State) (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B W k
  agree : Agree (lens c st bl) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j) s.mem s'.mem

theorem mem_kept {r : Reg} (h : r = .r3 ∨ r = .r29 ∨ r = .r30 ∨ r = .r31) : r ∈ kept := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The operations' registers are not kept. -/
theorem kept_ne : ∀ r ∈ kept, r ≠ .r8 ∧ r ≠ .r9 := by decide

/-- The operations' hypotheses, for `opsCode_wp`. -/
theorem ops_ok {len : Loc → Nat} {os : List Op} (h : ∀ o ∈ os, o.InBounds len) :
    ∀ o ∈ os, o.InBounds len ∧ o.dst ∈ allLocs :=
  fun o ho => ⟨h o ho, mem_allLocs _⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem pre_wp (hF : Fixed c s₀ B D n st bl W n₀ d)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.block (c.opsCode M.pre)) s
      (Mid cs s₀ B D st bl W j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  have hR := regs hF hj
  have hA : AreasOk c s (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hI.b hI.dp hI.wr
  rw [← List.append_nil (c.opsCode M.pre)]
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpre) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => wp_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact hI.b,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2,
    by rw [rd₂, hI.rd], by rw [wr₂, hI.wr],
    cs.ready_frame hI.ready (fun r hr _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2) rd₂ wr₂ sy₂ f₂
      hR.areasW hR.areasCore, a₂,
    f₂.sub hR.areasFine⟩

end

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem blkAddr_zero (c : Core) (B : Addr) : blkAddr c B 0 = slotA B c.buf := by
  simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]

/-- The core's block cipher, as the cipher `ciphB` on the buffer's first `bl`
bytes: what `crypt_wp` gives of the buffer's blocks determines them. -/
def BufCipher (c : Core) (ciph ciphB : Spec.Cbc.Cipher) (bl : Nat) : Prop :=
  ∀ (B : Addr) (m m' : Mem), (∀ j < c.G, bytesAt m' (blkAddr c B j) (4 * c.bw) =
    ciph (bytesAt m (blkAddr c B j) (4 * c.bw))) →
    bytesAt m' (slotA B c.buf) bl = ciphB (bytesAt m (slotA B c.buf) bl)

/-- One block: the cipher on the buffer's first block. -/
theorem bufCipher_one (hG : 0 < c.G) (ciph : Spec.Cbc.Cipher) : BufCipher c ciph ciph (4 * c.bw) :=
  fun B m m' h => by have e := h 0 hG; rwa [blkAddr_zero] at e

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem crypt_step (hF : Fixed c s₀ B D n st bl W n₀ d) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : Mid cs s₀ B D st bl W j k s a s₂) :
    WP isa c.crypt s₂ (Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB a)) := by
  have hR := regs hF hj
  have hst := hF.step
  have hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf bl ciphB (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
  · simp only [lens] at hi
    have e := hB B s₂.mem s₃.mem enc₃
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

end

theorem chunksAt_getElem {L : Nat} {m : Mem} {p : Addr} {n j : Nat} (hj : j < n) :
    (chunksAt L m p n)[j]'(by rw [chunksAt_length]; exact hj) = bytesAt m (p + BitVec.ofNat 64 (L * j)) L := by
  simp [chunksAt]

/-- Input step `j`, from the invariant. -/
theorem Inv.input {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {W : List Region} {n₀ d : Nat}
    {k : cs.Key} {F : StepFn} {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) (hxs : xs.length = n) (hj : j < n) :
    bytesAt s.mem (D + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega_using [hxs, hj]) := by
  have hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  have e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

theorem ofNat_pred64 {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem ofNat_sub64 {a b : Nat} (h : b ≤ a) : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mod_le a (2 ^ 64)
  by_cases hb : b < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hb]
    by_cases ha : a < 2 ^ 64
    · rw [Nat.mod_eq_of_lt ha]; omega
    · omega
  · omega

/-- What the instructions `ex` after a step's count do: change only `r8`,
establishing `X`. -/
def ExOk (ex : List Instr) (X : State → Prop) : Prop :=
  ∀ t, WP isa (.block ex) t fun t' => (∀ r, r ≠ .r8 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧
    t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.syms = t.syms ∧ X t'

theorem exOk_nil : ExOk [] fun _ => True := fun _ => wp_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, trivial⟩

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ d : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem post_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl)) (hcomp : ComputesB M (4 * c.bw) bl ciphB F)
    {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s s₃ : State} (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s)
    (hm : Mid cs s₀ B D st bl W j k s (cryptBuf bl ciphB
      (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.opsCode M.post ++ (.addi .r31 .r31 M.step :: .subi .r30 .r30 d :: ex))) s₃
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' := by
  have hR := regs hF hj
  have hL := hF.layout
  have hst := hF.step
  have hDf := hF.dataFit
  have hcnt : d * j + d ≤ n₀ := by rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hj) hF.cnt
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have k₃ : ∀ r, r = .r3 ∨ r = .r29 ∨ r = .r30 ∨ r = .r31 → s₃.gpr r = s.gpr r :=
    fun r hr => hm.kept r (mem_kept hr)
  have dp₃ : s₃.gpr .r31 = D + BitVec.ofNat 64 (st * j) := by rw [k₃ _ (by simp), hI.dp]
  have np₃ : s₃.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j) := by rw [k₃ _ (by simp), hI.np]
  have hA : AreasOk c s₃ (lens c st bl) (areas c B D st j) allLocs := areasOk hF hj hm.b dp₃ hm.wr
  refine VG.PPC64LE.WP.of_syms (opsCode_wp c (ops_ok hpost) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_)
  refine wp_addi (by decide) (by omega_using [hM, hst]) fun s₆ u₆ =>
    wp_subi (by decide) hF.dec fun s₇ u₇ => WP.mono (hex s₇) fun s₈ ⟨g₈, m₈, rd₈, wr₈, sy₈', x₈⟩ sy₈ => ⟨?_, x₈⟩
  have g₇ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r30 → r ≠ .r31 → s₈.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₈ r h1, u₇.other r h3, u₆.other r h4, g₅ r h1 h2]
  have m₇ : s₈.mem = s₅.mem := by rw [m₈, u₇.mem, u₆.mem]
  have r31₅ : s₅.gpr .r31 = D + BitVec.ofNat 64 (st * j) := by rw [g₅ _ (by decide) (by decide), dp₃]
  have r30₅ : s₅.gpr .r30 = BitVec.ofNat 64 (n₀ - d * j) := by rw [g₅ _ (by decide) (by decide), np₃]
  have sy₇ : s₈.syms = s₃.syms := sy₈
  -- The step's outputs.
  let A := areas c B D st j
  have hstep : Agree (lens c st bl) (cont A s₅.mem) (stepA M bl ciphB (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  have xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  have out₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  have chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  have all : Frame (fine c B D st j) s.mem s₅.mem := hm.frame.trans (f₅.sub hR.areasFine)
  have hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++
      [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    fun r hr h30 h31 => by
      rw [g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31, hm.kept r hr, hI.keep r hr h30 h31],
    by rw [rd₈, u₇.rd, u₆.rd, rd₅, hm.rd], by rw [wr₈, u₇.wr, u₆.wr, wr₅, hm.wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g₈ _ (by decide), u₇.other _ (by decide), u₆.gpr, r31₅, VG.Offset.add_add, hM, Nat.mul_succ]
  · rw [g₈ _ (by decide), u₇.gpr, u₆.other _ (by decide), r30₅, ofNat_sub64 (by omega_using [hcnt]), Nat.mul_succ]
    congr 1; omega_using [hcnt]
  · exact cs.ready_frame hm.ready (fun r hr _ h30 h31 => g₇ r (kept_ne r hr).1 (kept_ne r hr).2 h30 h31)
      (by rw [rd₈, u₇.rd, u₆.rd, rd₅]) (by rw [wr₈, u₇.wr, u₆.wr, wr₅]) sy₇ (by rw [m₇]; exact f₅)
      hR.areasW hR.areasCore
  · rw [m₇, chunksAt_set (j := j) (fun i hi hout => ?_), hI.data, out₅, run_set F c0 (by omega_using [hxs, hj])]
    refine all _ fun r hr hcon => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Region.Contains] at hcon
      have e := (VG.Offset.lt_iff (D + BitVec.ofNat 64 i) D (d := st * j) (n := st)
        (by omega_using [hDf, hjn])).mp (by omega_using [hcon])
      rw [sub_self_add _ (by omega_using [hDf, hi])] at e
      omega_using [hout, e]
    · exact hR.dataCore _ (contains_area hi (by omega_using [hDf])) hcon
    · exact hR.dataChn _ (contains_area hi (by omega_using [hDf])) hcon
  · rw [m₇, chn₅, hrun]
  · rw [m₇]; exact hI.frame.trans (all.sub hR.toBig)

/-! ## The step and the loop -/

/-- A step: `pre`, the core, `post`, the count, and `ex`. -/
theorem step_wp (hF : Fixed c s₀ B D n st bl W n₀ d) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) {ex : List Instr} {X : State → Prop} (hex : ExOk ex X)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ d k F c0 xs j s) :
    WP isa (.seq (.block (c.opsCode M.pre)) (.seq c.crypt
      (.block (c.opsCode M.post ++ (.addi .r31 .r31 M.step :: .subi .r30 .r30 d :: ex))))) s
      fun s' => Inv cs s₀ B D n st W n₀ d k F c0 xs (j + 1) s' ∧ X s' :=
  WP.seq (WP.mono (pre_wp cs hF hpre hj hI) fun _ h₂ =>
    WP.seq (WP.mono (crypt_step cs hF hB hj h₂) fun _ h₃ => post_wp cs hF hM hpost hcomp hex hxs hj hI h₃))

theorem body_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n₀ 1) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw))) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ 1 k F c0 xs j s) :
    WP isa (c.body M) s (Inv cs s₀ B D n st W n₀ 1 k F c0 xs (j + 1)) :=
  WP.mono (step_wp cs hF hM (bufCipher_one hF.layout.G_pos _) hpre hpost hcomp exOk_nil hxs hj hI) fun _ h => h.1

theorem loop_wp (hF : Fixed c s₀ B D n st (4 * c.bw) W n 1) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st (4 * c.bw))) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st (4 * c.bw)))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n 1 k F c0 xs 0 s) :
    WP isa (c.steps M) s (Inv cs s₀ B D n st W n 1 k F c0 xs n) := by
  have hn64 := hF.nFit
  have ev : ∀ {j t}, j ≤ n → t.gpr .r30 = BitVec.ofNat 64 (n - 1 * j) →
      isa.eval (.nonzero .d .r30) t = some (decide (n - 1 * j ≠ 0)) := fun hj h =>
    eval_nonzero_ofNat' _ _ (by omega_using [hn64, hj]) h
  unfold Core.steps
  by_cases hn : n = 0
  · subst hn
    exact WP.ite true (by rw [eval_zero_ofNat s .r30 (by decide) hI.np]; rfl) (fun _ => wp_nil hI)
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .r30 (by omega_using [hn64]) hI.np]; simp [hn])
    (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.body M) (c := .nonzero .d .r30) (Q := Inv cs s₀ B D n st W n 1 k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n 1 k F c0 xs j t)
    ?_ n s ⟨0, by omega_using [], by omega_using [hn], hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hM hpre hpost hcomp hxs hj h) fun t' h' => ?_
  have e := ev (j := j + 1) (by omega_using [hj]) h'.np
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

/-! ## A group of blocks a step -/

/-- `r8` is `r30 >> lg`: whether a group of `2 ^ lg` blocks is left. -/
def GroupsLeft (lg : Nat) (t : State) : Prop := t.gpr .r8 = t.gpr .r30 >>> lg

theorem exOk_groupsLeft {lg : Nat} (h : lg < 64) : ExOk [Core.groupsLeft lg] (GroupsLeft lg) :=
  fun t => VG.PPC64LE.WP.of_syms (wp_lsr h fun t' u => wp_nil fun sy =>
    ⟨fun r hr => u.other r hr, u.mem, u.rd, u.wr, sy, by
      simp only [GroupsLeft, u.gpr, u.other _ (show Reg.r30 ≠ .r8 by decide)]⟩)

theorem ushiftRight_ofNat {x lg : Nat} (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x >>> lg = BitVec.ofNat 64 (x / 2 ^ lg) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st bl : Nat}
  {W : List Region} {n₀ : Nat} {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

/-- The steps of `2 ^ lg` blocks, `n = n₀ / 2 ^ lg` of them. -/
theorem loopWide_wp {lg : Nat} (hlg : lg < 64) (hF : Fixed c s₀ B D n st bl W n₀ (2 ^ lg))
    (hn : n = n₀ / 2 ^ lg) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB bl)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st bl)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st bl))
    (hcomp : ComputesB M (4 * c.bw) bl ciphB F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s) :
    WP isa (c.loopWide M lg) s (Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n) := by
  have hn64 := hF.nFit
  -- After `j` steps, `r8` says whether `j < n`.
  have ev : ∀ {j : Nat} {t : State}, j ≤ n → t.gpr .r30 = BitVec.ofNat 64 (n₀ - 2 ^ lg * j) →
      GroupsLeft lg t → isa.eval (.nonzero .d .r8) t = some (decide (j < n)) ∧
        isa.eval (.zero .d .r8) t = some (decide (n ≤ j)) := fun {j t} hj h3 hg => by
    have hq : (n₀ - 2 ^ lg * j) / 2 ^ lg = n - j := by rw [Nat.sub_mul_div, hn]
    have h0 : t.gpr .r8 = BitVec.ofNat 64 (n - j) := by
      rw [hg, h3, ushiftRight_ofNat (by omega_using [hn64]), hq]
    have hlt : n - j < 2 ^ 64 := by
      have : n ≤ n₀ := by rw [hn]; exact Nat.div_le_self _ _
      omega_using [hn64, this]
    rw [eval_nonzero_ofNat' _ _ hlt h0, eval_zero_ofNat _ _ hlt h0]
    exact ⟨congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h], fun h => by omega_using [h]⟩),
      congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_using [h, hj], fun h => by omega_using [h]⟩)⟩
  unfold Core.loopWide
  refine WP.seq (VG.PPC64LE.WP.of_syms (wp_lsr hlg fun s₁ u₁ => wp_nil fun sy₁ => ?_))
  have hI₁ : Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs 0 s₁ :=
    ⟨by rw [u₁.other _ (by decide)]; exact hI.b,
      fun r hr h3 h2 => by rw [u₁.other r (kept_ne r hr).1]; exact hI.keep r hr h3 h2,
      by rw [u₁.rd, hI.rd], by rw [u₁.wr, hI.wr], by rw [u₁.other _ (by decide)]; exact hI.dp,
      by rw [u₁.other _ (by decide)]; exact hI.np,
      cs.ready_frame (rs := []) hI.ready (fun r hr _ _ _ => u₁.other r (kept_ne r hr).1) u₁.rd u₁.wr sy₁
        (by rw [u₁.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) (fun _ h => nomatch h),
      by rw [u₁.mem]; exact hI.data, by rw [u₁.mem]; exact hI.chn, by rw [u₁.mem]; exact hI.frame⟩
  have g₁ : GroupsLeft lg s₁ := by simp only [GroupsLeft, u₁.gpr, u₁.other _ (show Reg.r30 ≠ .r8 by decide)]
  obtain ⟨-, ez⟩ := ev (Nat.zero_le _) hI₁.np g₁
  by_cases hn0 : n = 0
  · subst hn0
    exact WP.ite true (by rw [ez]; rfl) (fun _ => wp_nil hI₁) (fun h => by cases h)
  refine WP.ite false (by rw [ez]; simp; omega_using [hn0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.bodyWide M lg) (c := .nonzero .d .r8)
    (Q := Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st W n₀ (2 ^ lg) k F c0 xs j t)
    ?_ n s₁ ⟨0, by omega_using [], by omega_using [hn0], hI₁⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (step_wp cs hF hM hB hpre hpost hcomp (exOk_groupsLeft hlg) hxs hj h) fun t' ⟨h', g'⟩ => ?_
  obtain ⟨e, -⟩ := ev (j := j + 1) (by omega_using [hj]) h'.np g'
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end

end VG.Proof.Modes.PPC64LE
