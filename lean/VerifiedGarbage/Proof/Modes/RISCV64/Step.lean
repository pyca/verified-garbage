module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Proof.Modes.RISCV64.Ops
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Syms

/-!
# One step of a mode on RISCV64

`body_wp`: one run of the loop's body (`Core.body`) takes the invariant
(`Inv`) from `j` steps done to `j + 1`. After `j` steps, the data are the
outputs of the mode's step function `F` on the first `j` input steps
followed by the other inputs, the chaining value is `F`'s after them, the
data pointer and the steps left are in `s2` and `s3`, and the key is
ready. The step's three areas (`areas`) are the data's step `j`, the
chaining value's slots and the core's first block; `pre` and `post` are
`opsCode_wp`, the block cipher `crypt_wp`, and `Computes M L ciph F`
relates them to `F`.
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The areas' lengths: a step's data, and blocks of `4 bw` bytes. -/
def lens (c : Core) (st : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => 4 * c.bw

/-- The areas' addresses, for step `j` of the data at `D`. -/
def areas (c : Core) (B D : Addr) (st j : Nat) : Loc → Addr
  | .dat => D + BitVec.ofNat 64 (st * j)
  | .chn => slotA B Core.chnSlot
  | .buf => slotA B c.buf

/-- The data. -/
abbrev dataRegion (D : Addr) (st n : Nat) : Region := ⟨D, st * n⟩

/-- The data of step `j`. -/
abbrev datRegion (D : Addr) (st j : Nat) : Region := ⟨D + BitVec.ofNat 64 (st * j), st⟩

/-- The chaining value's slots. -/
abbrev chnRegion (c : Core) (B : Addr) : Region := ⟨slotA B Core.chnSlot, 4 * c.bw⟩

/-- The whole frame. -/
abbrev scrRegion (c : Core) (B : Addr) : Region := ⟨B, 8 * c.total⟩

/-- What a run keeps fixed: the frame at `B`, the data at `D` of `n`
steps of `st` bytes, readable, and writable if the mode's operations write
to them (`.dat ∈ ws`, the areas they write), and the layout. -/
structure Fixed (c : Core) (s₀ : State) (B D : Addr) (n st : Nat) (ws : List Loc) : Prop where
  scr : ScrIn s₀ B c.total
  dataR : dataRegion D st n ∈ s₀.rd ++ s₀.wr
  dataW : Loc.dat ∈ ws → dataRegion D st n ∈ s₀.wr
  dataFit : D.toNat + st * n ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion D st n) (scrRegion c B)
  nFit : n < 2 ^ 64
  step : 0 < st ∧ st ≤ 4 * c.bw
  layout : Layout c

/-- The regions a mode writes: the data and the frame. -/
abbrev wrs (c : Core) (B D : Addr) (n st : Nat) : List Region := [dataRegion D st n, scrRegion c B]

/-- The regions a run changes. -/
abbrev big (c : Core) (B D : Addr) (n st : Nat) : List Region :=
  [coreRegion c B, chnRegion c B, dataRegion D st n]

/-- The invariant after `j` of the `n` steps from the inputs `xs` and the
chaining value `c0`. -/
structure Inv (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n st : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  keep : ∀ r ∈ kept, r ≠ .s3 → r ≠ .s2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.gpr .s2 = D + BitVec.ofNat 64 (st * j)
  np : s.gpr .s3 = BitVec.ofNat 64 (n - j)
  ready : cs.Ready s B (wrs c B D n st) k
  data : chunksAt st s.mem D n = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B Core.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (big c B D n st) s₀.mem s.mem

/-! ## Areas -/

theorem rd_cont (A : Loc → Addr) (m : Mem) (l : Loc) (n : Nat) : rd (cont A m) l n = bytesAt m (A l) n := rfl

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
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.savedSlot, coreSlot]); omega_arith))

theorem slot_contains {B : Addr} {total d n : Nat}
    (h : d + n ≤ min (8 * total) 2032) :
    (⟨B, min (8 * total) 2032⟩ : Region).Contains (B + BitVec.ofNat 64 d) n :=
  VG.Offset.contains_base _ h (by omega_using [h])

theorem slot_sub {B : Addr} {total d n : Nat} (h : d + n ≤ 8 * total) :
    Region.Sub ⟨B + BitVec.ofNat 64 d, n⟩ ⟨B, 8 * total⟩ :=
  VG.Offset.sub_base _ h

/-- Every byte of the areas at step `j`, as the code addresses them. -/
theorem areasOk {ws : List Loc} {s₀ s : State} {B D : Addr} {n st j : Nat} (hF : Fixed c s₀ B D n st ws) (hj : j < n)
    (hb : s.gpr sb = B) (hdp : s.gpr .s2 = D + BitVec.ofNat 64 (st * j)) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    AreasOk c s (lens c st) (areas c B D st j) ws := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hge := hL.buf_ge
  have hbuf := hL.buf_le
  have hdisp := hL.disp
  have hst := hF.step
  have hD := hF.dataFit
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hb4 : 8 * c.buf + 4 * c.bw ≤ min (8 * c.total) 2032 :=
    Nat.le_min.mpr ⟨Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hbuf,
      Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hdisp⟩
  -- The step's data, in the data, and the slots, in the frame.
  have hDat : ∀ off w, 0 < w → off + w ≤ st →
      (dataRegion D st n).Contains (D + BitVec.ofNat 64 (st * j) + BitVec.ofNat 64 off) w := fun off w hw0 ho => by
    rw [VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_using [hjn, ho]) (by omega_using [hD, hjn, ho, hw0])
  have hScr : ∀ l off w, l ≠ .dat → 0 < w → off + w ≤ lens c st l →
      InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w hl hw0 ho
    rw [hwr]
    cases l
    · exact absurd rfl hl
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.scr.low _ _ (by have := hge; simp only [coreSlot] at this; slot_omega)
    · simp only [lens, areas] at ho ⊢
      rw [VG.Offset.add_add]; exact hF.scr.low _ _ (by omega_using [hb4, ho])
  have hW : ∀ l ∈ ws, ∀ off w, 0 < w → off + w ≤ lens c st l →
      InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l hl off w hw0 ho
    cases l
    · simp only [lens, areas] at ho ⊢
      rw [hwr]; exact ⟨_, hF.dataW hl, hDat off w hw0 ho⟩
    · exact hScr _ off w (by decide) hw0 ho
    · exact hScr _ off w (by decide) hw0 ho
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, hW,
    fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hdp, Nat.zero_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, lens, areas] at ho ⊢
      rw [hb, VG.Offset.add_add]
  · cases l
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hst, hbw]
    · simp only [Core.loc, lens] at ho ⊢; slot_omega
    · simp only [Core.loc, lens] at ho ⊢; omega_using [ho, hb4, hdisp]
  · cases l
    · simp only [lens, areas] at ho ⊢
      rw [hrd, hwr]; exact ⟨_, hF.dataR, hDat off w hw0 ho⟩
    all_goals
      obtain ⟨r, hr, hc⟩ := hScr _ off w (by decide) hw0 ho
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 8 * c.total →
        Region.Disjoint ⟨D + BitVec.ofNat 64 (st * j), st⟩ ⟨B + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    have h6 : coreSlot = 6 := rfl
    have hb8 : 8 * c.buf + 4 * c.bw ≤ 8 * c.total := Nat.le_trans hb4 (Nat.min_le_left _ _)
    have hc : 8 * Core.chnSlot + 4 * c.bw ≤ 8 * c.buf := by
      simp only [Core.chnSlot]; omega_using [hge, h6, hbw]
    have dCB : Region.Disjoint ⟨slotA B Core.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inl hc) (by omega_using [hc, hfit, hb8]) (by omega_using [hfit, hb8])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lens, areas]
    · exact dD _ _ (by omega_using [hc, hb8])
    · exact dD _ _ hb8
    · exact (dD _ _ (by omega_using [hc, hb8])).symm
    · exact dCB
    · exact (dD _ _ hb8).symm
    · exact dCB.symm
  · cases l <;> simp only [lens] <;> omega_using [hst, hbw]

/-! ## The regions of a step -/

/-- The regions a step's operations and core change: the data of the step,
the core's slots and the chaining value. -/
abbrev fine (c : Core) (B D : Addr) (st j : Nat) : List Region :=
  [datRegion D st j, coreRegion c B, chnRegion c B]

/-- What a step needs of the regions. -/
structure Regs (c : Core) (B D : Addr) (n st j : Nat) : Prop where
  areasFine : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs,
    ∃ r' ∈ [dataRegion D st n, scrRegion c B], Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lens c st) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B)
  datCore : Region.Disjoint (datRegion D st j) (coreRegion c B)
  datData : Region.Sub (datRegion D st j) (dataRegion D st n)
  dataCore : Region.Disjoint (dataRegion D st n) (coreRegion c B)
  dataChn : Region.Disjoint (dataRegion D st n) (chnRegion c B)
  toBig : ∀ r ∈ fine c B D st j, ∃ r' ∈ big c B D n st, Region.Sub r r'

theorem regs {ws : List Loc} {s₀ : State} {B D : Addr} {n st j : Nat} (hF : Fixed c s₀ B D n st ws) (hj : j < n) :
    Regs c B D n st j := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hge := hL.buf_ge
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have subDat : Region.Sub (datRegion D st j) (dataRegion D st n) := VG.Offset.sub_base _ hjn
  have hb4 : 8 * c.buf + 4 * c.bw ≤ 8 * c.total :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hG) _) hbuf
  have h6 : coreSlot = 6 := rfl
  have subBuf : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (coreRegion c B) :=
    VG.Offset.sub _ (by omega_using [hge, h6]) (by omega_using [hge, hb4, h6])
  have subBlk : Region.Sub ⟨slotA B c.buf, 4 * c.bw⟩ (blkRegion c B) :=
    Region.sub_prefix (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hbG)
  have chnScr : Region.Sub (chnRegion c B) (scrRegion c B) :=
    VG.Offset.sub_base _ (by simp only [Core.chnSlot]; omega_using [hge, hb4, h6, hbw])
  have coreScr : Region.Sub (coreRegion c B) (scrRegion c B) :=
    VG.Offset.sub_base _ (by omega_using [hge, hb4, h6])
  have chnCore : Region.Disjoint (chnRegion c B) (coreRegion c B) :=
    VG.Offset.disjoint _ (.inl (by simp only [Core.chnSlot]; omega_using [hbw, h6]))
      (by simp only [Core.chnSlot]; omega_using [hfit, hge, hb4, h6, hbw]) (by omega_using [hfit, hge, hb4, h6])
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
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subDat⟩
    · exact ⟨_, m1, chnScr⟩
    · exact ⟨_, m1, fun x hx => coreScr x (subBuf x hx)⟩
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
structure Mid (cs : CoreSpec c) (s₀ : State) (B D : Addr) (n st j : Nat) (k : cs.Key) (s : State) (a : Areas)
    (s' : State) : Prop where
  b : s'.gpr sb = B
  kept : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B (wrs c B D n st) k
  agree : Agree (lens c st) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j) s.mem s'.mem

theorem mem_kept {r : Reg} (h : r = .a0 ∨ r = .s1 ∨ r = .s3 ∨ r = .s2) : r ∈ kept := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The operations' registers are not kept. -/
theorem kept_ne : ∀ r ∈ kept, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide

/-- The operations' hypotheses, for `opsCode_wp`. -/
theorem ops_ok {len : Loc → Nat} {os : List Op} {ws : List Loc} (h : ∀ o ∈ os, o.InBounds len)
    (hw : ∀ o ∈ os, o.dst ∈ ws) : ∀ o ∈ os, o.InBounds len ∧ o.dst ∈ ws :=
  fun o ho => ⟨h o ho, hw o ho⟩

/-- The regions of some of the areas are among those of all of them. -/
theorem areaRegions_sub {len : Loc → Nat} {A : Loc → Addr} {ws : List Loc} {r : Region}
    (h : r ∈ areaRegions len A ws) : r ∈ areaRegions len A allLocs := by
  simp only [areaRegions, List.mem_map] at h ⊢
  obtain ⟨l, _, rfl⟩ := h
  exact ⟨l, mem_allLocs l, rfl⟩

theorem pre_wp (cs : CoreSpec c) {ws : List Loc} {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st ws)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) (hpw : ∀ o ∈ M.pre, o.dst ∈ ws) {j : Nat} (hj : j < n)
    {s : State} (hI : Inv cs s₀ B D n st k F c0 xs j s) :
    WP isa (.block (c.opsCode M.pre)) s
      (Mid cs s₀ B D n st j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  have hR := regs hF hj
  have hA : AreasOk c s (lens c st) (areas c B D st j) ws := areasOk hF hj hI.b hI.dp hI.rd hI.wr
  rw [← List.append_nil (c.opsCode M.pre)]
  refine WP.of_syms (opsCode_wp c (ops_ok hpre hpw) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ => WP.block_nil fun sy₂ => ?_)
  exact ⟨by rw [g₂ _ (by decide) (by decide) (by decide)]; exact hI.b,
    fun r hr => g₂ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2,
    by rw [rd₂, hI.rd], by rw [wr₂, hI.wr],
    cs.ready_frame hI.ready (fun r hr _ _ _ _ => g₂ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2) rd₂ wr₂ sy₂ f₂
      (fun r hr => hR.areasW r (areaRegions_sub hr)) (fun r hr => hR.areasCore r (areaRegions_sub hr)), a₂,
    f₂.sub fun r hr => hR.areasFine r (areaRegions_sub hr)⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem blkAddr_zero (c : Core) (B : Addr) : blkAddr c B 0 = slotA B c.buf := by
  simp only [blkAddr, Nat.mul_zero, BitVec.add_zero]

theorem crypt_step (cs : CoreSpec c) {ws : List Loc} {s₀ : State} {B D : Addr} {n st : Nat} {k : cs.Key}
    (hF : Fixed c s₀ B D n st ws) {j : Nat} (hj : j < n) {s s₂ : State} {a : Areas}
    (hm : Mid cs s₀ B D n st j k s a s₂) :
    WP isa c.crypt s₂ (Mid cs s₀ B D n st j k s (cryptBuf (4 * c.bw) (cs.cipher k) a)) := by
  have hR := regs hF hj
  have hst := hF.step
  have hbw : c.bw ≤ 4 := by rcases hF.layout.bw with h | h <;> omega_using [h]
  refine WP.mono (cs.crypt_wp hm.b (hF.scr.congr hm.wr) hm.ready)
    fun s₃ ⟨b₃, kept₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  refine ⟨b₃, fun r hr => by rw [kept₃ r hr, hm.kept r hr], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf (4 * c.bw) (cs.cipher k) (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lens]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.datCore) (by show st ≤ 2 ^ 64; omega_using [hst, hbw]) hi
  · simp only [cryptBuf, cont, areas, lens] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hR.chnCore) (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) hi
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
theorem Inv.input {cs : CoreSpec c} {s₀ : State} {B D : Addr} {n st : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State} (hI : Inv cs s₀ B D n st k F c0 xs j s)
    (hxs : xs.length = n) (hj : j < n) :
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

theorem post_wp (cs : CoreSpec c) {ws : List Loc} {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st ws) (hM : M.step = st)
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c st)) (hqw : ∀ o ∈ M.post, o.dst ∈ ws)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F)
    (hxs : xs.length = n) {j : Nat} (hj : j < n) {s s₃ : State} (hI : Inv cs s₀ B D n st k F c0 xs j s)
    (hm : Mid cs s₀ B D n st j k s (cryptBuf (4 * c.bw) (cs.cipher k)
      (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.opsCode M.post ++ Core.advance M.step)) s₃ (Inv cs s₀ B D n st k F c0 xs (j + 1)) := by
  have hR := regs hF hj
  have hL := hF.layout
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hst := hF.step
  have hDf := hF.dataFit
  have hjn : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have k₃ : ∀ r, r = .a0 ∨ r = .s1 ∨ r = .s3 ∨ r = .s2 → s₃.gpr r = s.gpr r :=
    fun r hr => hm.kept r (mem_kept hr)
  have dp₃ : s₃.gpr .s2 = D + BitVec.ofNat 64 (st * j) := by rw [k₃ _ (by simp), hI.dp]
  have np₃ : s₃.gpr .s3 = BitVec.ofNat 64 (n - j) := by rw [k₃ _ (by simp), hI.np]
  have hA : AreasOk c s₃ (lens c st) (areas c B D st j) ws := areasOk hF hj hm.b dp₃ hm.rd hm.wr
  refine WP.of_syms (opsCode_wp c (ops_ok hpost hqw) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_)
  simp only [Core.advance]
  refine wp_addi (by omega_using [hM, hst, hbw]) fun s₆ u₆ =>
    wp_subi (imm := 1) (by decide) fun s₇ u₇ => WP.block_nil fun sy₇ => ?_
  have g₇ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s3 → r ≠ .s2 → s₇.gpr r = s₃.gpr r :=
    fun r h1 h2 h0 h3 h4 => by rw [u₇.other r h3, u₆.other r h4, g₅ r h1 h2 h0]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  have s2₅ : s₅.gpr .s2 = D + BitVec.ofNat 64 (st * j) := by rw [g₅ _ (by decide) (by decide) (by decide), dp₃]
  have s3₅ : s₅.gpr .s3 = BitVec.ofNat 64 (n - j) := by rw [g₅ _ (by decide) (by decide) (by decide), np₃]
  -- The step's outputs.
  let A := areas c B D st j
  have hstep : Agree (lens c st) (cont A s₅.mem) (stepA M (4 * c.bw) (cs.cipher k) (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  have xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  have out₅ : bytesAt s₅.mem (D + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  have chn₅ : bytesAt s₅.mem (slotA B Core.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← hc2]; exact rd_agree hstep (l := .chn) (Nat.le_refl _)
  have all : Frame (fine c B D st j) s.mem s₅.mem :=
    hm.frame.trans (f₅.sub fun r hr => hR.areasFine r (areaRegions_sub hr))
  have hrun : run F c0 (xs.take (j + 1)) = ((run F c0 (xs.take j)).1 ++
      [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    fun r hr h30 h31 => by
      rw [g₇ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2 h30 h31, hm.kept r hr, hI.keep r hr h30 h31],
    by rw [u₇.rd, u₆.rd, rd₅, hm.rd], by rw [u₇.wr, u₆.wr, wr₅, hm.wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, s2₅, VG.Offset.add_add, hM, Nat.mul_succ]
  · rw [u₇.gpr, u₆.other _ (by decide), s3₅, ofNat_pred64 (by omega_using [hj])]
    congr 1
  · exact cs.ready_frame hm.ready (fun r hr _ h31 h30 _ => g₇ r (kept_ne r hr).1 (kept_ne r hr).2.1 (kept_ne r hr).2.2 h30 h31)
      (by rw [u₇.rd, u₆.rd, rd₅]) (by rw [u₇.wr, u₆.wr, wr₅]) sy₇ (by rw [m₇]; exact f₅)
      (fun r hr => hR.areasW r (areaRegions_sub hr)) (fun r hr => hR.areasCore r (areaRegions_sub hr))
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

theorem body_wp (cs : CoreSpec c) {ws : List Loc} {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st ws) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st))
    (hpw : ∀ o ∈ M.pre, o.dst ∈ ws) (hqw : ∀ o ∈ M.post, o.dst ∈ ws)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {j : Nat} (hj : j < n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs j s) :
    WP isa (c.body M) s (Inv cs s₀ B D n st k F c0 xs (j + 1)) := by
  unfold Core.body
  exact WP.seq (WP.mono (pre_wp cs hF hpre hpw hj hI) fun _ h₂ =>
    WP.seq (WP.mono (crypt_step cs hF hj h₂) fun _ h₃ => post_wp cs hF hM hpost hqw hcomp hxs hj hI h₃))

theorem loop_wp (cs : CoreSpec c) {ws : List Loc} {M : Mode} {F : StepFn} {s₀ : State} {B D : Addr} {n st : Nat}
    {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)} (hF : Fixed c s₀ B D n st ws) (hM : M.step = st)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c st)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c st))
    (hpw : ∀ o ∈ M.pre, o.dst ∈ ws) (hqw : ∀ o ∈ M.post, o.dst ∈ ws)
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hxs : xs.length = n) {s : State}
    (hI : Inv cs s₀ B D n st k F c0 xs 0 s) :
    WP isa (.ite (.zero .s3) (.block []) (.loop (c.body M) (.nonzero .s3))) s
      (Inv cs s₀ B D n st k F c0 xs n) := by
  have hn64 := hF.nFit
  have ev : ∀ {j t}, j ≤ n → t.gpr .s3 = BitVec.ofNat 64 (n - j) →
      isa.eval (.nonzero .s3) t = some (decide (n - j ≠ 0)) := fun hj h =>
    eval_nonzero_ofNat _ _ (by omega_using [hn64, hj]) h
  by_cases hn : n = 0
  · subst hn
    exact WP.ite true (by rw [eval_zero_ofNat s .s3 (by decide) hI.np]; rfl) (fun _ => WP.block_nil hI)
      (fun h => by cases h)
  refine WP.ite false (by rw [eval_zero_ofNat s .s3 (by omega_using [hn64]) hI.np]; simp [hn])
    (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := c.body M) (c := .nonzero .s3) (Q := Inv cs s₀ B D n st k F c0 xs n)
    (fun (m : Nat) (t : State) => ∃ j, m = n - j ∧ j < n ∧ Inv cs s₀ B D n st k F c0 xs j t)
    ?_ n s ⟨0, by omega_using [], by omega_using [hn], hI⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (body_wp cs hF hM hpre hpost hpw hqw hcomp hxs hj h) fun t' h' => ?_
  have e := ev (j := j + 1) (by omega_using [hj]) h'.np
  by_cases he : j + 1 = n
  · left; exact ⟨by rw [e]; simp [he], he ▸ h'⟩
  · right; exact ⟨by rw [e]; simp; omega_using [hj, he], n - (j + 1), by omega_using [hj, he], j + 1, rfl,
      by omega_using [hj, he], h'⟩

end VG.Proof.Modes.RISCV64
