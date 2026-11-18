module

public import VerifiedGarbage.Proof.Modes.X86.Modes
public import VerifiedGarbage.Proof.Modes.Wide
public import VerifiedGarbage.Proof.Modes.WideCtr
public import VerifiedGarbage.Proof.Modes.Ctr32
public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Modes.StepsChained
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# Block cipher modes on x86 (32-bit), a group of blocks at a time

`seqLevels_wp`: `Core.seqLevels` (`Impl/Modes/X86/Wide.lean`), for a core
`c` with `CoreSpec c`, takes all the steps of the mode `Mn`, one block
each, as `c.seq Mn` does (`seq_wp`), as on RISC-V
(`Proof/Modes/RISCV64/Wide.lean`).

* A wide step (`bodyWide_wp`) is a step of `Seq.lean` over a group of `g`
  blocks: the data's step is the group, the buffer's area its first `g`
  blocks (`lensB`), which the core enciphers as `ciphB` (`BufCipher`,
  `bufCipher_blocks`), and the count goes down by `g` (`InvW`).
  `loopWide_wp` takes the `q = n / g` groups of the `n` blocks left.
* `wideThen_ok`: a wide loop of the mode `Mw` (whose level `WideOk` states
  what it needs), then code that takes all the steps from wherever it
  starts (`StepsOk`), takes them all. The data splits at the first `g q`
  blocks: running `group st g F` on the groups is running `F` on their
  blocks (`run_group_blocks`), and `F` goes on from where the groups left
  the chaining value (`run_append`). `levels_ok` is a wide loop for each
  level in turn, and `narrow_ok` the steps of `Mn` (`loop_wp`).
* `seqWith_wp`: the function, around loops that take all the steps
  (`LoopsOk`), as `seq_wp`.

`cbcDecLevels_wp`, `cfbDecLevels_wp`, `ctrLevels_wp`, `ctr32Levels_wp`:
`Core.seqLevels` over CBC decryption, CFB decryption and counter mode,
whose levels fit the core (`LevelsFit`), with the conclusions of
`cbcDecChained_wp`, `cfbDec_wp`, `ctr_wp` and `ctr32_wp`.
-/

@[expose] public section

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot, Core.savedSlot]); omega_arith))

/-! ## A wide step's areas -/

/-- The areas' lengths in a wide step: a step's data, a block of chaining
value, and the buffer's first `Lb` bytes. -/
def lensB (c : Core) (st Lb : Nat) : Loc → Nat
  | .dat => st
  | .chn => 4 * c.bw
  | .buf => Lb

/-- What a run of wide steps keeps fixed (`Fixed`, for steps of any length
`st` on the buffer's first `Lb ≥ st` bytes): the scratch buffer at `B`, the
data at `D` of `q` steps of `st` bytes, the stack the core uses below `esp`,
and the layout. -/
structure FixedW (c : Core) (s₀ : State) (B D : BitVec 32) (q st Lb : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dataW : ∃ (R : Addr) (e ℓ : Nat), (⟨R, ℓ⟩ : Region) ∈ s₀.wr ∧ D.setWidth 64 = R + BitVec.ofNat 64 e ∧
    e + st * q ≤ ℓ ∧ ℓ < 2 ^ 64
  dataFit : D.toNat + st * q ≤ 2 ^ 32
  dataScr : Region.Disjoint (dataRegion D st q) ⟨B.setWidth 64, 4 * c.total⟩
  stkData : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) (dataRegion D st q)
  stkMode : Region.Disjoint (stkRegion (s₀.gpr .esp) c.stack) ⟨slotA B c.slots, 40⟩
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  step : 0 < st ∧ st ≤ Lb
  buf : Lb ≤ 4 * (c.bw * c.G)
  layout : Layout c

/-- The count of blocks: `q` groups of `g` in the `n` blocks left. -/
structure Cnt (q n g : Nat) : Prop where
  q : q = n / g
  n : n < 2 ^ 32
  pos : 0 < g
  g : g < 2 ^ 32

/-- The invariant after `j` of the `q` wide steps (`Inv`, with `n - g j`
blocks left). -/
structure InvW (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (q st n g : Nat) (k : cs.Key) (F : StepFn)
    (c0 : List Byte) (xs : List (List Byte)) (j : Nat) (s : State) : Prop where
  b : s.gpr sb = B
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  dp : s.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j)
  np : s.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (n - g * j)
  ready : cs.Ready s B k
  data : chunksAt st s.mem (D.setWidth 64) q = (run F c0 (xs.take j)).1 ++ xs.drop j
  chn : bytesAt s.mem (slotA B c.chnSlot) (4 * c.bw) = (run F c0 (xs.take j)).2
  frame : Frame (big c B D q st (s₀.gpr .esp)) s₀.mem s.mem

/-- Every byte of the areas at wide step `j`, as the code addresses them. -/
theorem areasOkW {s₀ s : State} {B D : BitVec 32} {q st Lb j : Nat} (hF : FixedW c s₀ B D q st Lb) (hj : j < q)
    (hb : s.gpr sb = B) (hesi : s.gpr .esi = D + BitVec.ofNat 32 (st * j)) (hwr : s.wr = s₀.wr) :
    AreasOk c s (lensB c st Lb) (areas c B D st j) allLocs := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hst := hF.step
  have hLb := hF.buf
  have hD := hF.dataFit
  obtain hjn : st * j + st ≤ st * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hW : ∀ l off w, off + w ≤ lensB c st Lb l →
      InRegions s.wr (areas c B D st j l + BitVec.ofNat 64 off) w := by
    intro l off w ho
    rw [hwr]
    cases l
    · simp only [lensB, areas] at ho ⊢
      obtain ⟨R, e, ℓ, hR, hDR, heℓ, hℓ⟩ := hF.dataW
      refine ⟨_, hR, ?_⟩
      rw [VG.Offset.add_add, hDR, VG.Offset.add_add]
      exact VG.Offset.contains_base _ (by omega_using [hjn, ho, heℓ]) (by omega_using [hjn, ho, heℓ, hℓ])
    · simp only [lensB, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by simp only [Core.chnSlot]; omega_using [hroom, hbw, ho])
    · simp only [lensB, areas] at ho ⊢
      refine ⟨_, hF.scr.wr, ?_⟩
      rw [VG.Offset.add_add]; exact slot_contains hfit (by omega_using [hroom, hbuf, hLb, ho])
  refine ⟨fun l off ho => ?_, fun l off w ho => ?_, fun l _ off w ho => hW l off w ho, fun l l' hne => ?_, fun l => ?_⟩
  · cases l
    · simp only [Core.loc, lensB, areas] at ho ⊢
      rw [hesi, Nat.zero_add, addr, VG.Offset.add_add, ← addr, addr_eq (by omega_using [hD, hjn, ho]), VG.Offset.add_add]
    · simp only [Core.loc, lensB, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by simp only [Core.chnSlot]; omega_using [hroom, hbw, ho])
    · simp only [Core.loc, lensB, areas] at ho ⊢
      rw [hb]
      exact addr_slot hfit (by omega_using [hroom, hbuf, hLb, ho])
  · obtain ⟨r, hr, hc⟩ := hW l off w ho
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have dD : ∀ d m, d + m ≤ 4 * c.total →
        Region.Disjoint ⟨D.setWidth 64 + BitVec.ofNat 64 (st * j), st⟩ ⟨B.setWidth 64 + BitVec.ofNat 64 d, m⟩ :=
      fun d m h => (hF.dataScr.sub_left (VG.Offset.sub_base _ hjn)).sub_right (slot_sub h)
    obtain dCB : Region.Disjoint ⟨slotA B c.chnSlot, 4 * c.bw⟩ ⟨slotA B c.buf, Lb⟩ :=
      VG.Offset.disjoint _ (.inr (by simp only [Core.chnSlot]; omega_using [hbuf, hLb]))
        (by simp only [Core.chnSlot]; omega_using [hfit, hroom, hbw]) (by omega_using [hfit, hroom, hbuf, hLb])
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [lensB, areas]
    · exact dD _ _ (by simp only [Core.chnSlot]; omega_using [hroom, hbw])
    · exact dD _ _ (by omega_using [hroom, hbuf, hLb])
    · exact (dD _ _ (by simp only [Core.chnSlot]; omega_using [hroom, hbw])).symm
    · exact dCB
    · exact (dD _ _ (by omega_using [hroom, hbuf, hLb])).symm
    · exact dCB.symm
  · cases l <;> simp only [lensB] <;> omega_using [hst, hbw, hLb, hbuf, hroom, hfit]

/-- What a wide step needs of the regions (`Regs`, with the buffer's first
`Lb` bytes for its area). -/
structure RegsW (c : Core) (B D : BitVec 32) (q st Lb j : Nat) (E : BitVec 32) : Prop where
  areasFine : ∀ r ∈ areaRegions (lensB c st Lb) (areas c B D st j) allLocs, ∃ r' ∈ fine c B D st j E, Region.Sub r r'
  areasW : ∀ r ∈ areaRegions (lensB c st Lb) (areas c B D st j) allLocs,
    ∃ r' ∈ [dataRegion D st q, ⟨B.setWidth 64, 4 * c.total⟩], Region.Sub r r'
  areasCore : ∀ r ∈ areaRegions (lensB c st Lb) (areas c B D st j) allLocs,
    Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)
  slotsW : ∀ r ∈ dnSlots c B, ∃ r' ∈ [dataRegion D st q, ⟨B.setWidth 64, 4 * c.total⟩], Region.Sub r r'
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
    ⟨slotA B c.nSlot, 4⟩], Region.Disjoint (dataRegion D st q) r
  datData : Region.Sub (datRegion D st j) (dataRegion D st q)
  toBig : ∀ r ∈ fine c B D st j E ++ dnSlots c B, ∃ r' ∈ big c B D q st E, Region.Sub r r'

theorem regsW {s₀ : State} {B D : BitVec 32} {q st Lb j : Nat} (hF : FixedW c s₀ B D q st Lb) (hj : j < q) :
    RegsW c B D q st Lb j (s₀.gpr .esp) := by
  have hL := hF.layout
  have hfit := hF.scr.fit
  have hDf := hF.dataFit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hLb := hF.buf
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hjn : st * j + st ≤ st * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain subDat : Region.Sub (datRegion D st j) (dataRegion D st q) := VG.Offset.sub_base _ hjn
  obtain subChn : Region.Sub (chnRegion c B) (dnRegion c B) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  obtain subBuf : Region.Sub ⟨slotA B c.buf, Lb⟩ (coreRegion c B) := VG.Offset.sub_base _ (by slot_omega)
  obtain subBlk : Region.Sub ⟨slotA B c.buf, Lb⟩ (blkRegion c B) :=
    Region.sub_prefix (by rw [Nat.mul_assoc]; exact hLb)
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
  obtain dataDn : Region.Disjoint (dataRegion D st q) (dnRegion c B) := hF.dataScr.sub_right dnScr
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
  · simp only [areaRegions, allLocs, List.map, areas, lensB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, m2, fun _ h => h⟩
    · exact ⟨_, m1, subBuf⟩
  · simp only [areaRegions, allLocs, List.map, areas, lensB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, subDat⟩
    · exact ⟨_, m1, scrSub subChn⟩
    · exact ⟨_, m1, fun x hx => coreScr x (subBuf x hx)⟩
  · simp only [areaRegions, allLocs, List.map, areas, lensB, List.mem_cons, List.not_mem_nil, or_false] at hr
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

/-! ## The stages of a wide step -/

/-- In the middle of a wide step from `s` (`Mid`, with the buffer's first
`Lb` bytes for its area). -/
structure MidW (cs : CoreSpec c) (s₀ : State) (B D : BitVec 32) (st Lb j : Nat) (k : cs.Key) (s : State)
    (a : Areas) (s' : State) : Prop where
  b : s'.gpr sb = B
  esp : s'.gpr .esp = s₀.gpr .esp
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ready : cs.Ready s' B k
  agree : Agree (lensB c st Lb) (cont (areas c B D st j) s'.mem) a
  frame : Frame (fine c B D st j (s₀.gpr .esp)) s.mem s'.mem

theorem toWrW {s₀ t : State} {B D : BitVec 32} {q st Lb : Nat} (hF : FixedW c s₀ B D q st Lb) (hw : t.wr = s₀.wr)
    {rs : List Region} (h : ∀ r ∈ rs, ∃ r' ∈ [dataRegion D st q, ⟨B.setWidth 64, 4 * c.total⟩], Region.Sub r r') :
    ∀ r ∈ rs, ∃ r' ∈ t.wr, Region.Sub r r' := fun r hr => by
  obtain ⟨r', hr', hs⟩ := h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hw]
  rcases hr' with rfl | rfl
  · obtain ⟨R, e, ℓ, hR, hDR, heℓ, -⟩ := hF.dataW
    refine ⟨_, hR, fun a ha => ?_⟩
    have := VG.Offset.sub_base R (n := st * q) heℓ
    rw [← hDR] at this
    exact this a (hs a ha)
  · exact ⟨_, hF.scr.wr, hs⟩

/-- The core's block cipher, as the cipher `ciphB` on the buffer's first
`Lb` bytes: what `crypt_wp` gives of the buffer's blocks determines them. -/
def BufCipher (c : Core) (ciph ciphB : Spec.Cbc.Cipher) (Lb : Nat) : Prop :=
  ∀ (B : BitVec 32) (m m' : Mem), (∀ j < c.G, bytesAt m' (blkAddr c B j) (4 * c.bw) =
    ciph (bytesAt m (blkAddr c B j) (4 * c.bw))) →
    bytesAt m' (slotA B c.buf) Lb = ciphB (bytesAt m (slotA B c.buf) Lb)

/-- The core's block cipher on `g` blocks of its buffer. -/
theorem bufCipher_blocks {ciph : Spec.Cbc.Cipher} {g : Nat} (hg : g ≤ c.G) :
    BufCipher c ciph (blocksCipher (4 * c.bw) g ciph) (4 * c.bw * g) := fun B m m' h => by
  rw [Nat.mul_comm (4 * c.bw) g, blocksCipher, bytesAt_split, bytesAt_flatten]
  congr 1
  simp only [chunksAt, List.map_map]
  exact List.map_congr_left fun j hj => h j (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hg)

section
variable (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {B D : BitVec 32} {q st Lb n g : Nat}
  {k : cs.Key} {c0 : List Byte} {xs : List (List Byte)}

theorem preW_wp (hF : FixedW c s₀ B D q st Lb) (hpre : ∀ o ∈ M.pre, o.InBounds (lensB c st Lb)) {j : Nat}
    (hj : j < q) {s : State} (hI : InvW cs s₀ B D q st n g k F c0 xs j s) :
    WP isa (.block (c.load ++ c.opsCode M.pre)) s
      (MidW cs s₀ B D st Lb j k s (applyOps M.pre (cont (areas c B D st j) s.mem))) := by
  obtain hR := regsW hF hj
  refine WP.syms_intro ?_
  refine load_wp hI.b ⟨by rw [hI.wr]; exact hF.scr.wr, hF.scr.fit⟩ hF.layout fun s₁ esi₁ _ g₁ m₁ rd₁ wr₁ => ?_
  rw [← List.append_nil (c.opsCode M.pre)]
  obtain b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide) (by decide)]; exact hI.b
  obtain hA : AreasOk c s₁ (lensB c st Lb) (areas c B D st j) allLocs :=
    areasOkW hF hj b₁ (by rw [esi₁, hI.dp]) (by rw [wr₁, hI.wr])
  refine opsCode_wp c (fun o ho => ⟨hpre o ho, mem_allLocs _⟩) hA fun s₂ a₂ f₂ g₂ rd₂ wr₂ =>
    WP.block_nil fun sy₂ => ?_
  rw [m₁] at a₂ f₂
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), hI.esp]
  exact ⟨by rw [g₂ _ (by decide) (by decide)]; exact b₁, esp₂, by rw [rd₂, rd₁, hI.rd], by rw [wr₂, wr₁, hI.wr],
    cs.ready_frame hI.ready (by rw [esp₂, hI.esp]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) sy₂ f₂
      (toWrW hF hI.wr hR.areasW) hR.areasCore, a₂, f₂.sub hR.areasFine⟩

theorem cryptW_step (hF : FixedW c s₀ B D q st Lb) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB Lb) {j : Nat} (hj : j < q) {s s₂ : State} {a : Areas}
    (hm : MidW cs s₀ B D st Lb j k s a s₂) :
    WP isa c.crypt s₂ (MidW cs s₀ B D st Lb j k s (cryptBuf Lb ciphB a)) := by
  obtain hR := regsW hF hj
  have hDf := hF.dataFit
  obtain hjn : st * j + st ≤ st * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  refine WP.mono (cs.crypt_wp hm.b ⟨by rw [hm.wr]; exact hF.scr.wr, hF.scr.fit⟩ hm.ready
    (by rw [hm.esp]; exact hF.stack)) fun s₃ ⟨b₃, esp₃, ready₃, f₃, enc₃, rd₃, wr₃⟩ => ?_
  rw [hm.esp] at f₃
  refine ⟨b₃, by rw [esp₃, hm.esp], by rw [rd₃, hm.rd], by rw [wr₃, hm.wr], ready₃, ?_,
    hm.frame.trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp, fun _ h => h⟩)⟩
  refine Agree.trans (b := cryptBuf Lb ciphB (cont (areas c B D st j) s₂.mem)) ?_
    (cryptBuf_agree (by simp [lensB]) _ hm.agree)
  intro l i hi
  cases l
  · simp only [cryptBuf, cont, areas, lensB] at hi ⊢
    exact f₃.bytes (R := datRegion D st j) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.datCore
      · exact hR.datStk) (by show st ≤ 2 ^ 64; omega_using [hDf, hjn]) hi
  · simp only [cryptBuf, cont, areas, lensB] at hi ⊢
    exact f₃.bytes (R := chnRegion c B) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR.chnCore
      · exact hR.chnStk) (by show 4 * c.bw ≤ 2 ^ 64; have := hF.layout.bw; omega_using [this]) hi
  · simp only [lensB] at hi
    obtain e := hB B s₂.mem s₃.mem enc₃
    simp only [cryptBuf, cont, areas, ite_true]
    rw [← bytesAt_getD s₃.mem (slotA B c.buf) hi, e]
    rfl

/-- Input step `j`, from the invariant. -/
theorem InvW.input {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {q st n g : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s : State} (hI : InvW cs s₀ B D q st n g k F c0 xs j s)
    (hxs : xs.length = q) (hj : j < q) :
    bytesAt s.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st = xs[j]'(by omega_using [hxs, hj]) := by
  obtain hl : (run F c0 (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega_using [hxs, hj]
  obtain e := congrArg (·[j]?) hI.data
  simp only [List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self, List.getElem?_drop, Nat.add_zero] at e
  rw [List.getElem?_eq_getElem (by rw [chunksAt_length]; exact hj), List.getElem?_eq_getElem (by omega_using [hxs, hj]),
    chunksAt_getElem hj] at e
  exact Option.some.inj e

/-- Fewer than `g` blocks are left after `j` groups iff `j` is all of them. -/
theorem left_lt_iff {n g j : Nat} (hg : 0 < g) : n - g * j < g ↔ n / g ≤ j := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hg, Nat.succ_mul, Nat.mul_comm j g]
  omega

/-- On by `st` bytes, `g` blocks fewer, both stored back, and the blocks
left compared with `g`. -/
theorem advanceWide_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    (st g : Nat) {Q : State → Prop}
    (k : ∀ s', s'.cf = some (decide ((s.gpr .ebp - BitVec.ofNat 32 g).toNat < (BitVec.ofNat 32 g).toNat)) →
      (∀ r, r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (slotA B c.dSlot) (s.gpr .esi + BitVec.ofNat 32 st)).writeW (slotA B c.nSlot)
        (s.gpr .ebp - BitVec.ofNat 32 g) → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block (c.advanceWide st g)) s Q := by
  have := hL.room
  obtain hd : c.dSlot < c.total := by simp only [Core.dSlot]; omega_using [this]
  obtain hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega_using [this]
  simp only [Core.advanceWide, slotAt, at_]
  refine wp_addi fun s₁ u₁ => wp_subi fun s₂ u₂ _ _ => ?_
  obtain b₂ : s₂.gpr sb = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  refine wp_stm b₂ (by rw [u₂.wr, u₁.wr]; exact slot_inW hS hd) fun s₃ u₃ => ?_
  refine wp_stm (B := B) (by rw [u₃.gpr]; exact b₂) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hn)
    fun s₄ u₄ => wp_cmpi fun s₅ f₅ c₅ _ => WP.block_nil ?_
  refine k s₅ (by rw [c₅, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)]) (fun r h1 h2 => by
      rw [f₅.gpr, u₄.gpr, u₃.gpr, u₂.other r h2, u₁.other r h1]) ?_ (by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide),
    addr_slotA hS.fit hd, addr_slotA hS.fit hn]

theorem postW_wp (hF : FixedW c s₀ B D q st Lb) (hC : Cnt q n g) (hM : M.step = st)
    (hpost : ∀ o ∈ M.post, o.InBounds (lensB c st Lb)) {ciphB : Spec.Cbc.Cipher}
    (hcomp : ComputesB M (4 * c.bw) Lb ciphB F) (hxs : xs.length = q) {j : Nat} (hj : j < q) {s s₃ : State}
    (hI : InvW cs s₀ B D q st n g k F c0 xs j s)
    (hm : MidW cs s₀ B D st Lb j k s (cryptBuf Lb ciphB (applyOps M.pre (cont (areas c B D st j) s.mem))) s₃) :
    WP isa (.block (c.load ++ c.opsCode M.post ++ c.advanceWide M.step g)) s₃
      fun s' => InvW cs s₀ B D q st n g k F c0 xs (j + 1) s' ∧ s'.cf = some (decide (q ≤ j + 1)) := by
  obtain hR := regsW hF hj
  have hL := hF.layout
  obtain hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  have hDf := hF.dataFit
  obtain hjn : st * j + st ≤ st * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  obtain hgq : g * q ≤ n := by rw [hC.q]; exact Nat.mul_div_le _ _
  obtain hgj : g * j + g ≤ g * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have hn32 := hC.n
  have hg32 := hC.g
  obtain hS : ∀ {t : State}, t.wr = s₀.wr → ScrIn t B c.total := fun h => ⟨by rw [h]; exact hF.scr.wr, hF.scr.fit⟩
  obtain dp₃ : s₃.mem.readW (slotA B c.dSlot) 32 = D + BitVec.ofNat 32 (st * j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.dKeep (by decide), hI.dp]
  obtain np₃ : s₃.mem.readW (slotA B c.nSlot) 32 = BitVec.ofNat 32 (n - g * j) := by
    rw [hm.frame.readW (Region.contains_self _ _) hR.nKeep (by decide), hI.np]
  rw [List.append_assoc]
  refine WP.syms_intro ?_
  refine load_wp hm.b (hS hm.wr) hL fun s₄ esi₄ ebp₄ g₄ m₄ rd₄ wr₄ => ?_
  obtain b₄ : s₄.gpr sb = B := by rw [g₄ _ (by decide) (by decide)]; exact hm.b
  obtain hA : AreasOk c s₄ (lensB c st Lb) (areas c B D st j) allLocs :=
    areasOkW hF hj b₄ (by rw [esi₄, dp₃]) (by rw [wr₄, hm.wr])
  refine opsCode_wp c (fun o ho => ⟨hpost o ho, mem_allLocs _⟩) hA fun s₅ a₅ f₅ g₅ rd₅ wr₅ => ?_
  rw [m₄] at a₅ f₅
  obtain b₅ : s₅.gpr sb = B := by rw [g₅ _ (by decide) (by decide)]; exact b₄
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, hm.wr]
  refine advanceWide_wp b₅ (hS wr₅') hL M.step g fun s₆ c₆ g₆ m₆ rd₆ wr₆ => ?_
  intro sy₆
  obtain esi₅ : s₅.gpr .esi = D + BitVec.ofNat 32 (st * j) := by rw [g₅ _ (by decide) (by decide), esi₄, dp₃]
  obtain ebp₅ : s₅.gpr .ebp = BitVec.ofNat 32 (n - g * j) := by rw [g₅ _ (by decide) (by decide), ebp₄, np₃]
  obtain left₅ : BitVec.ofNat 32 (n - g * j) - BitVec.ofNat 32 g = BitVec.ofNat 32 (n - g * (j + 1)) := by
    rw [Wp.sub_ofNat (by omega_using [hgq, hgj]), Nat.mul_succ, Nat.sub_sub]
  rw [esi₅, ebp₅, left₅, hM] at m₆
  rw [ebp₅, left₅, Wp.toNat_ofNat_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn32), Wp.toNat_ofNat_lt hg32] at c₆
  -- The step's outputs.
  let A := areas c B D st j
  obtain hstep : Agree (lensB c st Lb) (cont A s₅.mem) (stepA M Lb ciphB (cont A s.mem)) :=
    Agree.trans a₅ (applyOps_agree hpost hm.agree)
  obtain ⟨hc1, hc2⟩ := hcomp (cont A s.mem)
  rw [hM] at hc1 hc2
  obtain xj : rd (cont A s.mem) .dat st = xs[j]'(by omega_using [hxs, hj]) := hI.input hxs hj
  have cj : rd (cont A s.mem) .chn (4 * c.bw) = (run F c0 (xs.take j)).2 := hI.chn
  rw [xj, cj] at hc1 hc2
  obtain out₅ : bytesAt s₅.mem (D.setWidth 64 + BitVec.ofNat 64 (st * j)) st =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1 := by
    rw [← hc1]; exact rd_agree hstep (l := .dat) (Nat.le_refl _)
  obtain chn₅ : bytesAt s₅.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
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
  obtain chn₆ : bytesAt s₆.mem (slotA B c.chnSlot) (4 * c.bw) =
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2 := by
    rw [← chn₅]
    exact List.map_congr_left fun i hi => keep6 dChn (by show 4 * c.bw ≤ 2 ^ 64; omega_using [hbw]) (List.mem_range.mp hi)
  obtain hrun : run F c0 (xs.take (j + 1)) =
      ((run F c0 (xs.take j)).1 ++ [(F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).1],
      (F (run F c0 (xs.take j)).2 (xs[j]'(by omega_using [hxs, hj]))).2) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega_using [hxs, hj]), Option.toList_some, run_snoc]
  obtain gg : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₆ r h1 h2, g₅ r h3 h4, g₄ r h1 h2]
  show InvW cs s₀ B D q st n g k F c0 xs (j + 1) s₆ ∧ s₆.cf = some (decide (q ≤ j + 1))
  refine ⟨⟨by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.b,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide)]; exact hm.esp,
    by rw [rd₆, rd₅, rd₄, hm.rd], by rw [wr₆, wr₅'], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m₆, readW_write_sep hR.dn, Mem.readW_writeW_self32, VG.Offset.add_add, Nat.mul_succ]
  · rw [m₆, Mem.readW_writeW_self32]
  · exact cs.ready_frame hm.ready (by rw [gg _ (by decide) (by decide) (by decide) (by decide)])
      (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) sy₆
      ((f₅.mono fun r hr => List.mem_append_left _ hr).trans (f₆.mono fun r hr => List.mem_append_right _ hr))
      (fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact toWrW hF hm.wr hR.areasW r h
        · exact toWrW hF hm.wr hR.slotsW r h)
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
  · rw [c₆]
    exact congrArg some (decide_eq_decide.mpr (by rw [hC.q]; exact left_lt_iff hC.pos))

/-! ## The wide step and its loop -/

theorem bodyWide_wp (hF : FixedW c s₀ B D q st Lb) (hC : Cnt q n g) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB Lb)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lensB c st Lb)) (hpost : ∀ o ∈ M.post, o.InBounds (lensB c st Lb))
    (hcomp : ComputesB M (4 * c.bw) Lb ciphB F) (hxs : xs.length = q) {j : Nat} (hj : j < q) {s : State}
    (hI : InvW cs s₀ B D q st n g k F c0 xs j s) :
    WP isa (c.bodyWide M g) s
      fun s' => InvW cs s₀ B D q st n g k F c0 xs (j + 1) s' ∧ s'.cf = some (decide (q ≤ j + 1)) := by
  unfold Core.bodyWide
  exact WP.seq (WP.mono (preW_wp cs hF hpre hj hI) fun _ h₂ =>
    WP.seq (WP.mono (cryptW_step cs hF hB hj h₂) fun _ h₃ => postW_wp cs hF hC hM hpost hcomp hxs hj hI h₃))

/-- The invariant, through a change of registers (but `sb` and `esp`) and
flags. -/
theorem InvW.congr {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {q st n g : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s s' : State} (hI : InvW cs s₀ B D q st n g k F c0 xs j s)
    (hb : s'.gpr sb = s.gpr sb) (hesp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) : InvW cs s₀ B D q st n g k F c0 xs j s' :=
  ⟨hb.trans hI.b, hesp.trans hI.esp, hrd.trans hI.rd, hwr.trans hI.wr, by rw [hm]; exact hI.dp,
    by rw [hm]; exact hI.np,
    cs.ready_frame (rs := []) hI.ready hesp hrd hwr hsy (by rw [hm]; exact Frame.refl _ _) (fun _ h => nomatch h)
      (fun _ h => nomatch h), by rw [hm]; exact hI.data, by rw [hm]; exact hI.chn, by rw [hm]; exact hI.frame⟩

theorem Inv.congr {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {n st : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {j : Nat} {s s' : State} (hI : Inv cs s₀ B D n st k F c0 xs j s)
    (hb : s'.gpr sb = s.gpr sb) (hesp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsy : s'.syms = s.syms) : Inv cs s₀ B D n st k F c0 xs j s' :=
  ⟨hb.trans hI.b, hesp.trans hI.esp, hrd.trans hI.rd, hwr.trans hI.wr, by rw [hm]; exact hI.dp,
    by rw [hm]; exact hI.np,
    cs.ready_frame (rs := []) hI.ready hesp hrd hwr hsy (by rw [hm]; exact Frame.refl _ _) (fun _ h => nomatch h)
      (fun _ h => nomatch h), by rw [hm]; exact hI.data, by rw [hm]; exact hI.chn, by rw [hm]; exact hI.frame⟩

/-- The blocks left, from their slot, to `eax`. -/
theorem leftLoad_wp {s : State} {B : BitVec 32} (hb : s.gpr sb = B) (hS : ScrIn s B c.total) (hL : Layout c)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .eax (s.mem.readW (slotA B c.nSlot) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .eax (.mem (slotAt c.nSlot)) :: is)) s Q := by
  have := hL.room
  obtain hn : c.nSlot < c.total := by simp only [Core.nSlot]; omega_using [this]
  simp only [slotAt, at_]
  refine wp_ldm hb (slot_in hS hn) fun s₁ u₁ => ?_
  rw [addr_slotA hS.fit hn] at u₁
  exact k s₁ u₁

/-- The steps of `g` blocks, `q = n / g` of them. The data's layout is
needed only if there is a group. -/
theorem loopWide_wp (hS : ScrIn s₀ B c.total) (hL : Layout c) (hC : Cnt q n g)
    (hF : q ≠ 0 → FixedW c s₀ B D q st Lb) (hM : M.step = st) {ciphB : Spec.Cbc.Cipher}
    (hB : BufCipher c (cs.cipher k) ciphB Lb)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lensB c st Lb)) (hpost : ∀ o ∈ M.post, o.InBounds (lensB c st Lb))
    (hcomp : ComputesB M (4 * c.bw) Lb ciphB F) (hxs : xs.length = q) {s : State}
    (hI : InvW cs s₀ B D q st n g k F c0 xs 0 s) :
    WP isa (c.loopWide M g) s (InvW cs s₀ B D q st n g k F c0 xs q) := by
  unfold Core.loopWide Core.leftCmp
  refine WP.seq (leftLoad_wp hI.b ⟨by rw [hI.wr]; exact hS.wr, hS.fit⟩ hL fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_)
  obtain hI₂ : InvW cs s₀ B D q st n g k F c0 xs 0 s₂ :=
    hI.congr (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms])
  obtain cf₂ : s₂.cf = some (decide (q ≤ 0)) := by
    rw [c₂, u₁.gpr, hI.np, Wp.toNat_ofNat_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hC.n), Wp.toNat_ofNat_lt hC.g]
    exact congrArg some (decide_eq_decide.mpr (by rw [hC.q]; exact left_lt_iff hC.pos))
  by_cases hq0 : q = 0
  · subst hq0
    exact WP.ite true (by show VG.X86.eval .b s₂ = _; simp [VG.X86.eval, cf₂]) (fun _ => WP.block_nil hI₂)
      (fun h => by cases h)
  refine WP.ite false (by show VG.X86.eval .b s₂ = _; simp [VG.X86.eval, cf₂, hq0]) (fun h => by cases h)
    fun _ => ?_
  have hFq := hF hq0
  refine WP.loop (M := isa) (body := c.bodyWide M g) (c := .ae) (Q := InvW cs s₀ B D q st n g k F c0 xs q)
    (fun (m : Nat) (t : State) => ∃ j, m = q - j ∧ j < q ∧ InvW cs s₀ B D q st n g k F c0 xs j t)
    ?_ q s₂ ⟨0, by omega_using [], by omega_using [hq0], hI₂⟩
  rintro _ t ⟨j, rfl, hj, h⟩
  refine WP.mono (bodyWide_wp cs hFq hC hM hB hpre hpost hcomp hxs hj h) fun t' ⟨h', hc'⟩ => ?_
  obtain ev : isa.eval .ae t' = some !decide (q ≤ j + 1) := by
    show VG.X86.eval .ae t' = _; simp [VG.X86.eval, hc']
  by_cases he : j + 1 = q
  · left; exact ⟨by rw [ev]; simp [he], he ▸ h'⟩
  · have hlt : ¬ q ≤ j + 1 := by omega_using [hj, he]
    right; exact ⟨by rw [ev]; simp [hlt], q - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], h'⟩

end

/-! ## A wide loop, then the rest -/

section
variable (cs : CoreSpec c) {Mw Mn : Mode} {F : StepFn} {k : cs.Key} {g : Nat}

/-- The code `P` takes all the steps of `Mn` from any state with `n` blocks
left at `D`, whose layout is needed only if there is one. -/
def StepsOk (Mn : Mode) (F : StepFn) (k : cs.Key) (P : Prog isa) : Prop :=
  ∀ {s : State} {B D : BitVec 32} {n : Nat} {c0 : List Byte} {xs : List (List Byte)},
    ScrIn s B c.total → Layout c → n < 2 ^ 32 → (n ≠ 0 → Fixed c s B D n Mn.step) →
    Inv cs s B D n Mn.step k F c0 xs 0 s → WP isa P s (Inv cs s B D n Mn.step k F c0 xs n)

/-- What a wide loop of the mode `Mw`, on groups of `g` blocks of the mode
`Mn`, needs. -/
structure WideOk (Mn : Mode) (F : StepFn) (k : cs.Key) (Mw : Mode) (g : Nat) : Prop where
  pos : 0 < g
  G : g ≤ c.G
  step : Mw.step = g * Mn.step
  pre : ∀ o ∈ Mw.pre, o.InBounds (lensB c Mw.step (4 * c.bw * g))
  post : ∀ o ∈ Mw.post, o.InBounds (lensB c Mw.step (4 * c.bw * g))
  ciph : ∃ ciphB, ComputesB Mw (4 * c.bw) (4 * c.bw * g) ciphB (group Mn.step g F) ∧
    BufCipher c (cs.cipher k) ciphB (4 * c.bw * g)

/-- The inputs, from the invariant before the first step. -/
theorem Inv.inputs {cs : CoreSpec c} {s₀ : State} {B D : BitVec 32} {n st : Nat} {k : cs.Key} {F : StepFn}
    {c0 : List Byte} {xs : List (List Byte)} {s : State} (hI : Inv cs s₀ B D n st k F c0 xs 0 s) :
    chunksAt st s.mem (D.setWidth 64) n = xs := by
  have e := hI.data
  simpa only [List.take_zero, run, List.nil_append, List.drop_zero] using e

/-- The steps of `Mn`, one block each. -/
theorem narrow_ok (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step))
    (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step)) (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) :
    StepsOk cs Mn F k (c.steps Mn) := by
  intro s B D n c0 xs hS hL hn hFx hI
  obtain hxs : xs.length = n := by rw [← hI.inputs, chunksAt_length]
  unfold Core.steps Core.leftTest
  refine WP.seq (leftLoad_wp hI.b hS hL fun s₁ u₁ => wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  obtain hI₂ : Inv cs s B D n Mn.step k F c0 xs 0 s₂ :=
    hI.congr (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd]) (by rw [f₂.wr, u₁.wr]) (by rw [f₂.syms, u₁.syms])
  obtain zf₂ : s₂.zf = some (decide (n = 0)) := by
    rw [z₂, u₁.gpr, hI.np, BitVec.and_self, Nat.sub_zero, Wp.ofNat_beq_zero hn]
  by_cases hn0 : n = 0
  · subst hn0
    exact WP.ite true (by show VG.X86.eval .e s₂ = _; simp [VG.X86.eval, zf₂]) (fun _ => WP.block_nil hI₂)
      (fun h => by cases h)
  · exact loop_wp cs (hFx hn0) rfl hpre hpost hcomp hxs hI₂ zf₂

/-- A wide loop of `Mw`, then `rest` on the blocks it leaves. -/
theorem wideThen_ok {rest : Prog isa} (hw : WideOk cs Mn F k Mw g) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hrest : StepsOk cs Mn F k rest) : StepsOk cs Mn F k (.seq (c.loopWide Mw g) rest) := by
  intro s₂ B D n iv xs hS hL hn hFx hI
  obtain ⟨hg, hG, hstw, hpreW, hpostW, ciphB, hcompW, hB⟩ := hw
  obtain hbw : 0 < c.bw ∧ c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]
  obtain hg32 : g < 2 ^ 32 := by
    have h1 := hL.buf_le
    have h2 := hL.room
    have h3 := hS.fit
    have h4 : c.G ≤ c.bw * c.G := Nat.le_mul_of_pos_left _ hbw.1
    omega_using [hG, h1, h2, h3, h4]
  obtain hivl : iv.length = 4 * c.bw := by
    have e : bytesAt s₂.mem (slotA B c.chnSlot) (4 * c.bw) = iv := hI.chn
    rw [← e]; simp [bytesAt]
  obtain hxs : xs.length = n := by rw [← hI.inputs, chunksAt_length]
  generalize hsd : Mn.step = st at hFx hI hstw hcompW hFb ⊢
  -- The groups and the blocks left.
  obtain ⟨q, hqd⟩ : ∃ q, q = n / g := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = n - g * q := ⟨_, rfl⟩
  obtain hq : g * q ≤ n := by rw [hqd]; exact Nat.mul_div_le _ _
  obtain hnr : n = g * q + r := by omega_using [hq, hrd]
  obtain hwq' : Mw.step * q = st * (g * q) := by rw [hstw, Nat.mul_assoc, Nat.mul_left_comm]
  obtain hwq : Mw.step * q + st * r = st * n := by rw [hwq', ← Nat.mul_add, ← hnr]
  obtain hn0 : ∀ {m : Nat}, m ≠ 0 → (m = q ∨ m = r) → n ≠ 0 := fun hm hor h0 => by
    subst h0
    rcases hor with rfl | rfl
    · exact hm (by rw [hqd, Nat.zero_div])
    · exact hm (by rw [hrd, Nat.zero_sub])
  have hC : Cnt q n g := ⟨hqd, hn, hg, hg32⟩
  obtain coreScr : Region.Sub (coreRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ :=
    Region.sub_prefix (by have := hL.room; omega_using [this])
  obtain dnScr : Region.Sub (dnRegion c B) ⟨B.setWidth 64, 4 * c.total⟩ :=
    VG.Offset.sub_base _ (by have := hL.room; simp only [Core.dSlot]; omega_using [this, hbw])
  -- The groups.
  obtain hFw : q ≠ 0 → FixedW c s₂ B D q Mw.step (4 * c.bw * g) := fun hq0 => by
    have hFx := hFx (hn0 hq0 (.inl rfl))
    obtain ⟨R, e, ℓ, hR, hDR, heℓ, hℓ⟩ := hFx.dataW
    have hDf := hFx.dataFit
    have hst := hFx.step
    exact ⟨hS, ⟨R, e, ℓ, hR, hDR, by omega_using [heℓ, hwq], hℓ⟩, by omega_using [hDf, hwq],
      hFx.dataScr.sub_left (Region.sub_prefix (by omega_using [hwq])),
      hFx.stkData.sub_right (Region.sub_prefix (by omega_using [hwq])), hFx.stkMode, hFx.stack,
      ⟨by rw [hstw]; exact Nat.mul_pos hg hst.1,
        by rw [hstw, Nat.mul_comm (4 * c.bw) g]; exact Nat.mul_le_mul_left _ hst.2⟩,
      by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG), hL⟩
  generalize hxw : chunksAt Mw.step s₂.mem (D.setWidth 64) q = xw
  obtain hIw : InvW cs s₂ B D q Mw.step n g k (group st g F) iv xw 0 s₂ := by
    refine ⟨hI.b, rfl, rfl, rfl, ?_, ?_, hI.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [hI.dp, Nat.mul_zero, Nat.mul_zero]
    · rw [hI.np, Nat.mul_zero]
    · simp only [hxw, List.take_zero, run, List.nil_append, List.drop_zero]
    · rw [hI.chn]; rfl
  obtain hxwl : xw.length = q := by rw [← hxw, chunksAt_length]
  refine WP.seq (WP.mono (loopWide_wp cs hS hL hC hFw rfl hB hpreW hpostW hcompW hxwl hIw) fun s₃ h₃ => ?_)
  -- The blocks left.
  obtain ⟨D', hD'⟩ : ∃ D' : BitVec 32, D' = D + BitVec.ofNat 32 (Mw.step * q) := ⟨_, rfl⟩
  obtain hS₃ : ScrIn s₃ B c.total := ⟨by rw [h₃.wr]; exact hS.wr, hS.fit⟩
  obtain hD'64 : r ≠ 0 → D'.setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (Mw.step * q) := fun hr => by
    have hFx := hFx (hn0 hr (.inr rfl))
    have hDf := hFx.dataFit
    have hpos : 0 < st * r := Nat.mul_pos hFx.step.1 (Nat.pos_of_ne_zero hr)
    rw [hD']
    exact addr_eq (by omega_using [hDf, hwq, hpos])
  obtain hsubN : Region.Sub (dataRegion D' st r) (dataRegion D st n) := by
    by_cases hr : r = 0
    · intro a ha
      have h0 : st * r = 0 := by rw [hr, Nat.mul_zero]
      simp only [Region.Contains] at ha
      omega_using [ha, h0]
    · show Region.Sub ⟨D'.setWidth 64, st * r⟩ ⟨D.setWidth 64, st * n⟩
      rw [hD'64 hr]
      exact VG.Offset.sub_base _ (by omega_using [hwq])
  obtain hFn : r ≠ 0 → Fixed c s₃ B D' r st := fun hr => by
    have hFx := hFx (hn0 hr (.inr rfl))
    obtain ⟨R, e, ℓ, hR, hDR, heℓ, hℓ⟩ := hFx.dataW
    have hDf := hFx.dataFit
    have hpos : 0 < st * r := Nat.mul_pos hFx.step.1 (Nat.pos_of_ne_zero hr)
    obtain hDn : D'.toNat = D.toNat + Mw.step * q := by
      rw [hD', VG.Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := Mw.step * q) (by omega_using [hDf, hwq, hpos]),
        Nat.mod_eq_of_lt (by omega_using [hDf, hwq, hpos])]
    exact ⟨hS₃, ⟨R, e + Mw.step * q, ℓ, by rw [h₃.wr]; exact hR, by rw [hD'64 hr, hDR, VG.Offset.add_add],
        by omega_using [heℓ, hwq], hℓ⟩, by omega_using [hDn, hDf, hwq], hFx.dataScr.sub_left hsubN,
      by rw [h₃.esp]; exact hFx.stkData.sub_right hsubN, by rw [h₃.esp]; exact hFx.stkMode,
      by rw [h₃.esp]; exact hFx.stack, hFx.step, hL⟩
  generalize hxn : chunksAt st s₃.mem (D'.setWidth 64) r = xn
  obtain hIn : Inv cs s₃ B D' r st k F (run (group st g F) iv xw).2 xn 0 s₃ := by
    refine ⟨h₃.b, rfl, rfl, rfl, ?_, ?_, h₃.ready, ?_, ?_, Frame.refl _ _⟩
    · rw [h₃.dp, Nat.mul_zero, BitVec.add_zero, hD']
    · rw [h₃.np, Nat.sub_zero, hrd]
    · simp only [hxn, List.take_zero, run, List.nil_append, List.drop_zero]
    · rw [h₃.chn, List.take_of_length_le (Nat.le_of_eq hxwl)]; rfl
  obtain hxnl : xn.length = r := by rw [← hxn, chunksAt_length]
  subst hsd
  refine WP.mono (hrest hS₃ hL (by omega_using [hn, hrd]) hFn hIn) fun s₄ d₄ => ?_
  -- What the two parts left.
  obtain data₃ : chunksAt Mw.step s₃.mem (D.setWidth 64) q = (run (group Mn.step g F) iv xw).1 := by
    rw [h₃.data, List.take_of_length_le (Nat.le_of_eq hxwl), List.drop_of_length_le (Nat.le_of_eq hxwl),
      List.append_nil]
  obtain data₄ : chunksAt Mn.step s₄.mem (D'.setWidth 64) r =
      (run F (run (group Mn.step g F) iv xw).2 xn).1 := by
    rw [d₄.data, List.take_of_length_le (Nat.le_of_eq hxnl), List.drop_of_length_le (Nat.le_of_eq hxnl),
      List.append_nil]
  obtain chn₄ : bytesAt s₄.mem (slotA B c.chnSlot) (4 * c.bw) = (run F (run (group Mn.step g F) iv xw).2 xn).2 := by
    rw [d₄.chn, List.take_of_length_le (Nat.le_of_eq hxnl)]
  -- The blocks left are as they were before the groups.
  obtain hxn₂ : chunksAt Mn.step s₂.mem (D'.setWidth 64) r = xn := by
    rw [← hxn]
    by_cases hr : r = 0
    · rw [hr]; rfl
    · have hFx := hFx (hn0 hr (.inr rfl))
      have hDf := hFx.dataFit
      refine (chunksAt_frame h₃.frame (fun R hR => ?_) (by omega_using [hDf, hwq])).symm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact (hFx.dataScr.sub_left hsubN).sub_right coreScr
      · exact (hFx.dataScr.sub_left hsubN).sub_right dnScr
      · show Region.Disjoint ⟨D'.setWidth 64, Mn.step * r⟩ ⟨D.setWidth 64, Mw.step * q⟩
        rw [hD'64 hr]
        exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hDf, hwq])
      · exact hFx.stkData.symm.sub_left hsubN
  -- The groups' blocks are as the groups left them.
  obtain head₄ : chunksAt Mn.step s₄.mem (D.setWidth 64) (g * q) =
      chunksAt Mn.step s₃.mem (D.setWidth 64) (g * q) := by
    by_cases hq0 : q = 0
    · rw [hq0, Nat.mul_zero]; rfl
    · have hFx := hFx (hn0 hq0 (.inl rfl))
      have hDf := hFx.dataFit
      obtain hpre' : Region.Sub (dataRegion D Mn.step (g * q)) (dataRegion D Mn.step n) :=
        Region.sub_prefix (by omega_using [hwq, hwq'])
      have f₄ := d₄.frame
      rw [h₃.esp] at f₄
      refine chunksAt_frame f₄ (fun R hR => ?_) (by omega_using [hDf, hwq, hwq'])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact (hFx.dataScr.sub_left hpre').sub_right coreScr
      · exact (hFx.dataScr.sub_left hpre').sub_right dnScr
      · by_cases hr : r = 0
        · intro a _ ha
          have h0 : Mn.step * r = 0 := by rw [hr, Nat.mul_zero]
          simp only [Region.Contains] at ha
          omega_using [ha, h0]
        · show Region.Disjoint ⟨D.setWidth 64, Mn.step * (g * q)⟩ ⟨D'.setWidth 64, Mn.step * r⟩
          rw [hD'64 hr, hwq']
          exact VG.Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hDf, hwq, hwq'])
      · exact hFx.stkData.symm.sub_left hpre'
  -- How the data split.
  obtain hsplit : ∀ m : Mem, chunksAt Mn.step m (D.setWidth 64) n =
      chunksAt Mn.step m (D.setWidth 64) (g * q) ++ chunksAt Mn.step m (D'.setWidth 64) r := fun m => by
    by_cases hr : r = 0
    · rw [hr, show chunksAt Mn.step m (D'.setWidth 64) 0 = [] from rfl, List.append_nil]
      congr 1
      omega_using [hnr, hr]
    · conv => lhs; rw [hnr]
      rw [chunksAt_add, hD'64 hr, hwq']
  obtain hgroup : ∀ m : Mem, chunksAt Mn.step m (D.setWidth 64) (g * q) =
      (chunksAt Mw.step m (D.setWidth 64) q).flatMap (split Mn.step g) := fun m => by rw [chunksAt_group, hstw]
  obtain hlen : ∀ x ∈ xw, x.length = g * Mn.step := fun x hx => by
    rw [← hxw] at hx
    simp only [chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨_, _, rfl⟩ := hx
    simp only [bytesAt, List.length_map, List.length_range, hstw]
  obtain ⟨rg1, rg2⟩ := run_group_blocks hFb iv xw hivl hlen
  -- The inputs: the groups' blocks, then the blocks left.
  obtain hxs' : xs = xw.flatMap (split Mn.step g) ++ xn := by
    rw [← hI.inputs, hsplit, hgroup, hxw, hxn₂]
  obtain hrun := run_append F iv (xw.flatMap (split Mn.step g)) xn
  rw [← rg2] at hrun
  have f₄ := d₄.frame
  rw [h₃.esp] at f₄
  refine ⟨d₄.b, d₄.esp.trans h₃.esp, d₄.rd.trans h₃.rd, d₄.wr.trans h₃.wr, ?_, ?_, d₄.ready, ?_, ?_, ?_⟩
  · rw [d₄.dp, hD', VG.Offset.add_add, hwq]
  · rw [d₄.np, Nat.sub_self, Nat.sub_self]
  · rw [List.take_of_length_le (Nat.le_of_eq hxs), List.drop_of_length_le (Nat.le_of_eq hxs), List.append_nil,
      hxs', hrun, hsplit, data₄, head₄, hgroup, data₃, rg1]
  · rw [List.take_of_length_le (Nat.le_of_eq hxs), hxs', hrun, chn₄]
  · refine (h₃.frame.sub fun R hR => ?_).trans (f₄.sub fun R hR => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
          Region.sub_prefix (by omega_using [hwq])⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hsubN⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          fun _ h => h⟩

/-- The wide loops of `levels`, then `rest`. -/
theorem levels_ok {wide : Nat → Mode} {gs : List Nat} {rest : Prog isa}
    (hw : ∀ g ∈ gs, WideOk cs Mn F k (wide g) g) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hrest : StepsOk cs Mn F k rest) : StepsOk cs Mn F k (c.levels wide gs rest) := by
  induction gs with
  | nil => exact hrest
  | cons g gs ih =>
    exact wideThen_ok cs (hw g List.mem_cons_self) hFb (ih fun l hl => hw l (List.mem_cons_of_mem _ hl))

end

/-! ## The function -/

/-- What the code `loops` must do, from the state after the setup, with the
mode's first step to take: all of them. -/
def LoopsOk (cs : CoreSpec c) (M : Mode) (F : StepFn) (s₀ : State) (k : cs.Key) (loops : Prog isa) : Prop :=
  ∀ s, Fixed c s (S s₀ c) (Dp s₀ c) (N s₀ c) M.step →
    Inv cs s (S s₀ c) (Dp s₀ c) (N s₀ c) M.step k F (iv0 c s₀) (xs0 c M s₀) 0 s →
    WP isa loops s (Inv cs s (S s₀ c) (Dp s₀ c) (N s₀ c) M.step k F (iv0 c s₀) (xs0 c M s₀) (N s₀ c))

/-- `seq_wp`, for any loops that take all the steps. -/
theorem seqWith_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} {loops : Prog isa}
    (hp : SeqPre c M s₀) (hloops : LoopsOk cs M F s₀ k loops) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqWith loops M.ivOut) s₀ fun s' => abiPreserved s₀ s' ∧
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
  unfold Core.seqWith
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  rw [WP.seq_iff] at h₁
  refine WP.seq (WP.mono h₁ fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  refine WP.seq (WP.mono (hloops s₃ h₃.fixed h₃.inv) fun s₄ h₄ => ?_)
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
    obtain argsOut : ∀ r ∈ big c (S s₀ c) (Dp s₀ c) (N s₀ c) M.step (E s₀), Region.Disjoint (argsR s₀ c) r :=
      fun r hr => by
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

section
variable (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

/-- `Core.seqLevels`: the levels' groups, then the blocks left. -/
theorem seqLevels_wp {wide : Nat → Mode} {gs : List Nat} {Mn : Mode} {F : StepFn} (hp : SeqPre c Mn s₀)
    (hw : ∀ g ∈ gs, WideOk cs Mn F k (wide g) g) (hFb : Blockwise F Mn.step (4 * c.bw))
    (hpre : ∀ o ∈ Mn.pre, o.InBounds (lens c Mn.step)) (hpost : ∀ o ∈ Mn.post, o.InBounds (lens c Mn.step))
    (hcomp : Computes Mn (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels wide gs Mn) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt Mn.step s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) = (run F (iv0 c s₀) (xs0 c Mn s₀)).1 ∧
      (Mn.ivOut = true →
        bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = (run F (iv0 c s₀) (xs0 c Mn s₀)).2) :=
  seqWith_wp cs hp (fun _ hF hI => levels_ok cs hw hFb (narrow_ok cs hpre hpost hcomp) hF.scr hF.layout
    (BitVec.isLt _) (fun _ => hF) hI) hk

/-- What the levels `gs` need: groups of at most `G` blocks. -/
abbrev LevelsFit (c : Core) (gs : List Nat) : Prop := ∀ g ∈ gs, 0 < g ∧ g ≤ c.G

theorem lensB_wide (G : Nat) (l : Loc) (hl : l ≠ .chn) :
    4 * c.bw * G ≤ lensB c (G * (4 * c.bw)) (4 * c.bw * G) l := by
  cases l <;> simp [lensB, Nat.mul_comm] at hl ⊢

/-- A level of CBC decryption, `g` blocks a step. -/
theorem cbcDecWide_ok {g : Nat} (hg : 0 < g) (hG : g ≤ c.G) :
    WideOk cs (Mode.cbcDecChained c.bw) (cbcDecF (cs.cipher k)) k (Mode.cbcDecWide c.bw g) g := by
  obtain ⟨hw1, hw2⟩ := cbcDecWide_inBounds (bw := c.bw) (len := lensB c (g * (4 * c.bw)) (4 * c.bw * g))
    g (lensB_wide _ _ (by decide)) (lensB_wide _ _ (by decide)) (by simp [lensB])
  exact ⟨hg, hG, rfl, hw1, hw2, ⟨_, cbcDecWide_computes (cs.cipher_len k) _, bufCipher_blocks hG⟩⟩

/-- A level of CFB decryption, `g` blocks a step. -/
theorem cfbDecWide_ok {g : Nat} (hg : 0 < g) (hG : g ≤ c.G) :
    WideOk cs (Mode.cfbDecEarly c.bw) (cfbDecF (cs.cipher k)) k (Mode.cfbDecWide c.bw g) g := by
  obtain ⟨hw1, hw2⟩ := cfbDecWide_inBounds (bw := c.bw) (len := lensB c (g * (4 * c.bw)) (4 * c.bw * g))
    g (lensB_wide _ _ (by decide)) (lensB_wide _ _ (by decide)) (by simp [lensB])
  exact ⟨hg, hG, rfl, hw1, hw2, ⟨_, cfbDecWide_computes (cs.cipher_len k) _, bufCipher_blocks hG⟩⟩

/-- CBC decryption, by groups of `g` blocks for each `g` of `gs` in turn,
then one block at a time. -/
theorem cbcDecLevels_wp {gs : List Nat} (hfit : LevelsFit c gs) (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀)
    (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels (Mode.cbcDecWide c.bw) gs (Mode.cbcDecChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  refine WP.mono (seqLevels_wp cs hp (fun g hg => cbcDecWide_ok cs (hfit g hg).1 (hfit g hg).2)
    (cbcDecF_blockwise (cs.cipher_len k)) (copyBlk_inBounds (b _) (b _)) (fun o ho => ?_)
    (cbcDecChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cbcDecChained, Mode.cbcDec, List.mem_append] at ho
    rcases ho with (ho | ho) | ho
    · exact xorBlk_inBounds (b _) (b _) (b _) o ho
    · exact copyBlk_inBounds (b _) (b _) o ho
    · exact copyBlk_inBounds (b _) (b _) o ho
  · exact h2.trans (by rw [decrypt_run]; rfl)
  · rw [h3 rfl, decrypt_run_next]; rfl

/-- CFB decryption, by groups of `g` blocks for each `g` of `gs` in turn,
then one block at a time. -/
theorem cfbDecLevels_wp {gs : List Nat} (hfit : LevelsFit c gs) (hp : SeqPre c (Mode.cfbDecEarly c.bw) s₀)
    (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels (Mode.cfbDecWide c.bw) gs (Mode.cfbDecEarly c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDecEarly c.bw).step) rfl
  exact WP.mono (seqLevels_wp cs hp (fun g hg => cfbDecWide_ok cs (hfit g hg).1 (hfit g hg).2)
    (cfbDecF_blockwise (cs.cipher_len k))
    (fun o ho => (List.mem_append.mp ho).elim (copyBlk_inBounds (b _) (b _) o) (copyBlk_inBounds (b _) (b _) o))
    (xorBlk_inBounds (b _) (b _) (b _)) (cfbDecEarly_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl), by rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl⟩

/-! ## Counter mode -/

/-- `Core.seqLevels` over counter mode with the counter block stepped by
`o` before the block cipher. -/
theorem ctrEarlyLevels_wp {o : Op} {gf : List Byte → List Byte} (hbw : c.bw = 4) (hg : IncOp o gf)
    (hsh : ∀ L st j, Op.shift L st j o = o) (hgl : ∀ x, x.length = 16 → (gf x).length = 16)
    (ho : ∀ len : Loc → Nat, 16 ≤ len .chn → o.InBounds len) {gs : List Nat} (hfit : LevelsFit c gs)
    (hp : SeqPre c (Mode.ctrEarlyWith o) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels (fun G => Mode.widen G 16 (Mode.ctrEarlyWith o)) gs (Mode.ctrEarlyWith o)) s₀ fun s' =>
      abiPreserved s₀ s' ∧
      chunksAt 16 s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        (run (ctrStep (cs.cipher k) gf) (iv0 c s₀) (xs0 c (Mode.ctrEarlyWith o) s₀)).1 ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) =
        (run (ctrStep (cs.cipher k) gf) (iv0 c s₀) (xs0 c (Mode.ctrEarlyWith o) s₀)).2 := by
  have e4 : 4 * c.bw = 16 := by rw [hbw]
  have hc : ∀ x, (cs.cipher k x).length = 16 := fun x => by rw [cs.cipher_len, e4]
  obtain ⟨hn1, hn2⟩ := ctrEarly_inBounds (len := lens c 16) (ho _ (by simp [lens, e4]))
    (by simp [lens]) (by simp [lens, e4]) (by simp [lens, e4])
  have hwide : ∀ g ∈ gs, WideOk cs (Mode.ctrEarlyWith o) (ctrStep (cs.cipher k) gf) k
      (Mode.widen g 16 (Mode.ctrEarlyWith o)) g := fun g hl => by
    obtain ⟨hw1, hw2⟩ := ctrWide_inBounds (len := lensB c (g * 16) (4 * c.bw * g)) hsh
      (ho _ (by simp [lensB, e4])) g (by simp [lensB, Nat.mul_comm]) (by simp [lensB, e4])
      (by simp [lensB, e4])
    have hcw := ctrWide_computes hc hg hsh hgl g
    have hB := bufCipher_blocks (c := c) (ciph := cs.cipher k) (hfit g hl).2
    rw [e4] at hB
    exact ⟨(hfit g hl).1, (hfit g hl).2, rfl, hw1, hw2, ⟨_, by rw [e4]; exact hcw, by rw [e4]; exact hB⟩⟩
  exact WP.mono (seqLevels_wp cs hp hwide (by rw [e4]; exact ctrStep_blockwise hc hgl) hn1 hn2
    (by rw [e4]; exact ctrEarly_computes hc hg hgl) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3 rfl⟩

/-- Counter mode, by groups of `g` blocks for each `g` of `gs` in turn,
then one block at a time. -/
theorem ctrLevels_wp (hbw : c.bw = 4) {gs : List Nat} (hfit : LevelsFit c gs) (hp : SeqPre c Mode.ctrEarly s₀)
    (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels Mode.ctrWide gs Mode.ctrEarly) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c) =
        Spec.Ctr.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw) = Spec.Ctr.next (iv0 c s₀) (N s₀ c) :=
  WP.mono (ctrEarlyLevels_wp cs hbw incOp_ctr (fun _ _ _ => rfl) inc_length
    (fun len h => ⟨by simpa [Op.width, Mode.ctrInc] using h, by simpa [Op.width, Mode.ctrInc] using h,
      fun _ _ h => by cases h⟩) hfit hp hk) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, by simpa [hbw, Mode.ctrEarly, Mode.ctrEarlyWith, xs0, blocks0, ← ctrF_eq] using
        h2.trans (ctr_run _ _ _).1.symm,
      by rw [h3, ← ctrF_eq, ← (ctr_run _ _ _).2, xs0, chunksAt_length]⟩

/-- Counter mode with GCM's `inc₃₂`, by groups of `g` blocks for each `g` of
`gs` in turn, then one block at a time. -/
theorem ctr32Levels_wp (hbw : c.bw = 4) {gs : List Nat} (hfit : LevelsFit c gs)
    (hp : SeqPre c Mode.ctr32Early s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seqLevels Mode.ctr32Wide gs Mode.ctr32Early) s₀ fun s' => abiPreserved s₀ s' ∧
      (chunksAt (4 * c.bw) s'.mem ((Dp s₀ c).setWidth 64) (N s₀ c)).map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks (cs.cipher k)) (Spec.Gcm.ofBytes (iv0 c s₀))
          ((blocks0 (c := c) s₀).map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (bytesAt s'.mem ((P s₀ c).setWidth 64) (4 * c.bw)) =
        Nat.repeat Spec.Gcm.inc32 (N s₀ c) (Spec.Gcm.ofBytes (iv0 c s₀)) := by
  have hc : ∀ x, (cs.cipher k x).length = 16 := by simpa [hbw] using cs.cipher_len k
  have ht : (iv0 c s₀).length = 16 := by simp [iv0, bytesAt, hbw]
  have hx : ∀ x ∈ blocks0 (c := c) s₀, x.length = 16 := by
    intro x hx
    simp only [blocks0, chunksAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    simp [bytesAt, hbw]
  obtain ⟨g1, g2⟩ := ctr32_gcm hc ht hx
  have e : xs0 c (Mode.ctrEarlyWith Mode.ctr32Inc) s₀ = blocks0 (c := c) s₀ := by
    simp [xs0, blocks0, Mode.ctrEarlyWith, hbw]
  have es : 16 = 4 * c.bw := by rw [hbw]
  refine WP.mono (ctrEarlyLevels_wp cs hbw incOp_ctr32 (fun _ _ _ => rfl) inc32B_length
    (fun len h => ⟨by simp [Op.width, Mode.ctr32Inc]; omega_using [h], by simp [Op.width, Mode.ctr32Inc]; omega_using [h],
      fun _ _ h => by cases h⟩) hfit hp hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · rw [← es, h2, e, ← ctr32F_eq]; exact g1
  · rw [h3, e, ← ctr32F_eq, g2, blocks0, chunksAt_length]

end

end VG.Proof.Modes.X86
