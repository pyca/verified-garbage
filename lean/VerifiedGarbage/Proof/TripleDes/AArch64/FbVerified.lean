module

public import VerifiedGarbage.Proof.TripleDes.FbScratch
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
public import VerifiedGarbage.Proof.Modes.Cfb8
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.SboxLit
meta import VerifiedGarbage.Proof.Modes.AArch64.CfbDec.Whole
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Fb
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
meta import VerifiedGarbage.Proof.Modes.Cfb8
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.TripleDes.AArch64.SboxTable
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
public import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.AArch64.Ctr
meta import VerifiedGarbage.Proof.Modes.AArch64.Cfb8Steps
meta import VerifiedGarbage.Impl.Modes.AArch64.Cfb8
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.AArch64.Words
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Modes.AArch64.Ctr
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
public import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Modes.AArch64.Core
public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Modes.AArch64.Core
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch
meta import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
meta import VerifiedGarbage.Proof.CmacTripleDes.Bytes
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Framework.Bswap

/-! ### `TripleDes.AArch64.Link`, which this module and modules that import it used -/

section

/-! ### `TripleDes.AArch64.ModeCore`, which this module and modules that import it used -/

section

/-!
# Triple DES's core for the modes on AArch64

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.AArch64.dirCore d`) meets what the modes need of a core of
one-word blocks (`Proof.Modes.AArch64.BlockSpec`), with the key a schedule,
its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption, and the key ready when its copy
in the core's slots is the schedule. `crypt` is the block function
(`block_ok`) on the buffer.

`batchCoreSpec d`: the batched core (`batchCore d`) meets it too, with the
same cipher, and the key ready when the schedule is at `x0`, readable and
outside every writable region (`SchedAt`), where nothing the modes or the
core write can reach it. `crypt` is the ECB functions' batch (`batch_ok`) on
the buffer's 128 blocks.

`tableCoreSpec`: the table core (`tableCore`) meets it for encryption, with
the key ready when the schedule is at `x4`, as `SchedAt` says. `crypt` is
CMAC's block (`CmacTripleDes.AArch64.block_ok`) on the buffer's block as a
big-endian integer.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp addImm_ok runBlock_app
  addr_add)
open VG.Spec.TripleDes (Direction)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `x0`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.TripleDes.scheduleAt s.mem p ∧ (⟨p, 384⟩ : Region) ∈ s.rd ∧
    p.toNat + 384 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 384⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 1 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 904⟩ := rfl
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 512, 8⟩ := rfl
theorem total_eq (d : Direction) : (dirCore d).total = 125 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 384⟩ ⟨B, 904⟩ := Offset.sub_base B (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'
    exact (Offset.disjoint B (.inr (by decide)) (by decide) (by decide)).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame p hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain hsep : Region.Disjoint ⟨p, 384⟩ ⟨B, 904⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 48) (u := .x7) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega_using [hw]) (by simp only [schedSlot]; omega_using [hw])⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_using [hw]) (by omega_using [hw])⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega_using []⟩) fun s' h => ?_
  refine ⟨scheduleAt_copy fun i hi => by rw [h.mem, over_at hi (by omega_using [])],
    by rw [h.regs _ (by decide) (by decide), hB], h.regs _ (by decide) (by decide), h.regs _ (by decide) (by decide),
    ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

/-- No instruction of the block function writes `x2`. -/
theorem block_keeps_x2 (d : Direction) : ∀ i ∈ instrs (dirBlock d), clobbers i .x2 = false := by
  obtain h : ((instrs (dirBlock d)).all fun i => decide (clobbers i .x2 = false)) = true := by
    cases d
    · change ((instrs encryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs decryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem blockCall_eq (d : Direction) : blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (dirBlock d) := by cases d <;> rfl

theorem dirBlock_correct (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    ∃ t s', Exec isa (dirBlock d) s t s' ∧ abiPreserved s s' ∧ (blockContract d).post s s' := by
  cases d
  · exact encrypt_correct s hs
  · exact decrypt_correct s hs

/-- The call of the block function on the buffer, with the schedule's copy
and the block function's slots in the core's slots at `B`. -/
theorem blockCall_ok (d : Direction) {s : State} {B : Addr}
    (x0 : s.gpr .x0 = schedAddr B) (x1 : s.gpr .x1 = B + BitVec.ofNat 64 512) (x2 : s.gpr .x2 = B)
    (hw : (⟨B, 1000⟩ : Region) ∈ s.wr) (hfB : B.toNat + 1000 ≤ 2 ^ 64) :
    WP isa (blockCall d) s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨B + BitVec.ofNat 64 512, 8⟩, ⟨B, 512⟩] s.mem s'.mem ∧
      s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
        blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (Spec.TripleDes.blockAt s.mem (s.gpr .x1)) := by
  obtain sub : ∀ off len, off + len ≤ 1000 → ∃ r' ∈ s.wr, ∃ o,
      (B + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + len ≤ r'.len :=
    fun off len h => ⟨_, hw, off, rfl, h⟩
  rw [blockCall_eq]
  refine WP.call (k := blockContract d) (dirBlock_correct d)
    (rd := [⟨schedAddr B, 384⟩]) (wr := [⟨B + BitVec.ofNat 64 512, 8⟩, ⟨B, 512⟩]) ?_
    (Covers.right (Covers.of_sub fun r hr => ?_)) (Covers.of_sub fun r hr => ?_) (fun s' hrd hwr _ hf hsv hk hpost => ?_)
    (by cases d <;> rfl)
  · simp only [blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      x0, x1, x2]
    exact ⟨trivial, trivial, Offset.disjoint_base B (by decide) (by have := hfB; rw [show schedSlot = 65 from rfl]; omega_using []),
      Offset.disjoint_base B (by decide) (by omega_using [])⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub (8 * schedSlot) 384 (by decide)
    · exact sub 512 8 (by decide)
    · obtain ⟨r', h1, o, h2, h3⟩ := sub 0 512 (by decide)
      exact ⟨r', h1, o, by rw [← h2]; exact (BitVec.add_zero B).symm, h3⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub 512 8 (by decide)
    · obtain ⟨r', h1, o, h2, h3⟩ := sub 0 512 (by decide)
      exact ⟨r', h1, o, by rw [← h2]; exact (BitVec.add_zero B).symm, h3⟩
  · refine ⟨hrd, hwr, hf, hk .x2 (by decide) (block_keeps_x2 d), hsv .x23 (by decide) (by decide),
      hsv .x24 (by decide) (by decide), ?_⟩
    change Spec.TripleDes.blockAt _ _ = _ at hpost
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs)] at hpost
    exact hpost

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hss : schedSlot = 65 := rfl
  have hw := hs.wr
  rw [total_eq] at hw
  -- `x0`, `x1` and `x2` to the schedule's copy, the buffer and the block function's slots.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := addImm_ok s .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .x1 sb (v := 8 * cbcBuf) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .x2 sb (v := 0) (by decide)
  obtain g₃ : ∀ x, x ≠ .x0 → x ≠ .x1 → x ≠ .x2 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₃ x h3, o₂ x h2, o₁ x h1]
  obtain x0₃ : s₃.gpr .x0 = schedAddr B := by rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hB]
  obtain x1₃ : s₃.gpr .x1 = B + BitVec.ofNat 64 512 := by
    rw [o₃ _ (by decide), r₂, o₁ _ (by decide), hB]; rfl
  obtain x2₃ : s₃.gpr .x2 = B := by
    rw [r₃, o₂ _ (by decide), o₁ _ (by decide), hB]; exact BitVec.add_zero _
  -- `x26` keeps the return address across the call.
  obtain ⟨s₃', e₃', -, o₃', m₃', rd₃'', wr₃''⟩ := addImm_ok s₃ .x26 .x30 (v := 0) (by decide)
  obtain g₃' : ∀ x, x ≠ .x0 → x ≠ .x1 → x ≠ .x2 → x ≠ .x26 → s₃'.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [o₃' x h4, g₃ x h1 h2 h3]
  replace x0₃ : s₃'.gpr .x0 = schedAddr B := by rw [o₃' _ (by decide), x0₃]
  replace x1₃ : s₃'.gpr .x1 = B + BitVec.ofNat 64 512 := by rw [o₃' _ (by decide), x1₃]
  replace x2₃ : s₃'.gpr .x2 = B := by rw [o₃' _ (by decide), x2₃]
  obtain mem₃ : s₃'.mem = s.mem := by rw [m₃', m₃, m₂, m₁]
  obtain rd₃' : s₃'.rd = s.rd := by rw [rd₃'', rd₃, rd₂, rd₁]
  obtain wr₃' : s₃'.wr = s.wr := by rw [wr₃'', wr₃, wr₂, wr₁]
  rw [show (dirCore d).crypt = .seq (.block ([.addImm .x .x0 sb (8 * schedSlot)] ++
      ([.addImm .x .x1 sb (8 * cbcBuf)] ++ ([.addImm .x .x2 sb 0] ++ ([.addImm .x .x26 .x30 0] : List Instr)))))
      (.seq (blockCall d) (.block ([.addImm .x sb .x2 0] ++ ([.addImm .x .x30 .x26 0] : List Instr)))) by
    cases d <;> rfl]
  refine WP.seq (WP.of_runBlock ⟨s₃', by
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, e₃'], ?_⟩)
  -- The block.
  refine WP.seq (WP.mono (blockCall_ok d x0₃ x1₃ x2₃ (by rw [wr₃']; exact hw) hfB) fun s₄ h₄ => ?_)
  obtain ⟨rd₄, wr₄, f₄, x2₄', x23₄, x24₄, res₄⟩ := h₄
  obtain ⟨s₅', e₅', r₅, o₅', m₅', rd₅', wr₅'⟩ := addImm_ok s₄ sb .x2 (v := 0) (by decide)
  obtain ⟨s₅, e₅, -, o₅'', m₅'', rd₅'', wr₅''⟩ := addImm_ok s₅' .x30 .x26 (v := 0) (by decide)
  obtain o₅ : ∀ x, x ≠ sb → x ≠ .x30 → s₅.gpr x = s₄.gpr x := fun x h1 h2 => by rw [o₅'' x h2, o₅' x h1]
  replace r₅ : s₅.gpr sb = s₄.gpr .x2 + BitVec.ofNat 64 0 := by rw [o₅'' _ (by decide), r₅]
  obtain m₅ : s₅.mem = s₄.mem := by rw [m₅'', m₅']
  obtain rd₅ : s₅.rd = s₄.rd := by rw [rd₅'', rd₅']
  obtain wr₅ : s₅.wr = s₄.wr := by rw [wr₅'', wr₅']
  refine WP.of_runBlock ⟨s₅, by rw [runBlock_app, e₅', Option.bind_some, e₅], ?_⟩
  obtain x2₄ : s₄.gpr .x2 = B := by rw [x2₄', x2₃]
  obtain fB : Frame [⟨B, 904⟩] s₃'.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  refine ⟨by rw [r₅, x2₄]; exact BitVec.add_zero _,
    by rw [o₅ _ (by decide) (by decide), x23₄, g₃' _ (by decide) (by decide) (by decide) (by decide)],
    by rw [o₅ _ (by decide) (by decide), x24₄, g₃' _ (by decide) (by decide) (by decide) (by decide)], ?_,
    by rw [m₅, core_eq, ← mem₃]; exact fB, fun j hj => ?_, by rw [rd₅, rd₄, rd₃'], by rw [wr₅, wr₄, wr₃']⟩
  · rw [ReadyAt, m₅, scheduleAt_eq_of_frame _ f₄ fun r hr => ?_, mem₃, hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint_base B (by decide) (by omega_using [hss])
  · have hG : (dirCore d).G = 1 := by cases d <;> rfl
    obtain hj0 : j = 0 := by omega_using [hj, hG]
    subst hj0
    obtain ea : blkAddr (dirCore d) B 0 = s₃'.gpr .x1 := by rw [x1₃]; rfl
    rw [dirCore_bw, ea, dirCipher_bytes, bytesAt_eq, m₅, res₄, x0₃, mem₃, hr]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-! ## The batched core -/

/-- The schedule at `p`: readable, within the address space, and outside
every writable region. -/
structure SchedAt (s : State) (p : Addr) : Prop where
  rd : (⟨p, 384⟩ : Region) ∈ s.rd
  fit : p.toNat + 384 ≤ 2 ^ 64
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨p, 384⟩ w

theorem SchedAt.congr {s s' : State} {p : Addr} (h : SchedAt s p) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SchedAt s' p :=
  ⟨by rw [hrd]; exact h.rd, h.fit, by rw [hwr]; exact h.sep⟩

/-- The schedule at `x0`, outside the regions `rs` and every writable one. -/
def BatchKeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ k = Spec.TripleDes.scheduleAt s.mem p ∧ SchedAt s p ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 384⟩ r

/-- The schedule at `x0` is `k`. -/
def BatchReady (s : State) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ Spec.TripleDes.scheduleAt s.mem p = k ∧ SchedAt s p

@[simp] theorem batchCore_bw (d : Direction) : (batchCore d).bw = 1 := rfl

theorem batchCore_eq (d : Direction) (B : Addr) : coreRegion (batchCore d) B = ⟨B, 1024⟩ := rfl
theorem batchTotal_eq (d : Direction) : (batchCore d).total = 140 := rfl

theorem x0_not_mode (d : Direction) : Reg.x0 ∉ Modes.AArch64.modeRegs (batchCore d) := by
  simp only [Modes.AArch64.modeRegs, batchCore]; decide

theorem batchReady_frame {d : Direction} {s s' : State} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : BatchReady s k) (hf : Frame rs s.mem s'.mem) (hw : Modes.AArch64.WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs (batchCore d) → s'.gpr r = s.gpr r) : BatchReady s' k := by
  obtain ⟨p, hp, hk, hS⟩ := h
  refine ⟨p, by rw [hg _ (x0_not_mode d), hp], ?_, hS.congr hw.rd hw.wr⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hS.sep w hw').sub_right hsub

theorem batchKeyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (h : BatchKeyArgs s rs k) (hr : ∀ r ∈ [Reg.x0], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) : BatchKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hS, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], ?_, hS.congr hrd hwr, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame p hf hdis).symm

theorem batchPrepare_wp {d : Direction} {s : State} {B : Addr} {rs : List Region}
    {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B) (_ : ScrIn s B (batchCore d).total)
    (_ : (⟨B, 8 * (batchCore d).total⟩ : Region) ∈ rs) (hk : BatchKeyArgs s rs k) :
    WP isa (batchCore d).prepare s fun s' => BatchReady s' k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (batchCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hk, hS, -⟩ := hk
  exact WP.block_nil ⟨⟨p, hp, hk.symm, hS⟩, hB, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

private theorem blockOut_eq (k : Spec.TripleDes.Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    VG.Proof.TripleDes.Bitslice.blockOut k d b = blockResult k d b := by
  cases d <;> rfl

theorem batchCrypt_wp {d : Direction} {s : State} {B : Addr} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (batchCore d).total) (hr : BatchReady s k) :
    WP isa (batchCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ BatchReady s' k ∧
      Frame [coreRegion (batchCore d) B] s.mem s'.mem ∧
      (∀ j < (batchCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (batchCore d) B j) (8 * (batchCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (batchCore d) B j) (8 * (batchCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hK, hS⟩ := hr
  have hw := hs.wr
  have hfit := hs.fit
  rw [batchTotal_eq] at hw hfit
  -- `sb` to `x16`, and `x4` to the buffer.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s .x16 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x4 sb
  obtain g₂ : ∀ r, r ≠ .x16 → r ≠ .x4 → s₂.gpr r = s.gpr r := fun r h1 h2 => by rw [o₂ r h2, o₁ r h1]
  obtain x16₂ : s₂.gpr .x16 = B := by rw [o₂ _ (by decide), r₁, hB]
  obtain x4₂ : s₂.gpr .x4 = B := by rw [r₂, o₁ _ (by decide), hB]
  obtain x0₂ : s₂.gpr .x0 = p := by rw [g₂ _ (by decide) (by decide), hp]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  obtain rdE₂ : s₂.rd = s.rd := by rw [rd₂, rd₁]
  obtain wrE₂ : s₂.wr = s.wr := by rw [wr₂, wr₁]
  show WP isa (.seq (.block ([Impl.Aes.AArch64.movR .x16 sb] ++ ([Impl.Aes.AArch64.movR .x4 sb] : List Instr)))
    (.seq (BitsliceNeon.batch d) (.block [Impl.Aes.AArch64.movR sb .x16]))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  -- The batch.
  obtain hRoom : BitslicedNeon.Room s₂ := ⟨fun j hj => by
    show InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * j)) 16
    rw [x4₂, wrE₂]
    have hj64 : j < 64 := hj
    exact ⟨_, hw, Offset.contains_base B (by omega_using [hj64]) (by omega_using [hj64])⟩,
    by decide⟩
  obtain hSched : BitslicedNeon.Sched s₂ := ⟨fun i hi => by
      rw [x0₂, rdE₂]
      exact ⟨_, List.mem_append_left _ hS.rd, Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])⟩,
    by
      show Region.Disjoint ⟨s₂.gpr .x0, 384⟩ ⟨s₂.gpr .x4, 1024⟩
      rw [x0₂, x4₂]
      exact (hS.sep _ hw).sub_right (Region.sub_prefix (by decide))⟩
  refine WP.seq (WP.mono (BitslicedNeon.batch_ok d hRoom hSched) fun s₃ P => ?_)
  -- `sb` back.
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movR_ok s₃ sb .x16
  refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
  obtain g₄ : ∀ r, r ≠ sb → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → r ≠ .x4 → s₄.gpr r = s.gpr r :=
    fun r h5 h7 h9 h10 h16 h4 => by rw [o₄ r h5, P.gpr r h5 h7 h9 h10, g₂ r h16 h4]
  obtain rdE : s₄.rd = s.rd := by rw [rd₄, P.rd, rdE₂]
  obtain wrE : s₄.wr = s.wr := by rw [wr₄, P.wr, wrE₂]
  obtain fr : Frame [⟨B, 1024⟩] s.mem s₄.mem := by
    have := P.frame
    rw [show BitslicedNeon.stateR s₂ = ⟨B, 1024⟩ by simp only [BitslicedNeon.stateR, x4₂], mem₂] at this
    rw [m₄]; exact this
  obtain sch : ∀ r ∈ [(⟨B, 1024⟩ : Region)], Region.Disjoint ⟨p, 384⟩ r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hS.sep _ hw).sub_right (Region.sub_prefix (by decide))
  refine ⟨by rw [r₄, P.gpr _ (by decide) (by decide) (by decide) (by decide), x16₂],
    g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ⟨p, by rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp], ?_,
      hS.congr rdE wrE⟩, by rw [batchCore_eq]; exact fr, fun j hj => ?_, rdE, wrE⟩
  · rw [scheduleAt_eq_of_frame _ fr sch]; exact hK
  · have hj128 : j < 128 := hj
    obtain ea : blkAddr (batchCore d) B j = VG.Proof.TripleDes.Bitslice.wAt (s₂.gpr .x4) j := by
      rw [x4₂]; simp only [blkAddr, batchCore, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    rw [batchCore_bw, Nat.mul_one, ea, dirCipher_bytes, bytesAt_eq, m₄, P.out j hj128, x0₂, mem₂, hK, blockOut_eq]

/-- The batched core meets what the modes need. -/
def batchCoreSpec (d : Direction) : BlockSpec (batchCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := BatchKeyArgs
  Ready s _ k := BatchReady s k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := batchKeyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg := batchReady_frame h hf hw hg
  prepare_wp := batchPrepare_wp
  crypt_wp := batchCrypt_wp

/-! ## The table core -/

/-- The schedule at `x4` is `k`. -/
def TableReady (s : State) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .x4 = p ∧ Spec.TripleDes.scheduleAt s.mem p = k ∧ SchedAt s p

@[simp] theorem tableCore_bw : tableCore.bw = 1 := rfl

theorem tableCore_eq (B : Addr) : coreRegion tableCore B = ⟨B, 464⟩ := rfl
theorem tableTotal_eq : tableCore.total = 70 := rfl

theorem x4_not_mode : Reg.x4 ∉ Modes.AArch64.modeRegs tableCore := by
  simp only [Modes.AArch64.modeRegs, tableCore]; decide

theorem tableReady_frame {s s' : State} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : TableReady s k) (hf : Frame rs s.mem s'.mem) (hw : Modes.AArch64.WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.AArch64.modeRegs tableCore → s'.gpr r = s.gpr r) : TableReady s' k := by
  obtain ⟨p, hp, hk, hS⟩ := h
  refine ⟨p, by rw [hg _ x4_not_mode, hp], ?_, hS.congr hw.rd hw.wr⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hS.sep w hw').sub_right hsub

theorem tablePrepare_wp {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (_ : ScrIn s B tableCore.total) (_ : (⟨B, 8 * tableCore.total⟩ : Region) ∈ rs)
    (hk : BatchKeyArgs s rs k) :
    WP isa tableCore.prepare s fun s' => TableReady s' k ∧ s'.gpr sb = B ∧
      s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x3 = s.gpr .x3 ∧
      Frame [coreRegion tableCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hk, hS, -⟩ := hk
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s .x4 .x0
  show WP isa (.block [Impl.Aes.AArch64.movR .x4 .x0]) s _
  exact WP.of_runBlock ⟨s₁, e₁, ⟨p, by rw [r₁, hp], by rw [m₁]; exact hk.symm, hS.congr rd₁ wr₁⟩,
    by rw [o₁ _ (by decide), hB], o₁ _ (by decide), o₁ _ (by decide), by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁⟩

theorem tableCrypt_wp {s : State} {B : Addr} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B tableCore.total) (hr : TableReady s k) :
    WP isa tableCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x3 = s.gpr .x3 ∧ TableReady s' k ∧
      Frame [coreRegion tableCore B] s.mem s'.mem ∧
      (∀ j < tableCore.G, Spec.Aes.bytesAt s'.mem (blkAddr tableCore B j) (8 * tableCore.bw) =
        dirCipher .encrypt k (Spec.Aes.bytesAt s.mem (blkAddr tableCore B j) (8 * tableCore.bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hK, hS⟩ := hr
  have hw := hs.wr
  rw [tableTotal_eq] at hw
  obtain hbuf : (⟨B, 8 * 70⟩ : Region).Contains (B + BitVec.ofNat 64 456) 8 :=
    Offset.contains_base B (by decide) (by decide)
  -- The schedule to `x14`, the scratch buffer to `x15`, and the buffer's
  -- block to `x5`, as a big-endian integer.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s .x14 .x4
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x15 sb
  obtain x15₂ : s₂.gpr .x15 = B := by rw [r₂, o₁ _ (by decide), hB]
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := Modes.AArch64.ldr_ok s₂ .x5 .x15 (off := 456) (by decide) (by
    rw [x15₂, wr₂, wr₁]
    exact ⟨_, List.mem_append_right _ hw, hbuf⟩)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.rev_ok s₃ .x5 .x5
  obtain g₄ : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x5 → s₄.gpr r = s.gpr r := fun r h14 h15 h5 => by
    rw [o₄ r h5, o₃ r h5, o₂ r h15, o₁ r h14]
  obtain x14₄ : s₄.gpr .x14 = p := by rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, hp]
  obtain x15₄ : s₄.gpr .x15 = B := by rw [o₄ _ (by decide), o₃ _ (by decide), x15₂]
  obtain mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain rdE₄ : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wrE₄ : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  obtain x5₄ : s₄.gpr .x5 = byteRev64 (s.mem.readW (B + BitVec.ofNat 64 456) 64) := by
    rw [r₄, r₃, x15₂, m₂, m₁]; rfl
  show WP isa (.seq (.block ([Impl.Aes.AArch64.movR .x14 .x4] ++ ([Impl.Aes.AArch64.movR .x15 sb] ++
      ([.ldr .x .x5 .x15 456] ++ ([.rev .x5 .x5] : List Instr)))))
    (.seq VG.Impl.CmacTripleDes.AArch64.block (.block ([.rev .x5 .x5] ++ ([.str .x .x5 .x15 456] ++
      ([Impl.Aes.AArch64.movR sb .x15] : List Instr)))))) s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, e₄], ?_⟩)
  -- The block.
  obtain hsep : Region.Disjoint ⟨p, 384⟩ ⟨B, 464⟩ := (hS.sep _ hw).sub_right (Region.sub_prefix (by decide))
  obtain hPre : VG.Proof.CmacTripleDes.AArch64.BlockPre s₄ :=
    ⟨⟨⟨p, 384⟩, by rw [rdE₄]; exact List.mem_append_left _ hS.rd, x14₄.symm, Nat.le_refl _,
        (by decide : (384 : Nat) < 2 ^ 64)⟩,
      ⟨⟨B, 8 * 70⟩, by rw [wrE₄]; exact hw, x15₄.symm, (by decide : (456 : Nat) ≤ 8 * 70),
        (by decide : (8 * 70 : Nat) < 2 ^ 64)⟩, by
      rw [x15₄, x14₄]
      exact (hsep.sub_right (Region.sub_prefix (by decide))).symm⟩
  refine WP.seq (WP.mono (VG.Proof.CmacTripleDes.AArch64.block_ok hPre) fun s₅ h₅ => ?_)
  obtain ⟨P, -, x5₅, -⟩ := h₅
  obtain x15₅ : s₅.gpr .x15 = B := by rw [P.x15, x15₄]
  -- The result back to the buffer, and `sb` back.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := Modes.AArch64.rev_ok s₅ .x5 .x5
  obtain x15₆ : s₆.gpr .x15 = B := by rw [o₆ _ (by decide), x15₅]
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := Modes.AArch64.str_ok s₆ .x5 .x15 (off := 456) (by decide) (by
    rw [x15₆, wr₆, P.wr, wrE₄]
    exact ⟨_, hw, hbuf⟩)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := Modes.AArch64.movR_ok s₇ sb .x15
  refine WP.of_runBlock ⟨s₈, by rw [runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some, e₈], ?_⟩
  obtain g₈ : ∀ r ∈ VG.Proof.CmacTripleDes.AArch64.outer, s₈.gpr r = s.gpr r := fun r hr => by
    obtain h5 : r ≠ .x5 := by rintro rfl; revert hr; decide
    obtain h14 : r ≠ .x14 := by rintro rfl; revert hr; decide
    obtain h15 : r ≠ .x15 := by rintro rfl; revert hr; decide
    rw [o₈ r h5, g₇, o₆ r h5, P.keep r hr, g₄ r h14 h15 h5]
  obtain rdE : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, P.rd, rdE₄]
  obtain wrE : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, P.wr, wrE₄]
  obtain val : s₈.mem.readW (B + BitVec.ofNat 64 456) 64 =
      byteRev64 (VG.Proof.CmacTripleDes.tdes k (byteRev64 (s.mem.readW (B + BitVec.ofNat 64 456) 64))) := by
    obtain hsch : VG.Proof.CmacTripleDes.AArch64.sch s₄ = k := by
      show Spec.TripleDes.scheduleAt s₄.mem (s₄.gpr .x14) = k
      rw [mem₄, x14₄]; exact hK
    rw [m₈, m₇, x15₆, Mem.readW_writeW_self64, r₆, x5₅, hsch, x5₄]; rfl
  obtain fr : Frame [⟨B, 464⟩] s.mem s₈.mem := by
    obtain f₅ : Frame [⟨B, 464⟩] s.mem s₅.mem := by
      have := P.frame
      rw [x15₄, mem₄] at this
      exact this.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    rw [m₈, m₇, m₆, x15₆]
    exact f₅.writeW (List.mem_singleton_self _) _ (Offset.contains_base B (by decide) (by decide))
  refine ⟨by rw [r₈, g₇, x15₆], g₈ _ (by decide), g₈ _ (by decide),
    ⟨p, by rw [g₈ _ (by decide), hp], ?_, hS.congr rdE wrE⟩, by rw [tableCore_eq]; exact fr, fun j hj => ?_,
    rdE, wrE⟩
  · rw [scheduleAt_eq_of_frame _ fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsep]
    exact hK
  · have hG : tableCore.G = 1 := rfl
    obtain hj0 : j = 0 := by omega_using [hj, hG]
    subst hj0
    have ea : blkAddr tableCore B 0 = B + BitVec.ofNat 64 456 := rfl
    rw [tableCore_bw, Nat.mul_one, ea, ← VG.Proof.Cmac.le8_readW s₈.mem, val,
      ← VG.Proof.CmacTripleDes.tdesWith_le8, VG.Proof.Cmac.le8_readW]
    rfl

/-- The table core meets what the modes need. -/
def tableCoreSpec : BlockSpec tableCore where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher .encrypt
  KeyArgs := BatchKeyArgs
  Ready s _ k := TableReady s k
  cipher_len _ _ := by simp [dirCipher, Spec.TripleDes.cipher]
  layout := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := batchKeyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg := tableReady_frame h hf hw hg
  prepare_wp := tablePrepare_wp
  crypt_wp := tableCrypt_wp

end VG.Proof.TripleDes.AArch64

end

end

/-!
# Triple DES's core for the modes on AArch64: the registers across the call

The core's `crypt` calls the block function, which overwrites the return
address (`x30`): `crypt` keeps it in `x26`, which the call keeps (it is
callee-saved), and moves it back (`crypt_keeps_x30`). `crypt_keeps_x25`: the
call keeps `x25`, where the feedback modes keep the IV's address. With
`KeepsReg.seq`, `.ite` and `.loop`, `keeps_x30` proves that a mode's code
keeps `x30`, `crypt` being the only code with a call.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Impl.Aes.AArch64 (sb)
open VG.Proof.Modes.AArch64 (KeepsReg addImm_ok runBlock_app)
open VG.Spec.TripleDes (Direction)

/-- `crypt` before the call: the arguments, and the return address to `x26`. -/
def cryptHead : List Instr :=
  [.addImm .x .x0 sb (8 * schedSlot), .addImm .x .x1 sb (8 * cbcBuf), .addImm .x .x2 sb 0, .addImm .x .x26 .x30 0]

/-- `crypt` after the call: `sb` and the return address back. -/
def cryptTail : List Instr := [.addImm .x sb .x2 0, .addImm .x .x30 .x26 0]

theorem crypt_eq (d : Direction) :
    (dirCore d).crypt = .seq (.block cryptHead) (.seq (blockCall d) (.block cryptTail)) := by
  cases d <;> rfl

/-- No instruction of the block function writes `r`. -/
theorem dirBlock_keeps {r : Reg} (hr : r = .x25 ∨ r = .x26) (d : Direction) :
    ∀ i ∈ instrs (dirBlock d), clobbers i r = false := by
  have h : ((instrs (dirBlock d)).all fun i => decide (clobbers i .x25 = false) && decide (clobbers i .x26 = false)) =
      true := by
    cases d
    · change ((instrs encryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs decryptBlock).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  rcases hr with rfl | rfl
  · exact this.1
  · exact this.2

theorem blockCall_keeps {r : Reg} (hr : r = .x25 ∨ r = .x26) (d : Direction) : KeepsReg r (blockCall d) := by
  intro s t s' h
  have hl : r ∉ linkRegs := by rcases hr with rfl | rfl <;> decide
  refine Exec.gpr (fun i hi => ?_) h (.inr hl)
  rw [blockCall_eq] at hi
  exact dirBlock_keeps hr d i (by cases d <;> exact hi)

theorem crypt_keeps_x25 (d : Direction) : KeepsReg .x25 (dirCore d).crypt := by
  rw [crypt_eq]
  exact KeepsReg.seq (Modes.AArch64.keepsReg_of_regSafe (by decide))
    (KeepsReg.seq (blockCall_keeps (.inl rfl) d) (Modes.AArch64.keepsReg_of_regSafe (by decide)))

/-- The block's state from `s`, as a function. -/
theorem block_det {is : List Instr} {s s₁ s' : State} {t : List Leak} (h : Exec isa (.block is) s t s')
    (e : runBlock isa is s = some s₁) : s' = s₁ := by
  have w : WP isa (.block is) s fun x => x = s₁ := WP.of_runBlock ⟨s₁, e, rfl⟩
  obtain ⟨t', s'', he, rfl⟩ := w
  exact (Exec.det h he).2

theorem crypt_keeps_x30_aux (d : Direction) {s s₁ s₂ s' : State} {t₁ t₂ t₃ : List Leak}
    (hA : Exec isa (.block cryptHead) s t₁ s₁) (hC : Exec isa (blockCall d) s₁ t₂ s₂)
    (hB : Exec isa (.block cryptTail) s₂ t₃ s') : s'.gpr .x30 = s.gpr .x30 := by
  obtain ⟨a₁, e₁, -, o₁, -⟩ := addImm_ok s .x0 sb (v := 8 * schedSlot) (by decide)
  obtain ⟨a₂, e₂, -, o₂, -⟩ := addImm_ok a₁ .x1 sb (v := 8 * cbcBuf) (by decide)
  obtain ⟨a₃, e₃, -, o₃, -⟩ := addImm_ok a₂ .x2 sb (v := 0) (by decide)
  obtain ⟨a₄, e₄, r₄, -⟩ := addImm_ok a₃ .x26 .x30 (v := 0) (by decide)
  have hs₁ : s₁ = a₄ := block_det hA (by
    rw [show cryptHead = [.addImm .x .x0 sb (8 * schedSlot)] ++ ([.addImm .x .x1 sb (8 * cbcBuf)] ++
      ([.addImm .x .x2 sb 0] ++ [.addImm .x .x26 .x30 0])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, e₄])
  subst hs₁
  obtain ⟨b₁, f₁, -, ob₁, -⟩ := addImm_ok s₂ sb .x2 (v := 0) (by decide)
  obtain ⟨b₂, f₂, q₂, -⟩ := addImm_ok b₁ .x30 .x26 (v := 0) (by decide)
  have hs' : s' = b₂ := block_det hB (by
    rw [show cryptTail = [.addImm .x sb .x2 0] ++ [.addImm .x .x30 .x26 0] from rfl, runBlock_app, f₁, Option.bind_some, f₂])
  subst hs'
  have k₂ : s₂.gpr .x26 = s₁.gpr .x26 := blockCall_keeps (.inr rfl) d _ _ _ hC
  rw [q₂, ob₁ _ (by decide), k₂, r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), BitVec.add_zero,
    BitVec.add_zero]

theorem crypt_keeps_x30 (d : Direction) : KeepsReg .x30 (dirCore d).crypt := by
  intro s t s' h
  rw [crypt_eq] at h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact crypt_keeps_x30_aux d hA hC hB

/-- `WP.gprs` for `x30`, from `KeepsReg` rather than the absence of calls. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (hk : KeepsReg .x30 c) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hk _ _ _ he⟩

/-- `KeepsReg .x30` of a mode's code: its structure, down to `crypt` and
blocks that do not write `x30`. -/
tactic_template "keeps_x30" : tactic => `(tactic| repeat (first
  | with_reducible exact crypt_keeps_x30 _
  | apply KeepsReg.seq
  | apply KeepsReg.ite
  | apply KeepsReg.loop
  | exact Modes.AArch64.keepsReg_of_regSafe (by decide)))

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `Modes.AArch64.Cfb8`, which only this module used -/

section

/-! ### `Modes.AArch64.Cfb8Loop`, which only this module used -/

section

/-!
# CFB8 on AArch64, for any core: the data loop

As on x86-64 (`Proof/Modes/X86_64/Cfb8Loop.lean`). `cfb8Block_wp`: one
iteration copies the input block `Iⱼ` from the IV to the buffer
(`copyN_wp`), enciphers it there (`BlockSpec.crypt_wp`), XORs the output's
first byte into byte `j` of the data (`cfb8Xor_wp`), making it `cfb8Out`,
and shifts the input block at the IV to `Iⱼ₊₁` (`cfb8Shift_wp`, `cfb8In`).
Blocks are `8 bw` bytes. The IV's address is kept in the register `ivR`,
which the core keeps (`KeepsReg`).
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeW8_apply)

variable {c : Core}

/-- What CFB8's data loop works on: the scratch buffer at `B`, the `n`
bytes at `D`, the input block at `P`. -/
structure C8Pre (c : Core) (s₀ : State) (B D P : Addr) (n : Nat) : Prop where
  scr : ScrIn s₀ B c.total
  dat : (⟨D, n⟩ : Region) ∈ s₀.wr
  ivw : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr
  sepD : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.total⟩
  sepP : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩
  sepPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩
  fitD : D.toNat + n ≤ 2 ^ 64
  small : n < 2 ^ 64

/-- The data loop, before byte `j`; `m₀` is the memory on entry, `iv` the
IV. -/
structure C8Inv (cs : BlockSpec c) (enc : Bool) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  ready : cs.Ready s B k
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 j
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) =
    if q < j then cfb8Out enc (cs.cipher k) m₀ D iv q else m₀ (D + BitVec.ofNat 64 q)
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = P

/-- The data loop, done. -/
structure C8Done (cs : BlockSpec c) (enc : Bool) (ivR : Reg) (s₀ : State) (m₀ : Mem) (B D P : Addr) (n : Nat)
    (k : cs.Key) (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  saved : ∀ i < 10, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  ivB : ∀ u < 8 * c.bw, s.mem (P + BitVec.ofNat 64 u) = (cfb8In enc (cs.cipher k) m₀ D iv n).getD u 0
  data : ∀ q < n, s.mem (D + BitVec.ofNat 64 q) = cfb8Out enc (cs.cipher k) m₀ D iv q
  frame : Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ivK : s.gpr ivR = P

theorem headD_eq_getD (l : List Byte) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem writeW8_frame (m : Mem) (A : Addr) (b : Byte) : Frame [⟨A, 1⟩] m (m.writeW A b) := fun x hx => by
  rw [writeW8_apply, ite_eq_right (fun h => hx _ List.mem_cons_self (by
    subst h; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []))]

theorem cfb8Block_wp (cs : BlockSpec c) (enc : Bool) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D P : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n)
    (hsc : KeepsReg ivR c.crypt) {j : Nat} {s : State} (hi : C8Inv cs enc ivR s₀ m₀ B D P n k iv j s) :
    WP isa (c.cfb8Block enc ivR) s fun s' =>
      (isa.eval (.nonzero .x c.leftReg) s' = some false ∧ C8Done cs enc ivR s₀ m₀ B D P n k iv s') ∨
      (isa.eval (.nonzero .x c.leftReg) s' = some true ∧ C8Inv cs enc ivR s₀ m₀ B D P n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbI := hL.bufImm
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hn64 := hp.small
  have hj := hi.lt
  obtain hL0 : 0 < 8 * c.bw := by omega_arith
  obtain hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨down, dsb, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨lown, lsb, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨d6, d7, -⟩ := not_own down
  obtain ⟨l6, l7, -⟩ := not_own lown
  obtain ⟨iown, idr, ilr⟩ := of_not_modeRegs hivR
  obtain ⟨i6, i7, -⟩ := not_own iown
  obtain p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 j
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  let S : Region := ⟨B, 8 * c.total⟩
  obtain hwS : S ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  obtain hwD : (⟨D, n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.ivw
  obtain subT : Region.Sub ⟨T, 8 * c.bw⟩ S := VG.Offset.sub_base B (by omega_arith)
  obtain subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  obtain subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega_arith)
  obtain subA : Region.Sub ⟨A, 1⟩ ⟨D, n⟩ := VG.Offset.sub_base D (by omega_arith)
  obtain dTP : Region.Disjoint ⟨T, 8 * c.bw⟩ ⟨P, 8 * c.bw⟩ := (hp.sepP.sub_right subT).symm
  obtain dAP : Region.Disjoint ⟨A, 1⟩ ⟨P, 8 * c.bw⟩ := (hp.sepPD.sub_right subA).symm
  obtain dAS : Region.Disjoint ⟨A, 1⟩ S := hp.sepD.sub_left subA
  obtain dPcore : Region.Disjoint ⟨P, 8 * c.bw⟩ (coreRegion c B) := hp.sepP.sub_right subCore
  obtain dDcore : Region.Disjoint ⟨D, n⟩ (coreRegion c B) := hp.sepD.sub_right subCore
  obtain inS : ∀ {d m : Nat}, d + m ≤ 8 * c.total → InRegions s.wr (B + BitVec.ofNat 64 d) m := fun h =>
    ⟨_, hwS, VG.Offset.contains_base B h (by omega_arith)⟩
  obtain inA : InRegions s.wr A 1 := ⟨_, hwD, VG.Offset.contains_base D (by omega_arith) (by omega_arith)⟩
  obtain slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega_arith)
  obtain slotOut : ∀ i < 10, ∀ {R : Region}, (R = ⟨T, 8 * c.bw⟩ ∨ R = coreRegion c B ∨ R = ⟨A, 1⟩ ∨
      R = ⟨P, 8 * c.bw⟩) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi10 R hR => by
    rcases hR with rfl | rfl | rfl | rfl
    · exact VG.Offset.disjoint B (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact VG.Offset.disjoint_base B (by omega_arith) (by omega_arith)
    · exact (dAS.sub_right (slotIn i hi10)).symm
    · exact (hp.sepP.sub_right (slotIn i hi10)).symm
  -- The input block to the buffer.
  unfold Core.cfb8Block
  refine WP.seq (WP.mono_syms (copyN_wp (k := c.bw) (t := .x6) (u := .x6) (rd := sb) (rs := ivR) (od := 8 * c.buf)
    (os := 0) (P := T) (Q := P)
    ⟨hi.base ▸ rfl, by rw [hi.ivK]; simp, by decide, Ne.symm i6, by decide, Ne.symm i6, by omega_arith, by decide,
      by omega_arith, by omega_arith, fun w hw => by rw [addr_add]; exact inS (by omega_arith),
      fun w hw => inRd ⟨_, hwP, VG.Offset.contains_base P (by omega_arith) (by omega_arith)⟩, dTP, by omega_arith⟩) fun s₁ h₁ sy₁ => ?_)
  have mem₁ : s₁.mem = over s.mem T (8 * c.bw) fun i => s.mem (P + BitVec.ofNat 64 i) := h₁.mem
  obtain f₁ : Frame [⟨T, 8 * c.bw⟩] s.mem s₁.mem := by rw [mem₁]; exact over_frame _ _ _ _
  obtain g₁ : ∀ x, x ≠ .x6 → s₁.gpr x = s.gpr x := fun x h => h₁.regs x h h
  obtain base₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hi.base]
  obtain ready₁ : cs.Ready s₁ B k := cs.ready_frame hi.ready f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr subTbuf)
    ⟨fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hwS, subT⟩, h₁.rd, h₁.wr, sy₁⟩
    fun r hr => by
    obtain ⟨h1, -, -⟩ := of_not_modeRegs hr; exact g₁ r (not_own h1).1
  obtain rd₁ : s₁.rd = s₀.rd := by rw [h₁.rd, hi.rd]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [h₁.wr, hi.wr]
  -- Enciphered.
  refine WP.seq (WP.mono (WP.keepReg hsc (cs.crypt_wp base₁ ⟨by rw [wr₁]; exact hp.scr.wr, hfit⟩ ready₁))
    fun s₂ ⟨⟨base₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, i₂⟩ => ?_)
  obtain eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  obtain hX : bytesAt s₁.mem T (8 * c.bw) = cfb8In enc ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [cfb8In_length enc ciph m₀ D hiv hL0])
    intro u h1 _
    obtain hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [mem₁, over_at hu (by omega_arith), hi.ivB u hu, List.getElem_eq_getD 0]
  obtain T₂ : s₂.mem T = (ciph (cfb8In enc ciph m₀ D iv j)).headD 0 := by
    obtain h0 := bytesAt_getD s₂.mem T hL0
    rw [p0] at h0
    rw [← h0, ← eT, ks₂ 0 hG0, eT, hX, headD_eq_getD]
  -- The memory outside the buffer and the core, as before.
  obtain out₂ : ∀ x, (∀ R ∈ [(⟨T, 8 * c.bw⟩ : Region), coreRegion c B], ¬ R.Contains x 1) → s₂.mem x = s.mem x :=
    fun x hx => by
      rw [f₂ x (fun R hR => hx R (by simp only [List.mem_singleton] at hR; subst hR; simp)),
        f₁ x (fun R hR => hx R (by simp only [List.mem_singleton] at hR; subst hR; simp))]
  obtain A₂ : s₂.mem A = m₀ A := by
    rw [out₂ A (fun R hR hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact (dAS.sub_right subT) A (Region.contains_self A 1) hc
      · exact (dAS.sub_right subCore) A (Region.contains_self A 1) hc)]
    have := hi.data j hj
    rw [ite_eq_right (Nat.lt_irrefl _)] at this
    exact this
  obtain data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, g₁ _ d6, hi.dataR]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, rd₁]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  obtain iv₂ : s₂.gpr ivR = P := by rw [i₂, g₁ _ i6, hi.ivK]
  -- The byte.
  refine WP.block_append (WP.block_append (WP.mono_syms (cfb8Xor_wp enc (T := T) hbI data₂ (by rw [base₂]) d6 d7
    (by rw [wr₂', ← hi.wr]; exact inA)
    (by rw [rd₂', wr₂', ← hi.rd, ← hi.wr]; exact inRd (inS (by omega_arith))))
    fun s₃ ⟨g₃, rd₃, wr₃, m₃, x₃⟩ sy₃ => ?_))
  obtain cj : (s₃.gpr .x6).setWidth 8 = cfb8C enc ciph m₀ D iv j := by
    rw [x₃, A₂, T₂]; rfl
  -- The shift.
  refine WP.mono_syms (cfb8Shift_wp (c := c) (P := P) i7 (by rw [g₃ _ i6 i7, iv₂]) (by rw [wr₃, wr₂']; exact hp.ivw) hbw0 hbw2)
    fun s₄ ⟨g₄, rd₄, wr₄, P₄, f₄⟩ sy₄ => ?_
  -- On to the next byte.
  obtain ⟨s₅a, e₅a, a₅a, o₅a, m₅a, rd₅a, wr₅a⟩ := addImm_ok s₄ c.dataReg c.dataReg (v := 1) (by decide)
  obtain ⟨s₅, e₅, l₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₅a c.leftReg c.leftReg (v := 1) (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [Core.cfb8Next, show ([.addImm .x c.dataReg c.dataReg 1, .subImm .x c.leftReg c.leftReg 1] : List Instr) =
      [.addImm .x c.dataReg c.dataReg 1] ++ [.subImm .x c.leftReg c.leftReg 1] from rfl, runBlock_app, e₅a,
      Option.bind_some, e₅], ?_⟩
  obtain keep₅ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ c.dataReg → x ≠ c.leftReg → s₅.gpr x = s₂.gpr x :=
    fun x h1 h2 h3 h4 => by rw [o₅ x h4, o₅a x h3, g₄ x h2, g₃ x h1 h2]
  obtain left₄ : s₅a.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [o₅a _ (Ne.symm hdl), g₄ _ l7, g₃ _ l6 l7, lr₂, g₁ _ l6, hi.leftR]
  obtain left₅ : s₅.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₅, left₄, VG.Offset.ofNat_sub_ofNat (by omega_arith), show n - j - 1 = n - (j + 1) by omega_arith]
  obtain hz₅ : isa.eval (.nonzero .x c.leftReg) s₅ = some !(decide (j + 1 = n)) := by
    rw [eval_nonzero, left₅, ofNat_beq_zero (by omega_arith), decide_eq_decide.mpr (show n - (j + 1) = 0 ↔ j + 1 = n by omega_arith)]
  obtain data₅ : s₅.gpr c.dataReg = D + BitVec.ofNat 64 (j + 1) := by
    rw [o₅ _ hdl, a₅a, g₄ _ d7, g₃ _ d6 d7, data₂, addr_add]
  obtain mem₅ : s₅.mem = s₄.mem := by rw [m₅, m₅a]
  obtain base₅ : s₅.gpr sb = B := by
    rw [keep₅ _ (by decide) (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
  obtain ivK₅ : s₅.gpr ivR = P := by rw [keep₅ _ i6 i7 idr ilr, iv₂]
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₅a, rd₄, rd₃, rd₂']
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₅a, wr₄, wr₃, wr₂']
  -- What changed after `crypt`: the data's byte and the input block.
  obtain f₅ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₅.mem := by
    rw [mem₅]
    refine (?_ : Frame [⟨A, 1⟩, ⟨P, 8 * c.bw⟩] s₂.mem s₃.mem).trans
      (f₄.mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp)
    rw [m₃]; exact (writeW8_frame _ _ _).mono fun R hR => by simp only [List.mem_singleton] at hR; subst hR; simp
  obtain ready₅ : cs.Ready s₅ B k := cs.ready_frame ready₂ f₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (dDcore.sub_left subA).symm
    · exact .inl dPcore.symm)
    ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwD, subA⟩
      · exact ⟨_, by rw [wr₂, wr₁, ← hi.wr]; exact hwP, fun _ h => h⟩,
      by rw [rd₅, rd₅a, rd₄, rd₃], by rw [wr₅, wr₅a, wr₄, wr₃],
      by rw [runBlock_syms e₅, runBlock_syms e₅a, sy₄, sy₃]⟩ fun r hr => by
    obtain ⟨h1, h2, h3⟩ := of_not_modeRegs hr
    exact keep₅ r (not_own h1).1 (not_own h1).2.1 h2 h3
  obtain saved₅ : ∀ i < 10, s₅.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi10 => by
    rw [← hi.saved i hi10]
    refine (f₅.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact slotOut i hi10 (.inr (.inr (.inl rfl)))
      · exact slotOut i hi10 (.inr (.inr (.inr rfl)))) (by decide)).trans ?_
    refine (f₂.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact slotOut i hi10 (.inr (.inl rfl))) (by decide)).trans ?_
    exact f₁.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact slotOut i hi10 (.inl rfl)) (by decide)
  obtain fr₅ : Frame [S, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s₅.mem :=
    hi.frame.trans (((f₁.sub fun r hr => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subT⟩).trans
      (f₂.sub fun r hr => ⟨S, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩)).trans
      (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩))
  -- The input block and the data.
  obtain hPout : ∀ u < 8 * c.bw, s₃.mem (P + BitVec.ofNat 64 u) = s.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    obtain hc : (⟨P, 8 * c.bw⟩ : Region).Contains (P + BitVec.ofNat 64 u) 1 :=
      VG.Offset.contains_base P (by omega_arith) (by omega_arith)
    rw [m₃, writeW8_apply, ite_eq_right (fun h => dAP _ (by rw [h]; exact Region.contains_self A 1) hc),
      out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact dTP _ hR' hc
        · exact dPcore _ hc hR')]
  obtain ivB₅ : ∀ u < 8 * c.bw, s₅.mem (P + BitVec.ofNat 64 u) = (cfb8In enc ciph m₀ D iv (j + 1)).getD u 0 :=
    fun u hu => by
      rw [mem₅, P₄ u hu, cfb8In_succ_getD enc ciph m₀ D hiv hL0 j hu]
      split
      · rename_i h; rw [hPout _ h, hi.ivB _ h]
      · rw [cj]
  obtain data₅' : ∀ q < n, s₅.mem (D + BitVec.ofNat 64 q) =
      if q < j + 1 then cfb8Out enc ciph m₀ D iv q else m₀ (D + BitVec.ofNat 64 q) := fun q hq => by
    obtain hcD : (⟨D, n⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := VG.Offset.contains_base D (by omega_arith) (by omega_arith)
    obtain hnP : ¬ (⟨P, 8 * c.bw⟩ : Region).Contains (D + BitVec.ofNat 64 q) 1 := fun h => hp.sepPD _ h hcD
    rw [mem₅, f₄ _ (fun R hR => by simp only [List.mem_singleton] at hR; subst hR; exact hnP), m₃, writeW8_apply]
    by_cases hqj : q = j
    · rw [ite_eq_left (by rw [hqj]), ite_eq_left (by omega_arith), A₂, T₂, hqj]; rfl
    · have hne : D + BitVec.ofNat 64 q ≠ A := fun h => hqj (by
        have := (sub_eq_iff (x := D + BitVec.ofNat 64 q) (P := D) (i := j) (by omega_arith)).mp h
        rwa [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this)
      rw [ite_eq_right hne, out₂ _ (fun R hR hR' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · exact (hp.sepD.sub_right subT) _ hcD hR'
        · exact dDcore _ hcD hR'), hi.data q hq]
      by_cases h3 : q < j
      · rw [ite_eq_left h3, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right h3, ite_eq_right (by omega_arith)]
  by_cases hdone : j + 1 = n
  · exact .inl ⟨by rw [hz₅, decide_eq_true hdone]; rfl, base₅, saved₅, by rw [← hdone]; exact ivB₅,
      fun q hq => by rw [data₅' q hq, ite_eq_left (by omega_arith)], fr₅, rd₅', wr₅', ivK₅⟩
  · exact .inr ⟨by rw [hz₅, decide_eq_false hdone]; rfl, base₅, ready₅, saved₅, data₅, left₅, by omega_arith, ivB₅,
      data₅', fr₅, rd₅', wr₅', ivK₅⟩

/-- The data loop. -/
theorem cfb8Loop_wp (cs : BlockSpec c) (enc : Bool) {ivR : Reg} (hivR : ivR ∉ modeRegs c) {s₀ : State} {m₀ : Mem}
    {B D P : Addr} {n : Nat} {k : cs.Key} {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : C8Pre c s₀ B D P n)
    (hsc : KeepsReg ivR c.crypt) {s : State} (hi : C8Inv cs enc ivR s₀ m₀ B D P n k iv 0 s) :
    WP isa (.loop (c.cfb8Block enc ivR) (.nonzero .x c.leftReg)) s (C8Done cs enc ivR s₀ m₀ B D P n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ C8Inv cs enc ivR s₀ m₀ B D P n k iv j s)
    (fun m s hs => ?_) n s ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (cfb8Block_wp cs enc hivR hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - (j + 1), by have := d.lt; have := hj.lt; omega_arith, j + 1, rfl, d⟩

end VG.Proof.Modes.AArch64

end

end


/-!
# CFB8 on AArch64, for any core: the whole function

`cfb8_wp`: `c.cfb8 enc r ivR`, for a core `c` with `BlockSpec c` whose
cipher is the forward cipher `CIPH_K`, its arguments in the registers `r`,
and the input block's address kept in `ivR` (which the core keeps:
`KeepsReg`), replaces the `n` bytes at `D` with CFB8's output (`cfb8Out`)
under the key `k` that its key arguments give, from the input block at `P`,
and that block with the input block after the last byte (`cfb8In`); it
keeps the callee-saved registers `x19`–`x28`, and writes nothing but the
scratch buffer, the data and the input block. As on x86-64
(`Proof/TripleDes/X86_64/FbVerified.lean`); `cfb8Enc_of` and `cfb8Dec_of`
(`Proof/Modes/Cfb8.lean`) state these as the specification's.
-/

@[expose] public section

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

theorem cfb8_wp (cs : BlockSpec c) (enc : Bool) {r : CtrRegs} (hr : RegsOk r) (hdn : c.dataReg ≠ r.n) {ivR : Reg}
    (hiv : IvRegOk c r ivR) {s₀ : State} {B P D : Addr} {n : Nat} {k : cs.Key} (hB : s₀.gpr r.scr = B)
    (hP : s₀.gpr r.ctr = P) (hD : s₀.gpr r.data = D) (hn : (s₀.gpr r.n).toNat = n) (hs : ScrIn s₀ B c.total)
    (hwP : (⟨P, 8 * c.bw⟩ : Region) ∈ s₀.wr) (hwD : (⟨D, n⟩ : Region) ∈ s₀.wr)
    (sPS : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨B, 8 * c.total⟩) (sDS : Region.Disjoint ⟨D, n⟩ ⟨B, 8 * c.total⟩)
    (sPD : Region.Disjoint ⟨P, 8 * c.bw⟩ ⟨D, n⟩) (fitD : D.toNat + n ≤ 2 ^ 64)
    (hk : cs.KeyArgs s₀ [⟨B, 8 * c.total⟩] k) (hsc : KeepsReg ivR c.prepare ∧ KeepsReg ivR c.crypt) :
    WP isa (c.cfb8 enc r ivR) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Core.savedRegs.getD i .x19) = s₀.gpr (Core.savedRegs.getD i .x19)) ∧
      bytesAt s'.mem D n = (List.range n).map (cfb8Out enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw))) ∧
      bytesAt s'.mem P (8 * c.bw) = cfb8In enc (cs.cipher k) s₀.mem D (bytesAt s₀.mem P (8 * c.bw)) n ∧
      Frame [⟨B, 8 * c.total⟩, ⟨D, n⟩, ⟨P, 8 * c.bw⟩] s₀.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  obtain hL0 : 0 < 8 * c.bw := by omega_using [hbw0]
  obtain hn64 : n < 2 ^ 64 := by rw [← hn]; exact BitVec.isLt _
  obtain hN : 8 * c.total < 2 ^ 64 := by omega_using [hsm]
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨-, dsb, dk⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨-, lsb, lk⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨cs', -⟩ := not_setupRegs hr.ctr
  obtain ⟨ds', -⟩ := not_setupRegs hr.data
  obtain ⟨ns', -⟩ := not_setupRegs hr.n
  obtain ⟨-, idr, ilr⟩ := of_not_modeRegs hiv.mode
  obtain ⟨isb, -⟩ := not_setupRegs hiv.setup
  let S : Region := ⟨B, 8 * c.total⟩
  obtain subMode : Region.Sub (modeRegion c B) S := VG.Offset.sub_base B (by omega_using [hroom])
  obtain subCore : Region.Sub (coreRegion c B) S := Region.sub_prefix (by omega_using [hroom])
  obtain slotIn : ∀ i < 10, Region.Sub ⟨wordAddr B (c.slots + i), 8⟩ S := fun i hi =>
    VG.Offset.sub_base B (by omega_using [hroom, hi])
  obtain slotCore : ∀ i < 10, Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ (coreRegion c B) := fun i hi =>
    VG.Offset.disjoint_base B (by omega_using []) (by omega_using [hsm, hroom, hi])
  -- The entry.
  obtain ⟨sE, eE, bE, svE, fE, gE, rdE, wrE⟩ := entry_ok hsm hroom s₀ hB hs
  obtain ⟨sS, eS, xS, gS, mS, rdS, wrS⟩ := movR_ok sE ivR r.ctr
  obtain ⟨sA, eA, drA, lrA, gA, mA, rdA, wrA⟩ := ctrArgs_ok sS r hdn hdl
  unfold Core.cfb8
  refine WP.seq (WP.of_runBlock ⟨sA, by
    rw [Core.fbEntry, runBlock_app, runBlock_app, eE, Option.bind_some, eS, Option.bind_some, eA], ?_⟩)
  obtain gA' : ∀ x, x ≠ sb → x ≠ ivR → x ≠ c.dataReg → x ≠ c.leftReg → sA.gpr x = s₀.gpr x :=
    fun x h1 h2 h3 h4 => by rw [gA x h3 h4, gS x h2, gE x h1]
  obtain bA : sA.gpr sb = B := by rw [gA _ (Ne.symm dsb) (Ne.symm lsb), gS _ (Ne.symm isb), bE]
  obtain ivA : sA.gpr ivR = P := by rw [gA _ idr ilr, xS, gE _ cs', hP]
  obtain rdA' : sA.rd = s₀.rd := by rw [rdA, rdS, rdE]
  obtain wrA' : sA.wr = s₀.wr := by rw [wrA, wrS, wrE]
  obtain fA : Frame [S] s₀.mem sA.mem := by
    rw [mA, mS]
    exact fE.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subMode⟩
  obtain svA : ∀ i < 10, sA.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by rw [mA, mS, svE i hi]
  obtain kr := keyRegs_ne cs.keyRegs_ok
  obtain hkA : cs.KeyArgs sA [S] k :=
    cs.keyArgs_congr hk (fun x hx => gA' x (not_setupRegs (kr x hx)).1 (fun e => hiv.key (e ▸ hx))
      (fun e => dk (e ▸ hx)) (fun e => lk (e ▸ hx))) rdA' wrA'
      (by rw [runBlock_syms eA, runBlock_syms eS, runBlock_syms eE]) fA
  -- The key.
  refine WP.seq (WP.mono (WP.keepReg hsc.1 (cs.prepare_wp bA ⟨by rw [wrA']; exact hs.wr, hs.fit⟩
    List.mem_cons_self hkA)) fun s₄ ⟨⟨ready₄, b₄, dr₄, lr₄, f₄, rd₄, wr₄⟩, iv₄⟩ => ?_)
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rdA']
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wrA']
  obtain ivR₄ : s₄.gpr ivR = P := by rw [iv₄, ivA]
  obtain sv₄ : ∀ i < 10, s₄.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.gpr (Core.savedRegs.getD i .x19) :=
    fun i hi => by
      rw [← svA i hi]
      exact f₄.readW (Region.contains_self _ _) (fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact slotCore i hi) (by decide)
  obtain left₄ : s₄.gpr c.leftReg = s₀.gpr r.n := by rw [lr₄, lrA, gS _ (Ne.symm hiv.n), gE _ ns']
  obtain hz₄ : isa.eval (.zero .x c.leftReg) s₄ = some (decide (n = 0)) := by
    rw [eval_zero, left₄]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by rw [← hn, h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [hn, h]; rfl)⟩
  obtain dDcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨D, n⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sDS.sub_right subCore
  obtain dPcore : ∀ x ∈ [coreRegion c B], Region.Disjoint ⟨P, 8 * c.bw⟩ x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact sPS.sub_right subCore
  obtain m₄P : ∀ u < 8 * c.bw, s₄.mem (P + BitVec.ofNat 64 u) = s₀.mem (P + BitVec.ofNat 64 u) := fun u hu => by
    rw [f₄.bytes (R := ⟨P, 8 * c.bw⟩) dPcore (show 8 * c.bw ≤ 2 ^ 64 by omega_using [hbw2]) hu]
    exact fA.bytes (R := ⟨P, 8 * c.bw⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sPS)
      (show 8 * c.bw ≤ 2 ^ 64 by omega_using [hbw2]) hu
  obtain m₄D : ∀ q < n, s₄.mem (D + BitVec.ofNat 64 q) = s₀.mem (D + BitVec.ofNat 64 q) := fun q hq => by
    rw [f₄.bytes (R := ⟨D, n⟩) dDcore (show n ≤ 2 ^ 64 by omega_using [hn]) hq]
    exact fA.bytes (R := ⟨D, n⟩) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact sDS)
      (show n ≤ 2 ^ 64 by omega_using [hn]) hq
  let iv := bytesAt s₀.mem P (8 * c.bw)
  obtain hivl : iv.length = 8 * c.bw := by simp [iv, bytesAt]
  obtain hp : C8Pre c s₄ B D P n := ⟨⟨by rw [wr₄']; exact hs.wr, hs.fit⟩, by rw [wr₄']; exact hwD,
    by rw [wr₄']; exact hwP, sDS, sPS, sPD, fitD, hn64⟩
  obtain fr₄ : Frame [S] s₀.mem s₄.mem :=
    fA.trans (f₄.sub fun x hx => ⟨S, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx; exact subCore⟩)
  -- The bytes.
  refine WP.seq (WP.mono (M := isa) (Q := C8Done cs enc ivR s₄ s₀.mem B D P n k iv)
    (WP.ite (decide (n = 0)) hz₄ (fun h0 => ?_) (fun h0 => ?_)) fun s₆ d₆ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨b₄, fun _ _ => rfl, fun u hu => by rw [hn0, m₄P u hu]; simp [cfb8In, iv, bytesAt, hu],
      fun q hq => by omega, Frame.refl _ _, rfl, rfl, ivR₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine cfb8Loop_wp cs enc hiv.mode hivl hp hsc.2 ⟨b₄, ready₄, fun _ _ => rfl, ?_, ?_, by omega_using [hn0],
      fun u hu => by rw [m₄P u hu]; simp [cfb8In, iv, bytesAt, hu], fun q hq => ?_, Frame.refl _ _, rfl, rfl, ivR₄⟩
    · rw [dr₄, drA, gS _ (Ne.symm hiv.data), gE _ ds', hD]; simp
    · rw [left₄, Nat.sub_zero, ← hn]; simp
    · rw [ite_eq_right (Nat.not_lt_zero _)]; exact m₄D q hq
  -- The exit.
  obtain rd₆ : s₆.rd = s₀.rd := by rw [d₆.rd, rd₄']
  obtain wr₆ : s₆.wr = s₀.wr := by rw [d₆.wr, wr₄']
  obtain hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  obtain hinj : ∀ i < 10, ∀ j < 10, Core.savedRegs.getD i .x19 = Core.savedRegs.getD j .x19 → i = j := by decide
  obtain ⟨s₈, e₈, v₈, -, m₈, rd₈, wr₈⟩ := loads_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₆
    d₆.base hsv hinj (by omega_using [hsm, hroom]) (fun i hi' => by
      rw [rd₆, wr₆]
      exact inRd (slot_wr hs.wr hN (by omega_using [hroom, hi'])))
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi' => ?_, ?_, ?_, ?_, by rw [rd₈, rd₆], by rw [wr₈, wr₆]⟩
  · rw [v₈ i hi', d₆.saved i hi', sv₄ i hi']
  · rw [m₈]
    apply List.ext_getElem (by simp [bytesAt])
    intro q h1 _
    obtain hq : q < n := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact d₆.data q hq
  · rw [m₈]
    apply List.ext_getElem (by
      rw [cfb8In_length (iv := bytesAt s₀.mem P (8 * c.bw)) enc _ _ _ (by simp [bytesAt]) hL0]; simp [bytesAt])
    intro u h1 _
    obtain hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [d₆.ivB u hu, List.getElem_eq_getD 0]
    rfl
  · rw [m₈]
    exact (fr₄.mono fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self).trans
      d₆.frame

end VG.Proof.Modes.AArch64

end

end

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on AArch64 meet their contracts

`ofb_wp`, …, `cfb8Decrypt_wp`: the modes' OFB, CFB and CFB8
(`Proof.Modes.AArch64.fb_wp`, `cfb8_wp`) over the table core
(`tableCoreSpec`), with the IV's address in `x28`, which the core
never writes (`keepsReg_of_regSafe`), and the specification's results
(`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each is correct and constant
time, by the taint analysis: the pointers, `n` (or `len`) and the stack
pointer are public, and so is everything the code computes from them, which
it keeps in registers that the block never reloads from the scratch buffer;
the IV is secret. `ofb_framed`, … run them with their working space on the
stack, zeroed on return: 560 bytes, the 70 words of the scratch buffer.

`cfbDecrypt_wp`: the modes' batched CFB decryption
(`Proof.Modes.AArch64.CfbDec.batched_wp`) over the batched core for
encryption (`batchCoreSpec .encrypt`), with that core's precondition
(`batchPre`) and working space: 1120 bytes, its 140 words.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The precondition of the feedback modes on AArch64, with the data `len`
bytes long and the working space at `x4`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 384⟩
  let iv : Region := ⟨s.gpr .x1, 8⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 70⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 70 ≤ 2 ^ 64

/-- The precondition of the modes over the batched core (`batchCore`), on
AArch64: `fbPre` with that core's working space, 140 words. -/
def batchPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .x0, 384⟩
  let iv : Region := ⟨s.gpr .x1, 8⟩
  let data : Region := ⟨s.gpr .x2, len s⟩
  let scratch : Region := ⟨s.gpr .x4, 8 * 140⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x0).toNat + 384 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8 * 140 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .x3).toNat

/-- `len` bytes. -/
abbrev byteLen (s : State) : Nat := (s.gpr .x3).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0))
abbrev ivOf (s : State) : List Byte := Spec.TripleDes.bytesAt s.mem (s.gpr .x1) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.TripleDes.cbcBlocksAt m (s.gpr .x2) (s.gpr .x3).toNat

def ofbAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := fbPub

def cfbEncAArch64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecAArch64 : Contract isa where
  pre := batchPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

def cfb8EncAArch64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .x2) (byteLen s) =
      Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 = Spec.Cfb8.next (ivOf s)
      (Spec.Cfb8.encrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)))
  pub := fbPub

def cfb8DecAArch64 : Contract isa where
  pre := fbPre byteLen
  post s s' := Spec.TripleDes.bytesAt s'.mem (s.gpr .x2) (byteLen s) =
      Spec.Cfb8.decrypt (ciphOf s) (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s)) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cfb8.next (ivOf s) (Spec.TripleDes.bytesAt s.mem (s.gpr .x2) (byteLen s))
  pub := fbPub

/-- The core keeps `x28`, where the modes keep the IV's address. -/
theorem keeps_x28 :
    Modes.AArch64.KeepsReg .x28 tableCore.prepare ∧ Modes.AArch64.KeepsReg .x28 tableCore.crypt :=
  ⟨Modes.AArch64.keepsReg_of_regSafe (by decide), Modes.AArch64.keepsReg_of_regSafe (by
    show Modes.AArch64.regSafe .x28 tableCrypt = true
    lit_decide)⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa (tableCore.fb mo fbRegs .x28) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 70⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp tableCoreSpec mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x28)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x28)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [tableCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

/-- What the modes' CFB8 gives: the data and the input block as `cfb8Out`
and `cfb8In`, keeping the callee-saved registers. -/
theorem cfb8_wp' (enc : Bool) {s₀ : State} (hp : fbPre byteLen s₀) :
    WP isa (tableCore.cfb8 enc fbRegs .x28) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x2) (byteLen s₀) =
        (List.range (byteLen s₀)).map (Modes.cfb8Out enc (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.cfb8In enc (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (byteLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 70⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cfb8_wp tableCoreSpec enc (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x28)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x28)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [tableCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbAArch64.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbAArch64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncAArch64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncAArch64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecAArch64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 140⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.CfbDec.batched_wp (batchCoreSpec .encrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩) fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, ?_⟩
  rw [batchCore_bw, Nat.mul_one] at hdata hiv
  refine ⟨?_, ?_⟩
  · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
  · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq]; exact hiv

theorem ivOf_ne (s : State) : ivOf s ≠ [] := by simp [ivOf, Spec.TripleDes.bytesAt]

theorem cfb8Encrypt_wp {s₀ : State} (hp : cfb8EncAArch64.pre s₀) :
    WP isa cfb8Encrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfb8EncAArch64.post s₀ s' :=
  WP.mono (cfb8_wp' true hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Enc_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .x2) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : cfb8DecAArch64.pre s₀) :
    WP isa cfb8Decrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfb8DecAArch64.post s₀ s' :=
  WP.mono (cfb8_wp' false hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfb8Dec_of (ciphOf s₀) s₀.mem (byteLen s₀) (s₀.gpr .x2) (ivOf s₀) (ivOf_ne s₀)
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-! ## Constant time -/

theorem fbTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : fbPre len s₁) (_ : fbPre len s₂)
    (hp : fbPub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem batchTaint_agree {len : State → Nat} (s₁ s₂ : State) (_ : batchPre len s₁) (_ : batchPre len s₂)
    (hp : fbPub s₁ s₂) : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 70⟩]

/-- A state satisfying the batched modes' precondition (one block). -/
def batchSat : State := { fbSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 8 * 140⟩] }

def cfb8Sat : State := { fbSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 70⟩] }

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one block (or byte) at `0x3000`. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]

def cfb8FrameSat : State := { fbFrameSat with wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩] }

theorem ofb_verified :
    Verified AArch64.target ofb (Proof.TripleDes.fbScratchContract AArch64.abi 70 Proof.TripleDes.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofb_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.ofbPost, ofbAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt (Proof.TripleDes.fbScratchContract AArch64.abi 70 Proof.TripleDes.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Proof.TripleDes.cfbEncPost, cfbEncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [fbSat] using fbSat)

theorem cfb8Encrypt_verified :
    Verified AArch64.target cfb8Encrypt
      (Proof.TripleDes.cfb8ScratchContract AArch64.abi 70 Proof.TripleDes.cfb8EncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfb8Encrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8EncPost, cfb8EncAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [cfb8Sat]
      using cfb8Sat)

theorem cfb8Decrypt_verified :
    Verified AArch64.target cfb8Decrypt
      (Proof.TripleDes.cfb8ScratchContract AArch64.abi 70 Proof.TripleDes.cfb8DecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfb8Decrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig,
      Proof.TripleDes.cfb8DecPost, cfb8DecAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [cfb8Sat]
      using cfb8Sat)

theorem ofbFrameSat_pre : ∃ s, (Spec.TripleDes.ofbContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.ofbContract, Spec.TripleDes.ofbSig, AArch64.abi, AArch64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.TripleDes.cfbEncryptContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.cfbEncryptContract, Spec.TripleDes.cfbSig, Spec.TripleDes.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.TripleDes.cfbDecryptContract AArch64.abi 1120).pre s := by
  implies_sat [Spec.TripleDes.cfbDecryptContract, Spec.TripleDes.cfbSig, Spec.TripleDes.ofbSig, AArch64.abi,
    AArch64.argRegs] [fbFrameSat] using fbFrameSat

theorem cfb8EncFrameSat_pre : ∃ s, (Spec.TripleDes.cfb8EncryptContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.cfb8EncryptContract, Spec.TripleDes.cfb8Sig, AArch64.abi, AArch64.argRegs]
    [cfb8FrameSat] using cfb8FrameSat

theorem cfb8DecFrameSat_pre : ∃ s, (Spec.TripleDes.cfb8DecryptContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.cfb8DecryptContract, Spec.TripleDes.cfb8Sig, AArch64.abi, AArch64.argRegs]
    [cfb8FrameSat] using cfb8FrameSat

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 ofb)
      (Spec.TripleDes.ofbContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.TripleDes.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) ofb_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.TripleDes.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- CFB8 encryption with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.TripleDes.cfb8EncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) cfb8Encrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfb8EncPostOut_local _) cfb8EncFrameSat_pre

/-- CFB8 decryption with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.TripleDes.cfb8DecPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) cfb8Decrypt_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cfb8DecPostOut_local _) cfb8DecFrameSat_pre

end VG.Proof.TripleDes.AArch64
