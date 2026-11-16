module

import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Modes.AArch64.Core
import VerifiedGarbage.Proof.Modes.AArch64.Words
public import VerifiedGarbage.Impl.TripleDes.AArch64.Cbc
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
public import VerifiedGarbage.Proof.TripleDes.AArch64.Pre
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Batch
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Block
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Bswap

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
