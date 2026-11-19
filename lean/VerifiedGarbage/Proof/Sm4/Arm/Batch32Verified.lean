module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchCT
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
import VerifiedGarbage.Proof.Sm4.Arm.BatchTaint
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.Ctr32Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
public import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Sm4
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Modes.Arm.Counter32
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Modes.Arm.Ops
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Inline

/-! ### `Sm4.Arm.Batch32Taint`, which only this module used -/

section

/-!
# Taint check for the group head of SM4's counter mode with `inc₃₂`

The one phase whose code differs from `BatchCtr`'s (`BatchTaint.lean`):
choosing the lanes, filling them (stepping the counter by `inc₃₂`) and the
call that encrypts them.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Taint

open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8])
    (.seq BatchCtr.count (.seq BatchCtr32.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.Batch32Taint

end

end

/-! ### `Sm4.Arm.Batch32Body`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.Batch32Loop`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.Batch32Fill`, which this module and modules that import it used -/

section

/-! ### `Modes.Arm.Counter32`, which only this module used -/

section

/-!
# GCM's `inc₃₂` on ARMv7

`inc32At` run once, with its memory as an explicit write (`inc32Mem`): the
last word, loaded, byte-reversed, plus 1, reversed again and stored.
`inc32Mem_bytes`: the block it leaves is `inc₃₂` of the one it read, as the
number `ctr32Val V 1` of its bytes (`Proof/Modes/Ctr32.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.Arm.Counter32

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Modes.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

/-- The memory after `inc32At` on the block at `Q`. -/
def inc32Mem (m : Mem) (Q : Addr) : Mem :=
  m.writeW (Q + BitVec.ofNat 64 12) (rev (rev (m.readW (Q + BitVec.ofNat 64 12) 32) + 1))

theorem incr32_ok (s : State) {base : Reg} (h9 : base ≠ .r9) {off : Nat} (hoff : off + 16 ≤ 4096) {Q : Addr}
    (ha : State.addr (s.gpr base + BitVec.ofNat 32 (off + 12)) = Q + BitVec.ofNat 64 12)
    (hr : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4)
    (hw : InRegions s.wr (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa (inc32At base off) s = some s' ∧
      (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = inc32Mem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := Proof.MdStream.Arm.op2_imm (by decide)
  have h12 : off + 12 < 4096 := by omega_using [hoff]
  refine ⟨_, by
    simp only [↓reduceIte, inc32At, runBlock_cons, runStep_some, runBlock_nil, exec,
      i1, State.load32, State.store32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      h9, h12, ha, hr, hw]
    rfl, ?_⟩
  exact ⟨fun r h₁ => by simp only [gpr_setReg, h₁, ite_false], rfl, rfl, rfl, rfl⟩

theorem rev_eq (a : BitVec 32) : rev a = AesCtr.rv32 a := rfl

theorem inc32Mem_bytes (m : Mem) (Q : Addr) :
    bytesAt (inc32Mem m Q) Q 16 = ofNat (Proof.Modes.ctr32Val (toNat (bytesAt m Q 16)) 1) 16 := by
  have split (m' : Mem) : bytesAt m' Q 16 = bytesAt m' Q 12 ++ bytesAt m' (Q + BitVec.ofNat 64 12) 4 :=
    AesCtr.bytesAt_append m' Q 12 4
  have hl : (bytesAt m Q 16).length = 16 := by simp [bytesAt]
  have hlo : (bytesAt m Q 12).length = 12 := by simp [bytesAt]
  generalize hV : toNat (bytesAt m Q 16) = V
  have hV' := hV
  have hdec : bytesAt m Q 16 = ofNat (V / 256 ^ 4) 12 ++ ofNat V 4 := by
    rw [← AesCtr.ofNat_add, ← hV]; exact (AesCtr.ofNat_toNat hl).symm
  rw [split m] at hdec
  obtain ⟨hhi, hlow⟩ := List.append_inj hdec (by rw [hlo, AesCtr.length_ofNat])
  have frame : bytesAt (inc32Mem m Q) Q 12 = bytesAt m Q 12 := by
    apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ _
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, inc32Mem, Mem.writeW]
    exact Mem.write_apply (by
      rw [show Q + BitVec.ofNat 64 i - (Q + BitVec.ofNat 64 12) = BitVec.ofNat 64 (2 ^ 64 - (12 - i)) by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h₁]]
      simp only [BitVec.toNat_ofNat]; omega_using [h₁])
  rw [split, frame, inc32Mem, rev_eq, rev_eq, AesCtr.bytesAt_writeW_rv32, show (16 : Nat) = 12 + 4 from rfl,
    AesCtr.ofNat_add, hhi]
  have h4 := congrArg toNat hlow
  rw [AesCtr.bytesAt_rv32, AesCtr.toNat_ofNat, AesCtr.toNat_ofNat] at h4
  have hw := (AesCtr.rv32 (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  congr 1
  · exact AesCtr.ofNat_congr (by unfold Proof.Modes.ctr32Val; omega_using [])
  · refine AesCtr.ofNat_congr ?_
    rw [BitVec.toNat_add, e1]
    unfold Proof.Modes.ctr32Val
    simp only [Nat.reducePow] at *
    omega_using [h4]

theorem inc32Mem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (inc32Mem m Q) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))

end VG.Proof.Modes.Arm.Counter32

end

end


/-!
# Filling SM4's counter batches with GCM's `inc₃₂` on ARMv7

As `BatchFill`, with the running counter stepped by `inc₃₂` (`step32`):
`next32 t j` is the counter block `j` steps from `t`, `ctr32Val (toNat t) j`
as 16 bytes (`next32_eq`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Fill

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord inc32At)
open VG.Proof.Modes.Arm
open VG.Proof.Sm4.Arm.BatchFill (counterAddr bufferAddr total_eq offset_nat workspace_part bytes_frame buffer_counter_sep buffer_sub fill_eval_ne fillArgs fillArgs_run)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

/-- GCM's `inc₃₂` on a counter block of 16 bytes. -/
def step32 (t : List Byte) : List Byte := ofNat (Proof.Modes.ctr32Val (toNat t) 1) 16

/-- The counter block `j` steps of `inc₃₂` from `t`. -/
def next32 (t : List Byte) (j : Nat) : List Byte := Nat.repeat step32 j t

theorem next32_succ (t : List Byte) (j : Nat) : next32 t (j + 1) = step32 (next32 t j) := rfl

theorem next32_add (t : List Byte) (a : Nat) : ∀ b, next32 t (a + b) = next32 (next32 t a) b
  | 0 => rfl
  | b + 1 => by rw [← Nat.add_assoc, next32_succ, next32_add t a b, next32_succ]

theorem next32_eq {t : List Byte} (ht : t.length = 16) :
    ∀ j, next32 t j = ofNat (Proof.Modes.ctr32Val (toNat t) j) 16
  | 0 => by rw [Proof.Modes.ctr32Val_zero]; exact (AesCtr.ofNat_toNat ht).symm
  | j + 1 => by
    rw [next32_succ, next32_eq ht j, step32, AesCtr.toNat_ofNat,
      Nat.mod_eq_of_lt (Proof.Modes.ctr32Val_lt (AesCtr.toNat_lt ht) j), Proof.Modes.ctr32Val_add]

/-- Copy the running counter into lane `j`, then step it by `inc₃₂`. -/
def copyIncCode : List Instr :=
  (List.range 4).flatMap (copyWord .r0 sb 0 (4 * BatchCtr.counterSlot)) ++ inc32At sb (4 * BatchCtr.counterSlot)

structure CopyIncPost (s : State) (B : BitVec 32) (j : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B j, 16⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  lane : bytesAt s'.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16
  counter : bytesAt s'.mem (counterAddr B) 16 = step32 (bytesAt s.mem (counterAddr B) 16)

theorem copyInc_wp {s : State} {B : BitVec 32} {j : Nat} (hj : j < 8)
    (hB : s.gpr sb = B) (hp : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa (.block copyIncCode) s (CopyIncPost s B j) := by
  have htail : 4 * tailSlot + 16 * j + 16 ≤ 4 * BatchCtr.totalSlots := by
    rw [tailSlot, total_eq]; omega_using [hj]
  have hctr : 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots := by decide
  have wt := workspace_part hw (4 * tailSlot + 16 * j) 16 htail
  have wc := workspace_part hw (4 * BatchCtr.counterSlot) 16 hctr
  have sep := buffer_counter_sep B hj
  have np : NPre 4 s .r0 sb 0 (4 * BatchCtr.counterSlot) (bufferAddr B j) (counterAddr B) :=
    ⟨by rw [BitVec.add_zero, hp, addr_add (by omega_using [fitB, htail])], by rw [hB],
      by rw [hp, offset_nat B _ (by omega_using [fitB, htail])]; omega_using [fitB, htail],
      by rw [hB]; omega_using [fitB, hctr], by decide, by decide, by decide, by decide, by decide, by decide,
      wt, Covers.right wc, sep⟩
  obtain ⟨t₁, s₁, he₁, h₁⟩ := copyN_wp np
  have b₁ : s₁.gpr sb = B := (h₁.regs _ (by decide) (by decide)).trans hB
  obtain ⟨s₂, e₂, g₂, sp₂, m₂, rd₂, wr₂⟩ := Counter32.incr32_ok s₁ (base := sb) (off := 4 * BatchCtr.counterSlot)
    (by decide) (by decide)
    (by rw [b₁, addr_add (by omega_using [fitB, hctr]), Offset.add_add])
    (by
      rw [h₁.rd, h₁.wr]
      exact Covers.right wc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by decide) (by decide)⟩)
    (by
      rw [h₁.wr]
      exact wc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by decide) (by decide)⟩)
  have fc : Frame [⟨bufferAddr B j, 16⟩] s.mem s₁.mem := by
    rw [h₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  have fi : Frame [⟨counterAddr B, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Counter32.inc32Mem_frame _ _
  have sameCounter : bytesAt s₁.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [h₁.mem]
    exact bytesAt_over_other _ _ sep (by decide)
  have sameLane : bytesAt s₂.mem (bufferAddr B j) 16 = bytesAt s₁.mem (bufferAddr B j) 16 :=
    bytes_frame fi fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sep
  have copied : bytesAt s₁.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [h₁.mem, bytesAt_over_self _ _ _ (by decide)]
    rfl
  refine WP.block_append_iff.mpr ⟨t₁, s₁, he₁, WP.of_runBlock ⟨s₂, e₂, ?_⟩⟩
  refine ⟨fun r h9 h10 => (g₂ r h9).trans (h₁.regs r h9 h10), rd₂.trans h₁.rd,
    wr₂.trans h₁.wr, sp₂.trans h₁.sp,
    (fc.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans (fi.mono fun r hr => List.mem_cons_of_mem _ hr),
    sameLane.trans copied, ?_⟩
  rw [m₂, Counter32.inc32Mem_bytes, sameCounter, step32]

structure FillStepPost (s : State) (B : BitVec 32) (j n : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r
  ptr : s'.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * (j + 1))
  left : s'.gpr .r1 = BitVec.ofNat 32 (n - 1)
  z : s'.z = decide (n = 1)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B j, 16⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  lane : bytesAt s'.mem (bufferAddr B j) 16 = bytesAt s.mem (counterAddr B) 16
  counter : bytesAt s'.mem (counterAddr B) 16 = step32 (bytesAt s.mem (counterAddr B) 16)

theorem fillBody_eq : BatchCtr32.fillBody = copyIncCode ++
    ([.dp .add .r0 .r0 (.imm 16), .subs .r1 .r1 (.imm 1)] : List Instr) := by
  simp only [BatchCtr32.fillBody, copyIncCode, List.append_assoc]

theorem fillStep_wp {s : State} {B : BitVec 32} {j n : Nat} (hj : j < 8) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hB : s.gpr sb = B) (hp : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j))
    (hN : s.gpr .r1 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa (.block BatchCtr32.fillBody) s (FillStepPost s B j n) := by
  rw [fillBody_eq]
  apply WP.block_append_iff.mpr
  refine WP.mono (copyInc_wp hj hB hp fitB hw) fun s₁ h₁ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_imm (by decide)) fun s₃ u₃ hz => ?_
  refine WP.block_nil ⟨fun r h9 h10 h0 h1 => by
      rw [u₃.other r h1, u₂.other r h0, h₁.regs r h9 h10], ?_, ?_, ?_,
    by rw [u₃.rd, u₂.rd, h₁.rd], by rw [u₃.wr, u₂.wr, h₁.wr], by rw [u₃.sp, u₂.sp, h₁.sp],
    by rw [u₃.mem, u₂.mem]; exact h₁.frame,
    by rw [u₃.mem, u₂.mem]; exact h₁.lane,
    by rw [u₃.mem, u₂.mem]; exact h₁.counter⟩
  · rw [u₃.other _ (by decide), u₂.gpr, h₁.regs _ (by decide) (by decide), hp,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_add]
    congr 2
  · rw [u₃.gpr, u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN]
    exact Offset.ofNat_sub_ofNat hn
  · rw [hz, u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat hn]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have hnat := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn8])] at hnat
      have : (0 : BitVec 32).toNat = 0 := rfl
      rw [this] at hnat
      omega_using [hn, hnat]
    · intro h; subst h; rfl

structure FillInv (s₀ : State) (B : BitVec 32) (g : Nat) (t : List Byte) (j : Nat) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s.gpr r = s₀.gpr r
  ptr : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j)
  left : s.gpr .r1 = BitVec.ofNat 32 (g - j)
  bound : j ≤ g
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨bufferAddr B 0, 16 * j⟩, ⟨counterAddr B, 16⟩] s₀.mem s.mem
  counter : bytesAt s.mem (counterAddr B) 16 = next32 t j
  lanes : ∀ k < j, bytesAt s.mem (bufferAddr B k) 16 = next32 t k

theorem fillInv_step {s₀ s : State} {B : BitVec 32} {g j : Nat} {t : List Byte}
    (hg : g ≤ 8) (hj : j < g) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (h : FillInv s₀ B g t j s) :
    WP isa (.block BatchCtr32.fillBody) s fun s' => FillInv s₀ B g t (j + 1) s' ∧ s'.z = decide (j + 1 = g) := by
  have base : s.gpr sb = B := (h.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  refine WP.mono (fillStep_wp (by omega_using [hg, hj]) (by omega_using [hj]) (by omega_using [hg]) base h.ptr h.left fitB
    (by rw [h.wr]; exact hw)) fun s' hs => ?_
  refine ⟨⟨fun r h9 h10 h0 h1 => (hs.regs r h9 h10 h0 h1).trans (h.regs r h9 h10 h0 h1), hs.ptr,
    by rw [hs.left, show g - j - 1 = g - (j + 1) by omega_using []], by omega_using [hj],
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, ?_, ?_, ?_⟩, ?_⟩
  · have old : Frame [⟨bufferAddr B 0, 16 * (j + 1)⟩, ⟨counterAddr B, 16⟩] s₀.mem s.mem :=
      h.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega_using [])⟩
        · exact ⟨_, by simp, fun _ hi => hi⟩
    exact old.trans (hs.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, buffer_sub B (by omega_using []) (by omega_using [hg, hj])⟩
      · exact ⟨_, by simp, fun _ hi => hi⟩)
  · rw [hs.counter, h.counter, next32_succ]
  · intro k hk
    by_cases he : k = j
    · subst he; exact hs.lane.trans h.counter
    · have hk' : k < j := by omega_using [hk, he]
      rw [bytes_frame hs.frame (fun r hr => ?_), h.lanes k hk']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · apply Offset.disjoint (State.addr B)
        · left; change 4 * tailSlot + 16 * k + 16 ≤ 4 * tailSlot + 16 * j; omega_using [hk, he]
        · change 4 * tailSlot + 16 * k + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj, hk]
        · change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj]
      · exact buffer_counter_sep B (by omega_using [hg, hj, hk])
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_using []

theorem fillLoop_wp {s₀ : State} {B : BitVec 32} {g : Nat} {t : List Byte}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s₀.gpr sb = B)
    (hp : s₀.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot))
    (hN : s₀.gpr .r1 = BitVec.ofNat 32 g) (hC : bytesAt s₀.mem (counterAddr B) 16 = t)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr) :
    WP isa (.loop (.block BatchCtr32.fillBody) .ne) s₀ (FillInv s₀ B g t g) := by
  have hi : FillInv s₀ B g t 0 s₀ :=
    ⟨fun _ _ _ _ _ => rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hp,
      by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC,
      fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ j, m = g - j ∧ j < g ∧ FillInv s₀ B g t j s)
    (fun m s hs => ?_) g s₀ ⟨0, by omega_using [], by omega_using [hg], hi⟩
  obtain ⟨j, rfl, hj, hs⟩ := hs
  refine WP.mono (fillInv_step hg8 hj hB fitB hw hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : j + 1 = g
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      g - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, he], h'⟩

structure FillPost (s : State) (B : BitVec 32) (g : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨bufferAddr B 0, 16 * g⟩, ⟨counterAddr B, 16⟩] s.mem s'.mem
  counter : bytesAt s'.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) g
  lanes : ∀ k < g, bytesAt s'.mem (bufferAddr B k) 16 = next32 (bytesAt s.mem (counterAddr B) 16) k

theorem fill_wp {s : State} {B : BitVec 32} {g : Nat} (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hB : s.gpr sb = B) (hN : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr) :
    WP isa BatchCtr32.fill s (FillPost s B g) := by
  have hb : (fillArgs s).gpr sb = B := by simpa [fillArgs, State.setReg, sb] using hB
  have hp : (fillArgs s).gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot) := by
    simp only [fillArgs, RegUpd.gpr_setReg]; simp only [reduceCtorEq, ↓reduceIte]; rw [hB]
  have hn : (fillArgs s).gpr .r1 = BitVec.ofNat 32 g := by rw [fillArgs, RegUpd.gpr_setReg_self, hN]
  refine WP.seq (WP.of_runBlock ⟨fillArgs s, fillArgs_run s, ?_⟩)
  refine WP.mono (fillLoop_wp hg hg8 hb hp hn rfl fitB hw) fun s' h => ?_
  refine ⟨fun r h9 h10 h0 h1 => ?_, h.rd, h.wr, h.sp, h.frame, h.counter, h.lanes⟩
  rw [h.regs r h9 h10 h0 h1]
  simp only [fillArgs, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h0]

end VG.Proof.Sm4.Arm.Batch32Fill

end

end

/-! ### `Sm4.Arm.Batch32Group`, which only this module used -/

section

/-! # One complete batch of SM4's counter mode with `inc₃₂` on ARMv7

As `BatchGroup`, with the lanes filled by `Batch32Fill`. -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Group

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR lsrOp)
open VG.Proof.Sm4.Arm.BatchFill (counterAddr bufferAddr total_eq counter_eq workspace_part bytes_frame)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr xor_wp)
open VG.Proof.Sm4.Arm.BatchGroup (table_frame count_wp encrypted_lane batchRegions difference_zero)
open VG.Proof.Sm4.Arm.Batch32Fill (next32 fill_wp)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure BatchPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r7, .r8, .r11], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * g)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) g
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k))

theorem batch_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hG : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr32.batch s (BatchPost s B D K g) := by
  refine WP.seq (WP.mono (fill_wp hg hg8 hB hG fitB hw) fun s₁ f₁ => ?_)
  obtain sb₁ : s₁.gpr sb = B := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  obtain r6₁ : s₁.gpr .r6 = D := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hD
  obtain r11₁ : s₁.gpr .r11 = BitVec.ofNat 32 g :=
    (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hG
  obtain hH₁ : Holds layout s₁.mem (State.addr B) K .encrypt := table_frame hH f₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * g ≤ 384; rw [tailSlot]; omega_using [hg8]
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * g ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg8]
    · apply Offset.disjoint (State.addr B)
      · left; change 384 + 1024 ≤ 4 * BatchCtr.counterSlot; decide
      · decide
      · decide
  obtain f₁wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.mem s₁.mem :=
    f₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg8])⟩
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by decide)⟩
  obtain f₁batch : Frame (batchRegions B D g) s.mem s₁.mem := f₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self,
        Offset.sub_base _ (by rw [tailSlot, slots_eq]; omega_using [hg8])⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  obtain wc₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using [])
  refine WP.seq (WP.mono (BatchCalls.crypt_wp sb₁ (by rw [total_eq] at fitB; rw [slots_eq]; omega_using [fitB]) wc₁ hH₁)
    fun s₂ ⟨c₂, table₂, ecb₂⟩ => ?_)
  obtain sb₂ : s₂.gpr sb = B := (c₂.regs _ (by decide) (by decide)).trans sb₁
  obtain r6₂ : s₂.gpr .r6 = D := (c₂.regs _ (by decide) (by decide)).trans r6₁
  obtain r11₂ : s₂.gpr .r11 = BitVec.ofNat 32 g := (c₂.regs _ (by decide) (by decide)).trans r11₁
  obtain c₂wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₁.mem s₂.mem :=
    c₂.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
        Region.sub_prefix (by rw [slots_eq, total_eq]; omega_using [])⟩
  obtain c₂batch : Frame (batchRegions B D g) s₁.mem s₂.mem :=
    c₂.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  obtain phaseFrame := f₁wide.trans c₂wide
  obtain counter₂ : bytesAt s₂.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) g := by
    rw [bytes_frame c₂.frame (fun r hr => ?_), f₁.counter]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by rw [slots_eq, counter_eq]; omega_using []) (by decide)
  obtain cipher₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 =
      Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k) := by
    intro k hk
    rw [encrypted_lane ecb₂ (by omega_using [hg8, hk]), f₁.lanes k hk]
  obtain plain₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    apply bytes_frame phaseFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.sub_left (Offset.sub_base _ (by omega_using [hk]))
  refine WP.mono (xor_wp hg hg8 sb₂ r6₂ r11₂ fitB fitD
    (by rw [c₂.wr, f₁.wr]; exact hw) (by rw [c₂.wr, f₁.wr]; exact wd) sep) fun s₃ x₃ => ?_
  obtain table₃ : Holds layout s₃.mem (State.addr B) K .encrypt := table_frame table₂ x₃.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 384 + 1024 ≤ 4 * BatchCtr.totalSlots; rw [total_eq]; omega_using []))
  obtain counter₃ : bytesAt s₃.mem (counterAddr B) 16 = bytesAt s₂.mem (counterAddr B) 16 := by
    apply bytes_frame x₃.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  refine ⟨fun r hr => ?_, x₃.data, x₃.rd.trans (c₂.rd.trans f₁.rd), x₃.wr.trans (c₂.wr.trans f₁.wr),
    x₃.sp.trans (c₂.sp.trans f₁.sp),
    (f₁batch.trans c₂batch).trans (x₃.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp [batchRegions]), table₃,
    counter₃.trans counter₂, fun k hk => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [x₃.regs _ (by decide) (by decide) (by decide) (by decide) (by decide),
        c₂.regs _ (by decide) (by decide), f₁.regs _ (by decide) (by decide) (by decide) (by decide)]
  · rw [x₃.blocks k hk, plain₂ k hk, cipher₂ k hk]

structure GroupPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * min n 8)
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - min n 8)
  z : s'.z = decide (n = min n 8)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D (min n 8)) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = next32 (bytesAt s.mem (counterAddr B) 16) (min n 8)
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (next32 (bytesAt s.mem (counterAddr B) 16) k))

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr32.group s (GroupPost s B D K n) := by
  obtain hgN : min n 8 ≤ n := Nat.min_le_left _ _
  obtain hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain hg : 1 ≤ min n 8 := by omega_using [hn]
  refine WP.seq (WP.mono (count_wp hN hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  obtain b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  obtain d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  obtain n₁ : s₁.gpr .r7 = BitVec.ofNat 32 n := (o₁ _ (by decide) (by decide)).trans hN
  obtain wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * min n 8 ≤ 16 * n; omega_using []⟩
  refine WP.seq (WP.mono (batch_wp hg hg8 b₁ d₁ g₁ fitB (by omega_using [fitD])
    (by rw [wr₁]; exact hw) wd₁ (sep.sub_left (Region.sub_prefix (by omega_using [])))
    (by rw [m₁]; exact hH)) fun s₂ b₂ => ?_)
  obtain n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b₂.regs _ (by simp)).trans n₁
  obtain g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b₂.regs _ (by simp)).trans g₁
  obtain ⟨s₃, e₃, r₃, z₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := subsR_ok s₂ .r7 .r7 .r11
  refine WP.of_runBlock ⟨s₃, e₃, fun r hr => ?_, ?_, ?_, ?_,
    rd₃.trans (b₂.rd.trans rd₁), wr₃.trans (b₂.wr.trans wr₁), sp₃.trans (b₂.sp.trans sp₁), ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [o₃ _ (by decide), b₂.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [o₃ _ (by decide)]; exact b₂.data
  · rw [r₃, n₂, g₂]; exact Offset.ofNat_sub_ofNat hgN
  · rw [z₃, n₂, g₂]; exact difference_zero hn32 hgN
  · rw [m₃, ← m₁]; exact b₂.frame
  · rw [m₃]; exact b₂.table
  · rw [m₃, ← m₁]; exact b₂.counter
  · intro k hk
    rw [m₃, b₂.blocks k hk, m₁]

end VG.Proof.Sm4.Arm.Batch32Group

end

end


/-! # The arbitrary-length batched loop of SM4's counter mode with `inc₃₂` on ARMv7

As `BatchLoop`, with the batches of `Batch32Group`. -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Loop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill (counterAddr total_eq offset_nat bytes_frame fill_eval_ne)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr)
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions)
open VG.Proof.Sm4.Arm.BatchLoop (future_data)
open VG.Proof.Sm4.Arm.Batch32Fill (next32 next32_add)
open VG.Proof.Sm4.Arm.Batch32Group
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- The intended block at index `j`, from the original data and counter. -/
def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m (dataAddr D j) 16) (Spec.Sm4.cipher K (next32 t j))

structure LoopInv (s₀ : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte)
    (n i : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s.gpr r = s₀.gpr r
  data : s.gpr .r6 = D + BitVec.ofNat 32 (16 * i)
  left : s.gpr .r7 = BitVec.ofNat 32 (n - i)
  bound : i ≤ n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (batchRegions B D i) s₀.mem s.mem
  table : Holds layout s.mem (State.addr B) K .encrypt
  counter : bytesAt s.mem (counterAddr B) 16 = next32 t i
  blocks : ∀ j < i, bytesAt s.mem (dataAddr D j) 16 = outBlock s₀.mem D K t j

theorem loopInv_step {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : LoopInv s₀ B D K t n i s) :
    WP isa BatchCtr32.group s fun s' =>
      LoopInv s₀ B D K t n (i + min (n - i) 8) s' ∧ s'.z = decide (i + min (n - i) 8 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g := min (n - i) 8
  obtain hg : 1 ≤ g := by dsimp only [g]; omega_using [hi]
  obtain hgn : g ≤ n - i := Nat.min_le_left _ _
  obtain hgi : i + g ≤ n := by omega_using [hi]
  obtain diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_using [hi, fitD])
  obtain diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, fitD])
  obtain subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_using [hi])
  obtain wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  obtain sb' : s.gpr sb = B := (h.regs _ (by simp [sb])).trans hB
  refine WP.mono (group_wp (by omega_using [hi]) (by omega_using [hn32]) sb' h.data h.left fitB
    (by rw [diNat]; omega_using [hi, fitD]) (by rw [h.wr]; exact hw) wdi (sep.sub_left subD) h.table)
    fun s' hs => ?_
  obtain fNew : Frame (batchRegions B D (i + g)) s.mem s'.mem := hs.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], ?_⟩
      rw [diAddr]; exact Offset.sub_base _ (by omega_using [])
  obtain fOld : Frame (batchRegions B D (i + g)) s₀.mem s.mem := h.frame.sub fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [batchRegions], Region.sub_prefix (by omega_using [])⟩
  refine ⟨⟨fun r hr => (hs.regs r hr).trans (h.regs r hr), ?_, ?_, hgi,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, fOld.trans fNew, hs.table, ?_, ?_⟩, ?_⟩
  · rw [hs.data]
    change D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (16 * g) = _
    rw [Offset.add_add]; congr 2; omega_using []
  · rw [hs.left, show n - i - min (n - i) 8 = n - (i + min (n - i) 8) by omega_using []]
  · rw [hs.counter, h.counter, ← next32_add]
  · intro j hj
    by_cases hjOld : j < i
    · rw [bytes_frame (P := dataAddr D j) hs.frame (fun r hr => ?_), h.blocks j hjOld]
      simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))).sub_right
          (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using []))
      · exact (sep.sub_left (Offset.sub_base _ (by omega_using [hi, hj]))).sub_right
          (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
      · rw [diAddr]
        exact Offset.disjoint _ (.inl (by omega_using [hjOld])) (by omega_using [hn32, hi, hj]) (by omega_using [hn32, hi])
    · have hjG : j - i < g := by omega_using [hi, hj]
      obtain ha : dataAddr Di (j - i) = dataAddr D j := by
        change State.addr Di + BitVec.ofNat 64 (16 * (j - i)) = _
        rw [diAddr, Offset.add_add]
        congr 2; omega_using [hjOld]
      obtain hb := hs.blocks (j - i) hjG
      rw [ha, future_data hn32 (by omega_using [hjOld]) (by omega_using [hi, hj]) sep h.frame, h.counter, ← next32_add,
        show i + (j - i) = j by omega_using [hjOld]] at hb
      exact hb
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_using [hi]

theorem loop_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.loop BatchCtr32.group .ne) s₀ (LoopInv s₀ B D K t n n) := by
  obtain hi : LoopInv s₀ B D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega_using [], by omega_using [hn], hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + min (n - i) 8 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + min (n - i) 8), by omega_using [hi],
      i + min (n - i) 8, rfl, by have := h'.bound; omega_using [hi, he], h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .encrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop BatchCtr32.group .ne)) s₀ (LoopInv s₀ B D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩
  · have hn : 1 ≤ n := by simp at hz; omega_using [hz]
    exact loop_wp hn hn32 hB hD hN fitB fitD hw wd sep hH hC

end VG.Proof.Sm4.Arm.Batch32Loop

end

end

/-!
# Functional composition of the prepared, eight-block SM4 counter mode with `inc₃₂`

As `BatchBody`, and the blocks and the counter block it leaves as
`Spec.Gcm.ctr32`'s and `inc₃₂ⁿ` of the counter block (`ctr32_of_blocks`,
`next32_eq`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm.Batch32Body

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor (dataAddr)
open VG.Proof.Sm4.Arm.BatchFill (bytes_frame)
open VG.Proof.Sm4.Arm.BatchEntry (mode_slots restore_wp)
open VG.Proof.Sm4.Arm.BatchChain (ChainPre counterOut_wp)
open VG.Proof.Sm4.Arm.BatchGroup (batchRegions)
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Proof.Sm4.Arm.Batch32Fill (next32 next32_eq)
open VG.Proof.Sm4.Arm.Batch32Loop (loopOrEmpty_wp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

theorem cipher_length (K : Spec.Sm4.Schedule) (b : List Byte) : (Spec.Sm4.cipher K b).length = 16 :=
  Vector.length_toList

attribute [local irreducible] Spec.Sm4.cipher

/-- The blocks of counter mode with `inc₃₂` from the counter block `t`, one
at a time, as `Spec.Gcm.ctr32`'s. -/
theorem ctr32_of_blocks {K : Spec.Sm4.Schedule} {m₀ m : Mem} {D : Addr} {n : Nat} {t : List Byte}
    (ht : t.length = 16)
    (h : ∀ j < n, bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16) (Spec.Sm4.cipher K (next32 t j))) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher K) (Spec.Gcm.ofBytes t) (Spec.Gcm.blocksAt m₀ D n) := by
  have hl : (Spec.Gcm.blocksAt m₀ D n).length = n := by simp [Spec.Gcm.blocksAt]
  rw [Spec.Gcm.ctr32, hl, Spec.Gcm.keystream, Spec.Gcm.blocksAt, Spec.Gcm.blocksAt, List.zipWith_map,
    List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hctr : Spec.Gcm.toBytes (Nat.repeat Spec.Gcm.inc32 j (Spec.Gcm.ofBytes t)) = next32 t j := by
    rw [Proof.Modes.toBytes_eq_ofNat, Proof.Modes.toNat_repeat_inc32, Proof.Modes.toNat_ofBytes ht,
      next32_eq ht]
  rw [Spec.Sm4.gcmCipher, hctr, Spec.Gcm.blockAt, Spec.Gcm.blockAt, h j hj]
  exact Ocb.ofBytes_xor (Cmac.bytesAt_length _ _ _) (cipher_length _ _)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Gcm.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Gcm.ctr32 (Spec.Sm4.gcmCipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (Spec.Gcm.blockAt s₀.mem (State.addr (Iv s₀))) (Spec.Gcm.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : Spec.Gcm.blockAt s.mem (State.addr (Iv s₀)) =
    Nat.repeat Spec.Gcm.inc32 (N s₀) (Spec.Gcm.blockAt s₀.mem (State.addr (Iv s₀)))
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCtr32.ctr32 s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  have hl : (bytesAt s₀.mem (State.addr (Iv s₀)) 16).length = 16 := Cmac.bytesAt_length _ _ _
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have plain₁ : ∀ j < N s₀, bytesAt s₁.mem (dataAddr (Dp s₀) j) 16 = bytesAt s₀.mem (dataAddr (Dp s₀) j) 16 :=
    fun j hj => bytes_frame p.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ds.sub_left (Offset.sub_base _ (by change 16 * j + 16 ≤ 16 * N s₀; omega_using [hj]))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have out₃ : ∀ j < N s₀, bytesAt s₃.mem (dataAddr (Dp s₀) j) 16 =
      Spec.Cbc.xor (bytesAt s₀.mem (dataAddr (Dp s₀) j) 16)
        (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀)))
          (next32 (bytesAt s₀.mem (State.addr (Iv s₀)) 16) j)) := by
    intro j hj
    rw [bytes_frame c.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.id.symm.sub_left (Offset.sub_base _ (by change 16 * j + 16 ≤ 16 * N s₀; omega_using [hj]))),
      l.blocks j hj, Batch32Loop.outBlock, plain₁ j hj]
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, Spec.Gcm.blockAt]
    exact ctr32_of_blocks hl out₃
  · rw [mem]
    refine Proof.Modes.ctr32_next ?_
    rw [c.block, l.counter, next32_eq hl]

end VG.Proof.Sm4.Arm.Batch32Body

end

end

/-! ### `Sm4.Arm.Batch32CT`, which only this module used -/

section

/-!
# Constant-time composition for batched SM4 counter mode with `inc₃₂`

As `BatchCT`: the prologue and the exit are `BatchCtr`'s, and so is every
check but the group head's (`Batch32Taint`), whose fill steps the counter
by `inc₃₂`.
-/

@[expose] public section
namespace VG.Proof.Sm4.Arm.Batch32CT

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchCT (append_eq result checked Pub prologue_ct)
open VG.Proof.Sm4.Arm.BatchHead (HeadPre HeadPost groupTail)
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Proof.Sm4.Arm.BatchFill (counterAddr workspace_part total_eq)
open VG.Proof.Sm4.Arm.BatchGroup (count_wp table_frame)
open VG.Proof.Sm4.Arm.Batch32Loop
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq BatchCtr.count (.seq BatchCtr32.fill BatchCtr.crypt)

theorem head_wp {s : State} {B : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (h : HeadPre B n s) : WP isa groupHead s (HeadPost s n) := by
  have hg : 1 ≤ min n 8 := by omega_arith
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans h.base
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := by
    rw [m₁]; exact hH
  refine WP.seq (WP.mono (Batch32Fill.fill_wp hg hg8 b₁ g₁ h.fit (by rw [wr₁]; exact h.writable)) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.regs _ (by decide) (by decide) (by decide) (by decide)).trans b₁
  have table₂ : Holds layout s₂.mem (State.addr B) K .encrypt := table_frame table₁ f.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * min n 8 ≤ 384; rw [tailSlot]; omega_arith
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * min n 8 ≤ 2 ^ 64; rw [tailSlot]; omega_arith
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.writable 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; decide)
  refine WP.mono (BatchCalls.crypt_wp b₂ (by have := h.fit; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_arith) wc table₂)
    fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide) (by decide) (by decide), g₁]

/-- Reassociate the group at the point where the helper returns. -/
theorem group_split {s s' : State} {t : List Leak} (e : Exec isa BatchCtr32.group s t s') :
    ∃ m th tt, Exec isa groupHead s th m ∧ Exec isa groupTail m tt s' ∧ t = th ++ tt := by
  cases e with | seq a b =>
    cases b with | seq c d =>
      cases c with | seq f g =>
        cases g with | seq k x =>
          exact ⟨_, _, _, .seq a (.seq f k), .seq x d, by simp only [List.append_assoc]⟩

theorem group_ct {B : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : HeadPre B n s₁) (h₂ : HeadPre B n s₂) (hd : s₁.gpr .r6 = s₂.gpr .r6)
    (e₁ : Exec isa BatchCtr32.group s₁ t₁ s₁') (e₂ : Exec isa BatchCtr32.group s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨m₁, th₁, tt₁, eh₁, et₁, tr₁⟩ := group_split e₁
  obtain ⟨m₂, th₂, tt₂, eh₂, et₂, tr₂⟩ := group_split e₂
  have ht : th₁ = th₂ := checked Batch32Taint.groupHead_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.left, h₂.left]
    · exact h₁.base.trans h₂.base.symm) eh₁ eh₂
  have p₁ := result (head_wp hn hn32 h₁) eh₁
  have p₂ := result (head_wp hn hn32 h₂) eh₂
  have tt : tt₁ = tt₂ := checked BatchTaint.groupTail_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), hd]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), h₁.left, h₂.left]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.base.trans h₂.base.symm
    · rw [p₁.group, p₂.group]) et₁ et₂
  rw [tr₁, tr₂, ht, tt]

section
variable {s₀ s₀' : State} {B D : BitVec 32} {K K' : Spec.Sm4.Schedule} {t t' : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hB' : s₀'.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (hw' : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀'.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (wd' : Covers [⟨State.addr D, 16 * n⟩] s₀'.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)

def LoopRel (s₀ s₀' : State) (B D : BitVec 32) (K K' : Spec.Sm4.Schedule) (t t' : List Byte)
    (n m : Nat) (a b : State) : Prop :=
  ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i a ∧ LoopInv s₀' B D K' t' n i b

include hn32 hB hB' fitB fitD hw hw' wd wd' sep in
theorem loop_ct (m : Nat) :
    RelCT isa (LoopRel s₀ s₀' B D K K' t t' n m) (.loop BatchCtr32.group .ne)
      (fun a b => LoopInv s₀ B D K t n n a ∧ LoopInv s₀' B D K' t' n n b) := by
  refine RelCT.loop (M := isa) (LoopRel s₀ s₀' B D K K' t t' n) (fun m => ?_) m
  intro a b ta tb a' b' ⟨i, hm, hi, l, l'⟩ ea eb
  have p : HeadPre B (n - i) a := ⟨(l.regs _ (by simp [sb])).trans hB, l.left, fitB,
    by rw [l.wr]; exact hw, K, l.table⟩
  have p' : HeadPre B (n - i) b := ⟨(l'.regs _ (by simp [sb])).trans hB', l'.left, fitB,
    by rw [l'.wr]; exact hw', K', l'.table⟩
  have eqtr := group_ct (by omega_arith) (by omega_arith) p p' (by rw [l.data, l'.data]) ea eb
  obtain ⟨la, za⟩ := result (loopInv_step hn32 hi hB fitB fitD hw wd sep l) ea
  obtain ⟨lb, zb⟩ := result (loopInv_step hn32 hi hB' fitB fitD hw' wd' sep l') eb
  have evA : isa.eval .ne a' = some !decide (i + min (n - i) 8 = n) := by
    change some (!a'.z) = _; rw [za]
  have evB : isa.eval .ne b' = some !decide (i + min (n - i) 8 = n) := by
    change some (!b'.z) = _; rw [zb]
  refine ⟨eqtr, by rw [evA, evB], ?_, ?_⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 = n := by simpa using h
    rw [he] at la lb
    exact ⟨la, lb⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 ≠ n := by simpa using h
    refine ⟨n - (i + min (n - i) 8), by omega_arith, i + min (n - i) 8, rfl, ?_, la, lb⟩
    have := la.bound
    omega_arith

include hn32 hB hB' fitB fitD hw hw' wd wd' sep in
theorem dataLoop_ct :
    RelCT isa (fun a b => LoopInv s₀ B D K t n 0 a ∧ LoopInv s₀' B D K' t' n 0 b ∧
      a.z = decide (n = 0) ∧ b.z = decide (n = 0)) BatchCtr32.dataLoop (fun _ _ => True) := by
  have ev {a : State} (h : a.z = decide (n = 0)) : isa.eval .eq a = some (decide (n = 0)) := by
    change some a.z = _; rw [h]
  refine RelCT.ite (fun a b h => by rw [ev h.2.2.1, ev h.2.2.2]) ?_ ?_
  · obtain ⟨_, hc⟩ := BatchTaint.nil_check
    exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (fun r hr => by simp at hr)) hc
  · refine (loop_ct (K := K) (K' := K') (t := t) (t' := t') hn32 hB hB' fitB fitD hw hw' wd wd' sep n).mono (fun a b h => ?_) (fun _ _ _ => trivial)
    have he := h.2
    rw [ev h.1.2.2.1] at he
    have hn : 0 < n := by
      have : n ≠ 0 := by simpa using he
      omega_arith
    exact ⟨0, by omega_arith, hn, h.1.1, h.1.2.1⟩

end

theorem initial {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hD : s.gpr .r6 = D) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Proof.Sm4.Prepared.Holds layout s.mem (State.addr B) K .encrypt)
    (hC : Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t) : LoopInv s B D K t n 0 s :=
  ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
    by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
    by change Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩

theorem ctr32_ct : ConstantTime isa Pre Pub BatchCtr32.ctr32 := by
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' hp₁ hp₂ hq e₁ e₂
  have eB : Sc s₂ = Sc s₁ := hq.2.2.2.2.2.symm
  have eD : Dp s₂ = Dp s₁ := hq.2.2.2.1.symm
  have eN : N s₂ = N s₁ := by unfold N; rw [hq.2.2.2.2.1]
  have hw₁ := hp₁.writable (r := wsR s₁) (by simp)
  have hw₂ := hp₂.writable (r := wsR s₂) (by simp)
  have wd₁ := hp₁.writable (r := dataR s₁) (by simp)
  have wd₂ := hp₂.writable (r := dataR s₂) (by simp)
  cases e₁ with | seq pro rest =>
    cases rest with | seq dl fin =>
      cases e₂ with | seq pro' rest' =>
        cases rest' with | seq dl' fin' =>
          have eqP := prologue_ct hp₁ hp₂ hq pro pro'
          have p := result (prologue_wp hp₁) pro
          have p' := result (prologue_wp hp₂) pro'
          have pb' := p'.base
          have pd' := p'.data
          have pn' := p'.left
          have pt' := p'.table
          have pc' := p'.counter
          have pz' := p'.z
          rw [eB] at pb' pt' pc'
          rw [eD] at pd'
          rw [eN] at pn' pz'
          have ib := initial p.data p.left p.table p.counter
          have ib' := initial pd' pn' pt' pc'
          have w₁ := hw₁
          have w₂ := hw₂
          have d₁ := wd₁
          have d₂ := wd₂
          rw [← p.wr] at w₁ d₁
          rw [← p'.wr] at w₂ d₂
          change Covers [⟨State.addr (Sc s₂), 4 * BatchCtr.totalSlots⟩] _ at w₂
          change Covers [⟨State.addr (Dp s₂), 16 * N s₂⟩] _ at d₂
          rw [eB] at w₂
          rw [eD, eN] at d₂
          have rel := dataLoop_ct (K := Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₁)))
            (K' := Spec.Sm4.scheduleAt s₂.mem (State.addr (Kp s₂)))
            (t := Spec.Aes.bytesAt s₁.mem (State.addr (Iv s₁)) 16)
            (t' := Spec.Aes.bytesAt s₂.mem (State.addr (Iv s₂)) 16)
            (s₁.gpr .r3).isLt p.base pb' hp₁.fitB hp₁.fitD w₁ w₂ d₁ d₂ hp₁.ds
          have eqL := (rel _ _ _ _ _ _ ⟨ib, ib', p.z, pz'⟩ dl dl').1
          have l := result (loopOrEmpty_wp (s₁.gpr .r3).isLt p.base p.data p.left p.z hp₁.fitB hp₁.fitD w₁ d₁ hp₁.ds p.table p.counter) dl
          have l' := result (loopOrEmpty_wp (s₁.gpr .r3).isLt pb' pd' pn' pz' hp₁.fitB hp₁.fitD w₂ d₂ hp₁.ds pt' pc') dl'
          have eqF := checked BatchTaint.finish_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [l.regs _ (by simp), l'.regs _ (by simp), p.iv, p'.iv]; exact hq.2.2.1
            · rw [l.regs _ (by simp), l'.regs _ (by simp)]
              exact p.base.trans pb'.symm) fin fin'
          exact append_eq eqP (append_eq eqL eqF)

end VG.Proof.Sm4.Arm.Batch32CT

end

end


/-! # Batched ARMv7 SM4 counter mode with `inc₃₂` meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.Batch32Verified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.Batch32Body
open VG.Proof.Sm4.Arm.BatchCT (Pub)
open VG.Proof.Sm4.Arm.Batch32CT (ctr32_ct)

def ctr32Arm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : ctr32Arm.pre s) :
    ∃ t s', Exec isa BatchCtr32.ctr32 s t s' ∧ abiPreserved s s' ∧ ctr32Arm.post s s' := by
  obtain ⟨t, s', e, p⟩ := body_wp h
  exact ⟨t, s', e, ⟨p.regs, p.sp⟩, p⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0, 1512⟩]

theorem implies : ctr32Arm.Implies (Proof.Sm4.ctr32ScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Post, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.ctr32ScratchContract, Proof.Sm4.ctr32ScratchSig, Proof.Sm4.ctr32Sig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCtr32.ctr32 (Proof.Sm4.ctr32ScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct ctr32_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Proof.Sm4.ctr32Contract Arm.abi 1520).pre s := by
  implies_sat [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    BatchCtr32.ctr32Framed
    (Proof.Sm4.ctr32Contract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Proof.Sm4.ctr32Sig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.ctr32Post Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.ctr32Post_local _)
    (Proof.Sm4.ctr32PostOut_local _) frameSat

end VG.Proof.Sm4.Arm.Batch32Verified
