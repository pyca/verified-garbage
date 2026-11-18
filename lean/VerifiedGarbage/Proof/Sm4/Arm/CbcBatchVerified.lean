module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Cbc
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Sm4.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.BatchTaint
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.Spec.Sm4
import VerifiedGarbage.Proof.Modes.Cbc
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-! ### `Sm4.Arm.CbcTaint`, which only this module used -/

section

/-! # Constant-time checks around CBC's prepared cipher phase -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcTaint
open VG VG.Arm VG.Impl.Sm4.Arm

theorem groupHead_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8])
    (.seq BatchCtr.count (.seq BatchCbc.fill BatchCtr.crypt)) h).isSome = true := ⟨_, by taint_decide⟩

theorem groupTail_check : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6, .r7, .r8, .r11])
    (.seq (BatchCbc.chooseXor 0 8) (.seq (.block BatchCtr.copyCounterIn) (.block BatchCbc.advance))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem proHead_check : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4)
    (.seq (.block BatchCtr.entry) BatchCbc.prepare) h).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.Sm4.Arm.CbcTaint

end

end

/-! ### `Sm4.Arm.CbcLoop`, which only this module used -/

section

/-! ### `Sm4.Arm.CbcPrologue`, which the modules that import this one used -/

section

/-! ### `Sm4.Arm.CbcPrepare`, which this module and modules that import it used -/

section

/-! # Preparing decryption keys for the batched CBC mode -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcPrepare

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchCalls (CallInv)
open VG.Proof.Sm4.Prepared (Holds)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Arm.BatchChain (ChainPre counterIn_wp)
open VG.Proof.Sm4.Arm.BatchFill (counterAddr)
open VG.Proof.Sm4.Arm.BatchGroup (table_frame difference_zero)

/-- Call preparation from its ABI arguments, with narrowed permissions. -/
theorem prepare_call_wp {s : State} {K B : BitVec 32}
    (h0 : s.gpr .r0 = K) (h1 : s.gpr .r1 = 1) (h2 : s.gpr .r2 = B) (h3 : s.gpr .r3 = 182)
    (fitK : K.toNat + 128 ≤ 2 ^ 32) (fitB : B.toNat + 4 * slots ≤ 2 ^ 32)
    (sep : Region.Disjoint ⟨State.addr K, 128⟩ ⟨State.addr B, 4 * slots⟩)
    (rK : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr))
    (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr) :
    WP isa (.call "vg_sm4_prepare_keys" prepareKeys) s fun s' =>
      CallInv s B s' ∧ Holds layout s'.mem (State.addr B) (Spec.Sm4.scheduleAt s.mem (State.addr K)) .decrypt := by
  have hp : prepArm.pre (s.callEntry.withRegions [⟨State.addr K, 128⟩] [⟨State.addr B, 4 * slots⟩]) := by
    simp only [prepArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr s (r := .r0) (by decide), State.callEntry_gpr s (r := .r1) (by decide),
      State.callEntry_gpr s (r := .r2) (by decide), State.callEntry_gpr s (r := .r3) (by decide), h0, h1, h2, h3]
    exact ⟨True.intro, by rw [slots_eq]; rfl, by change Region.Disjoint ⟨State.addr K, 128⟩ ⟨State.addr B, 4 * slots⟩; exact sep, fitK,
      by change B.toNat + 4 * slots ≤ 2 ^ 32; exact fitB, by decide, by rw [prepared_size_eq, slots_eq]; decide⟩
  refine WP.call prepared_prep_correct hp (Covers.append_left rK (Covers.right wB)) wB ?_
  intro s' rd wr sp frame regs _ post
  refine ⟨⟨rd, wr, sp, regs, frame⟩, ?_⟩
  have h := post.1
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (r := .r0) (by decide), State.callEntry_gpr s (r := .r1) (by decide),
    State.callEntry_gpr s (r := .r2) (by decide), h0, h1, h2] at h
  exact h

def prepArgs (s : State) : State :=
  (((s.setReg .r0 (s.gpr .r4)).setReg .r1 1).setReg .r2 (s.gpr sb)).setReg .r3 182

theorem prepArgs_run (s : State) :
    runBlock isa [movR .r0 .r4, .mov .r1 (.imm 1), movR .r2 sb, .mov .r3 (.imm 182)] s = some (prepArgs s) := by
  rfl

theorem prepare_wp {s : State} {K B : BitVec 32} (hK : s.gpr .r4 = K) (hB : s.gpr sb = B)
    (fitK : K.toNat + 128 ≤ 2 ^ 32) (fitB : B.toNat + 4 * slots ≤ 2 ^ 32)
    (sep : Region.Disjoint ⟨State.addr K, 128⟩ ⟨State.addr B, 4 * slots⟩)
    (rK : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr))
    (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr) :
    WP isa BatchCbc.prepare s fun s' => CallInv s B s' ∧
      Holds layout s'.mem (State.addr B) (Spec.Sm4.scheduleAt s.mem (State.addr K)) .decrypt := by
  refine WP.seq (WP.of_runBlock ⟨prepArgs s, prepArgs_run s, ?_⟩)
  have hg : ∀ r ∈ preserved, r ≠ .lr → (prepArgs s).gpr r = s.gpr r := by
    intro r hr hlr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [prepArgs, State.setReg, sb]
  refine WP.mono (prepare_call_wp (by simp [prepArgs, State.setReg, hK])
    (by simp [prepArgs, State.setReg]) (by simpa [prepArgs, State.setReg, sb] using hB)
    (by simp [prepArgs, State.setReg]) fitK fitB sep rK wB) fun s' h => ?_
  exact ⟨⟨h.1.rd, h.1.wr, h.1.sp, fun r hr hlr => (h.1.regs r hr hlr).trans (hg r hr hlr), h.1.frame⟩, h.2⟩


structure SetupPost (s : State) (B I : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨counterAddr B, 16⟩] s.mem s'.mem
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (State.addr I) 16
  table : Holds layout s'.mem (State.addr B) K .decrypt
  z : s'.z = decide (n = 0)

theorem setup_wp {s : State} {B I : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (h : ChainPre s B I) (hn : n < 2 ^ 32) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) :
    WP isa (.block (BatchCtr.copyCounterIn ++ ([.cmp .r7 (.imm 0)] : List Instr))) s (SetupPost s B I K n) := by
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterIn) (l₂ := [.cmp .r7 (.imm 0)])).mpr
  refine WP.mono (counterIn_wp h) fun s₁ c₁ => ?_
  have table₁ : Holds layout s₁.mem (State.addr B) K .decrypt := table_frame hH c₁.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  refine Proof.MdStream.Arm.wp_cmp (Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ hz => ?_
  refine WP.block_nil ⟨fun r h9 h10 => by rw [u₂.gpr, c₁.regs r h9 h10], u₂.rd.trans c₁.rd,
    u₂.wr.trans c₁.wr, u₂.sp.trans c₁.sp,
    by rw [u₂.mem]; exact c₁.frame, by rw [u₂.mem]; exact c₁.block,
    by rw [u₂.mem]; exact table₁, ?_⟩
  rw [hz, c₁.regs _ (by decide) (by decide), hN]
  exact difference_zero hn (Nat.zero_le n)

end VG.Proof.Sm4.Arm.CbcPrepare

end

end

/-! # The CBC decryption prologue -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcPrologue
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

structure Ready (s₀ : State) (s : State) : Prop where
  base : s.gpr sb = Sc s₀
  key : s.gpr .r4 = Kp s₀
  iv : s.gpr .r5 = Iv s₀
  data : s.gpr .r6 = Dp s₀
  left : s.gpr .r7 = BitVec.ofNat 32 (N s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  saved : Spill.Saved s.mem (State.addr (Sc s₀)) s₀.gpr BatchCtr.modeSaved
  frame : Frame [wsR s₀] s₀.mem s.mem
  table : Holds layout s.mem (State.addr (Sc s₀)) (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))) .decrypt
  counter : bytesAt s.mem (counterAddr (Sc s₀)) 16 = bytesAt s₀.mem (State.addr (Iv s₀)) 16
  z : s.z = decide (N s₀ = 0)

theorem prologue_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCbc.prologue s₀ (Ready s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  have ha : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 :=
    ⟨argR s₀, List.mem_append_left _ (by rw [hp.rd]; simp), Region.contains_self _ _⟩
  refine WP.seq (WP.mono (entry_wp rfl ha rfl hp.fitB hw) fun s₁ e₁ => ?_)
  have eWide : Frame [wsR s₀] s₀.mem s₁.mem := e₁.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Offset.sub_base _ (by change 1456 + 36 ≤ 4 * BatchCtr.totalSlots; decide)⟩
  have sch₁ : Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₀)) = Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀)) :=
    Proof.Sm4.scheduleAt_congr fun i hi => eWide.bytes
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.ks)
      (by change 128 ≤ 2 ^ 64; decide) hi
  have wc : Covers [⟨State.addr (Sc s₀), 4 * slots⟩] s₁.wr := by
    rw [e₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using [])
  refine WP.seq (WP.mono (CbcPrepare.prepare_wp e₁.key e₁.base hp.fitK
    (by have h := hp.fitB; change (Sc s₀).toNat + 4 * slots ≤ 2 ^ 32; rw [slots_eq]; change (Sc s₀).toNat + 1512 ≤ 2 ^ 32 at h; omega_using [h])
    (hp.ks.sub_right (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using [])))
    (by rw [e₁.rd, e₁.wr]; exact hp.key) wc) fun s₂ ⟨p₂, table₂⟩ => ?_)
  rw [sch₁] at table₂
  have base₂ : s₂.gpr sb = Sc s₀ := (p₂.regs _ (by decide) (by decide)).trans e₁.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (p₂.regs _ (by decide) (by decide)).trans e₁.iv
  have pWide : Frame [wsR s₀] s₁.mem s₂.mem := p₂.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_using [])⟩
  have prefixFrame := eWide.trans pWide
  have saved₂ := e₁.saved.frame mode_slots p₂.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide))
  have counterPre : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [p₂.wr, e₁.wr]; exact hw,
      by rw [p₂.wr, e₁.wr]; exact hi, hp.ivs⟩
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 (N s₀) := by
    rw [p₂.regs _ (by decide) (by decide), e₁.left]
    exact (BitVec.ofNat_toNat 32 (s₀.gpr .r3)).symm
  refine WP.mono (CbcPrepare.setup_wp counterPre (s₀.gpr .r3).isLt n₂ table₂) fun s₃ u₃ => ?_
  have uWide : Frame [wsR s₀] s₂.mem s₃.mem := u₃.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wsR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩
  have saved₃ := saved₂.frame mode_slots u₃.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, u₃.rd.trans (p₂.rd.trans e₁.rd), u₃.wr.trans (p₂.wr.trans e₁.wr),
    u₃.sp.trans (p₂.sp.trans e₁.sp), saved₃, prefixFrame.trans uWide, u₃.table, ?_, u₃.z⟩
  · rw [u₃.regs _ (by decide) (by decide)]; exact base₂
  · rw [u₃.regs _ (by decide) (by decide), p₂.regs _ (by decide) (by decide)]; exact e₁.key
  · rw [u₃.regs _ (by decide) (by decide)]; exact iv₂
  · rw [u₃.regs _ (by decide) (by decide), p₂.regs _ (by decide) (by decide)]; exact e₁.data
  · rw [u₃.regs _ (by decide) (by decide)]; exact n₂
  · rw [u₃.counter]
    apply bytes_frame prefixFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs

end VG.Proof.Sm4.Arm.CbcPrologue

end

end

/-! ### `Sm4.Arm.CbcGroup`, which this module and modules that import it used -/

section

/-! ### `Sm4.Arm.CbcFill`, which only this module used -/

section

/-! ### `Sm4.Arm.CbcReverse`, which only this module used -/

section

/-! # Combining CBC's decrypted blocks in reverse order -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcReverse
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (copyWord xorWord)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

/-- Keep the source's observable fields separate, so flag-only changes are
irrelevant to this effect. -/
structure Effect (g₀ : Reg → BitVec 32) (m₀ : Mem) (rd₀ wr₀ : List Region) (sp₀ : BitVec 32)
    (rs : List Region) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → s.gpr r = g₀ r
  rd : s.rd = rd₀
  wr : s.wr = wr₀
  sp : s.sp = sp₀
  frame : Frame rs m₀ s.mem

abbrev effect (s₀ : State) (rs : List Region) (s : State) : Prop :=
  Effect s₀.gpr s₀.mem s₀.rd s₀.wr s₀.sp rs s

def blockPost (s₀ : State) (P : Addr) (out : List Byte) (s : State) : Prop :=
  effect s₀ [⟨P, 16⟩] s ∧ bytesAt s.mem P 16 = out

def prevAddr (B D : BitVec 32) (j : Nat) : Addr :=
  if j = 0 then counterAddr B else dataAddr D (j - 1)

def outBlock (m : Mem) (B D : BitVec 32) (j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m (bufferAddr B j) 16) (bytesAt m (prevAddr B D j) 16)

def prefixPost (s₀ : State) (B D : BitVec 32) (n : Nat) (s : State) : Prop :=
  effect s₀ [⟨State.addr D, 16 * n⟩] s ∧
    ∀ k < n, bytesAt s.mem (dataAddr D k) 16 = outBlock s₀.mem B D k

theorem xorN_block {s : State} {rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre 4 s rd rs od os P Q) :
    WP isa (.block ((List.range 4).flatMap (xorWord rd rs od os))) s
      (blockPost s P (Spec.Cbc.xor (bytesAt s.mem P 16) (bytesAt s.mem Q 16))) := by
  refine WP.mono (xorN_wp h) fun s' c => ⟨⟨c.regs, c.rd, c.wr, c.sp, ?_⟩, ?_⟩
  · rw [c.mem]; exact Proof.Modes.over_frame _ _ _ _
  · rw [c.mem, bytesAt_over_self _ _ _ (by decide), xor_bytes]

theorem data_part {s : State} {B D : BitVec 32} {g j : Nat} (h : CfbFill.Pre B D g s) (hj : j < g) :
    Covers [⟨dataAddr D j, 16⟩] s.wr :=
  (Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * g⟩, List.mem_singleton_self _, 16 * j, rfl, by change 16 * j + 16 ≤ 16 * g; omega_using [hj]⟩).trans h.wd

theorem copy_plain_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block ((List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)))) s
      (CopyPost s (dataAddr D j) (bufferAddr B j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.data], by rw [h.base], by rw [h.data]; have := h.fitD; omega_using [hj, this],
    by rw [h.base]; have := h.fitB; rw [total_eq, tailSlot] at *; omega_using [hg, hj, this],
    by change 16 * j + 16 ≤ 4096; omega_using [hg, hj], by change 4 * tailSlot + 16 * j + 16 ≤ 4096; rw [tailSlot]; omega_using [hg, hj],
    by decide, by decide, by decide, by decide, data_part h hj,
    Covers.right (workspace_part h.hw (4 * tailSlot + 16 * j) 16 (by rw [tailSlot, total_eq]; omega_using [hg, hj])),
    (h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hj]))⟩

theorem xor_prev_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block ((List.range 4).flatMap (if j = 0 then xorWord .r6 sb 0 (4 * BatchCtr.counterSlot)
      else xorWord .r6 .r6 (16 * j) (16 * (j - 1))))) s
      (blockPost s (dataAddr D j) (Spec.Cbc.xor (bytesAt s.mem (dataAddr D j) 16)
        (bytesAt s.mem (prevAddr B D j) 16))) := by
  by_cases he : j = 0
  · subst j
    simp only [↓reduceIte, prevAddr]
    apply xorN_block
    exact ⟨by rw [h.data, BitVec.add_zero]; simp only [dataAddr, Nat.mul_zero, BitVec.add_zero], by rw [h.base],
      by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by rw [h.base]; have := h.fitB; change B.toNat + 1512 ≤ 2 ^ 32 at this; change B.toNat + 1492 + 16 ≤ 2 ^ 32; omega_using [this],
      by decide, by decide, by decide, by decide, by decide, by decide, data_part h hj,
      Covers.right (workspace_part h.hw 1492 16 (by decide)),
      (h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame⟩
  · simp only [he, ↓reduceIte, prevAddr]
    apply xorN_block
    exact ⟨by rw [h.data], by rw [h.data], by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by rw [h.data]; have := h.fitD; omega_using [hj, this],
      by change 16 * j + 16 ≤ 4096; omega_using [hg, hj], by change 16 * (j - 1) + 16 ≤ 4096; omega_using [hg, hj],
      by decide, by decide, by decide, by decide, data_part h hj, Covers.right (data_part h (j := j - 1) (by omega_using [hj])),
      Offset.disjoint _ (.inr (by omega_using [he])) (by omega_using [hg, hj]) (by omega_using [hg, hj])⟩

theorem step_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block (BatchCbc.xorBlock j)) s (blockPost s (dataAddr D j) (outBlock s.mem B D j)) := by
  apply (WP.block_append_iff (M := isa)
    (l₁ := (List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)))
    (l₂ := (List.range 4).flatMap (if j = 0 then xorWord .r6 sb 0 (4 * BatchCtr.counterSlot)
      else xorWord .r6 .r6 (16 * j) (16 * (j - 1))))).mpr
  refine WP.mono (copy_plain_wp h hg hj) fun s₁ c => ?_
  obtain p : CfbFill.Pre B D g s₁ := ⟨(c.regs _ (by decide) (by decide)).trans h.base,
    (c.regs _ (by decide) (by decide)).trans h.data, (c.regs _ (by decide) (by decide)).trans h.group,
    h.fitB, h.fitD, by rw [c.wr]; exact h.hw, by rw [c.wr]; exact h.wd, h.sep⟩
  obtain prev : bytesAt s₁.mem (prevAddr B D j) 16 = bytesAt s.mem (prevAddr B D j) 16 := by
    apply bytes_frame c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    by_cases he : j = 0
    · simp only [prevAddr, he, ↓reduceIte]
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega_using [he])) (by omega_using [hg, hj]) (by omega_using [hg, hj])
  refine WP.mono (xor_prev_wp p hg hj) fun s₂ ⟨x, out⟩ => ?_
  refine ⟨⟨fun r h9 h10 => (x.regs r h9 h10).trans (c.regs r h9 h10), x.rd.trans c.rd,
    x.wr.trans c.wr, x.sp.trans c.sp, c.frame.trans x.frame⟩, ?_⟩
  rw [out, c.block, prev]
  rfl

theorem Effect.pre {s₀ s : State} {B D : BitVec 32} {g : Nat} {rs : List Region}
    (h : CfbFill.Pre B D g s₀) (e : effect s₀ rs s) : CfbFill.Pre B D g s :=
  ⟨(e.regs _ (by decide) (by decide)).trans h.base, (e.regs _ (by decide) (by decide)).trans h.data,
    (e.regs _ (by decide) (by decide)).trans h.group, h.fitB, h.fitD,
    by rw [e.wr]; exact h.hw, by rw [e.wr]; exact h.wd, h.sep⟩

theorem out_kept {s : State} {m' : Mem} {B D : BitVec 32} {g j k : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) (hk : k < j)
    (hf : Frame [⟨dataAddr D j, 16⟩] s.mem m') : outBlock m' B D k = outBlock s.mem B D k := by
  unfold outBlock
  obtain buf : bytesAt m' (bufferAddr B k) 16 = bytesAt s.mem (bufferAddr B k) 16 := by
    apply bytes_frame hf
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right
      (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hj, hk]))).symm
  obtain prv : bytesAt m' (prevAddr B D k) 16 = bytesAt s.mem (prevAddr B D k) 16 := by
    apply bytes_frame hf
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    by_cases he : k = 0
    · simp only [prevAddr, he, ↓reduceIte]
      exact ((h.sep.sub_left (Offset.sub_base _ (by omega_using [hj]))).sub_right CfbFill.counter_frame).symm
    · simp only [prevAddr, he, ↓reduceIte]
      exact Offset.disjoint _ (.inl (by omega_using [hk])) (by omega_using [hg, hj, hk]) (by omega_using [hg, hj])
  rw [buf, prv]

theorem prefix_wp {s : State} {B D : BitVec 32} {g j : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (BatchCbc.xorPrefix j) s (prefixPost s B D (j + 1)) := by
  induction j generalizing s with
  | zero =>
    refine WP.mono (step_wp h hg hj) fun s' ⟨e, out⟩ => ⟨⟨e.regs, e.rd, e.wr, e.sp, ?_⟩, ?_⟩
    · simpa only [dataAddr, Nat.mul_zero, BitVec.add_zero] using e.frame
    · intro k hk
      obtain he : k = 0 := by omega_using [hk]
      subst k
      exact out
  | succ j ih =>
    refine WP.seq (WP.mono (step_wp h hg hj) fun s₁ ⟨e, out⟩ => ?_)
    refine WP.mono (ih (e.pre h) (by omega_using [hj])) fun s₂ ⟨e', blocks⟩ => ?_
    obtain f₁ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s.mem s₁.mem := e.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [])⟩
    obtain f₂ : Frame [⟨State.addr D, 16 * (j + 1 + 1)⟩] s₁.mem s₂.mem := e'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1 + 1)⟩, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
    refine ⟨⟨fun r h9 h10 => (e'.regs r h9 h10).trans (e.regs r h9 h10), e'.rd.trans e.rd,
      e'.wr.trans e.wr, e'.sp.trans e.sp, f₁.trans f₂⟩, ?_⟩
    intro k hk
    by_cases he : k = j + 1
    · subst k
      rw [bytes_frame (P := dataAddr D (j + 1)) e'.frame (fun r hr => ?_), out]
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by omega_using []) (by omega_using [hg, hj])
    · rw [blocks k (by omega_using [hk, he])]
      exact out_kept h hg hj (by omega_using [hk, he]) e.frame

theorem choose_wp {s : State} {B D : BitVec 32} {g j m : Nat}
    (h : CfbFill.Pre B D g s) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) :
    WP isa (BatchCbc.chooseXor j m) s (prefixPost s B D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    obtain jj : j < 8 := by omega_using [hg, hj]
    let sc := subFlags s (s.gpr .r11) (BitVec.ofNat 32 (j + 1))
    obtain pc : CfbFill.Pre B D g sc := ⟨h.base, h.data, h.group, h.fitB, h.fitD, h.hw, h.wd, h.sep⟩
    refine WP.seq (WP.of_runBlock ⟨sc, CfbFill.compare_run s j jj, ?_⟩)
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj h.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      obtain p := prefix_wp pc hg hj
      rw [eq] at p
      exact p
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih pc (by omega_using [hj, ne]) (by omega_using [hm])

theorem xor_wp {s : State} {B D : BitVec 32} {g : Nat}
    (h : CfbFill.Pre B D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) :
    WP isa (BatchCbc.chooseXor 0 8) s (prefixPost s B D g) := choose_wp h hg8 (by omega_using [hg]) hg8

end VG.Proof.Sm4.Arm.CbcReverse

end

end


/-! # CBC decryption inputs and the ciphertext saved for continuation -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcFill
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.CbcReverse (effect Effect data_part)
open VG.Proof.Modes.Arm
open VG.Spec.Aes (bytesAt)

structure Pre (B I D : BitVec 32) (g : Nat) (s : State) : Prop where
  core : CfbFill.Pre B D g s
  iv : s.gpr .r5 = I
  fitI : I.toNat + 16 ≤ 2 ^ 32
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * g⟩
  ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

def regions (B I : BitVec 32) : List Region := [⟨bufferAddr B 0, 128⟩, ⟨State.addr I, 16⟩]

structure Inv (s₀ : State) (B I D : BitVec 32) (j : Nat) (s : State) : Prop where
  kept : effect s₀ (regions B I) s
  lanes : ∀ k < j, bytesAt s.mem (bufferAddr B k) 16 = bytesAt s₀.mem (dataAddr D k) 16

structure Post (s₀ : State) (B I D : BitVec 32) (g : Nat) (s : State) : Prop extends Inv s₀ B I D g s where
  iv : bytesAt s.mem (State.addr I) 16 = bytesAt s₀.mem (dataAddr D (g - 1)) 16

theorem Inv.pre {s₀ s : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (i : Inv s₀ B I D j s) : Pre B I D g s :=
  ⟨i.kept.pre h.core, (i.kept.regs _ (by decide) (by decide)).trans h.iv, h.fitI,
    by rw [i.kept.wr]; exact h.hi, h.id, h.ib⟩

theorem Inv.cmp {s₀ s : State} {B I D : BitVec 32} {j : Nat} (h : Inv s₀ B I D j s) (a b : BitVec 32) :
    Inv s₀ B I D j (subFlags s a b) :=
  ⟨⟨h.kept.regs, h.kept.rd, h.kept.wr, h.kept.sp, h.kept.frame⟩, h.lanes⟩

theorem Inv.data_kept {s₀ s : State} {B I D : BitVec 32} {g j k : Nat}
    (h : Pre B I D g s₀) (i : Inv s₀ B I D j s) (hk : k < g) :
    bytesAt s.mem (dataAddr D k) 16 = bytesAt s₀.mem (dataAddr D k) 16 := by
  apply bytes_frame i.kept.frame
  intro r hr
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Offset.sub_base _ (by decide))
  · exact h.id.symm.sub_left (Offset.sub_base _ (by omega_using [hk]))

theorem save_wp {s : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s) (hg : g ≤ 8) (hj : j < g) :
    WP isa (.block (BatchCbc.saveLast j)) s (CopyPost s (State.addr I) (dataAddr D j)) := by
  apply copyBlock_wp
  exact ⟨by rw [h.iv, BitVec.add_zero], by rw [h.core.data],
    by rw [h.iv]; have := h.fitI; omega_using [this],
    by rw [h.core.data]; have := h.core.fitD; omega_using [hj, this],
    by decide, by change 16 * j + 16 ≤ 4096; omega_using [hg, hj],
    by decide, by decide, by decide, by decide, h.hi, Covers.right (data_part h.core hj),
    h.id.sub_right (Offset.sub_base _ (by omega_using [hj]))⟩

theorem Inv.copy {s₀ s s' : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (i : Inv s₀ B I D j s)
    (c : CopyPost s (bufferAddr B j) (dataAddr D j) s') : Inv s₀ B I D (j + 1) s' := by
  obtain cf : Frame (regions B I) s.mem s'.mem := c.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨bufferAddr B 0, 128⟩, List.mem_cons_self, CfbFill.lane_frame (by omega_using [hg, hj])⟩
  refine ⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.kept.regs r h9 h10), c.rd.trans i.kept.rd,
    c.wr.trans i.kept.wr, c.sp.trans i.kept.sp, i.kept.frame.trans cf⟩, ?_⟩
  intro k hk
  by_cases he : k = j
  · subst k
    rw [c.block, i.data_kept h hj]
  · rw [bytes_frame (P := bufferAddr B k) c.frame (fun r hr => ?_)]
    exact i.lanes k (by omega_using [hk, he])
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by change 4 * tailSlot + 16 * k + 16 ≤ 4 * tailSlot + 16 * j; omega_using [hk, he]))
      (by change 4 * tailSlot + 16 * k + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj, hk])
      (by change 4 * tailSlot + 16 * j + 16 ≤ 2 ^ 64; rw [tailSlot]; omega_using [hg, hj])

theorem Inv.last {s₀ s s' : State} {B I D : BitVec 32} {g j : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j + 1 = g) (i : Inv s₀ B I D g s)
    (c : CopyPost s (State.addr I) (dataAddr D j) s') : Post s₀ B I D g s' := by
  obtain cf : Frame (regions B I) s.mem s'.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  refine ⟨⟨⟨fun r h9 h10 => (c.regs r h9 h10).trans (i.kept.regs r h9 h10), c.rd.trans i.kept.rd,
    c.wr.trans i.kept.wr, c.sp.trans i.kept.sp, i.kept.frame.trans cf⟩, ?_⟩, ?_⟩
  · intro k hk
    rw [bytes_frame (P := bufferAddr B k) c.frame (fun r hr => ?_)]
    exact i.lanes k hk
    simp only [List.mem_singleton] at hr; subst hr
    exact h.ib.symm.sub_left (Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_using [hg, hk]))
  · rw [c.block, i.data_kept h (by omega_using [hj]), show j = g - 1 by omega_using [hj]]

theorem steps_wp {s₀ s : State} {B I D : BitVec 32} {g j m : Nat}
    (h : Pre B I D g s₀) (hg : g ≤ 8) (hj : j < g) (hm : g ≤ j + m) (i : Inv s₀ B I D j s) :
    WP isa (BatchCbc.fillSteps j m) s (Post s₀ B I D g) := by
  induction m generalizing j s with
  | zero => omega
  | succ m ih =>
    obtain jj : j < 8 := by omega_using [hg, hj]
    obtain p := i.pre h
    refine WP.seq ?_
    apply (WP.block_append_iff (M := isa) (l₁ := BatchCbc.copyLane j)
      (l₂ := [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))])).mpr
    refine WP.mono (CfbFill.data_copy_wp (o := 4 * tailSlot + 16 * j) p.core hg hj
      (by rw [tailSlot, total_eq]; omega_using [jj])) fun s₁ c => ?_
    obtain i₁ := i.copy h hg hj c
    let sc := subFlags s₁ (s₁.gpr .r11) (BitVec.ofNat 32 (j + 1))
    obtain ic : Inv s₀ B I D (j + 1) sc := i₁.cmp _ _
    refine WP.of_runBlock ⟨sc, CfbFill.compare_run s₁ j jj, ?_⟩
    refine WP.ite (decide (j + 1 = g)) (CfbFill.compare_eq hg jj (i₁.pre h).core.group) (fun he => ?_) (fun he => ?_)
    · have eq : j + 1 = g := of_decide_eq_true he
      obtain icg : Inv s₀ B I D g sc := eq ▸ ic
      exact WP.mono (save_wp (ic.pre h) hg hj) fun s' cp => icg.last h hg eq cp
    · have ne : j + 1 ≠ g := by simpa using he
      exact ih (by omega_using [hj, ne]) (by omega_using [hm]) ic

theorem fill_wp {s : State} {B I D : BitVec 32} {g : Nat}
    (h : Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8) : WP isa BatchCbc.fill s (Post s B I D g) := by
  refine WP.seq (WP.of_runBlock ⟨s, CfbFill.pad_run s, ?_⟩)
  exact steps_wp h hg8 (by omega_using [hg]) hg8
    ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩, fun _ hk => by omega⟩

end VG.Proof.Sm4.Arm.CbcFill

end

end


/-! # One batch of CBC decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcGroup
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (blockAt_of_ecb table_frame count_wp difference_zero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

def regions (B I D : BitVec 32) (g : Nat) : List Region :=
  [⟨State.addr B, 4 * slots⟩, ⟨counterAddr B, 16⟩, ⟨State.addr I, 16⟩, ⟨State.addr D, 16 * g⟩]

def prevBlock (m : Mem) (B D : BitVec 32) (k : Nat) : List Byte :=
  if k = 0 then bytesAt m (counterAddr B) 16 else bytesAt m (dataAddr D (k - 1)) 16

theorem decrypted_lane {K : Spec.Sm4.Schedule} {m m' : Mem} {B : BitVec 32}
    (h : Spec.Sm4.blocksAt m' (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb K .decrypt (Spec.Sm4.blocksAt m (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks))
    {j : Nat} (hj : j < 8) :
    bytesAt m' (bufferAddr B j) 16 = Spec.Sm4.invCipher K (bytesAt m (bufferAddr B j) 16) := by
  obtain hb := blockAt_of_ecb h hj
  obtain ha : State.addr B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) = bufferAddr B j := by
    rw [Offset.add_add]; rfl
  rw [ha] at hb
  rw [Proof.Sm4.bytesAt_eq_blockAt, hb]
  rw [Spec.Sm4.invCipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]
  rfl

structure BatchPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r6, .r7, .r8, .r11], s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

def batch : Prog isa := .seq BatchCbc.fill
  (.seq BatchCtr.crypt (.seq (BatchCbc.chooseXor 0 8) (.block BatchCtr.copyCounterIn)))

theorem batch_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (h : CbcFill.Pre B I D g s) (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa batch s (BatchPost s B I D K g) := by
  refine WP.seq (WP.mono (CbcFill.fill_wp h hg hg8) fun s₁ f => ?_)
  obtain p₁ := f.toInv.pre h
  obtain hH₁ : Holds layout s₁.mem (State.addr B) K .decrypt := table_frame hH f.kept.frame fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left (Offset.sub_base _ (by decide))
  obtain counter₁ : bytesAt s₁.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    apply bytes_frame f.kept.frame
    intro r hr
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left CfbFill.counter_frame
  obtain wc : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f.kept.wr]
    simpa only [BitVec.add_zero] using workspace_part h.core.hw 0 (4 * slots) (by decide)
  refine WP.seq (WP.mono (BatchCalls.crypt_wp p₁.core.base
    (by have := h.core.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this])
    wc hH₁) fun s₂ ⟨c, table₂, ecb₂⟩ => ?_)
  obtain p₂ : CbcFill.Pre B I D g s₂ := ⟨⟨(c.regs _ (by decide) (by decide)).trans p₁.core.base,
    (c.regs _ (by decide) (by decide)).trans p₁.core.data, (c.regs _ (by decide) (by decide)).trans p₁.core.group,
    h.core.fitB, h.core.fitD, by rw [c.wr]; exact p₁.core.hw, by rw [c.wr]; exact p₁.core.wd, h.core.sep⟩,
    (c.regs _ (by decide) (by decide)).trans p₁.iv, h.fitI, by rw [c.wr]; exact p₁.hi, h.id, h.ib⟩
  obtain iv₂ : bytesAt s₂.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) c.frame (fun r hr => ?_), f.iv]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.ib.sub_right (Region.sub_prefix (by decide))
  obtain data₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    rw [bytes_frame (P := dataAddr D k) c.frame (fun r hr => ?_), f.toInv.data_kept h hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right (Region.sub_prefix (by decide))
  obtain counter₂ : bytesAt s₂.mem (counterAddr B) 16 = bytesAt s.mem (counterAddr B) 16 := by
    rw [bytes_frame (P := counterAddr B) c.frame (fun r hr => ?_), counter₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  obtain plain₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 = Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16) := by
    intro k hk
    rw [decrypted_lane ecb₂ (by omega_using [hg8, hk]), f.lanes k hk]
  refine WP.seq (WP.mono (CbcReverse.xor_wp p₂.core hg hg8) fun s₃ ⟨x, blocks⟩ => ?_)
  obtain p₃ : ChainPre s₃ B I := ⟨(x.regs _ (by decide) (by decide)).trans p₂.core.base,
    (x.regs _ (by decide) (by decide)).trans p₂.iv, h.core.fitB, h.fitI,
    by rw [x.wr]; exact p₂.core.hw, by rw [x.wr]; exact p₂.hi, h.ib⟩
  obtain iv₃ : bytesAt s₃.mem (State.addr I) 16 = bytesAt s.mem (dataAddr D (g - 1)) 16 := by
    rw [bytes_frame (P := State.addr I) x.frame (fun r hr => ?_), iv₂]
    simp only [List.mem_singleton] at hr; subst hr
    exact h.id
  obtain table₃ := table_frame table₂ x.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.core.sep.symm.sub_left (Offset.sub_base _ (by decide)))
  refine WP.mono (counterIn_wp p₃) fun s₄ v => ?_
  obtain ff : Frame (regions B I D g) s.mem s₁.mem := f.kept.frame.sub fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr I, 16⟩, by simp [regions], fun _ h => h⟩
  obtain fc : Frame (regions B I D g) s₁.mem s₂.mem := c.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  obtain fx : Frame (regions B I D g) s₂.mem s₃.mem := x.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  obtain fv : Frame (regions B I D g) s₃.mem s₄.mem := v.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [regions]
  refine ⟨?_, v.rd.trans (x.rd.trans (c.rd.trans f.kept.rd)), v.wr.trans (x.wr.trans (c.wr.trans f.kept.wr)),
    v.sp.trans (x.sp.trans (c.sp.trans f.kept.sp)), ((ff.trans fc).trans fx).trans fv, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [v.regs _ (by decide) (by decide), x.regs _ (by decide) (by decide), c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide)]
  · exact table_frame table₃ v.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide))
  · rw [v.block, iv₃]
  · intro k hk
    rw [bytes_frame (P := dataAddr D k) v.frame (fun r hr => ?_), blocks k hk]
    unfold CbcReverse.outBlock
    rw [plain₂ k hk]
    by_cases he : k = 0
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [counter₂]
    · simp only [CbcReverse.prevAddr, prevBlock, he, ↓reduceIte]
      rw [data₂ (k - 1) (by omega_using [hk])]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.core.sep.sub_left (Offset.sub_base _ (by omega_using [hk]))).sub_right CfbFill.counter_frame

structure Pre (B I D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  iv : s.gpr .r5 = I
  data : s.gpr .r6 = D
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  fitI : I.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  hi : Covers [⟨State.addr I, 16⟩] s.wr
  wd : Covers [⟨State.addr D, 16 * n⟩] s.wr
  id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩
  ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩
  db : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

structure GroupPost (s : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * min n 8)
  left : s'.gpr .r7 = BitVec.ofNat 32 (n - min n 8)
  z : s'.z = decide (n = min n 8)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (regions B I D (min n 8)) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .decrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = bytesAt s.mem (dataAddr D (min n 8 - 1)) 16
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt s.mem (dataAddr D k) 16)) (prevBlock s.mem B D k)

theorem shift_group (g : Nat) : (BitVec.ofNat 32 g <<< 4) = BitVec.ofNat 32 (16 * g) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 g * BitVec.ofNat 32 16 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem group_wp {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (h : Pre B I D n s) (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (hH : Holds layout s.mem (State.addr B) K .decrypt) : WP isa BatchCbc.group s (GroupPost s B I D K n) := by
  obtain hgN : min n 8 ≤ n := Nat.min_le_left _ _
  obtain hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain hg : 1 ≤ min n 8 := by omega_using [hn]
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  obtain wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero], by change 0 + 16 * min n 8 ≤ 16 * n; omega_using []⟩
  obtain fp : CbcFill.Pre B I D (min n 8) s₁ := ⟨⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fitB, by have := h.fitD; omega_using [this],
    by rw [wr₁]; exact h.hw, wd₁, h.db.sub_left (Region.sub_prefix (by omega_using []))⟩,
    (o₁ _ (by decide) (by decide)).trans h.iv, h.fitI, by rw [wr₁]; exact h.hi,
    h.id.sub_right (Region.sub_prefix (by omega_using [])), h.ib⟩
  refine WP.seq (WP.mono (batch_wp fp hg hg8 (by rw [m₁]; exact hH)) fun s₂ b => ?_)
  obtain d₂ : s₂.gpr .r6 = D := (b.regs _ (by simp)).trans fp.core.data
  obtain n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b.regs _ (by simp)).trans ((o₁ _ (by decide) (by decide)).trans h.left)
  obtain g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b.regs _ (by simp)).trans g₁
  refine Proof.MdStream.Arm.wp_mov (show Op2.eval s₂ (.shifted .r11 .lsl 4) = some (s₂.gpr .r11 <<< 4) from rfl) fun s₃ u₃ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_reg s₃ .r0) fun s₄ u₄ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_reg s₄ .r11) fun s₅ u₅ hz => ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (b.rd.trans rd₁))),
    u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (b.wr.trans wr₁))), u₅.sp.trans (u₄.sp.trans (u₃.sp.trans (b.sp.trans sp₁))), ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), b.regs _ (by simp), o₁ _ (by decide) (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), d₂, u₃.gpr, g₂, shift_group]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact Offset.ofNat_sub_ofNat hgN
  · rw [hz, u₄.other _ (by decide), u₃.other _ (by decide), n₂,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂]
    exact difference_zero hn32 hgN
  · rw [u₅.mem, u₄.mem, u₃.mem, ← m₁]; exact b.frame
  · rw [u₅.mem, u₄.mem, u₃.mem]; exact b.table
  · rw [u₅.mem, u₄.mem, u₃.mem, b.counter, m₁]
  · intro k hk
    rw [u₅.mem, u₄.mem, u₃.mem, b.blocks k hk, m₁]

end VG.Proof.Sm4.Arm.CbcGroup

end

end

/-! # The arbitrary-length batched SM4-CBC decryption loop on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.CbcLoop

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor VG.Proof.Sm4.Arm.CbcGroup
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- Blocks at and after `i` are outside a frame writing only earlier data
blocks and the separate working space. -/
theorem future_data {m m' : Mem} {B I D : BitVec 32} {n i j : Nat}
    (hn : n < 2 ^ 32) (hi : i ≤ j) (hj : j < n)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (hf : Frame (regions B I D i) m m') : bytesAt m' (dataAddr D j) 16 = bytesAt m (dataAddr D j) 16 := by
  apply bytes_frame hf
  intro r hr
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith))
  · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
  · exact id.symm.sub_left (Offset.sub_base _ (by omega_arith))
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

def chain (m : Mem) (D : BitVec 32) (t : List Byte) (i : Nat) : List Byte :=
  if i = 0 then t else bytesAt m (dataAddr D (i - 1)) 16

/-- CBC decryption's block at index `j`, from the original ciphertext. -/
def outBlock (m : Mem) (D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte) (j : Nat) : List Byte :=
  Spec.Cbc.xor (Spec.Sm4.invCipher K (bytesAt m (dataAddr D j) 16)) (chain m D t j)

structure LoopInv (s₀ : State) (B I D : BitVec 32) (K : Spec.Sm4.Schedule) (t : List Byte)
    (n i : Nat) (s : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r8], s.gpr r = s₀.gpr r
  data : s.gpr .r6 = D + BitVec.ofNat 32 (16 * i)
  left : s.gpr .r7 = BitVec.ofNat 32 (n - i)
  bound : i ≤ n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (regions B I D i) s₀.mem s.mem
  table : Holds layout s.mem (State.addr B) K .decrypt
  counter : bytesAt s.mem (counterAddr B) 16 = chain s₀.mem D t i
  blocks : ∀ j < i, bytesAt s.mem (dataAddr D j) 16 = outBlock s₀.mem D K t j

theorem loopInv_step {s₀ s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : LoopInv s₀ B I D K t n i s) :
    WP isa BatchCbc.group s fun s' =>
      LoopInv s₀ B I D K t n (i + min (n - i) 8) s' ∧ s'.z = decide (i + min (n - i) 8 = n) := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  let g := min (n - i) 8
  have hg : 1 ≤ g := by dsimp only [g]; omega_arith
  have hgn : g ≤ n - i := Nat.min_le_left _ _
  have hgi : i + g ≤ n := by omega_arith
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_arith)
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_arith)
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_arith)
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_arith⟩
  have sb' : s.gpr sb = B := (h.regs _ (by simp [sb])).trans hB
  have gp : CbcGroup.Pre B I Di (n - i) s := ⟨sb', (h.regs _ (by simp)).trans hI, h.data, h.left,
    fitB, fitI, by rw [diNat]; omega_arith, by rw [h.wr]; exact hw, by rw [h.wr]; exact hiv, wdi,
    id.sub_right subD, ib, sep.sub_left subD⟩
  refine WP.mono (group_wp gp (by omega_arith) (by omega_arith) h.table)
    fun s' hs => ?_
  have fNew : Frame (regions B I D (i + g)) s.mem s'.mem := hs.frame.sub fun r hr => by
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [regions], fun _ h => h⟩
    · exact ⟨⟨State.addr I, 16⟩, by simp [regions], fun _ h => h⟩
    · refine ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [regions], ?_⟩
      rw [diAddr]; exact Offset.sub_base _ (by omega_arith)
  have fOld : Frame (regions B I D (i + g)) s₀.mem s.mem := h.frame.sub fun r hr => by
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [regions], fun _ h => h⟩
    · exact ⟨⟨State.addr I, 16⟩, by simp [regions], fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * (i + g)⟩, by simp [regions], Region.sub_prefix (by omega_arith)⟩
  refine ⟨⟨fun r hr => (hs.regs r hr).trans (h.regs r hr), ?_, ?_, hgi,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, fOld.trans fNew, hs.table, ?_, ?_⟩, ?_⟩
  · rw [hs.data]
    change D + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (16 * g) = _
    rw [Offset.add_add]; congr 2; omega_arith
  · rw [hs.left, show n - i - min (n - i) 8 = n - (i + min (n - i) 8) by omega_arith]
  · rw [hs.counter]
    have ha : dataAddr Di (g - 1) = dataAddr D (i + g - 1) := by
      change State.addr Di + BitVec.ofNat 64 (16 * (g - 1)) = _
      rw [diAddr, Offset.add_add]
      congr 2; omega_arith
    rw [ha, future_data hn32 (by omega_arith) (by omega_arith) sep id h.frame]
    simp only [chain, show i + min (n - i) 8 ≠ 0 by omega_arith, ↓reduceIte]
    rfl
  · intro j hj
    by_cases hjOld : j < i
    · rw [bytes_frame (P := dataAddr D j) hs.frame (fun r hr => ?_), h.blocks j hjOld]
      simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
          (Region.sub_prefix (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith))
      · exact (sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
          (Offset.sub_base _ (by change 4 * BatchCtr.counterSlot + 16 ≤ 4 * BatchCtr.totalSlots; decide))
      · exact id.symm.sub_left (Offset.sub_base _ (by omega_arith))
      · rw [diAddr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · have hjG : j - i < g := by omega_arith
      have ha : dataAddr Di (j - i) = dataAddr D j := by
        change State.addr Di + BitVec.ofNat 64 (16 * (j - i)) = _
        rw [diAddr, Offset.add_add]
        congr 2; omega_arith
      have hb := hs.blocks (j - i) hjG
      rw [ha, future_data hn32 (by omega_arith) (by omega_arith) sep id h.frame] at hb
      have inp : prevBlock s.mem B Di (j - i) = chain s₀.mem D t j := by
        by_cases he : j = i
        · subst j
          simpa only [prevBlock, Nat.sub_self, ↓reduceIte] using h.counter
        · have ne : j - i ≠ 0 := by omega_arith
          have az : dataAddr Di (j - i - 1) = dataAddr D (j - 1) := by
            change State.addr Di + BitVec.ofNat 64 (16 * (j - i - 1)) = _
            rw [diAddr, Offset.add_add]
            congr 2; omega_arith
          simp only [prevBlock, ne, ↓reduceIte, chain, show j ≠ 0 by omega_arith]
          rw [az, future_data hn32 (by omega_arith) (by omega_arith) sep id h.frame]
      rw [inp] at hb
      exact hb
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_arith

theorem loop_wp {s₀ : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .decrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.loop BatchCbc.group .ne) s₀ (LoopInv s₀ B I D K t n n) := by
  have hi : LoopInv s₀ B I D K t n 0 s₀ :=
    ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
      by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B I D K t n i s)
    (fun m s hs => ?_) n s₀ ⟨0, by omega_arith, by omega_arith, hi⟩
  obtain ⟨i, rfl, hi, hs⟩ := hs
  refine WP.mono (loopInv_step hn32 hi hB fitB fitD hI fitI hiv id ib hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : i + min (n - i) 8 = n
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      n - (i + min (n - i) 8), by omega_arith,
      i + min (n - i) 8, rfl, by have := h'.bound; omega_arith, h'⟩

theorem loopOrEmpty_wp {s₀ : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r7 = BitVec.ofNat 32 n) (hZ : s₀.z = decide (n = 0))
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s₀.mem (State.addr B) K .decrypt) (hC : bytesAt s₀.mem (counterAddr B) 16 = t) :
    WP isa (.ite .eq (.block []) (.loop BatchCbc.group .ne)) s₀ (LoopInv s₀ B I D K t n n) := by
  refine WP.ite (decide (n = 0)) (by change some s₀.z = some (decide (n = 0)); rw [hZ]) (fun hz => ?_) (fun hz => ?_)
  · have hn : n = 0 := of_decide_eq_true hz
    subst hn
    exact WP.block_nil
      ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
        by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
        by change bytesAt s₀.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩
  · have hn : 1 ≤ n := by simp at hz; omega_arith
    exact loop_wp hn hn32 hB hD hN fitB fitD hI fitI hiv id ib hw wd sep hH hC

theorem blocks_getD {m : Mem} {D : BitVec 32} {n k : Nat} (hk : k < n) :
    (Spec.Cbc.blocksAt m (State.addr D) n).getD k [] = bytesAt m (dataAddr D k) 16 := by
  rw [← List.getElem_eq_getD (h := by simp only [Spec.Cbc.blocksAt, List.length_map, List.length_range]; exact hk) []]
  simp only [Spec.Cbc.blocksAt, List.getElem_map, List.getElem_range]

theorem loop_output {s₀ s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (h : LoopInv s₀ B I D K t n n s) :
    Spec.Cbc.blocksAt s.mem (State.addr D) n =
      Spec.Cbc.decrypt (Spec.Sm4.invCipher K) t (Spec.Cbc.blocksAt s₀.mem (State.addr D) n) := by
  rw [Proof.Modes.decrypt_eq, show (Spec.Cbc.blocksAt s₀.mem (State.addr D) n).length = n by simp [Spec.Cbc.blocksAt]]
  conv => lhs; unfold Spec.Cbc.blocksAt
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  rw [blocks_getD hjn, h.blocks j hjn]
  unfold outBlock chain
  by_cases he : j = 0
  · simp only [he, ↓reduceIte]
  · simp only [he, ↓reduceIte]
    rw [blocks_getD (by omega_arith)]

theorem chain_next (m : Mem) (D : BitVec 32) (t : List Byte) (n : Nat) :
    chain m D t n = Spec.Cbc.next t (Spec.Cbc.blocksAt m (State.addr D) n) := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [Spec.Cbc.blocksAt, Spec.Cbc.next, Proof.Modes.getLastD_map_range]
    simp only [chain, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]

end VG.Proof.Sm4.Arm.CbcLoop

end

end

/-! ### `Sm4.Arm.CbcBody`, which only this module used -/

section

/-! # Functional composition of the prepared, eight-block SM4-CBC decryption implementation -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.CbcBody

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.CbcLoop VG.Proof.Sm4.Arm.CbcGroup
open VG.Proof.Sm4.Arm.CbcPrologue
open VG.Spec.Aes (bytesAt)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (bytesAt s₀.mem (State.addr (Iv s₀)) 16) (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 =
    Spec.Cbc.next (bytesAt s₀.mem (State.addr (Iv s₀)) 16)
      (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCbc.decrypt s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have blocks₁ : Spec.Cbc.blocksAt s₁.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) p.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ds.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD p.iv hp.fitI (by rw [p.wr]; exact hi) hp.id hp.ivs
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [CbcGroup.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide))
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  have output := loop_output l
  rw [blocks₁] at output
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have blocks₃ : Spec.Cbc.blocksAt s₃.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₂.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.id.symm.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, blocks₃]; exact output
  · rw [mem, c.block, l.counter, chain_next, blocks₁]

end VG.Proof.Sm4.Arm.CbcBody

end

end

/-! ### `Sm4.Arm.CbcCT`, which only this module used -/

section

/-! ### `Sm4.Arm.CbcHead`, which only this module used -/

section

/-! # Public registers across the CBC decryption cipher phase -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcHead
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (count_wp table_frame)
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq BatchCtr.count (.seq BatchCbc.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq (BatchCbc.chooseXor 0 8)
  (.seq (.block BatchCtr.copyCounterIn) (.block BatchCbc.advance))
def proHead : Prog isa := .seq (.block BatchCtr.entry) BatchCbc.prepare

structure HeadPre (B I D : BitVec 32) (n : Nat) (s : State) : Prop extends CbcGroup.Pre B I D n s where
  table : ∃ K, Holds layout s.mem (State.addr B) K .decrypt

structure HeadPost (s : State) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r5, .r6, .r7, .r8], s'.gpr r = s.gpr r
  group : s'.gpr .r11 = BitVec.ofNat 32 (min n 8)

theorem head_wp {s : State} {B I D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (h : HeadPre B I D n s) : WP isa groupHead s (HeadPost s n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega_using [hn]
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero], by change 0 + 16 * min n 8 ≤ 16 * n; omega_using []⟩
  have fp : CbcFill.Pre B I D (min n 8) s₁ := ⟨⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fitB, by have := h.fitD; omega_using [this],
    by rw [wr₁]; exact h.hw, wd₁, h.db.sub_left (Region.sub_prefix (by omega_using []))⟩,
    (o₁ _ (by decide) (by decide)).trans h.iv, h.fitI, by rw [wr₁]; exact h.hi,
    h.id.sub_right (Region.sub_prefix (by omega_using [])), h.ib⟩
  have table₁ : Holds layout s₁.mem (State.addr B) K .decrypt := by rw [m₁]; exact hH
  refine WP.seq (WP.mono (CbcFill.fill_wp fp hg hg8) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.kept.regs _ (by decide) (by decide)).trans fp.core.base
  have table₂ : Holds layout s₂.mem (State.addr B) K .decrypt := table_frame table₁ f.kept.frame fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left (Offset.sub_base _ (by decide))
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.kept.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.hw 0 (4 * slots) (by decide)
  refine WP.mono (BatchCalls.crypt_wp b₂
    (by have := h.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this])
    wc table₂) fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide), g₁]

theorem proHead_wp {s : State} (hp : BatchPrologue.Pre s) : WP isa proHead s fun s' =>
    s'.gpr .r5 = Iv s ∧ s'.gpr .r7 = BitVec.ofNat 32 (N s) ∧ s'.gpr sb = Sc s := by
  have hw := hp.writable (r := wsR s) (by simp)
  have ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
    ⟨argR s, List.mem_append_left _ (by rw [hp.rd]; simp), Region.contains_self _ _⟩
  refine WP.seq (WP.mono (entry_wp rfl ha rfl hp.fitB hw) fun s₁ e => ?_)
  have wc : Covers [⟨State.addr (Sc s), 4 * slots⟩] s₁.wr := by
    rw [e.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by decide)
  refine WP.mono (CbcPrepare.prepare_wp e.key e.base hp.fitK
    (by have := hp.fitB; change (Sc s).toNat + 1456 ≤ 2 ^ 32; change (Sc s).toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this])
    (hp.ks.sub_right (Region.sub_prefix (by decide)))
    (by rw [e.rd, e.wr]; exact hp.key) wc) fun s₂ ⟨p, _⟩ => ?_
  refine ⟨(p.regs _ (by decide) (by decide)).trans e.iv, ?_, (p.regs _ (by decide) (by decide)).trans e.base⟩
  rw [p.regs _ (by decide) (by decide), e.left]
  exact (BitVec.ofNat_toNat 32 (s.gpr .r3)).symm

theorem loop_pre {s₀ s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : CbcLoop.LoopInv s₀ B I D K t n i s) : HeadPre B I (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_using [hi, fitD])
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, fitD])
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_using [hi])
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  exact ⟨⟨(h.regs _ (by simp [sb])).trans hB, (h.regs _ (by simp)).trans hI, h.data, h.left,
    fitB, fitI, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega_using [hi, fitD],
    by rw [h.wr]; exact hw, by rw [h.wr]; exact hiv, wdi,
    id.sub_right subD, ib, sep.sub_left subD⟩, ⟨K, h.table⟩⟩

end VG.Proof.Sm4.Arm.CbcHead

end

end


/-! # Constant-time composition for batched SM4-CBC decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcCT

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.CbcHead VG.Proof.Sm4.Arm.CbcLoop
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchFill
open VG.Proof.Sm4.Arm.CbcPrologue
open VG.Proof.Sm4.Arm.CbcGroup

theorem append_eq {a b c d : List Leak} (h : a = b) (h' : c = d) : a ++ c = b ++ d := by rw [h, h']

/-- Functional postconditions hold of any execution, by determinism. -/
theorem result {c : Prog isa} {s s' : State} {t : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s t s') : Q s' := by
  obtain ⟨_, _, e', h'⟩ := h
  obtain ⟨_, rfl⟩ := Exec.det e e'
  exact h'

theorem checked {rs : List Reg} {c : Prog isa}
    (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (hag : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (P := fun a b => ∀ r ∈ rs, a.gpr r = b.gpr r)
    (Taint.ofRegs rs) (fun _ _ h => Taint.agree_ofRegs h) hc) _ _ _ _ _ _ hag e₁ e₂).1

/-- Reassociate the existing group at the point where the helper returns. -/
theorem group_split {s s' : State} {t : List Leak} (e : Exec isa BatchCbc.group s t s') :
    ∃ m th tt, Exec isa groupHead s th m ∧ Exec isa groupTail m tt s' ∧ t = th ++ tt := by
  cases e with | seq a b =>
    cases b with | seq c d =>
      cases c with | seq f g =>
        cases g with | seq k x =>
          cases x with | seq xx cp =>
            exact ⟨_, _, _, .seq a (.seq f k), .seq xx (.seq cp d), by simp only [List.append_assoc]⟩

theorem group_ct {B I D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : HeadPre B I D n s₁) (h₂ : HeadPre B I D n s₂) (hd : s₁.gpr .r6 = s₂.gpr .r6)
    (e₁ : Exec isa BatchCbc.group s₁ t₁ s₁') (e₂ : Exec isa BatchCbc.group s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨m₁, th₁, tt₁, eh₁, et₁, tr₁⟩ := group_split e₁
  obtain ⟨m₂, th₂, tt₂, eh₂, et₂, tr₂⟩ := group_split e₂
  have ht : th₁ = th₂ := checked CbcTaint.groupHead_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h₁.iv.trans h₂.iv.symm
    · exact hd
    · rw [h₁.left, h₂.left]
    · exact h₁.base.trans h₂.base.symm) eh₁ eh₂
  have p₁ := result (head_wp hn hn32 h₁) eh₁
  have p₂ := result (head_wp hn hn32 h₂) eh₂
  have tt : tt₁ = tt₂ := checked CbcTaint.groupTail_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.iv.trans h₂.iv.symm
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), hd]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), h₁.left, h₂.left]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.base.trans h₂.base.symm
    · rw [p₁.group, p₂.group]) et₁ et₂
  rw [tr₁, tr₂, ht, tt]

section
variable {s₀ s₀' : State} {B I D : BitVec 32} {K K' : Spec.Sm4.Schedule} {t t' : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hB' : s₀'.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (hI' : s₀'.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr) (hiv' : Covers [⟨State.addr I, 16⟩] s₀'.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (hw' : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀'.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (wd' : Covers [⟨State.addr D, 16 * n⟩] s₀'.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)

def LoopRel (s₀ s₀' : State) (B I D : BitVec 32) (K K' : Spec.Sm4.Schedule) (t t' : List Byte)
    (n m : Nat) (a b : State) : Prop :=
  ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B I D K t n i a ∧ LoopInv s₀' B I D K' t' n i b

include hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep in
 theorem loop_ct (m : Nat) :
    RelCT isa (LoopRel s₀ s₀' B I D K K' t t' n m) (.loop BatchCbc.group .ne)
      (fun a b => LoopInv s₀ B I D K t n n a ∧ LoopInv s₀' B I D K' t' n n b) := by
  refine RelCT.loop (M := isa) (LoopRel s₀ s₀' B I D K K' t t' n) (fun m => ?_) m
  intro a b ta tb a' b' ⟨i, hm, hi, l, l'⟩ ea eb
  have p := loop_pre hn32 hi hB fitB fitD hI fitI hiv id ib hw wd sep l
  have p' := loop_pre hn32 hi hB' fitB fitD hI' fitI hiv' id ib hw' wd' sep l'
  have eqtr := group_ct (by omega_using [hi]) (by omega_using [hn32]) p p' (by rw [l.data, l'.data]) ea eb
  obtain ⟨la, za⟩ := result (loopInv_step hn32 hi hB fitB fitD hI fitI hiv id ib hw wd sep l) ea
  obtain ⟨lb, zb⟩ := result (loopInv_step hn32 hi hB' fitB fitD hI' fitI hiv' id ib hw' wd' sep l') eb
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
    refine ⟨n - (i + min (n - i) 8), by omega_using [hm, hi], i + min (n - i) 8, rfl, ?_, la, lb⟩
    have := la.bound
    omega_using [hi, he]

include hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep in
 theorem dataLoop_ct :
    RelCT isa (fun a b => LoopInv s₀ B I D K t n 0 a ∧ LoopInv s₀' B I D K' t' n 0 b ∧
      a.z = decide (n = 0) ∧ b.z = decide (n = 0)) BatchCbc.dataLoop (fun _ _ => True) := by
  have ev {a : State} (h : a.z = decide (n = 0)) : isa.eval .eq a = some (decide (n = 0)) := by
    change some a.z = _; rw [h]
  refine RelCT.ite (fun a b h => by rw [ev h.2.2.1, ev h.2.2.2]) ?_ ?_
  · obtain ⟨_, hc⟩ := BatchTaint.nil_check
    exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (fun r hr => by simp at hr)) hc
  · refine (loop_ct (K := K) (K' := K') (t := t) (t' := t') hn32 hB hB' fitB fitD hI hI' fitI hiv hiv' id ib hw hw' wd wd' sep n).mono (fun a b h => ?_) (fun _ _ _ => trivial)
    have he := h.2
    rw [ev h.1.2.2.1] at he
    have hn : 0 < n := by
      have : n ≠ 0 := by simpa using he
      omega_using [this]
    exact ⟨0, by omega_using [], hn, h.1.1, h.1.2.1⟩

end

def Pub (s s' : State) : Prop :=
  s.sp = s'.sp ∧ s.gpr .r0 = s'.gpr .r0 ∧ s.gpr .r1 = s'.gpr .r1 ∧
  s.gpr .r2 = s'.gpr .r2 ∧ s.gpr .r3 = s'.gpr .r3 ∧ Sc s = Sc s'

theorem arg_wf {s : State} (h : BatchPrologue.Pre s) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  refine ⟨h.spFit, ?_⟩
  intro r hr
  have he : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  rw [he, h.wr] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.ia.symm, h.da.symm, h.sa.symm]

theorem prologue_ct {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : BatchPrologue.Pre s₁) (h₂ : BatchPrologue.Pre s₂) (hq : Pub s₁ s₂)
    (e₁ : Exec isa BatchCbc.prologue s₁ t₁ s₁') (e₂ : Exec isa BatchCbc.prologue s₂ t₂ s₂') : t₁ = t₂ := by
  cases e₁ with | seq a b =>
    cases b with | seq p u =>
      cases e₂ with | seq a' b' =>
        cases b' with | seq p' u' =>
          have eh := Exec.seq a p
          have eh' := Exec.seq a' p'
          have hag : VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) s₁ s₂ :=
            agree_argTaint (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl
              exacts [hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) hq.1 (arg_wf h₁) (arg_wf h₂)
              (argMem_of (j := 1) hq.1 h₁.spFit (fun i hi => by
                have he : i = 0 := by omega_using [hi]
                subst i
                exact hq.2.2.2.2.2))
          obtain ⟨_, hc⟩ := CbcTaint.proHead_check
          have heq := ((RelCT.taint (A := taint) (P := fun a b => VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) a b)
            (argTaint [.r0, .r1, .r2, .r3] 4) (fun _ _ h => h) hc) _ _ _ _ _ _ hag eh eh').1
          obtain ⟨i, n, b⟩ := result (proHead_wp h₁) eh
          obtain ⟨i', n', b'⟩ := result (proHead_wp h₂) eh'
          have heq' := checked BatchTaint.setup_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · rw [i, i']; exact hq.2.2.1
            · rw [n, n']; unfold N; rw [hq.2.2.2.2.1]
            · exact b.trans (hq.2.2.2.2.2.trans b'.symm)) u u'
          simpa only [List.append_assoc] using append_eq heq heq'

theorem initial {s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hD : s.gpr .r6 = D) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Proof.Sm4.Prepared.Holds layout s.mem (State.addr B) K .decrypt)
    (hC : Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t) : LoopInv s B I D K t n 0 s :=
  ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
    by simpa only [Nat.sub_zero] using hN, by omega_using [], rfl, rfl, rfl, Frame.refl _ _, hH,
    by change Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega⟩

theorem cbc_ct : ConstantTime isa BatchPrologue.Pre Pub BatchCbc.decrypt := by
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' hp₁ hp₂ hq e₁ e₂
  have eB : Sc s₂ = Sc s₁ := hq.2.2.2.2.2.symm
  have eI : Iv s₂ = Iv s₁ := hq.2.2.1.symm
  have eD : Dp s₂ = Dp s₁ := hq.2.2.2.1.symm
  have eN : N s₂ = N s₁ := by unfold N; rw [hq.2.2.2.2.1]
  have hw₁ := hp₁.writable (r := wsR s₁) (by simp)
  have hw₂ := hp₂.writable (r := wsR s₂) (by simp)
  have hi₁ := hp₁.writable (r := ivR s₁) (by simp)
  have hi₂ := hp₂.writable (r := ivR s₂) (by simp)
  have wd₁ := hp₁.writable (r := dataR s₁) (by simp)
  have wd₂ := hp₂.writable (r := dataR s₂) (by simp)
  cases e₁ with | seq pro rest =>
    cases rest with | seq dl fin =>
      cases e₂ with | seq pro' rest' =>
        cases rest' with | seq dl' fin' =>
          have eqP := prologue_ct hp₁ hp₂ hq pro pro'
          have p := result (CbcPrologue.prologue_wp hp₁) pro
          have p' := result (CbcPrologue.prologue_wp hp₂) pro'
          have pb' := p'.base
          have pi' := p'.iv
          rw [eI] at pi'
          have pd' := p'.data
          have pn' := p'.left
          have pt' := p'.table
          have pc' := p'.counter
          have pz' := p'.z
          rw [eB] at pb' pt' pc'
          rw [eD] at pd'
          rw [eN] at pn' pz'
          have ib := initial (I := Iv s₁) p.data p.left p.table p.counter
          have ib' := initial (I := Iv s₁) pd' pn' pt' pc'
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
          have i₁ := hi₁
          have i₂ := hi₂
          rw [← p.wr] at i₁
          rw [← p'.wr] at i₂
          change Covers [⟨State.addr (Iv s₂), 16⟩] _ at i₂
          rw [eI] at i₂
          have rel := dataLoop_ct (K := Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₁)))
            (K' := Spec.Sm4.scheduleAt s₂.mem (State.addr (Kp s₂)))
            (t := Spec.Aes.bytesAt s₁.mem (State.addr (Iv s₁)) 16)
            (t' := Spec.Aes.bytesAt s₂.mem (State.addr (Iv s₂)) 16)
            (s₁.gpr .r3).isLt p.base pb' hp₁.fitB hp₁.fitD p.iv pi' hp₁.fitI i₁ i₂ hp₁.id hp₁.ivs w₁ w₂ d₁ d₂ hp₁.ds
          have eqL := (rel _ _ _ _ _ _ ⟨ib, ib', p.z, pz'⟩ dl dl').1
          have l := result (loopOrEmpty_wp (s₁.gpr .r3).isLt p.base p.data p.left p.z hp₁.fitB hp₁.fitD p.iv hp₁.fitI i₁ hp₁.id hp₁.ivs w₁ d₁ hp₁.ds p.table p.counter) dl
          have l' := result (loopOrEmpty_wp (s₁.gpr .r3).isLt pb' pd' pn' pz' hp₁.fitB hp₁.fitD pi' hp₁.fitI i₂ hp₁.id hp₁.ivs w₂ d₂ hp₁.ds pt' pc') dl'
          have eqF := checked BatchTaint.finish_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [l.regs _ (by simp), l'.regs _ (by simp), p.iv, p'.iv]; exact hq.2.2.1
            · rw [l.regs _ (by simp), l'.regs _ (by simp)]
              exact p.base.trans pb'.symm) fin fin'
          exact append_eq eqP (append_eq eqL eqF)

end VG.Proof.Sm4.Arm.CbcCT

end

end


/-! # Batched ARMv7 SM4-CBC decryption meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcBatchVerified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.CbcBody VG.Proof.Sm4.Arm.CbcCT

def cbcArm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : cbcArm.pre s) :
    ∃ t s', Exec isa BatchCbc.decrypt s t s' ∧ abiPreserved s s' ∧ cbcArm.post s s' := by
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

theorem implies : cbcArm.Implies (Proof.Sm4.cbcDecChainedScratchContract Arm.abi 189 0) where
  pre s h := by
    sig_pre [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Proof.Sm4.cbcDecChainedPost, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.cbcDecChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCbc.decrypt (Proof.Sm4.cbcDecChainedScratchContract Arm.abi 189 0) :=
  Verified.of_correct correct cbc_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Spec.Sm4.cbcDecryptChainedContract Arm.abi 1520).pre s := by
  implies_sat [Spec.Sm4.cbcDecryptChainedContract, Spec.Sm4.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCbc.decrypt)
    (Spec.Sm4.cbcDecryptChainedContract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cbcDecChainedPost_local _)
    (Proof.Sm4.cbcDecChainedPostOut_local _) frameSat

end VG.Proof.Sm4.Arm.CbcBatchVerified
