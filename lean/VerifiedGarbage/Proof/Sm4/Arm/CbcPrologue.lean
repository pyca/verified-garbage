module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem

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
