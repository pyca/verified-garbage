module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sm4.Arm.Core
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

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
