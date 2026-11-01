module

public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Calls of the prepared-key SM4 helpers from ARMv7 modes -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchCalls

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Prepared (Holds Keeps)

/-- The permissions, ABI registers and memory outside the cipher's workspace
survive a helper call. The caller's return address is kept separately. -/
structure CallInv (s : State) (b : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  regs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem

/-- Call preparation from its ABI arguments, with narrowed permissions. -/
theorem prepare_call_wp {s : State} {K B : BitVec 32}
    (h0 : s.gpr .r0 = K) (h1 : s.gpr .r1 = 0) (h2 : s.gpr .r2 = B) (h3 : s.gpr .r3 = 182)
    (fitK : K.toNat + 128 ≤ 2 ^ 32) (fitB : B.toNat + 4 * slots ≤ 2 ^ 32)
    (sep : Region.Disjoint ⟨State.addr K, 128⟩ ⟨State.addr B, 4 * slots⟩)
    (rK : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr))
    (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr) :
    WP isa (.call "vg_sm4_prepare_keys" prepareKeys) s fun s' =>
      CallInv s B s' ∧ Holds layout s'.mem (State.addr B) (Spec.Sm4.scheduleAt s.mem (State.addr K)) .encrypt := by
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
  (((s.setReg .r0 (s.gpr .r4)).setReg .r1 0).setReg .r2 (s.gpr sb)).setReg .r3 182

theorem prepArgs_run (s : State) :
    runBlock isa [movR .r0 .r4, .mov .r1 (.imm 0), movR .r2 sb, .mov .r3 (.imm 182)] s = some (prepArgs s) := by
  rfl

theorem prepare_wp {s : State} {K B : BitVec 32} (hK : s.gpr .r4 = K) (hB : s.gpr sb = B)
    (fitK : K.toNat + 128 ≤ 2 ^ 32) (fitB : B.toNat + 4 * slots ≤ 2 ^ 32)
    (sep : Region.Disjoint ⟨State.addr K, 128⟩ ⟨State.addr B, 4 * slots⟩)
    (rK : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr))
    (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr) :
    WP isa BatchCtr.prepare s fun s' => CallInv s B s' ∧
      Holds layout s'.mem (State.addr B) (Spec.Sm4.scheduleAt s.mem (State.addr K)) .encrypt := by
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

theorem table_kept {m m' : Mem} {B : BitVec 32} {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : Holds layout m (State.addr B) K d)
    (hk : Keeps (State.addr B) 182 layout.cryptScratch m m') : Holds layout m' (State.addr B) K d := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [hk (384 + i) (by omega) (by
    intro r hr
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; change 384 ≤ 384 + i; omega
    · left; change 384 + i < 1408; omega)]
  exact h (384, 1024) (by rw [layout_table]; simp) i hi

/-- Inline the eight-block cipher on its already prepared workspace. -/
theorem crypt_inline_wp {s : State} {B : BitVec 32} {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h0 : s.gpr .r0 = B) (h1 : s.gpr .r1 = 182)
    (fitB : B.toNat + 4 * slots ≤ 2 ^ 32) (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr)
    (hH : Holds layout s.mem (State.addr B) K d) :
    WP isa cryptPrepared s fun s' =>
      CallInv s B s' ∧ Holds layout s'.mem (State.addr B) K d ∧
      Spec.Sm4.blocksAt s'.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb K d (Spec.Sm4.blocksAt s.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  have hp : cryptArm.pre (s.withRegions [] [⟨State.addr B, 4 * slots⟩]) := by
    simp only [cryptArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_mem, h0, h1]
    exact ⟨True.intro, by rw [slots_eq]; rfl,
      by change B.toNat + 4 * slots ≤ 2 ^ 32; exact fitB,
      by rw [prepared_size_eq, slots_eq]; decide, K, d, hH⟩
  refine WP.inline prepared_crypt_correct hp (by simpa only [List.nil_append] using Covers.right wB) wB ?_
  intro s' rd wr abi frame _ post
  have post' :
      (∀ k d, Holds layout s.mem (State.addr B) k d →
        Spec.Sm4.blocksAt s'.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
          Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (State.addr B) 182 layout.cryptScratch s.mem s'.mem := by
    simpa only [cryptArm, State.withRegions_gpr, State.withRegions_mem, h0, h1, show (182 : BitVec 32).toNat = 182 from rfl] using post
  exact ⟨⟨rd, wr, abi.2, fun r hr _ => abi.1 r hr, frame⟩, table_kept hH post'.2, post'.1 K d hH⟩

def cryptArgs (s : State) : State := (s.setReg .r0 (s.gpr sb)).setReg .r1 182

theorem cryptArgs_run (s : State) :
    runBlock isa [movR .r0 sb, .mov .r1 (.imm 182)] s = some (cryptArgs s) := by rfl

theorem crypt_wp {s : State} {B : BitVec 32} {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (hB : s.gpr sb = B) (fitB : B.toNat + 4 * slots ≤ 2 ^ 32)
    (wB : Covers [⟨State.addr B, 4 * slots⟩] s.wr)
    (hH : Holds layout s.mem (State.addr B) K d) :
    WP isa BatchCtr.crypt s fun s' => CallInv s B s' ∧ Holds layout s'.mem (State.addr B) K d ∧
      Spec.Sm4.blocksAt s'.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb K d (Spec.Sm4.blocksAt s.mem (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  refine WP.seq (WP.of_runBlock ⟨cryptArgs s, cryptArgs_run s, ?_⟩)
  have hg : ∀ r ∈ preserved, r ≠ .lr → (cryptArgs s).gpr r = s.gpr r := by
    intro r hr hlr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cryptArgs, State.setReg, sb]
  refine WP.mono (crypt_inline_wp (by simpa [cryptArgs, State.setReg, sb] using hB)
    (by simp [cryptArgs, State.setReg]) fitB wB hH) fun s' h => ?_
  exact ⟨⟨h.1.rd, h.1.wr, h.1.sp, fun r hr hlr => (h.1.regs r hr hlr).trans (hg r hr hlr), h.1.frame⟩, h.2⟩

end VG.Proof.Sm4.Arm.BatchCalls
