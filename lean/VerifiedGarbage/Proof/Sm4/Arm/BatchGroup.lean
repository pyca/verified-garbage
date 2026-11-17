module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedVerified
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Modes.Arm.Ops

/-! ### `Sm4.Arm.BatchXor`, which this module and modules that import it used -/

section

/-! # XORing an encrypted SM4 counter batch into the data on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchXor

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Impl.Modes.Arm (xorWord)
open VG.Proof.Modes.Arm VG.Proof.Sm4.Arm.BatchFill
open VG.Spec.Aes (bytesAt)

abbrev dataAddr (D : BitVec 32) (j : Nat) : Addr := State.addr D + BitVec.ofNat 64 (16 * j)

/-- The XOR of two blocks, as a bytewise map. -/
theorem xor_bytes (m : Mem) (P Q : Addr) :
    (List.range 16).map (fun i => m (P + BitVec.ofNat 64 i) ^^^ m (Q + BitVec.ofNat 64 i)) =
      Spec.Cbc.xor (bytesAt m P 16) (bytesAt m Q 16) := by
  apply List.ext_getElem
  · simp [Spec.Cbc.xor, bytesAt]
  · intro i h₁ h₂
    simp [Spec.Cbc.xor, bytesAt]

/-- A nonzero bounded counter reaches zero exactly at one. -/
theorem sub_one_zero (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    (BitVec.ofNat 32 n - 1 == 0) = decide (n = 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat hn]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at hnat
    have : (0 : BitVec 32).toNat = 0 := rfl
    rw [this] at hnat
    omega_arith
  · intro h; subst h; rfl

structure XorStepPost (s : State) (B D : BitVec 32) (j n : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → r ≠ .r6 → s'.gpr r = s.gpr r
  ptr : s'.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * (j + 1))
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * (j + 1))
  left : s'.gpr .r1 = BitVec.ofNat 32 (n - 1)
  z : s'.z = decide (n = 1)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨dataAddr D j, 16⟩] s.mem s'.mem
  block : bytesAt s'.mem (dataAddr D j) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D j) 16) (bytesAt s.mem (bufferAddr B j) 16)

theorem xorStep_wp {s : State} {B D : BitVec 32} {g j n : Nat}
    (hj : j < g) (hg8 : g ≤ 8) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hp : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j))
    (hD : s.gpr .r6 = D + BitVec.ofNat 32 (16 * j)) (hN : s.gpr .r1 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩) :
    WP isa (.block BatchCtr.xorBody) s (XorStepPost s B D j n) := by
  have sd : Region.Sub ⟨dataAddr D j, 16⟩ ⟨State.addr D, 16 * g⟩ := Offset.sub_base _ (by omega_arith)
  have sbuf : Region.Sub ⟨bufferAddr B j, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩ :=
    Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_arith)
  have wdest : Covers [⟨dataAddr D j, 16⟩] s.wr :=
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * g⟩, List.mem_singleton_self _, 16 * j, rfl, by change 16 * j + 16 ≤ 16 * g; omega_arith⟩).trans wd
  have wbuf := workspace_part hw (4 * tailSlot + 16 * j) 16 (by rw [tailSlot, total_eq]; omega_arith)
  have np : NPre 4 s .r6 .r0 0 0 (dataAddr D j) (bufferAddr B j) :=
    ⟨by rw [BitVec.add_zero, hD, addr_add (by omega_arith)],
      by rw [BitVec.add_zero, hp, addr_add (by rw [tailSlot, total_eq] at *; omega_arith)],
      by rw [hD, offset_nat _ _ (by omega_arith)]; omega_arith,
      by rw [hp, offset_nat _ _ (by rw [tailSlot, total_eq] at *; omega_arith)]; rw [tailSlot, total_eq] at *; omega_arith,
      by decide, by decide, by decide, by decide, by decide, by decide,
      wdest, Covers.right wbuf, (sep.sub_left sd).sub_right sbuf⟩
  apply WP.block_append_iff.mpr
  refine WP.mono (xorN_wp np) fun s₁ h₁ => ?_
  have frame₁ : Frame [⟨dataAddr D j, 16⟩] s.mem s₁.mem := by
    rw [h₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  have out₁ : bytesAt s₁.mem (dataAddr D j) 16 =
      Spec.Cbc.xor (bytesAt s.mem (dataAddr D j) 16) (bytesAt s.mem (bufferAddr B j) 16) := by
    rw [h₁.mem, bytesAt_over_self _ _ _ (by decide), xor_bytes]
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ => ?_
  refine Proof.MdStream.Arm.wp_add (Proof.MdStream.Arm.op2_imm (by decide)) fun s₃ u₃ => ?_
  refine Proof.MdStream.Arm.wp_subs (Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ u₄ hz => ?_
  refine WP.block_nil ⟨fun r h9 h10 h0 h1 h6 => by
      rw [u₄.other r h1, u₃.other r h6, u₂.other r h0, h₁.regs r h9 h10], ?_, ?_, ?_, ?_,
    by rw [u₄.rd, u₃.rd, u₂.rd, h₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, h₁.wr],
    by rw [u₄.sp, u₃.sp, u₂.sp, h₁.sp],
    by rw [u₄.mem, u₃.mem, u₂.mem]; exact frame₁,
    by rw [u₄.mem, u₃.mem, u₂.mem]; exact out₁⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, h₁.regs _ (by decide) (by decide), hp,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_add]
    congr 2
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hD,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.add_add]
    congr 2
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN]
    exact Offset.ofNat_sub_ofNat hn
  · rw [hz, u₃.other _ (by decide), u₂.other _ (by decide), h₁.regs _ (by decide) (by decide), hN]
    exact sub_one_zero n hn hn8

structure XorInv (s₀ : State) (B D : BitVec 32) (g j : Nat) (s : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → r ≠ .r6 → s.gpr r = s₀.gpr r
  ptr : s.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot + 16 * j)
  data : s.gpr .r6 = D + BitVec.ofNat 32 (16 * j)
  left : s.gpr .r1 = BitVec.ofNat 32 (g - j)
  bound : j ≤ g
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr D, 16 * j⟩] s₀.mem s.mem
  blocks : ∀ k < j, bytesAt s.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s₀.mem (dataAddr D k) 16) (bytesAt s₀.mem (bufferAddr B k) 16)

theorem xorInv_step {s₀ s : State} {B D : BitVec 32} {g j : Nat}
    (hg : g ≤ 8) (hj : j < g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : XorInv s₀ B D g j s) :
    WP isa (.block BatchCtr.xorBody) s fun s' => XorInv s₀ B D g (j + 1) s' ∧ s'.z = decide (j + 1 = g) := by
  refine WP.mono (xorStep_wp hj hg (by omega_arith) (by omega_arith) h.ptr h.data h.left fitB fitD
    (by rw [h.wr]; exact hw) (by rw [h.wr]; exact wd) sep) fun s' hs => ?_
  refine ⟨⟨fun r h9 h10 h0 h1 h6 => (hs.regs r h9 h10 h0 h1 h6).trans (h.regs r h9 h10 h0 h1 h6),
    hs.ptr, hs.data, by rw [hs.left, show g - j - 1 = g - (j + 1) by omega_arith], by omega_arith,
    hs.rd.trans h.rd, hs.wr.trans h.wr, hs.sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · have fOld : Frame [⟨State.addr D, 16 * (j + 1)⟩] s₀.mem s.mem :=
      h.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr D, 16 * (j + 1)⟩, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
    exact fOld.trans (hs.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr D, 16 * (j + 1)⟩, List.mem_singleton_self _, Offset.sub_base _ (by omega_arith)⟩)
  · intro k hk
    by_cases he : k = j
    · subst k
      have sameData : bytesAt s.mem (dataAddr D j) 16 = bytesAt s₀.mem (dataAddr D j) 16 :=
        bytes_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base (State.addr D) (by omega_arith) (by omega_arith)
      have sameBuf : bytesAt s.mem (bufferAddr B j) 16 = bytesAt s₀.mem (bufferAddr B j) 16 :=
        bytes_frame h.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have subB : Region.Sub ⟨bufferAddr B j, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩ :=
            Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_arith)
          exact (sep.symm.sub_left subB).sub_right (Region.sub_prefix (by omega_arith))
      rw [hs.block, sameData, sameBuf]
    · have hk' : k < j := by omega_arith
      rw [bytes_frame (P := dataAddr D k) hs.frame (fun r hr => ?_), h.blocks k hk']
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · rw [hs.z, Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    omega_arith

theorem xorLoop_wp {s₀ : State} {B D : BitVec 32} {g : Nat} (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hp : s₀.gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot)) (hD : s₀.gpr .r6 = D)
    (hN : s₀.gpr .r1 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩) :
    WP isa (.loop (.block BatchCtr.xorBody) .ne) s₀ (XorInv s₀ B D g g) := by
  have hi : XorInv s₀ B D g 0 s₀ :=
    ⟨fun _ _ _ _ _ _ => rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hp,
      by simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hD,
      by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, fun _ h => by omega_arith⟩
  refine WP.loop (M := isa)
    (fun m s => ∃ j, m = g - j ∧ j < g ∧ XorInv s₀ B D g j s)
    (fun m s hs => ?_) g s₀ ⟨0, by omega_arith, by omega_arith, hi⟩
  obtain ⟨j, rfl, hj, hs⟩ := hs
  refine WP.mono (xorInv_step hg8 hj fitB fitD hw wd sep hs) fun s' ⟨h', hz⟩ => ?_
  by_cases he : j + 1 = g
  · exact .inl ⟨by rw [fill_eval_ne, hz]; simp [he], by rw [he] at h'; exact h'⟩
  · exact .inr ⟨by rw [fill_eval_ne, hz]; simp only [he, decide_false, Bool.not_false],
      g - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩

structure XorPost (s : State) (B D : BitVec 32) (g : Nat) (s' : State) : Prop where
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r0 → r ≠ .r1 → r ≠ .r6 → s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * g)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨State.addr D, 16 * g⟩] s.mem s'.mem
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16) (bytesAt s.mem (bufferAddr B k) 16)

theorem xor_wp {s : State} {B D : BitVec 32} {g : Nat} (hg : 1 ≤ g) (hg8 : g ≤ 8)
    (hB : s.gpr sb = B) (hD : s.gpr .r6 = D) (hN : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩) :
    WP isa BatchCtr.xorGroup s (XorPost s B D g) := by
  have hp : (fillArgs s).gpr .r0 = B + BitVec.ofNat 32 (4 * tailSlot) := by
    simp only [fillArgs, RegUpd.gpr_setReg]; simp only [reduceCtorEq, ↓reduceIte]; rw [hB]
  have hd : (fillArgs s).gpr .r6 = D := by simpa [fillArgs, State.setReg, sb] using hD
  have hn : (fillArgs s).gpr .r1 = BitVec.ofNat 32 g := by rw [fillArgs, RegUpd.gpr_setReg_self, hN]
  refine WP.seq (WP.of_runBlock ⟨fillArgs s, fillArgs_run s, ?_⟩)
  refine WP.mono (xorLoop_wp hg hg8 hp hd hn fitB fitD hw wd sep) fun s' h => ?_
  refine ⟨fun r h9 h10 h0 h1 h6 => ?_, h.data, h.rd, h.wr, h.sp, h.frame, h.blocks⟩
  rw [h.regs r h9 h10 h0 h1 h6]
  simp only [fillArgs, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h0]

end VG.Proof.Sm4.Arm.BatchXor

end

end

/-! ### `Sm4.Arm.BatchCalls`, which this module and modules that import it used -/

section

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
  rw [hk (384 + i) (by omega_using [hi]) (by
    intro r hr
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; change 384 ≤ 384 + i; omega_using []
    · left; change 384 + i < 1408; omega_using [hi])]
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

end

end

/-! # One complete batch of SM4-CTR on ARMv7 -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.BatchGroup

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR lsrOp)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchXor
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- Block `j` of an ECB batch. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have h' := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at h'
  simpa [Spec.Sm4.blocksAt, hj] using h'

theorem encrypted_lane {K : Spec.Sm4.Schedule} {m m' : Mem} {B : BitVec 32}
    (h : Spec.Sm4.blocksAt m' (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb K .encrypt (Spec.Sm4.blocksAt m (State.addr B + BitVec.ofNat 64 layout.buf) layout.blocks))
    {j : Nat} (hj : j < 8) :
    bytesAt m' (bufferAddr B j) 16 = Spec.Sm4.cipher K (bytesAt m (bufferAddr B j) 16) := by
  have hb := blockAt_of_ecb h hj
  have ha : State.addr B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) = bufferAddr B j := by
    rw [Offset.add_add]; rfl
  rw [ha] at hb
  rw [Proof.Sm4.bytesAt_eq_blockAt, hb]
  rw [Spec.Sm4.cipher, Proof.Sm4.bytesAt_eq_blockAt, Proof.Sm4.ofFn_toList]
  rfl

/-- The key table survives writes disjoint from its one contiguous range. -/
theorem table_frame {m m' : Mem} {B : BitVec 32} {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    {rs : List Region} (h : Holds layout m (State.addr B) K d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr B + BitVec.ofNat 64 384, 1024⟩ r) :
    Holds layout m' (State.addr B) K d := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [← Offset.add_add, hf.bytes hd (by change 1024 ≤ 2 ^ 64; decide) hi]
  change m (State.addr B + BitVec.ofNat 64 384 + BitVec.ofNat 64 i) = _
  rw [Offset.add_add]
  exact h (384, 1024) (by rw [layout_table]; simp) i hi

/-- Choose `min(n, 8)` useful counter lanes. -/
theorem count_wp {s : State} {v : Nat} (hn : s.gpr .r7 = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    WP isa BatchCtr.count s fun s' => s'.gpr .r11 = BitVec.ofNat 32 (min v 8) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₂ := s.setReg .r10 (s.gpr .r7 >>> 3)
  let s₃ := subFlags s₂ (s₂.gpr .r10) 0
  have e₂₃ : runBlock isa [.mov .r10 (lsrOp .r7 3), .cmp .r10 (.imm 0)] s = some s₃ := by
    rw [runBlock_cons, show exec (.mov .r10 (lsrOp .r7 3)) s = some s₂ by simp [exec, Op2.eval, lsrOp, s₂],
      runStep_some, runBlock_cons,
      show exec (.cmp .r10 (.imm 0)) s₂ = some s₃ by simp [exec, Op2.eval, s₃]; decide,
      runStep_some, runBlock_nil]
  have z₃ : s₃.z = (BitVec.ofNat 32 v >>> 3 - 0 == 0) := by
    show (s₂.gpr .r10 - 0 == 0) = _; rw [RegUpd.gpr_setReg_self, hn]
  have o₃ : ∀ r, r ≠ .r10 → s₃.gpr r = s.gpr r := fun r hr => by
    show s₂.gpr r = _; rw [RegUpd.gpr_setReg_of_ne _ _ hr]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 v := by rw [o₃ _ (by decide), hn]
  unfold BatchCtr.count
  refine WP.seq (WP.of_runBlock ⟨s₃, e₂₃, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_ne s₃).trans (by
      rw [z₃, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith)) (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movImm_ok s₃ .r11 8 (by decide)
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, Nat.min_eq_right (by simp at h; omega_arith)]; rfl
  · obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r11 .r7
    refine WP.of_runBlock ⟨s₄, e₄, ?_, fun r h1 h2 => by rw [o₄ r h1, o₃ r h2], m₄, rd₄, wr₄, sp₄⟩
    rw [r₄, r7₃, Nat.min_eq_left (by simp at h; omega_arith)]

/-- Writes of one batch: the core's workspace, its running counter, and
the useful data blocks. The saved mode registers lie outside all three. -/
def batchRegions (B D : BitVec 32) (g : Nat) : List Region :=
  [⟨State.addr B, 4 * slots⟩, ⟨counterAddr B, 16⟩, ⟨State.addr D, 16 * g⟩]

structure BatchPost (s : State) (B D : BitVec 32) (K : Spec.Sm4.Schedule) (g : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r4, .r5, .r7, .r8, .r11], s'.gpr r = s.gpr r
  data : s'.gpr .r6 = D + BitVec.ofNat 32 (16 * g)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame (batchRegions B D g) s.mem s'.mem
  table : Holds layout s'.mem (State.addr B) K .encrypt
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) g
  blocks : ∀ k < g, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k))

theorem batch_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {g : Nat}
    (hg : 1 ≤ g) (hg8 : g ≤ 8) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hG : s.gpr .r11 = BitVec.ofNat 32 g)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * g ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * g⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * g⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr.batch s (BatchPost s B D K g) := by
  refine WP.seq (WP.mono (fill_wp hg hg8 hB hG fitB hw) fun s₁ f₁ => ?_)
  have sb₁ : s₁.gpr sb = B := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hB
  have r6₁ : s₁.gpr .r6 = D := (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hD
  have r11₁ : s₁.gpr .r11 = BitVec.ofNat 32 g :=
    (f₁.regs _ (by decide) (by decide) (by decide) (by decide)).trans hG
  have hH₁ : Holds layout s₁.mem (State.addr B) K .encrypt := table_frame hH f₁.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * g ≤ 384; rw [tailSlot]; omega_arith
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * g ≤ 2 ^ 64; rw [tailSlot]; omega_arith
    · apply Offset.disjoint (State.addr B)
      · left; change 384 + 1024 ≤ 4 * BatchCtr.counterSlot; decide
      · decide
      · decide
  have f₁wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.mem s₁.mem :=
    f₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by rw [tailSlot, total_eq]; omega_arith)⟩
      · exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
          Offset.sub_base _ (by decide)⟩
  have f₁batch : Frame (batchRegions B D g) s.mem s₁.mem := f₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr B, 4 * slots⟩, List.mem_cons_self,
        Offset.sub_base _ (by rw [tailSlot, slots_eq]; omega_arith)⟩
    · exact ⟨⟨counterAddr B, 16⟩, by simp [batchRegions], fun _ h => h⟩
  have wc₁ : Covers [⟨State.addr B, 4 * slots⟩] s₁.wr := by
    rw [f₁.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; rw [slots_eq, total_eq]; omega_arith)
  refine WP.seq (WP.mono (BatchCalls.crypt_wp sb₁ (by rw [total_eq] at fitB; rw [slots_eq]; omega_arith) wc₁ hH₁)
    fun s₂ ⟨c₂, table₂, ecb₂⟩ => ?_)
  have sb₂ : s₂.gpr sb = B := (c₂.regs _ (by decide) (by decide)).trans sb₁
  have r6₂ : s₂.gpr .r6 = D := (c₂.regs _ (by decide) (by decide)).trans r6₁
  have r11₂ : s₂.gpr .r11 = BitVec.ofNat 32 g := (c₂.regs _ (by decide) (by decide)).trans r11₁
  have c₂wide : Frame [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₁.mem s₂.mem :=
    c₂.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr B, 4 * BatchCtr.totalSlots⟩, List.mem_singleton_self _,
        Region.sub_prefix (by rw [slots_eq, total_eq]; omega_arith)⟩
  have c₂batch : Frame (batchRegions B D g) s₁.mem s₂.mem :=
    c₂.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
  have phaseFrame := f₁wide.trans c₂wide
  have counter₂ : bytesAt s₂.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) g := by
    rw [bytes_frame c₂.frame (fun r hr => ?_), f₁.counter]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by rw [slots_eq, counter_eq]; omega_arith) (by decide)
  have cipher₂ : ∀ k < g, bytesAt s₂.mem (bufferAddr B k) 16 =
      Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k) := by
    intro k hk
    rw [encrypted_lane ecb₂ (by omega_arith), f₁.lanes k hk]
  have plain₂ : ∀ k < g, bytesAt s₂.mem (dataAddr D k) 16 = bytesAt s.mem (dataAddr D k) 16 := by
    intro k hk
    apply bytes_frame phaseFrame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.sub_left (Offset.sub_base _ (by omega_arith))
  refine WP.mono (xor_wp hg hg8 sb₂ r6₂ r11₂ fitB fitD
    (by rw [c₂.wr, f₁.wr]; exact hw) (by rw [c₂.wr, f₁.wr]; exact wd) sep) fun s₃ x₃ => ?_
  have table₃ : Holds layout s₃.mem (State.addr B) K .encrypt := table_frame table₂ x₃.frame fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sep.symm.sub_left (Offset.sub_base _ (by change 384 + 1024 ≤ 4 * BatchCtr.totalSlots; rw [total_eq]; omega_arith))
  have counter₃ : bytesAt s₃.mem (counterAddr B) 16 = bytesAt s₂.mem (counterAddr B) 16 := by
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

theorem difference_zero {n g : Nat} (hn : n < 2 ^ 32) (hg : g ≤ n) :
    (BitVec.ofNat 32 n - BitVec.ofNat 32 g == 0) = decide (n = g) := by
  rw [Offset.ofNat_sub_ofNat hg, Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at hnat
    have : (0 : BitVec 32).toNat = 0 := rfl
    rw [this] at hnat
    omega_arith
  · intro h; subst h; simp

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
  counter : bytesAt s'.mem (counterAddr B) 16 = Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) (min n 8)
  blocks : ∀ k < min n 8, bytesAt s'.mem (dataAddr D k) 16 =
    Spec.Cbc.xor (bytesAt s.mem (dataAddr D k) 16)
      (Spec.Sm4.cipher K (Spec.Ctr.next (bytesAt s.mem (counterAddr B) 16) k))

theorem group_wp {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {n : Nat}
    (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hB : s.gpr sb = B) (hD : s.gpr .r6 = D)
    (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hH : Holds layout s.mem (State.addr B) K .encrypt) :
    WP isa BatchCtr.group s (GroupPost s B D K n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega_arith
  refine WP.seq (WP.mono (count_wp hN hn32) fun s₁ ⟨g₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans hB
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans hD
  have n₁ : s₁.gpr .r7 = BitVec.ofNat 32 n := (o₁ _ (by decide) (by decide)).trans hN
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * min n 8 ≤ 16 * n; omega_arith⟩
  refine WP.seq (WP.mono (batch_wp hg hg8 b₁ d₁ g₁ fitB (by omega_arith)
    (by rw [wr₁]; exact hw) wd₁ (sep.sub_left (Region.sub_prefix (by omega_arith)))
    (by rw [m₁]; exact hH)) fun s₂ b₂ => ?_)
  have n₂ : s₂.gpr .r7 = BitVec.ofNat 32 n := (b₂.regs _ (by simp)).trans n₁
  have g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (min n 8) := (b₂.regs _ (by simp)).trans g₁
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

end VG.Proof.Sm4.Arm.BatchGroup
