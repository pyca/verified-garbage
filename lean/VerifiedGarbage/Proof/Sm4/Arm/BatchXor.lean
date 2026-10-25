module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchFill
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Modes.Arm.Ops
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

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
