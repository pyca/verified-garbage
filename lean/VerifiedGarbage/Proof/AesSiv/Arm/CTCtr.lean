import VerifiedGarbage.Proof.AesSiv.Arm.CTFinish

/-!
# AES-SIV on ARMv7: CTR is constant time

Untrusted: everything here is checked by Lean. Two runs of `ctr 0` on data
at the same address and of the same length (`CtrI`) leak the same: the
first block loads the data's address and length from the stack arguments,
the same in both runs; the branches are on the length, and so are the
numbers of blocks and bytes; the calls of `vg_aes_ctr32` get the same
arguments in both runs (`ctrWholeArgs_ok`, `ctrTailArgs_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm
open VG.Proof.AesGcm.Arm (CT CtrCall ctr_call)
open VG.Impl.AesGcm.Arm (imm addI xorLoop)
open VG.Impl.CmacAes.Arm (mov)

/-- Before CTR's pieces: the data, `n` bytes at `D`, in `r6` and `r5`. -/
structure CI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  dat : Dat c w sp s D n
  r6 : s.gpr .r6 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n

/-- After code that keeps the callee-saved registers. -/
theorem CI.keep {c w sp D : BitVec 32} {R n : Nat} {s s' : State} (h : CI c w sp R D n s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : CI c w sp R D n s' :=
  ⟨h.env.of_saved hg hsp hrd hwr, h.dat.of_eq hrd hwr, by rw [hg _ (by decide) (by decide), h.r6],
    by rw [hg _ (by decide) (by decide), h.r5]⟩

/-- Before CTR: the data's address and length as the stack arguments, which
the regions the code may write are apart from. -/
structure CtrI (c w sp : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c w sp R s
  dat : Dat c w sp s D n
  wa : ∀ r ∈ s.wr, (⟨State.addr sp, 16⟩ : Region).Disjoint r
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  m0 : s.mem.readW (State.addr sp) 32 = D
  m1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  n32 : n < 2 ^ 32

/-- The first two stack arguments: the data's address and length. -/
theorem CtrI.arg {c w sp D : BitVec 32} {R n : Nat} {s : State} (h : CtrI c w sp R D n s) :
    stackArg s 0 = D ∧ stackArg s 1 = BitVec.ofNat 32 n := by
  have hsp := h.env.sp
  refine ⟨?_, ?_⟩
  · rw [stackArg, stackArgAddr, hsp, show 4 * 0 = 0 from rfl, BitVec.add_zero, h.m0]
  · rw [stackArg, stackArgAddr, hsp, addr_add (by have := h.afit; omega), h.m1]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp) (hR : R = 10 ∨ R = 12 ∨ R = 14)
include L hR

/-- The whole blocks. -/
theorem ctrWhole_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CI c w sp R D n) ctrWhole := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r6, .r9, .r10, .r11])
      (.block (ctrArgs ++ [mov .r3 .r6])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := fun s => CI c w sp R D n s ∧ s.z = decide (n / 16 = 0) ∧
      s.gpr .r12 = BitVec.ofNat 32 (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h12, hz, g, k⟩ := split16_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, hz, h12⟩) ?_
  refine CT.ite (decide (n / 16 = 0)) (fun s h => h.2.1) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => Env c w sp R s ∧
      CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D (w + BitVec.ofNat 32 256) R (n / 16))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1.r6, h₂.1.r6]
      all_goals exact env_eq h₁.1.env h₂.1.env (by simp)) hB)
    (fun s h => by
      obtain ⟨s', run, he, _, _, C⟩ := ctrWholeArgs_ok L h.1.env hR h.1.dat h.1.r6 rfl h.2.2
      exact WP.of_runBlock ⟨s', run, he, C⟩) ?_
  exact CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.sp, h₂.1.sp]⟩

/-- What the whole blocks keep. -/
theorem ctrWhole_keeps {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) {s : State} (h : CI c w sp R D n s) :
    WP isa ctrWhole s (CI c w sp R D n) := by
  obtain ⟨s₁, run₁, h12, hz, g, k⟩ := split16_ok hn h.r5
  have h₁ : CI c w sp R D n s₁ := ⟨h.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
    by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · exact WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil h₁)
      (fun h => by cases h)
  refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
  obtain ⟨s₂, run₂, _, g₂, k₂, C⟩ := ctrWholeArgs_ok L h₁.env hR h₁.dat h₁.r6 rfl h12
  have h₂ : CI c w sp R D n s₂ := h₁.keep (fun r hr hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2 hlr) k₂.sp k₂.rd k₂.wr
  exact WP.seq (WP.of_runBlock ⟨s₂, run₂, WP.mono (ctr_call C) fun s₃ p => h₂.keep p.saved p.sp p.rd p.wr⟩)

/-- The last bytes. -/
theorem ctrTail_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CI c w sp R D n) ctrTail := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r5])
      (.block [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r9, .r10, .r11])
      (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)])) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6, .r11])
      (.seq (.block [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4), .dp .add .r2 .r2 (.reg .r6), mov .r3 .r4])
        xorLoop) h).isSome = true := ⟨_, by taint_decide⟩
  let J (s : State) : Prop := CI c w sp R D n s ∧ s.gpr .r4 = BitVec.ofNat 32 (n % 16)
  refine CT.seq (J := fun s => J s ∧ s.z = decide (n % 16 = 0))
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hA)
    (fun s h => by
      obtain ⟨s', run, h4, hz, g, k⟩ := tailPre_ok hn h.r5
      exact WP.of_runBlock ⟨s', run, ⟨⟨h.env.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr, h.dat.of_eq k.rd k.wr,
        by rw [g _ (by decide), h.r6], by rw [g _ (by decide), h.r5]⟩, h4⟩, hz⟩) ?_
  refine CT.ite (decide (n % 16 = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  refine CT.seq (J := fun s => J s ∧ CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff)
      (w + BitVec.ofNat 32 ksOff) (w + BitVec.ofNat 32 256) R 1)
    (CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact env_eq h₁.1.1.env h₂.1.1.env (by simp)) hB)
    (fun s h => WP.mono (ctrTailArgs_ok L h.1.1.env hR) fun s' ⟨he, g, rd, wr, _, _, C⟩ =>
      ⟨⟨⟨he, h.1.1.dat.of_eq rd wr,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r6],
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.r5]⟩,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.2]⟩, C⟩) ?_
  refine CT.seq (J := J)
    (CT.ctr fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, _, h₁.2, h₂.2, by rw [h₁.1.1.env.sp, h₂.1.1.env.sp]⟩)
    (fun s h => WP.mono (ctr_call h.2) fun s' p =>
      ⟨h.1.1.keep p.saved p.sp p.rd p.wr, by rw [p.saved _ (by decide) (by decide), h.1.2]⟩) ?_
  exact CT.taint _ (fun s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2, h₂.2]
    · rw [h₁.1.r5, h₂.1.r5]
    · rw [h₁.1.r6, h₂.1.r6]
    · exact env_eq h₁.1.env h₂.1.env (by simp)) hC

/-- CTR from the IV at `W`. -/
theorem ctr_ct {D : BitVec 32} {n : Nat} (hn : n < 2 ^ 32) : CT (CtrI c w sp R D n) (ctr 0) := by
  obtain ⟨_, hA⟩ : ∃ h, (Taint.check VG.Arm.taint (argTaint [.r9, .r10, .r11] (4 * 2))
      (.block (counter 0 ++ [.ldrSp .r6 0, .ldrSp .r5 4])) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.seq (J := CI c w sp R D n)
    (CT.argTaint _ _ (fun s₁ s₂ h₁ h₂ => env_regs h₁.env h₂.env)
      (fun s₁ s₂ h₁ h₂ => by rw [h₁.env.sp, h₂.env.sp])
      (fun s h => ⟨by rw [h.env.sp]; have := h.afit; omega, fun r hr => by
        rw [h.env.sp]; exact (h.wa r hr).sub_left (Region.sub_prefix (by decide))⟩)
      (fun s₁ s₂ h₁ h₂ => argMem_of (by rw [h₁.env.sp, h₂.env.sp]) (by rw [h₁.env.sp]; have := h₁.afit; omega)
        fun i hi => by
          rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
          · rw [h₁.arg.1, h₂.arg.1]
          · rw [h₁.arg.2, h₂.arg.2]) hA)
    (fun s h => WP.mono (ctrPre_ok L h.env h.dat h.afit h.args h.args_w h.m0 h.m1)
      fun s' ⟨he, hD, h6, h5, _⟩ => ⟨he, hD, h6, h5⟩) ?_
  exact CT.seq (ctrWhole_ct L hR hn) (fun s h => ctrWhole_keeps L hR hn h) (ctrTail_ct L hR hn)

end

end VG.Proof.AesSiv.Arm
