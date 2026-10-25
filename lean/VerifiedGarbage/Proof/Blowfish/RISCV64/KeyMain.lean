module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Frame
public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.Impl.Blowfish.RISCV64
import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyInit
import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyP
import VerifiedGarbage.Proof.Blowfish.RISCV64.KeyEnc
import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
import VerifiedGarbage.Proof.Blowfish.KeyTable
import VerifiedGarbage.Proof.Blowfish.KeySched
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Blowfish on RISC-V: key expansion

`expandKey_wp`: the schedule at `a2` becomes the expansion of the key at
`a0`, built in the frame of 4176 bytes below the stack pointer, copied out,
and the frame zeroed (`Zeroed`) before it is freed.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What key expansion may assume: the key readable, the schedule writable,
apart from each other and from the 4176 bytes below the stack pointer, and
a valid key length. -/
structure KeyPre (s : State) : Prop where
  valid : validKey (s.gpr .a1).toNat
  rd : s.rd = [⟨s.gpr .a0, (s.gpr .a1).toNat⟩]
  wr : s.wr = [⟨s.gpr .a2, 4168⟩]
  keyS : (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩
  al : s.sp.toNat % 16 = 0
  sp : 4176 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
  stackSched : (⟨s.sp - 4176, 4176⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩

theorem expandKey_wp {s : State} (h : KeyPre s) :
    WP isa Impl.Blowfish.RISCV64.expandKey s fun s' =>
      scheduleAt s'.mem (s.gpr .a2) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) ∧
      Zeroed (frameBase s) s'.mem := by
  have hv := h.valid
  unfold validKey at hv
  have hF : frameBase s = s.sp - 4176 := frameBase_eq s
  have hFal : (frameBase s).toNat % 16 = 0 := frameBase_al s h.al h.sp
  -- The frame's regions.
  have fK : (⟨frameBase s, 4168⟩ : Region).Disjoint ⟨s.gpr .a0, (s.gpr .a1).toNat⟩ :=
    h.stackKey.sub_left (by rw [hF]; exact Region.sub_prefix (by decide))
  have fS : (⟨frameBase s, 4168⟩ : Region).Disjoint ⟨s.gpr .a2, 4168⟩ :=
    h.stackSched.sub_left (by rw [hF]; exact Region.sub_prefix (by decide))
  have keyIn : ∀ c < (s.gpr .a1).toNat,
      (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Contains (s.gpr .a0 + BitVec.ofNat 64 c) 1 :=
    fun c hc => Offset.contains_base _ (by omega) (by omega)
  have keyFrame : ∀ {m m' : Mem} {r : Region}, (⟨s.gpr .a0, (s.gpr .a1).toNat⟩ : Region).Disjoint r →
      Frame [r] m m' → bytesAt m' (s.gpr .a0) (s.gpr .a1).toNat = bytesAt m (s.gpr .a0) (s.gpr .a1).toNat :=
    fun hd hf => bytesAt_frame hf fun c hc r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd _ (keyIn c hc) hcon
  have W : Writable (inner s).wr (frameBase s) := frame_writable s
  refine inFrame_wp h.sp ?_
  unfold expandMain initSchedule
  -- The initial schedule.
  apply WP.seq
  rw [show ∀ l : List Instr, Instr.addSp sch 0 :: Instr.addi rowPtr sch 0 :: l =
      ([.addSp sch 0, .addi rowPtr sch 0] : List Instr) ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7, .t0] (Q := fun t => t.gpr .a7 = frameBase s ∧ t.gpr .t0 = frameBase s ∧
      t.mem = s.mem) (by brun [inner_sp, inner_mem]; all_goals rfl) (by decide) rfl)
    fun a ⟨⟨a7, a0, am⟩, ak⟩ => ?_
  refine WP.mono (initSteps_run (S := frameBase s) a0 (by omega) (fun i hi => by
      rw [ak.2.2]; exact W _ _ (by omega) (by omega)) 1042 (Nat.le_refl _))
    fun t₁ ⟨held, _, F₁, k₁⟩ => ?_
  rw [am] at F₁
  have hT : ∀ o < 4168, t₁.mem (frameBase s + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o :=
    fun o ho => table_byte held ho
  have B₁ : bytesAt t₁.mem (s.gpr .a0) (s.gpr .a1).toNat = bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat :=
    keyFrame fK.symm F₁
  have g₁ : ∀ r, r ∉ [Reg.t4, .t0] → r ∉ [Reg.a7, .t0] → t₁.gpr r = s.gpr r := fun r h1 h2 =>
    (k₁.gpr h1).trans ((ak.gpr h2).trans (by rw [inner_gpr]))
  have rd₁ : t₁.rd = s.rd := k₁.2.1.trans ak.2.1
  have wr₁ : t₁.wr = (inner s).wr := k₁.2.2.trans ak.2.2
  -- The keyed P-array.
  have E : KeyPEnv (frameBase s) (s.gpr .a0) (s.gpr .a1).toNat t₁ := by
    refine ⟨by omega, (s.gpr .a1).isLt, fun c hc => ?_, g₁ _ (by decide) (by decide),
      by rw [g₁ _ (by decide) (by decide)]; simp, (k₁.gpr (by decide)).trans a7, by rw [wr₁]; exact W,
      fun c hc hcon => fK _ hcon (keyIn c hc), by omega⟩
    rw [rd₁, h.rd]; exact ⟨_, List.mem_append_left _ List.mem_cons_self, keyIn c hc⟩
  apply WP.seq
  refine WP.mono (keyP_run E) fun t₂ I₂ => ?_
  have hS₂ : ∀ o < 4096, t₂.mem (frameBase s + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := fun o ho => by
    rw [← hT o (by omega)]
    refine I₂.frame _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (frameBase s) (d := o) (n := 1) (e := 4096) (k := 4 * 18) (.inl (by omega))
      (by omega) (by omega) _ (Region.contains_self _ _) hc
  have hK₂ : scheduleAt t₂.mem (frameBase s) = keyed (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    refine keyed_of_mem hS₂ fun i hi => ?_
    rw [I₂.done i hi, table_P hT hi, B₁]
  have g₂ : ∀ r, r ∉ keyPRegs → t₂.gpr r = t₁.gpr r := fun r hr => I₂.keep.gpr hr
  -- The setup of the encryptions.
  apply WP.seq
  refine WP.mono (WP.keep [.a3, .a4] (Q := fun t => t.gpr .a3 = 0#64 ∧ t.gpr .a4 = 0#64 ∧ t.mem = t₂.mem)
    (by brun; all_goals rfl) (by decide) rfl) fun t₃ ⟨⟨b₃, c₃, m₃⟩, k₃⟩ => ?_
  have wr₃ : t₃.wr = (inner s).wr := by rw [k₃.2.2, I₂.keep.2.2, wr₁]
  have EE : EncEnv (frameBase s) t₃ :=
    ⟨by rw [k₃.gpr (by decide), g₂ _ (by decide), (k₁.gpr (by decide))]; exact a7, by omega,
      by rw [wr₃]; exact W⟩
  have I₃ : EncInv (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (frameBase s) t₃ 0 t₃ :=
    ⟨by rw [m₃, hK₂, ksIter_zero], by rw [b₃, c₃, ksIter_zero]; rfl, Keep.refl _ _, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (encryptP_run EE I₃) fun t₄ I₄ => ?_
  apply WP.seq
  refine WP.mono (encryptS_run EE I₄) fun t₅ I₅ => ?_
  have g₅ : ∀ r, r ∉ encRegs → r ∉ [Reg.a3, .a4] → r ∉ keyPRegs → r ∉ [Reg.t4, .t0] → r ∉ [Reg.a7, .t0] →
      t₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 =>
    (I₅.keep.gpr h1).trans ((k₃.gpr h2).trans ((g₂ r h3).trans (g₁ r h4 h5)))
  have a7₅ : t₅.gpr .a7 = frameBase s := by
    rw [I₅.keep.gpr (by decide), k₃.gpr (by decide), g₂ _ (by decide), k₁.gpr (by decide)]; exact a7
  have wr₅ : t₅.wr = (inner s).wr := by rw [I₅.keep.2.2, wr₃]
  have rd₅ : t₅.rd = s.rd := by rw [I₅.keep.2.1, k₃.2.1, I₂.keep.2.1, rd₁]
  have hK₅ : scheduleAt t₅.mem (frameBase s) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [I₅.sched, expandKey_eq]
  -- The schedule copied out.
  apply WP.seq
  refine WP.mono (WP.keep [.t0, .t4] (Q := fun t => t.gpr .t0 = frameBase s ∧ t.gpr .t4 = BitVec.ofNat 64 4168 ∧
      t.mem = t₅.mem) (by unfold li4168; brun [a7₅, shl_4168]; all_goals rfl) (by decide) rfl)
    fun c ⟨⟨c0, c4, cm⟩, ck⟩ => ?_
  have a2c : c.gpr .a2 = s.gpr .a2 := by
    rw [ck.gpr (by decide)]; exact g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have wrc : c.wr = (inner s).wr := ck.2.2.trans wr₅
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t0) (dst := .a2) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c (N := 4168) (by decide) (by decide) c4
    (fun i hi => by
      rw [c0]; obtain ⟨r, hr, hc⟩ := W i 1 (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ (by rw [wrc]; exact hr), hc⟩)
    (fun i hi => ⟨⟨s.gpr .a2, 4168⟩, by rw [wrc, inner_wr, h.wr]; simp,
      by rw [a2c]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [a2c, c0]; exact sep_of_disjoint fS.symm))
    fun d ⟨dc, df, dk⟩ => ?_
  rw [a2c, c0, cm] at dc
  rw [a2c] at df
  have hKd : scheduleAt d.mem (s.gpr .a2) = expandKey (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
    rw [scheduleAt_copy dc, hK₅]
  have a7d : d.gpr .a7 = frameBase s := by rw [dk.gpr (by decide), ck.gpr (by decide)]; exact a7₅
  have wrd : d.wr = (inner s).wr := dk.2.2.trans wrc
  -- The frame zeroed.
  unfold wipe
  apply WP.seq
  refine WP.mono (WP.keep [.t1, .t0, .t4] (Q := fun t => t.gpr .t0 = frameBase s ∧
      t.gpr .t4 = BitVec.ofNat 64 522 ∧ t.gpr .t1 = 0#64 ∧ t.mem = d.mem) (by brun [a7d]) (by decide) rfl)
    fun f ⟨⟨f0, f4, f1, fm⟩, fk⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) f
    (N := 522) (by decide) (by decide) f4 (by rw [f0]; omega)
    (fun i hi => by rw [fk.2.2, wrd, f0]; exact frame_in s (by omega) (by omega)))
    fun t ⟨tz, tf, _⟩ => ⟨?_, fun j hj => by rw [← f0, ← f1]; exact tz j hj⟩
  rw [f0, fm] at tf
  show scheduleAt t.mem (s.gpr .a2) = _
  rw [scheduleAt_eq_of_frame _ tf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stackSched.sub_left (r₁' := ⟨frameBase s, 8 * 522⟩) (by
        rw [hF]; exact Region.sub_prefix (by decide))).symm, hKd]

end VG.Proof.Blowfish.RISCV64
