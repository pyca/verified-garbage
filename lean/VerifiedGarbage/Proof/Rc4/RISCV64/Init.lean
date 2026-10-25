module

import VerifiedGarbage.Proof.Rc4.RISCV64.Schedule
import VerifiedGarbage.Proof.Rc4.RISCV64.Apply
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Rc4.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # RC4 on RISC-V: checked initialization

`init` builds the table in its frame (`identity_loop`, `schedule_loop`),
copies it to the context with two zero PRGA indices, and zeroes the frame. -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-- Copying the table to the context with two zero PRGA indices, returning 0,
and zeroing the frame. -/
theorem init_end (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hF : InRegions s.wr (s.gpr .a7) 256) (hp : InRegions s.wr (s.gpr .a2) 258)
    (hFc : Mem.Sep (s.gpr .a7) 256 (s.gpr .a2) 258) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .a7 .a2 0 0 256 ++
      ([.li .t2 0, .store .b .t2 .a2 256, .store .b .t2 .a2 257, .li .a0 0] : List Instr) ++ wipe)) s
      fun t =>
      (∀ k < 256, t.mem (s.gpr .a2 + BitVec.ofNat 64 k) = s.mem (s.gpr .a7 + BitVec.ofNat 64 k)) ∧
      t.mem (s.gpr .a2 + 256#64) = 0#8 ∧ t.mem (s.gpr .a2 + 257#64) = 0#8 ∧ t.gpr .a0 = 0#64 := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨region, h, hc⟩ := hF
    exact ⟨region, List.mem_append_right _ h, hc⟩
  have hw : InRegions s.wr (s.gpr .a2) 256 := by
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hp
  have hsep : Mem.Sep (s.gpr .a2) 256 (s.gpr .a7) 256 := fun x hx hy => hFc x hy (by omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy256_ok s (by decide) (by decide) hr hw hsep) fun u ⟨uc, _, ug, _, uwr, _⟩ => ?_
  have u7 : u.gpr .a7 = s.gpr .a7 := ug _ (by decide)
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hb : WP isa (.block [.li .t2 0, .store .b .t2 .a2 256, .store .b .t2 .a2 257, .li .a0 0]) u
      fun v => v.mem = (u.mem.write (s.gpr .a2 + 256#64) 1 0#8).write (s.gpr .a2 + 257#64) 1 0#8 ∧
        v.gpr .a0 = 0#64 ∧ v.gpr .a7 = u.gpr .a7 ∧ v.wr = u.wr := by
    have h256' : InRegions u.wr (s.gpr .a2 + BitVec.ofNat 64 256) 1 := by rw [uwr]; exact h256
    have h257' : InRegions u.wr (s.gpr .a2 + BitVec.ofNat 64 257) 1 := by rw [uwr]; exact h257
    rrun [h256', h257', ug _ (show Reg.a2 ≠ .t0 by decide)]
    rfl
  refine WP.mono hb fun v ⟨vm, v0, v7, vwr⟩ => ?_
  rw [u7] at v7
  refine WP.mono (WP.rdwr (WP.keep [] (wipe_ok v (by rw [v7]; exact hal)
    (by rw [vwr, uwr, v7]; exact hF)) (by decide +kernel)))
    fun t ⟨⟨⟨tf, _⟩, tk⟩, _⟩ => ?_
  rw [v7] at tf
  have hne (k : Nat) (hk : k < 256) (e : Nat) (he : 256 ≤ e) (he' : e < 258) :
      s.gpr .a2 + BitVec.ofNat 64 k ≠ s.gpr .a2 + BitVec.ofNat 64 e :=
    Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have hout (k : Nat) (hk : k < 258) : ¬ (s.gpr .a2 + BitVec.ofNat 64 k - s.gpr .a7).toNat < 256 :=
    fun h => hFc _ h (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)
  refine ⟨fun k hk => ?_, ?_, ?_, (tk.gpr (by decide)).trans v0⟩
  · rw [frame_byte tf (hout k (by omega)), vm, write_byte, ite_eq_right (hne k hk 257 (by decide) (by decide)),
      write_byte, ite_eq_right (hne k hk 256 (by decide) (by decide)), uc k hk]
  · rw [frame_byte tf (hout 256 (by decide)), vm, write_byte,
      ite_eq_right (Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)), write_byte, ite_eq_left rfl]
  · rw [frame_byte tf (hout 257 (by decide)), vm, write_byte, ite_eq_left rfl]

/-- Key scheduling, with its frame at the stack pointer. -/
theorem init_main (s : State) (hal : s.sp.toNat % 8 = 0) (hF : InRegions s.wr s.sp 256)
    (hlen : 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .a2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat)
    (hs : Mem.Sep (s.gpr .a0) (s.gpr .a1).toNat s.sp 256)
    (hFc : Mem.Sep s.sp 256 (s.gpr .a2) 258) :
    WP isa initMain s fun t => t.gpr .a0 = 0#64 ∧
      contextAt t.mem (s.gpr .a2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat), i := 0, j := 0 } := by
  have hstart : WP isa (.block [.addSp .a7 0, .li .a3 0]) s
      fun a => a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .a7 = s.sp ∧
        a.gpr .a0 = s.gpr .a0 ∧ a.gpr .a1 = s.gpr .a1 ∧ a.gpr .a2 = s.gpr .a2 ∧
        a.gpr .a3 = 0#64 := by
    rrun
  unfold initMain
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, hap, ha0, ha1, ha2, ha3⟩ := ha
  have hpa : InRegions a.wr (a.gpr .a7) 256 := by rw [haw, hap]; exact hF
  have hia : IdentityInv a 0 a :=
    ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, rfl, rfl, ha3⟩
  refine WP.seq (WP.mono (identity_loop a a (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hbp, hb0, hb1, hb2, _⟩ := hb
  have hreset : WP isa (.block [.li .a3 0, .li .t3 0, .li .a4 0, .li .t6 0]) b
      fun c => c.mem = b.mem ∧ c.rd = b.rd ∧ c.wr = b.wr ∧ c.gpr .a7 = b.gpr .a7 ∧
        c.gpr .a0 = b.gpr .a0 ∧ c.gpr .a1 = b.gpr .a1 ∧ c.gpr .a2 = b.gpr .a2 ∧
        c.gpr .a3 = 0#64 ∧ c.gpr .t3 = 0#64 ∧ c.gpr .a4 = 0#64 ∧ c.gpr .t6 = 0#64 := by
    rrun
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcp, hc0, hc1, hc2, hc3, hct3, hc4, hc6⟩ := hc
  have hcp' : c.gpr .a7 = s.sp := by rw [hcp, hbp, hap]
  have hlc : 1 ≤ (c.gpr .a1).toNat ∧ (c.gpr .a1).toNat ≤ 256 := by
    rw [hc1, hb1, ha1]; exact hlen
  have hpc : InRegions c.wr (c.gpr .a7) 256 := by rw [hcw, hbw, haw, hcp']; exact hF
  have hkc : InRegions (c.rd ++ c.wr) (c.gpr .a0) (c.gpr .a1).toNat := by
    rw [hcr, hcw, hc0, hc1, hbr, hbw, hb0, hb1, har, haw, ha0, ha1]; exact hk
  have hsc : Mem.Sep (c.gpr .a0) (c.gpr .a1).toNat (c.gpr .a7) 256 := by
    rw [hc0, hc1, hcp', hb0, hb1, ha0, ha1]; exact hs
  have hic : ScheduleInv c 0 c := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, hc6, rfl, rfl⟩
    · rw [hcm, hbm, hcp, hbp, identityMem_table, schedule_zero]
    · rw [hc4]; rfl
    · rw [hc3]
    · rw [hct3, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop c c (by decide) hlc (by rw [hcp']; exact hal) hpc hkc hsc
    hic) fun d hd => ?_)
  have hd7 : d.gpr .a7 = s.sp := hd.p.trans hcp'
  have hd2 : d.gpr .a2 = s.gpr .a2 := by rw [hd.ctx, hc2, hb2, ha2]
  have hdw : d.wr = s.wr := by rw [hd.wr, hcw, hbw, haw]
  refine WP.mono (init_end d (by rw [hd7]; exact hal) (by rw [hdw, hd7]; exact hF)
    (by rw [hdw, hd2]; exact hp) (by rw [hd7, hd2]; exact hFc)) fun e ⟨etab, ei, ej, e0⟩ => ?_
  rw [hd2, hd7] at etab
  rw [hd2] at ei ej
  have hkey : keyAt c = bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat := by
    unfold keyAt
    rw [hcm, hc0, hc1, hb0, hb1, ha0, ha1, hbm, ham]
    exact bytes_table_frame _ _ _ _ _ (s.gpr .a1).isLt
      (identityMem_frame _ _ _ (by decide)) (by rw [hap]; exact hs)
  refine ⟨e0, context_of ?_ ei ej⟩
  rw [table_copy etab, ← hcp', hd.table, ← keySchedule_eq, hkey]

theorem valid_check (s : State) :
    WP isa (.block [.addi .t2 .a1 (-1), .shift .srl .d .t2 .t2 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .a0 = s.gpr .a0 ∧
      t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a2 ∧
      t.gpr .t2 = (s.gpr .a1 - 1#64) >>> 8 := by
  rrun

/-- The checked initializer, including both key-length boundaries, in its
frame of 256 bytes below the stack pointer. -/
theorem init_ok (s : State) (hal : s.sp.toNat % 16 = 0) (hsp : 256 ≤ s.sp.toNat)
    (hp : InRegions s.wr (s.gpr .a2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0) (s.gpr .a1).toNat)
    (hs : Mem.Sep (s.gpr .a0) (s.gpr .a1).toNat (s.sp - 256#64) 256)
    (hFc : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a2) 258) :
    WP isa VG.Impl.Rc4.RISCV64.init s fun t =>
      match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) with
      | .ok ctx => t.gpr .a0 = 0#64 ∧ contextAt t.mem (s.gpr .a2) = ctx
      | .error .invalidKeyLength => t.gpr .a0 = 1#64 := by
  unfold VG.Impl.Rc4.RISCV64.init
  refine WP.seq (WP.mono (valid_check s) fun t ht => ?_)
  obtain ⟨htm, htr, htw, htsp, ht0, ht1, ht2, ht12⟩ := ht
  let good := 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256
  have hcond : isa.eval (.nonzero .t2) t = some (decide (¬ good)) := by
    rw [Steps.eval_nonzero, ht12, bne]
    congr 1
    by_cases hg : good
    · rw [beq_iff_eq.mpr ((valid_length _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [beq_eq_false_iff_ne.mpr (fun h => hg ((valid_length _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hF : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    refine WP.alloc (n := frameBytes) (by decide) (by rw [htsp]; exact hsp) ?_
    have hsp' : (allocd frameBytes t).sp = s.sp - 256#64 := by
      show t.sp - BitVec.ofNat 64 256 = _
      rw [htsp]
    refine WP.mono (init_main (allocd frameBytes t) (by rw [hsp', hF]; omega)
      ⟨⟨s.sp - 256#64, 256⟩, by
        show _ ∈ (⟨t.sp - BitVec.ofNat 64 256, 256⟩ :: t.wr : List Region)
        rw [htsp]; exact List.mem_cons_self, by rw [hsp']; exact Region.contains_self _ _⟩
      (by rw [show (allocd frameBytes t).gpr = t.gpr from rfl, ht1]; exact hg)
      (by
        show InRegions (⟨_, _⟩ :: t.wr) (t.gpr .a2) 258
        obtain ⟨r, hr, hc⟩ := hp
        exact ⟨r, List.mem_cons_of_mem _ (by rw [htw]; exact hr), by rw [ht2]; exact hc⟩)
      (by
        show InRegions (t.rd ++ ⟨_, _⟩ :: t.wr) (t.gpr .a0) (t.gpr .a1).toNat
        obtain ⟨r, hr, hc⟩ := hk
        refine ⟨r, ?_, by rw [ht0, ht1]; exact hc⟩
        rw [htr, htw] at *
        rcases List.mem_append.mp hr with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))
      (by rw [hsp', show (allocd frameBytes t).gpr = t.gpr from rfl, ht0, ht1]; exact hs)
      (by rw [hsp', show (allocd frameBytes t).gpr = t.gpr from rfl, ht2]; exact hFc))
      fun u ⟨hu0, huc⟩ => ?_
    refine ⟨hu0, ?_⟩
    rw [show (allocd frameBytes t).gpr = t.gpr from rfl, ht0, ht1, ht2,
      show (allocd frameBytes t).mem = t.mem from rfl, htm] at huc
    exact huc

end VG.Proof.Rc4.RISCV64
