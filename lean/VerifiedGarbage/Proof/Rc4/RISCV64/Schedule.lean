module

import VerifiedGarbage.Proof.Rc4.RISCV64.Replace
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-! # RC4 on RISC-V: key scheduling, in the frame -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .a7) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .a7 = s₀.gpr .a7 ∧ s.gpr .a0 = s₀.gpr .a0 ∧ s.gpr .a1 = s₀.gpr .a1 ∧
    s.gpr .a2 = s₀.gpr .a2 ∧ s.gpr .a3 = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .a7) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.gpr .t2 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  obtain ⟨hm, hrd, hwr, hp7, h0, h1, h2, h3⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .a7 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hp
  have hadd : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hp7, h0, h1, h2, h3, hadd, ofNat_low, IdentityInv]
  exact identityMem_store _ _ _ hr

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .a7) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) (.nonzero .t2)) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [Steps.eval_nonzero, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    rw [Steps.eval_nonzero, hz, bne, sub256_ne j (by omega)]
    rfl

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h4 : s.gpr .a4 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1) :
    WP isa (.block (loadI ++ ([.add .a4 .a4 .t0, .add .t2 .a0 .t3, .load .b .t0 .t2 0,
      .add .a4 .a4 .t0, .shift .sll .d .a4 .a4 56, .shift .srl .d .a4 .a4 56] : List Instr))) s
      fun t => t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .a0 + s.gpr .t3)).setWidth 64 ∧ Keep [.t0, .a4, .t2] s t ∧
        t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .a7 + s.gpr .a3) 1 := by
    rw [hcx, byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .a4 = (j + s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .a0 + s.gpr .t3)).setWidth 64 ∧ t.mem = s.mem) [.t0, .a4, .t2] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rrun [hi, hk, h4]
  rw [hcx, byte_addr i, byte_add3]

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (hax : s.gpr .a5 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.add .t2 .a7 .a3, .store .b .a5 .t2 0,
      .addi .t3 .t3 1, .sub .t2 .t3 .a1, .addi .t0 .t2 (-1), .logic .xor .t0 .t0 .t2,
      .shift .srl .d .t2 .t0 63, .addi .t2 .t2 (-1), .logic .and .t3 .t3 .t2,
      .addi .a3 .a3 1, .li .t2 256, .sub .t2 .a3 .t2]) s fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep [.t0, .t3, .a3, .t2] s t := by
  have hw' : InRegions s.wr (s.gpr .a7 + s.gpr .a3) 1 := by rw [hcx, byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256) [.t0, .t3, .a3, .t2] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hax, low_byte, offNext]
  rw [hcx, byte_addr i]
  exact ⟨rfl, rfl, rfl⟩

/-- One key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .a3 = i.setWidth 64) (h4 : s.gpr .a4 = j.setWidth 64)
    (hal : (s.gpr .a7).toNat % 8 = 0) (hp : InRegions s.wr (s.gpr .a7) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1) :
    let a := s.mem (s.gpr .a7 + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .a0 + s.gpr .t3)
    let b := s.mem (s.gpr .a7 + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .a7 + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .t3 = offNext (s.gpr .t3) (s.gpr .a1) ∧
      t.gpr .a4 = jj.setWidth 64 ∧ t.gpr .a3 = i.setWidth 64 + 1#64 ∧
      t.gpr .t2 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep ([.t0, .a4, .t2] ++ [.t0, .a5, .t1, .t2, .t5] ++ [.t0, .t3, .a3, .t2]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j hcx h4 hr hk) fun t ⟨t4, tk, tm⟩ => ?_
  have tcx : t.gpr .a3 = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tp : t.gpr .a7 = s.gpr .a7 := tk.gpr (by decide)
  have tr3 : t.gpr .t3 = s.gpr .t3 := tk.gpr (by decide)
  have tr1 : t.gpr .a1 = s.gpr .a1 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .a7) 256 := by rw [tk.2.2, tp]; exact hp
  refine WP.mono (WP.keep [.t0, .a5, .t1, .t2, .t5]
    (replace_core t jj i t4 tcx (by rw [tp]; exact hal) htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .a3 = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have up : u.gpr .a7 = s.gpr .a7 := (uk.gpr (by decide)).trans tp
  have ur3 : u.gpr .t3 = s.gpr .t3 := (uk.gpr (by decide)).trans tr3
  have ur1 : u.gpr .a1 = s.gpr .a1 := (uk.gpr (by decide)).trans tr1
  have u4 : u.gpr .a4 = jj.setWidth 64 := (uk.gpr (by decide)).trans t4
  rw [tm, tp] at uax um
  have hw : InRegions u.wr (u.gpr .a7 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, up]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (schedule_after u i b ucx uax hw) fun v ⟨vm, v3, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u4, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, up]
  · rw [v3, ur3, ur1]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .a7) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .a7)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .a4 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .a3 = BitVec.ofNat 64 r
  off : s.gpr .t3 = BitVec.ofNat 64 (r % (s₀.gpr .a1).toNat)
  p : s.gpr .a7 = s₀.gpr .a7
  len : s.gpr .a1 = s₀.gpr .a1
  key : s.gpr .a0 = s₀.gpr .a0
  ctx : s.gpr .a2 = s₀.gpr .a2
  zero : s.gpr .t6 = 0#64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 256)
    (hal : (s₀.gpr .a7).toNat % 8 = 0) (hp : InRegions s₀.wr (s₀.gpr .a7) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    (hs : Mem.Sep (s₀.gpr .a0) (s₀.gpr .a1).toNat (s₀.gpr .a7) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.gpr .t2 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .a3 = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .a7) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .a1).toNat by omega)
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .a0 + s.gpr .t3) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hk
  have hkeybyte : s.mem (s.gpr .a0 + s.gpr .t3) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .a0 + BitVec.ofNat 64 (r % (s₀.gpr .a1).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .a7 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .a7) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ hi h.j (by rw [h.p]; exact hal) hpoint hkeypoint)
    fun t ⟨tm, t3, t4, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [byte_addr, hrt, BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, (tk.gpr (by decide)).trans h.ctx,
    (tk.gpr (by decide)).trans h.zero, tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t4, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t3, h.off, h.len]
    exact offNext_eq r _ (by omega) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .a1).toNat ∧ (s₀.gpr .a1).toNat ≤ 256)
    (hal : (s₀.gpr .a7).toNat % 8 = 0) (hp : InRegions s₀.wr (s₀.gpr .a7) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .a0) (s₀.gpr .a1).toNat)
    (hs : Mem.Sep (s₀.gpr .a0) (s₀.gpr .a1).toNat (s₀.gpr .a7) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) (.nonzero .t2)) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj hlen hal hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [Steps.eval_nonzero, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    rw [Steps.eval_nonzero, hz, bne, sub256_ne j (by omega)]
    rfl

end VG.Proof.Rc4.RISCV64
