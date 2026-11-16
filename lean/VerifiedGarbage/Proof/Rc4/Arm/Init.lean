module

import VerifiedGarbage.Proof.Rc4.Arm.Replace
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
public import VerifiedGarbage.Proof.Rc4.Arm.Lookup
public import VerifiedGarbage.Proof.Rc4.Arm.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Rc4.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Rc4.Arm.Schedule`, which only this module used -/

section

/-! # RC4 on ARMv7: key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The address of byte `r` of the table at `P`. -/
theorem idx_addr' {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {r : Nat} (hr : r < 256) :
    State.addr (P + BitVec.ofNat 32 r + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 r := by
  rw [BitVec.add_zero]
  exact addr_add (by omega_using [hP, hr])

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) r ∧ Keep [.r4, .r9] s₀ s ∧
    s.gpr .r4 = BitVec.ofNat 32 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) := by
  obtain ⟨hm, hk, h4⟩ := h
  obtain h12 : s.gpr .r12 = s₀.gpr .r12 := hk.gpr (by decide)
  obtain hw : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 r + BitVec.ofNat 32 0)) 1 := by
    rw [h12, idx_addr' hfit hr, hk.2.2.1]
    exact region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hp
  obtain hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [← BitVec.ofNat_add]
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = identityMem s₀.mem (State.addr (s₀.gpr .r12)) (r + 1) ∧
      t.gpr .r4 = BitVec.ofNat 32 (r + 1) ∧
      t.z = (BitVec.ofNat 32 r + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r4, .r9] ?_
    (by decide)) fun t ⟨⟨tm, t4, tz⟩, tk⟩ => ⟨⟨tm, (hk.trans tk).mono (by decide), t4⟩, tz⟩
  unfold identityStep
  arun [h4, hw, hadd]
  rw [h12, idx_addr' hfit hr, hm, writeW_byte8, ofNat_low32, identityMem_store _ _ _ hr]

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .r12).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr (State.addr (s₀.gpr .r12)) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hfit hp ht) fun u ⟨hu, hz⟩ => ?_
  obtain hadd : BitVec.ofNat 32 j + BitVec.ofNat 32 1 = BitVec.ofNat 32 (j + 1) := by
    rw [← BitVec.ofNat_add]
  rw [hadd] at hz
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [eval_ne, hz, hend]
    rfl
  · right
    obtain hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

/-! ## One round -/

/-- What the key schedule keeps throughout: the table at `P`, the key at `K`
(`Lk` bytes), all ones. -/
structure ScheduleEnv (s : State) (P K Lk : BitVec 32) : Prop where
  p : s.gpr .r12 = P
  k : s.gpr .r0 = K
  l : s.gpr .r1 = Lk
  ones : s.gpr .r10 = BitVec.allOnes 32
  len : 1 ≤ Lk.toNat ∧ Lk.toNat ≤ 256
  fit : P.toNat + 256 ≤ 2 ^ 32
  table : InRegions s.wr (State.addr P) 256
  key : InRegions (s.rd ++ s.wr) (State.addr K) Lk.toNat
  keyFit : K.toNat + Lk.toNat ≤ 2 ^ 32
  keySep : Mem.Sep (State.addr K) Lk.toNat (State.addr P) 256

theorem ScheduleEnv.keep {s t : State} {P K Lk : BitVec 32} (h : ScheduleEnv s P K Lk)
    {rs : List Reg} (hk : Keep rs s t) (hrs : ∀ r ∈ rs, r ≠ .r12 ∧ r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r10) :
    ScheduleEnv t P K Lk :=
  { h with
    p := (hk.gpr fun hm => (hrs _ hm).1 rfl).trans h.p
    k := (hk.gpr fun hm => (hrs _ hm).2.1 rfl).trans h.k
    l := (hk.gpr fun hm => (hrs _ hm).2.2.1 rfl).trans h.l
    ones := (hk.gpr fun hm => (hrs _ hm).2.2.2 rfl).trans h.ones
    table := by rw [hk.2.2.1]; exact h.table
    key := by rw [hk.2.1, hk.2.2.1]; exact h.key }

theorem ScheduleEnv.tableEnv {s : State} {P K Lk : BitVec 32} (h : ScheduleEnv s P K Lk)
    {idx : Byte} (h6 : s.gpr .r6 = idx.setWidth 32) : TableEnv s idx :=
  ⟨h6, h.ones, by rw [h.p]; exact h.fit, by rw [h.p]; exact h.table⟩

theorem schedule_before (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 o) (ho : o < Lk.toNat) :
    WP isa (.block (loadI ++ ([.dp .add .r5 .r5 (.reg .r11), .dp .add .r9 .r0 (.reg .r2),
      .ldrb .r9 .r9 0, .dp .add .r5 .r5 (.reg .r9), .dp .and .r5 .r5 (imm 255),
      .mov .r6 (.reg .r5)] : List Instr))) s
      fun t => t.gpr .r5 = (j + s.mem (State.addr P + BitVec.ofNat 64 i.toNat) +
          s.mem (State.addr K + BitVec.ofNat 64 o)).setWidth 32 ∧ t.gpr .r6 = t.gpr .r5 ∧
        Keep [.r5, .r6, .r9, .r11] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok s i h4 (by rw [he.p]; exact he.fit) (by rw [he.p]; exact region_in he.table))
    fun t ⟨t11, tk, tm⟩ => ?_
  rw [he.p] at t11
  obtain t5 : t.gpr .r5 = j.setWidth 32 := (tk.gpr (by decide)).trans h5
  obtain t0 : t.gpr .r0 = K := (tk.gpr (by decide)).trans he.k
  obtain t2 : t.gpr .r2 = BitVec.ofNat 32 o := (tk.gpr (by decide)).trans h2
  obtain hka : State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 o := by
    rw [BitVec.add_zero]
    exact addr_add (by have := he.keyFit; omega_using [ho, this])
  obtain hk : InRegions (t.rd ++ t.wr) (State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0)) 1 := by
    rw [hka, tk.2.1, tk.2.2.1]
    exact region_offset _ _ _ _ _ (by have := he.keyFit; omega_using [ho]) (by omega_using [ho]) he.key
  refine WP.mono (WP.keep (Q := fun u => u.gpr .r5 = (j + s.mem (State.addr P +
      BitVec.ofNat 64 i.toNat) + s.mem (State.addr K + BitVec.ofNat 64 o)).setWidth 32 ∧
      u.gpr .r6 = u.gpr .r5 ∧ u.mem = s.mem) [.r5, .r6, .r9] ?_ (by decide))
    fun u ⟨⟨u5, u6, um⟩, uk⟩ => ⟨u5, u6, (tk.trans uk).mono (by decide), um⟩
  arun [t5, t11, t0, t2, hk, tm]
  rw [hka, byte_add3_32]

/-- The key offset after `cmp`, `adc` and `and`. -/
theorem next_off (x L : BitVec 32) :
    x &&& (BitVec.allOnes 32 + BitVec.ofNat 32 0 +
      BitVec.ofNat 32 (decide (L.toNat ≤ x.toNat)).toNat) =
      if x.toNat < L.toNat then x else 0#32 := by
  rw [adc_mask']
  by_cases h : x.toNat < L.toNat
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega_using [h]), ite_eq_left h]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; omega_using [h]), ite_eq_right h]
    rfl

theorem schedule_after (s : State) (i b : Byte) {P K Lk : BitVec 32}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h7 : s.gpr .r7 = b.setWidth 32) :
    WP isa (.block [.dp .add .r2 .r2 (imm 1), .cmp .r2 (.reg .r1), .adc .r9 .r10 (imm 0),
      .dp .and .r2 .r2 (.reg .r9), .dp .add .r9 .r12 (.reg .r4), .strb .r7 .r9 0,
      .dp .add .r4 .r4 (imm 1), .cmp .r4 (imm 256)]) s fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.r2, .r4, .r9] s t := by
  obtain hw : InRegions s.wr (State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr he.fit i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) he.table
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (State.addr P + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (s.gpr .r2 + BitVec.ofNat 32 1).toNat < Lk.toNat then
        s.gpr .r2 + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32)) [.r2, .r4, .r9] ?_
    (by decide)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  arun [he.p, he.l, he.ones, h4, h7, hw]
  rw [idx_addr he.fit i, writeW_byte8, low_byte32, next_off]
  conj_rfl

/-- One key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte) {P K Lk : BitVec 32} {o : Nat}
    (he : ScheduleEnv s P K Lk) (h4 : s.gpr .r4 = i.setWidth 32) (h5 : s.gpr .r5 = j.setWidth 32)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 o) (ho : o < Lk.toNat) :
    let p := State.addr P
    let a := s.mem (p + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (State.addr K + BitVec.ofNat 64 o)
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
        (p + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r2 = (if (BitVec.ofNat 32 o + BitVec.ofNat 32 1).toNat < Lk.toNat then
        BitVec.ofNat 32 o + BitVec.ofNat 32 1 else 0#32) ∧
      t.gpr .r5 = jj.setWidth 32 ∧ t.gpr .r4 = i.setWidth 32 + BitVec.ofNat 32 1 ∧
      t.z = (i.setWidth 32 + BitVec.ofNat 32 1 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s t := by
  intro p a jj b
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j he h4 h5 h2 ho) fun t ⟨t5, t6, tk, tm⟩ => ?_
  obtain het := he.keep tk (by decide)
  refine WP.mono (replace_core t jj i (het.tableEnv (t6.trans t5)) ((tk.gpr (by decide)).trans h4))
    fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  obtain heu := het.keep uk (by decide)
  refine WP.mono (schedule_after u i b heu ((uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h4))
    u7) fun v ⟨vm, v2, v4, vz, vk⟩ => ?_
  refine ⟨by rw [vm, um], ?_, (vk.gpr (by decide)).trans ((uk.gpr (by decide)).trans t5), v4, vz,
    ((tk.trans uk).trans vk).mono (by decide)⟩
  rw [v2, (uk.gpr (by decide) : u.gpr .r2 = t.gpr .r2), (tk.gpr (by decide) : t.gpr .r2 = s.gpr .r2), h2]

/-- The key bytes, at `K` (32-bit), `Lk` of them. -/
def keyOf (m : Mem) (K Lk : BitVec 32) : List Byte := bytesAt m (State.addr K) Lk.toNat

structure ScheduleInv (s₀ : State) (P K Lk : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : TableFrame (State.addr P) s₀.mem s.mem
  table : (contextAt s.mem (State.addr P)).table = (schedulePrefix (keyOf s₀.mem K Lk) r).1
  j : s.gpr .r5 = (schedulePrefix (keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .r4 = BitVec.ofNat 32 r
  off : s.gpr .r2 = BitVec.ofNat 32 (r % Lk.toNat)
  keep : Keep [.r2, .r4, .r5, .r6, .r7, .r8, .r9, .r11] s₀ s

theorem schedule_inv_step (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : ScheduleEnv s₀ P K Lk) (h : ScheduleInv s₀ P K Lk r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ P K Lk (r + 1) t ∧
      t.z = (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  let key := keyOf s₀.mem K Lk
  let st := schedulePrefix key r
  have hlen := he₀.len
  obtain he := he₀.keep h.keep (by decide)
  obtain hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  obtain hi : s.gpr .r4 = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  obtain hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega_using [hlen])
  obtain hkeybyte : s.mem (State.addr K + BitVec.ofNat 64 (r % Lk.toNat)) =
      key.getD (r % key.length) 0 := by
    obtain hsep := he₀.keySep (State.addr K + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hmod])]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  obtain htablebyte : s.mem (State.addr P + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    obtain hg := table_get s.mem (State.addr P) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ he hi h.j h.off hmod)
    fun t ⟨tm, t2, t5, t4, tz, tk⟩ => ?_
  obtain hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  obtain hcast : (BitVec.ofNat 8 r).setWidth 32 + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (h.keep.trans tk).mono (by decide)⟩, ?_⟩
  · rw [tm]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, table_swap, h.table, hnext, hrt]
    rw [htablebyte, hkeybyte]
  · rw [t5, hrt, htablebyte, hkeybyte, hnext]
  · rw [t4, hcast]
  · rw [t2]
    exact key_next32 r _ (by omega_using [hlen]) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {P K Lk : BitVec 32} {r : Nat} (hr : r < 256)
    (he₀ : ScheduleEnv s₀ P K Lk) (h : ScheduleInv s₀ P K Lk r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (ScheduleInv s₀ P K Lk 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ P K Lk j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj he₀ ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [eval_ne, hz, hend]
    rfl
  · right
    obtain hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_using [hj, hend, h']
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm

end

end


/-! # RC4 on ARMv7: checked initialization -/

@[expose] public section

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-! ## Our caller's registers -/

theorem saved_slots : Spill.Slots 0 32 saved := by decide

theorem saved_restorable : Spill.Restorable .r3 saved := by decide

/-- The registers `saved` lists. -/
theorem saved_regs : saved.map Prod.fst = [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := rfl

/-- Saving the registers in `scratch` at `S`. -/
theorem save_ok (s : State) (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3)) 64) :
    WP isa (.block save) s fun t =>
      t.mem = Spill.saveMem s.mem (State.addr (s.gpr .r3)) s.gpr saved ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Spill.save_block_ok saved_slots (by omega_arith) fun d _ hd =>
    region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hw) (by decide)) fun t ⟨h, hk⟩ => ⟨h.2.2.2, hk⟩

/-- What saving changes: the first 32 bytes of `scratch`. -/
theorem save_frame (m : Mem) (S : Addr) (g : Reg → BitVec 32) :
    Frame [⟨S, 64⟩] m (Spill.saveMem m S g saved) :=
  Spill.saveMem_frame _ _ _ (by decide) _ (by decide)

/-- The saved registers survive writes to the table. -/
theorem saved_after {m m' : Mem} {S P : Addr} {g : Reg → BitVec 32}
    (h : Spill.Saved m S g saved) (hf : Frame [⟨P, 258⟩] m m')
    (hd : Region.Disjoint ⟨P, 258⟩ ⟨S, 64⟩) : Spill.Saved m' S g saved := by
  refine h.frame saved_slots hf fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hd.symm.sub_left (by
    rw [BitVec.add_zero]
    exact Region.sub_prefix (by decide)))

/-- Restoring them. -/
theorem restore_ok (s : State) {g : Reg → BitVec 32} (hfit : (s.gpr .r3).toNat + 64 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r3)) 64)
    (hs : Spill.Saved s.mem (State.addr (s.gpr .r3)) g saved) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ saved.map Prod.fst, t.gpr r = g r) ∧
      Keep [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  refine WP.mono (Spill.restore_block_ok saved_slots saved_restorable (by omega_arith)
    (fun d _ hd => region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hr) hs)
    fun t ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨fun r hr => Spill.restored_reg h₁ hr,
      ⟨fun r hr => h₂ r (by rw [saved_regs]; exact hr), h₄, h₅, h₆⟩, h₃⟩

/-! ## Initialization -/

theorem init_finish (s : State) {P : BitVec 32} (h12 : s.gpr .r12 = P)
    (hfit : P.toNat + 258 ≤ 2 ^ 32) (hp : InRegions s.wr (State.addr P) 258) :
    WP isa (.block [.mov .r9 (imm 0), .strb .r9 .r12 256, .strb .r9 .r12 257]) s
      fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
          (State.addr P + 257#64) 1 0#8 ∧ Keep [.r9] s t := by
  obtain a256 : State.addr (P + BitVec.ofNat 32 256) = State.addr P + 256#64 := addr_add (by omega_arith)
  obtain a257 : State.addr (P + BitVec.ofNat 32 257) = State.addr P + 257#64 := addr_add (by omega_arith)
  obtain h256 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 256)) 1 := by
    rw [a256]; exact region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 : InRegions s.wr (State.addr (P + BitVec.ofNat 32 257)) 1 := by
    rw [a257]; exact region_offset _ _ _ 257 1 (by decide) (by decide) hp
  refine WP.mono (WP.keep (Q := fun t => t.mem = (s.mem.write (State.addr P + 256#64) 1 0#8).write
      (State.addr P + 257#64) 1 0#8) [.r9] ?_ (by decide)) fun t ⟨h, hk⟩ => ⟨h, hk⟩
  arun [h12, h256, h257]
  rw [a256, a257, writeW_byte8, writeW_byte8]
  rfl

theorem init_valid (s : State) (hs : initC.pre s)
    (hlen : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) :
    WP isa initValid s fun t => t.gpr .r0 = 0#32 ∧
      contextAt t.mem (State.addr (s.gpr .r2)) =
        { table := keySchedule (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat),
          i := 0, j := 0 } ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  obtain ⟨hrd, hwr, kc, ks, cs, kfit, cfit, sfit⟩ := hs
  generalize hP : s.gpr .r2 = P at hwr kc cs cfit ⊢
  generalize hK : s.gpr .r0 = K at hrd kc ks kfit ⊢
  generalize hL : s.gpr .r1 = Lk at hrd kc ks kfit hlen ⊢
  generalize hS : s.gpr .r3 = Sc at hwr ks cs sfit
  obtain hctx : InRegions s.wr (State.addr P) 258 := ⟨_, by rw [hwr]; exact List.mem_cons_self,
    Region.contains_self _ _⟩
  obtain hscr : InRegions s.wr (State.addr Sc) 64 := ⟨_, by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
  obtain htab : InRegions s.wr (State.addr P) 256 := by
    obtain h' := region_offset _ _ _ 0 256 (by decide) (by decide) hctx
    simpa only [BitVec.add_zero] using h'
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (by rw [hS]; exact sfit) (by rw [hS]; exact hscr))
    fun a ⟨ham, hak⟩ => ?_
  rw [hS] at ham
  obtain haf : Frame [⟨State.addr Sc, 64⟩] s.mem a.mem := by rw [ham]; exact save_frame _ _ _
  obtain hb : WP isa (.block [.mov .r12 (.reg .r2), .mov .r4 (imm 0)]) a fun b =>
      b.gpr .r12 = P ∧ b.gpr .r4 = 0#32 ∧ b.mem = a.mem := by
    arun [hak.gpr (r := .r2) (by decide), hP]
  refine WP.mono (WP.keep [.r12, .r4] hb (by decide)) fun b ⟨⟨hb12, hb4, hbm⟩, hbk⟩ => ?_
  obtain kb : Keep [.r12, .r4] s b := (hak.trans hbk).mono (by decide)
  obtain hpb : InRegions b.wr (State.addr (b.gpr .r12)) 256 := by rw [kb.2.2.1, hb12]; exact htab
  obtain hfit : (b.gpr .r12).toNat + 256 ≤ 2 ^ 32 := by rw [hb12]; omega_arith
  obtain hib : IdentityInv b 0 b := ⟨by rw [identityMem_zero], Keep.refl _ _, hb4⟩
  refine WP.seq (WP.mono (identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hck, _⟩ := hc
  obtain hd : WP isa (.block (([.mov .r4 (imm 0), .mov .r2 (imm 0), .mov .r5 (imm 0)] : List Instr) ++
      ones)) c fun d => d.gpr .r4 = 0#32 ∧ d.gpr .r2 = 0#32 ∧ d.gpr .r5 = 0#32 ∧
        d.gpr .r10 = BitVec.allOnes 32 ∧ d.mem = c.mem := by
    unfold ones
    arun [ones_eq]
  refine WP.seq (WP.mono (WP.keep [.r4, .r2, .r5, .r10] hd (by decide))
    fun d ⟨⟨hd4, hd2, hd5, hd10, hdm⟩, hdk⟩ => ?_)
  obtain kd : Keep [.r4, .r2, .r5, .r10, .r9, .r12] s d :=
    ((kb.trans (hck.trans hdk)).mono (by decide))
  obtain hd12 : d.gpr .r12 = P := ((hck.trans hdk).gpr (by decide)).trans hb12
  obtain hdmem : d.mem = identityMem a.mem (State.addr P) 256 := by rw [hdm, hcm, hbm, hb12]
  -- The key is untouched by the saves and the identity permutation.
  obtain hkey : keyOf d.mem K Lk = bytesAt s.mem (State.addr K) Lk.toNat := by
    unfold keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    obtain hk' := List.mem_range.mp hk
    obtain hin : (⟨State.addr K, Lk.toNat⟩ : Region).Contains (State.addr K + BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [hdmem, identityMem_frame _ _ _ (by decide) _ fun hl =>
      kc _ hin (by simp only [Region.Contains] at hl ⊢; omega_arith)]
    exact haf _ fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ks _ hin
  obtain hen : ScheduleEnv d P K Lk :=
    { p := hd12
      k := (kd.gpr (by decide)).trans hK
      l := (kd.gpr (by decide)).trans hL
      ones := hd10
      len := hlen
      fit := by omega_arith
      table := by rw [kd.2.2.1]; exact htab
      key := by
        rw [kd.2.1, kd.2.2.1, hrd]
        exact ⟨_, List.mem_cons_self, Region.contains_self _ _⟩
      keyFit := kfit
      keySep := fun x h₁ h₂ => kc x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega_arith) }
  obtain hid : ScheduleInv d P K Lk 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, Keep.refl _ _⟩
    · rw [hdmem, identityMem_table, schedule_zero]
    · rw [hd5]; rfl
    · rw [hd4]
    · rw [hd2, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop d d (by decide) hen hid) fun e he => ?_)
  obtain ke : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s e :=
    (kd.trans he.keep).mono (by decide)
  obtain he12 : e.gpr .r12 = P := (he.keep.gpr (by decide)).trans hd12
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (init_finish e he12 cfit (by rw [ke.2.2.1]; exact hctx)) fun f ⟨hfm, hfk⟩ => ?_
  obtain kf : Keep [.r4, .r2, .r5, .r10, .r9, .r12, .r6, .r7, .r8, .r11] s f :=
    (ke.trans hfk).mono (by decide)
  obtain hctxf : Frame [⟨State.addr P, 258⟩] a.mem f.mem := by
    rw [hfm]
    refine frame_finish ?_ _ _
    obtain h1 := frame_of_table he.frame
    obtain h0 := frame_of_table (identityMem_frame a.mem (State.addr P) 256 (by decide))
    rw [hdmem] at h1
    exact h0.trans h1
  obtain hf3 : f.gpr .r3 = Sc := (kf.gpr (by decide)).trans hS
  obtain hsaved : Spill.Saved f.mem (State.addr (f.gpr .r3)) s.gpr saved := by
    rw [hf3]
    refine saved_after ?_ hctxf cs
    rw [ham]
    exact Spill.saveMem_saved _ _ _ _ saved_slots
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok f (by rw [hf3]; exact sfit)
    (by rw [kf.2.1, kf.2.2.1, hf3]; exact region_in hscr) hsaved)
    fun g ⟨hgr, hgk, hgm⟩ => ?_
  obtain h0 : WP isa (.block [.mov .r0 (imm 0)]) g fun t => t.gpr .r0 = 0#32 ∧ t.mem = g.mem := by
    arun
  refine WP.mono (WP.keep [.r0] h0 (by decide)) fun t ⟨⟨t0, tm⟩, tk⟩ => ?_
  refine ⟨t0, ?_, ?_, tk.2.2.2.trans (hgk.2.2.2.trans kf.2.2.2)⟩
  · have ht := he.table
    rw [tm, hgm, hfm, context_finish, ht, ← keySchedule_eq, hkey]
    rfl
  · intro r hr
    rw [tk.gpr (by simp only [preserved] at hr; revert hr; revert r; decide)]
    by_cases hs : r ∈ saved.map Prod.fst
    · exact hgr r hs
    · rw [hgk.gpr (by rw [← saved_regs]; exact hs)]
      have : r = .lr := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [saved_regs] at hs
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs ⊢
      subst this
      exact kf.gpr (by decide)

/-- `(len - 1) >> 8` is zero iff `len` is in `1..=256`. -/
theorem valid_len (L : BitVec 32) :
    ((L - BitVec.ofNat 32 1) >>> 8 - BitVec.ofNat 32 0 == 0#32) =
      decide (1 ≤ L.toNat ∧ L.toNat ≤ 256) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, BitVec.sub_zero,
    ← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  have := L.isLt
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega_arith

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State) (hs : initC.pre s) :
    WP isa VG.Impl.Rc4.Arm.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) with
      | .ok ctx => t.gpr .r0 = 0#32 ∧ contextAt t.mem (State.addr (s.gpr .r2)) = ctx
      | .error .invalidKeyLength => t.gpr .r0 = 1#32) ∧
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  obtain hcheck : WP isa (.block [.dp .sub .r12 .r1 (imm 1), .mov .r12 (.shifted .r12 .lsr 8),
      .cmp .r12 (imm 0)]) s fun t => t.mem = s.mem ∧
      t.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
    arun
    exact valid_len _
  unfold VG.Impl.Rc4.Arm.init
  refine WP.seq (WP.mono (WP.keep [.r12] hcheck (by decide)) fun t ⟨⟨htm, htz⟩, htk⟩ => ?_)
  obtain htp : initC.pre t := by
    obtain ⟨hrd, hwr, h⟩ := hs
    refine ⟨?_, ?_, ?_⟩ <;> simp only [htk.2.1, htk.2.2.1, htk.gpr (r := .r0) (by decide),
      htk.gpr (r := .r1) (by decide), htk.gpr (r := .r2) (by decide),
      htk.gpr (r := .r3) (by decide)] <;> with_reducible assumption
  have hreg (r : Reg) (hr : r ≠ .r12) : t.gpr r = s.gpr r := htk.gpr (by simpa using hr)
  refine WP.ite (!t.z) rfl (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256) := by
      intro hg; rw [htz, decide_eq_true hg] at hn; exact absurd hn (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    obtain h1 : WP isa (.block [.mov .r0 (imm 1)]) t fun u => u.gpr .r0 = 1#32 := by
      arun
    refine WP.mono (WP.keep [.r0] h1 (by decide)) fun u ⟨hu, huk⟩ => ⟨hu, ?_, ?_⟩
    · intro r hr
      have : r ≠ .r0 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [huk.gpr (by simpa using this.1), hreg r this.2]
    · exact huk.2.2.2.trans htk.2.2.2
  · have hg : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 256 := by
      by_contra hg; rw [htz, decide_eq_false hg] at hy; exact absurd hy (by decide)
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    refine WP.mono (init_valid t htp (by rw [hreg .r1 (by decide)]; exact hg))
      fun u ⟨hu0, huc, hup, husp⟩ => ?_
    rw [hreg .r0 (by decide), hreg .r1 (by decide), hreg .r2 (by decide), htm] at huc
    refine ⟨⟨hu0, huc⟩, fun r hr => ?_, husp.trans htk.2.2.2⟩
    rw [hup r hr]
    refine hreg r ?_
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.Rc4.Arm
