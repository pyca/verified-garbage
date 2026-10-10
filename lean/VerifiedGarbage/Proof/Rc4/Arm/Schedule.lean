import VerifiedGarbage.Proof.Rc4.Arm.Replace
import VerifiedGarbage.Proof.Rc4.Identity
import VerifiedGarbage.Proof.Rc4.Schedule

/-! # RC4 on ARMv7: key scheduling -/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Spec.Rc4 VG.Proof.Rc4

/-- The address of byte `r` of the table at `P`. -/
theorem idx_addr' {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {r : Nat} (hr : r < 256) :
    State.addr (P + BitVec.ofNat 32 r + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 r := by
  rw [BitVec.add_zero]
  exact addr_add (by omega_arith)

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
  have h12 : s.gpr .r12 = s₀.gpr .r12 := hk.gpr (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr .r12 + BitVec.ofNat 32 r + BitVec.ofNat 32 0)) 1 := by
    rw [h12, idx_addr' hfit hr, hk.2.2.1]
    exact region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hp
  have hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
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
  have hadd : BitVec.ofNat 32 j + BitVec.ofNat 32 1 = BitVec.ofNat 32 (j + 1) := by
    rw [← BitVec.ofNat_add]
  rw [hadd] at hz
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    rw [eval_ne, hz, hend]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_arith
    refine ⟨?_, 256 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, hu⟩
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
  have t5 : t.gpr .r5 = j.setWidth 32 := (tk.gpr (by decide)).trans h5
  have t0 : t.gpr .r0 = K := (tk.gpr (by decide)).trans he.k
  have t2 : t.gpr .r2 = BitVec.ofNat 32 o := (tk.gpr (by decide)).trans h2
  have hka : State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0) =
      State.addr K + BitVec.ofNat 64 o := by
    rw [BitVec.add_zero]
    exact addr_add (by have := he.keyFit; omega_arith)
  have hk : InRegions (t.rd ++ t.wr) (State.addr (K + BitVec.ofNat 32 o + BitVec.ofNat 32 0)) 1 := by
    rw [hka, tk.2.1, tk.2.2.1]
    exact region_offset _ _ _ _ _ (by have := he.keyFit; omega_arith) (by omega_arith) he.key
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
  · rw [ite_eq_right (by simp only [decide_eq_true_eq]; omega_arith), ite_eq_left h]
  · rw [ite_eq_left (by simp only [decide_eq_true_eq]; omega_arith), ite_eq_right h]
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
  have hw : InRegions s.wr (State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0)) 1 := by
    rw [idx_addr he.fit i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_arith) (by have := i.isLt; omega_arith) he.table
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
  have het := he.keep tk (by decide)
  refine WP.mono (replace_core t jj i (het.tableEnv (t6.trans t5)) ((tk.gpr (by decide)).trans h4))
    fun u ⟨u7, um, uk⟩ => ?_
  rw [tm, het.p] at u7 um
  have heu := het.keep uk (by decide)
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
  have he := he₀.keep h.keep (by decide)
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .r4 = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  have hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega_arith)
  have hkeybyte : s.mem (State.addr K + BitVec.ofNat 64 (r % Lk.toNat)) =
      key.getD (r % key.length) 0 := by
    have hsep := he₀.keySep (State.addr K + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (State.addr P + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    have hg := table_get s.mem (State.addr P) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ he hi h.j h.off hmod)
    fun t ⟨tm, t2, t5, t4, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 32 + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (h.keep.trans tk).mono (by decide)⟩, ?_⟩
  · rw [tm]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, table_swap, h.table, hnext, hrt]
    rw [htablebyte, hkeybyte]
  · rw [t5, hrt, htablebyte, hkeybyte, hnext]
  · rw [t4, hcast]
  · rw [t2]
    exact key_next32 r _ (by omega_arith) hlen.2
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
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega_arith
    refine ⟨?_, 256 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, hu⟩
    rw [eval_ne, hz, beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.Arm
