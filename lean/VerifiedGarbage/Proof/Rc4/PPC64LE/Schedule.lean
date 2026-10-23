module

public import VerifiedGarbage.Proof.Rc4.PPC64LE.Replace
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Rc4.Qword
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-! # RC4 on PPC64LE: key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mask255 (x : BitVec 64) : (x <<< 56) >>> 56 = (x.setWidth 8).setWidth 64 := by
  rw [low8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem byte_add (a b : Byte) :
    ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

theorem byte_add3 (j a k : Byte) :
    ((j.setWidth 64 + a.setWidth 64 + k.setWidth 64) <<< 56) >>> 56 = (j + a + k).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .r3) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .r3 = s₀.gpr .r3 ∧ s.gpr .r7 = s₀.gpr .r7 ∧ s.gpr .r4 = s₀.gpr .r4 ∧
    s.gpr .r6 = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.gpr .r12 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  obtain ⟨hm, hrd, hwr, hp3, h7, h4, h6⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .r3 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hp
  have hadd : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hp3, h7, h4, h6, hadd, ofNat_low, IdentityInv]
  exact identityMem_store _ _ _ hr

theorem sub256_ne (j : Nat) (hj : j + 1 < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 == (0 : BitVec 64)) = false :=
  beq_eq_false_iff_ne.mpr (by bv_omega)

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) (.nonzero .d .r12)) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne]
    rw [sub256_ne j (by omega)]
    rfl

/-! ## The key offset -/

/-- The key offset after `o`, as the code advances it to `o + 1`: back to 0 at
the key length `len`, without a branch. -/
def offNext (o len : BitVec 64) : BitVec 64 :=
  (o + 1#64) &&& (((o + 1#64 - len - 1#64) ^^^ (o + 1#64 - len)) >>> 63 - 1#64)

theorem offNext_eq (r : Nat) (len : BitVec 64) (hl : 0 < len.toNat) (hlen : len.toNat ≤ 256) :
    offNext (BitVec.ofNat 64 (r % len.toNat)) len = BitVec.ofNat 64 ((r + 1) % len.toNat) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len.toNat) + 1#64).toNat = r % len.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len.toNat < 2 ^ 64 by omega)]
    change (r % len.toNat + 1) % 2 ^ 64 = _
    omega
  have ha : (r + 1) % len.toNat = (r % len.toNat + 1) % len.toNat := by
    simp only [Nat.add_mod, Nat.mod_mod]
  unfold offNext
  by_cases h : r % len.toNat + 1 < len.toNat
  · have hd : ∀ x : BitVec 64, x.toNat = 2 ^ 64 - (len.toNat - (r % len.toNat + 1)) →
        x >>> 63 = 1#64 := by
      intro x hx
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    have h1 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len) >>> 63 = 1#64 :=
      hd _ (by rw [BitVec.toNat_sub, ht]; omega)
    have h2 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len - 1#64) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_sub, ht]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    rw [BitVec.ushiftRight_xor_distrib, h1, h2, show (1#64 ^^^ 1#64) - 1#64 = BitVec.allOnes 64 by
      decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len.toNat + 1 < 2 ^ 64 by omega)]
  · have he : BitVec.ofNat 64 (r % len.toNat) + 1#64 = len := by
      apply BitVec.eq_of_toNat_eq
      rw [ht]; omega
    rw [he, BitVec.sub_self, ha, show r % len.toNat + 1 = len.toNat by omega, Nat.mod_self,
      show (0#64 - 1#64 ^^^ 0#64) >>> 63 - 1#64 = 0#64 by decide, BitVec.and_zero]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1) :
    WP isa (.block (loadI ++ ([.add .r9 .r9 .r0, .add .r12 .r7 .r5, .lbz .r0 .r12 0,
      .add .r9 .r9 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr))) s
      fun t => t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .r7 + s.gpr .r5)).setWidth 64 ∧ Keep [.r0, .r9, .r12] s t ∧
        t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r6) 1 := by
    rw [hcx, byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .r7 + s.gpr .r5)).setWidth 64 ∧ t.mem = s.mem) [.r0, .r9, .r12] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rrun [hi, hk, h9]
  rw [hcx, byte_addr i, byte_add3]

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (hax : s.gpr .r10 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.add .r12 .r3 .r6, .stb .r10 .r12 0,
      .addi .r5 .r5 1, .sub .r12 .r5 .r4, .subi .r0 .r12 1, .logic .xor .r0 .r0 .r12,
      .lsr .d .r12 .r0 63, .subi .r12 .r12 1, .logic .and .r5 .r5 .r12,
      .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12]) s fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep [.r0, .r5, .r6, .r12] s t := by
  have hw' : InRegions s.wr (s.gpr .r3 + s.gpr .r6) 1 := by rw [hcx, byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256) [.r0, .r5, .r6, .r12] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hax, low_byte, offNext]
  rw [hcx, byte_addr i]
  exact ⟨rfl, rfl, rfl⟩

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1) :
    let a := s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .r7 + s.gpr .r5)
    let b := s.mem (s.gpr .r3 + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .r3 + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r9 = jj.setWidth 64 ∧ t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep ([.r0, .r9, .r12] ++ [.r0, .r10, .r11, .r12] ++ [.r0, .r5, .r6, .r12]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j hcx h9 hr hk) fun t ⟨t9, tk, tm⟩ => ?_
  have tcx : t.gpr .r6 = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tp : t.gpr .r3 = s.gpr .r3 := tk.gpr (by decide)
  have t8 : t.gpr .r8 = 0 := (tk.gpr (by decide)).trans h8
  have tr5 : t.gpr .r5 = s.gpr .r5 := tk.gpr (by decide)
  have tr4 : t.gpr .r4 = s.gpr .r4 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .r3) 256 := by rw [tk.2.2, tp]; exact hp
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (replace_core t jj i t9 t8 tcx htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .r6 = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have up : u.gpr .r3 = s.gpr .r3 := (uk.gpr (by decide)).trans tp
  have ur5 : u.gpr .r5 = s.gpr .r5 := (uk.gpr (by decide)).trans tr5
  have ur4 : u.gpr .r4 = s.gpr .r4 := (uk.gpr (by decide)).trans tr4
  have u9 : u.gpr .r9 = jj.setWidth 64 := (uk.gpr (by decide)).trans t9
  rw [tm, tp] at uax um
  have hw : InRegions u.wr (u.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, up]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega) (by have := i.isLt; omega) hp
  refine WP.mono (schedule_after u i b ucx uax hw) fun v ⟨vm, v5, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u9, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, up]
  · rw [v5, ur5, ur4]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .r7) (s.gpr .r4).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .r3) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .r3)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .r9 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .r6 = BitVec.ofNat 64 r
  off : s.gpr .r5 = BitVec.ofNat 64 (r % (s₀.gpr .r4).toNat)
  p : s.gpr .r3 = s₀.gpr .r3
  len : s.gpr .r4 = s₀.gpr .r4
  key : s.gpr .r7 = s₀.gpr .r7
  zero : s.gpr .r8 = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7) (s₀.gpr .r4).toNat)
    (hs : Mem.Sep (s₀.gpr .r7) (s₀.gpr .r4).toNat (s₀.gpr .r3) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.gpr .r12 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .r6 = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .r3) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .r4).toNat by omega)
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hk
  have hkeybyte : s.mem (s.gpr .r7 + s.gpr .r5) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .r7 + BitVec.ofNat 64 (r % (s₀.gpr .r4).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .r3 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .r3) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ hi h.j h.zero hpoint hkeypoint)
    fun t ⟨tm, t5, t9, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [byte_addr, hrt, BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, (tk.gpr (by decide)).trans h.zero, tk.2.1.trans h.rd,
    tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t9, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t5, h.off, h.len]
    exact offNext_eq r _ (by omega) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7) (s₀.gpr .r4).toNat)
    (hs : Mem.Sep (s₀.gpr .r7) (s₀.gpr .r4).toNat (s₀.gpr .r3) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) (.nonzero .d .r12)) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj hlen hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne]
    rw [sub256_ne j (by omega)]
    rfl

end VG.Proof.Rc4.PPC64LE
