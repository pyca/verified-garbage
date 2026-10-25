module

public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Mac
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Cancel
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Value
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! The first words of both rows: each quotient cancels the low word it is
computed from, and the scan starts with nothing stored. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mul wp_dp op2_imm dpVal)

/-- The registers `first` writes. -/
abbrev firstClobbers : List Reg := [.r2, .r3, .r5, .r6, .r7, .r8, .r10, .r11, .lr]

theorem first_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4 ≤ n)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 acc)
    (source : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (modulus : s.gpr .r4 = base + BitVec.ofNat 32 mod)
    (count : s.gpr .lr = BitVec.ofNat 32 n)
    (inv2 : s.gpr .r10 = s.gpr .r2)
    (c7 : s.gpr .r7 = 0) (c8 : s.gpr .r8 = 0) (c5 : s.gpr .r5 = 0) (c11 : s.gpr .r11 = 0)
    (inverse : (w32 s.mem (State.addr base) mod * (s.gpr .r2).toNat + 1) % 2 ^ 32 = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.first s fun t =>
      Inv s (s.gpr .r1) (t.gpr .r2) (s.gpr .r9) (t.gpr .r10) base acc b mod n 0 0 t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have ws := ctx.workspace
  let K : List Reg := firstClobbers
  -- r6 := T₀
  rw [VG.Impl.Bignum.Arm.Fios2.first, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (acc + 0)) (by decide) (ws.ea ptr (by omega_arith)) (ws.read (by omega_arith))
    fun s1 h1 => WP.block_nil ?_
  have k1 : Rest K s s1 := h1.rest (by simp [K])
  -- r6 + 2³² r7 := T₀ + B₀ a₀
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s1 (ws.congr k1.wr) ((k1.gpr .r12 (by simp [K])).trans source) (k := 0)
    (by omega_arith) (by decide) (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro s2 ⟨x1, m2, r2⟩
  have k2 : Rest K s s2 := k1.trans (r2.mono (by simp [K]))
  -- q₀ := m' (r6)
  rw [WP.seq_iff]
  refine wp_mul fun s3 h3 => WP.block_nil ?_
  have k3 : Rest K s s3 := k2.trans (h3.rest (by simp [K]))
  -- r6 + 2³² r8 := q₀ M₀ + r6, low word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s3 (ws.congr k3.wr) ((k3.gpr .r4 (by simp [K])).trans modulus) (k := 0)
    (by omega_arith) (by decide) (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro s4 ⟨x2, m4, r4⟩
  have k4 : Rest K s s4 := k3.trans (r4.mono (by simp [K]))
  -- r6 := T₁
  rw [WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (acc + 4)) (by decide)
    ((ws.congr k4.wr).ea ((k4.gpr .r0 (by simp [K])).trans ptr) (by omega_arith))
    ((ws.congr k4.wr).read (by omega_arith))
    fun s5 h5 => WP.block_nil ?_
  have k5 : Rest K s s5 := k4.trans (h5.rest (by simp [K]))
  -- r6 + 2³² r7 := T₁ + B₁ a₀ + r7
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s5 (ws.congr k5.wr) ((k5.gpr .r12 (by simp [K])).trans source) (k := 4)
    (by omega_arith) (by decide) (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro s6 ⟨x3, m6, r6⟩
  have k6 : Rest K s s6 := k5.trans (r6.mono (by simp [K]))
  -- r6 + 2³² r8 := M₁ q₀ + r6 + r8: row i's output word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s6 (ws.congr k6.wr) ((k6.gpr .r4 (by simp [K])).trans modulus) (k := 4)
    (by omega_arith) (by decide) (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro s7 ⟨x4, m7, r7⟩
  have k7 : Rest K s s7 := k6.trans (r7.mono (by simp [K]))
  -- r6 + 2³² r5 := B₀ a₁ + r6
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s7 (ws.congr k7.wr) ((k7.gpr .r12 (by simp [K])).trans source) (k := 0)
    (by omega_arith) (by decide) (c := .r5) (x := .r9) (by decide) (by decide) (by decide)) ?_
  rintro s8 ⟨x5, m8, r8⟩
  have k8 : Rest K s s8 := k7.trans (r8.mono (by simp [K]))
  -- q₁ := m' (r6)
  rw [WP.seq_iff]
  refine wp_mul fun s9 h9 => WP.block_nil ?_
  have k9 : Rest K s s9 := k8.trans (h9.rest (by simp [K]))
  -- r6 + 2³² r11 := M₀ q₁ + r6, low word 0
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok s9 (ws.congr k9.wr) ((k9.gpr .r4 (by simp [K])).trans modulus) (k := 0)
    (by omega_arith) (by decide) (c := .r11) (x := .r10) (by decide) (by decide) (by decide)) ?_
  rintro s10 ⟨x6, m10, r10⟩
  have k10 : Rest K s s10 := k9.trans (r10.mono (by simp [K]))
  -- the count
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  have kt : Rest K s t := k10.trans (ht.rest (by simp [K]))
  have keep (r : Reg) (h : r ∉ K) : t.gpr r = s.gpr r := kt.gpr r h
  -- registers through the steps
  have q0t : t.gpr .r2 = s3.gpr .r2 := by
    rw [ht.other .r2 (by decide), r10.gpr .r2 (by simp), h9.other .r2 (by decide), r8.gpr .r2 (by simp),
      r7.gpr .r2 (by simp), r6.gpr .r2 (by simp), h5.other .r2 (by decide), r4.gpr .r2 (by simp)]
  have q1t : t.gpr .r10 = s9.gpr .r10 := by
    rw [ht.other .r10 (by decide), r10.gpr .r10 (by simp)]
  have q0 : s3.gpr .r2 = s.gpr .r2 * s2.gpr .r6 := by
    rw [h3.gpr, r2.gpr .r2 (by simp), h1.other .r2 (by decide)]
  have q1 : s9.gpr .r10 = s.gpr .r2 * s8.gpr .r6 := by
    rw [h9.gpr, r8.gpr .r10 (by simp), r7.gpr .r10 (by simp), r6.gpr .r10 (by simp),
      h5.other .r10 (by decide), r4.gpr .r10 (by simp), h3.other .r10 (by decide),
      r2.gpr .r10 (by simp), h1.other .r10 (by decide), inv2]
  -- memory: unchanged throughout
  have mem2 : s2.mem = s.mem := m2.trans h1.mem
  have mem4 : s4.mem = s.mem := m4.trans (h3.mem.trans mem2)
  have mem6 : s6.mem = s.mem := m6.trans (h5.mem.trans mem4)
  have mem7 : s7.mem = s.mem := m7.trans mem6
  have mem8 : s8.mem = s.mem := m8.trans mem7
  have mem10 : s10.mem = s.mem := m10.trans (h9.mem.trans mem8)
  have memt : t.mem = s.mem := ht.mem.trans mem10
  -- each product in terms of `s`, the quotients and the words in flight
  have s1r1 : s1.gpr .r1 = s.gpr .r1 := h1.other .r1 (by decide)
  have s5r1 : s5.gpr .r1 = s.gpr .r1 := by
    rw [h5.other .r1 (by decide), r4.gpr .r1 (by simp), h3.other .r1 (by decide), r2.gpr .r1 (by simp), s1r1]
  have s7r9 : s7.gpr .r9 = s.gpr .r9 := by
    rw [r7.gpr .r9 (by simp), r6.gpr .r9 (by simp), h5.other .r9 (by decide), r4.gpr .r9 (by simp),
      h3.other .r9 (by decide), r2.gpr .r9 (by simp), h1.other .r9 (by decide)]
  have s6r2 : s6.gpr .r2 = s3.gpr .r2 := by
    rw [r6.gpr .r2 (by simp), h5.other .r2 (by decide), r4.gpr .r2 (by simp)]
  have e1 : (s2.gpr .r6).toNat + 2 ^ 32 * (s2.gpr .r7).toNat =
      w32 s.mem (State.addr base) b * (s.gpr .r1).toNat + w32 s.mem (State.addr base) acc := by
    rw [h1.mem, s1r1, h1.gpr, h1.other .r7 (by decide), c7] at x1
    simpa only [Nat.add_zero, w32, show (0 : BitVec 32).toNat = 0 from rfl] using x1
  have x2' : (s4.gpr .r6).toNat + 2 ^ 32 * (s4.gpr .r8).toNat =
      w32 s.mem (State.addr base) mod * (s3.gpr .r2).toNat + (s2.gpr .r6).toNat + 0 := by
    rw [h3.mem, mem2, h3.other .r6 (by decide), h3.other .r8 (by decide), r2.gpr .r8 (by simp),
      h1.other .r8 (by decide), c8] at x2
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x2
  have z1 : s4.gpr .r6 = 0 := cancel_low q0 x2' rfl inverse
  have e2 : 0 + 2 ^ 32 * (s4.gpr .r8).toNat =
      w32 s.mem (State.addr base) mod * (s3.gpr .r2).toNat + (s2.gpr .r6).toNat := by
    rw [z1, Nat.add_zero] at x2'
    exact x2'
  have e3 : (s6.gpr .r6).toNat + 2 ^ 32 * (s6.gpr .r7).toNat =
      w32 s.mem (State.addr base) (b + 4) * (s.gpr .r1).toNat + w32 s.mem (State.addr base) (acc + 4) +
        (s2.gpr .r7).toNat := by
    rw [h5.mem, s5r1, h5.gpr, mem4, h5.other .r7 (by decide), r4.gpr .r7 (by simp),
      h3.other .r7 (by decide)] at x3
    simpa only [w32] using x3
  have e4 : (s7.gpr .r6).toNat + 2 ^ 32 * (s7.gpr .r8).toNat =
      w32 s.mem (State.addr base) (mod + 4) * (s3.gpr .r2).toNat + (s6.gpr .r6).toNat +
        (s4.gpr .r8).toNat := by
    rw [mem6, s6r2, r6.gpr .r8 (by simp), h5.other .r8 (by decide)] at x4
    exact x4
  have e5 : (s8.gpr .r6).toNat + 2 ^ 32 * (s8.gpr .r5).toNat =
      w32 s.mem (State.addr base) b * (s.gpr .r9).toNat + (s7.gpr .r6).toNat := by
    rw [mem7, s7r9, r7.gpr .r5 (by simp), r6.gpr .r5 (by simp), h5.other .r5 (by decide),
      r4.gpr .r5 (by simp), h3.other .r5 (by decide), r2.gpr .r5 (by simp), h1.other .r5 (by decide),
      c5] at x5
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x5
  have x6' : (s10.gpr .r6).toNat + 2 ^ 32 * (s10.gpr .r11).toNat =
      w32 s.mem (State.addr base) mod * (s9.gpr .r10).toNat + (s8.gpr .r6).toNat + 0 := by
    rw [h9.mem, mem8, h9.other .r6 (by decide), h9.other .r11 (by decide), r8.gpr .r11 (by simp),
      r7.gpr .r11 (by simp), r6.gpr .r11 (by simp), h5.other .r11 (by decide), r4.gpr .r11 (by simp),
      h3.other .r11 (by decide), r2.gpr .r11 (by simp), h1.other .r11 (by decide), c11] at x6
    simpa only [Nat.add_zero, show (0 : BitVec 32).toNat = 0 from rfl] using x6
  have z2 : s10.gpr .r6 = 0 := cancel_low q1 x6' rfl inverse
  have e6 : 0 + 2 ^ 32 * (s10.gpr .r11).toNat =
      w32 s.mem (State.addr base) mod * (s9.gpr .r10).toNat + (s8.gpr .r6).toNat := by
    rw [z2, Nat.add_zero] at x6'
    exact x6'
  have total := first_value e1 e2 e3 e4 e5 e6
  -- the carries at the end
  have t7 : t.gpr .r7 = s6.gpr .r7 := by
    rw [ht.other .r7 (by decide), r10.gpr .r7 (by simp), h9.other .r7 (by decide), r8.gpr .r7 (by simp),
      r7.gpr .r7 (by simp)]
  have t8 : t.gpr .r8 = s7.gpr .r8 := by
    rw [ht.other .r8 (by decide), r10.gpr .r8 (by simp), h9.other .r8 (by decide), r8.gpr .r8 (by simp)]
  have t5 : t.gpr .r5 = s8.gpr .r5 := by
    rw [ht.other .r5 (by decide), r10.gpr .r5 (by simp), h9.other .r5 (by decide)]
  have t11 : t.gpr .r11 = s10.gpr .r11 := ht.other .r11 (by decide)
  refine ⟨by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, keep .r1 (by simp [K]), rfl, keep .r9 (by simp [K]), rfl,
    by rw [memt, Nat.mul_zero]; exact Outside.refl _ _ _ _, ?_, kt.mono (by simp [K, roundClobbers])⟩
  · rw [keep .r0 (by simp [K]), ptr, Nat.mul_zero, Nat.add_zero]
  · rw [keep .r12 (by simp [K]), source, Nat.mul_zero, Nat.add_zero]
  · rw [keep .r4 (by simp [K]), modulus, Nat.mul_zero, Nat.add_zero]
  · rw [ht.gpr, dpVal, r10.gpr .lr (by simp), h9.other .lr (by decide), r8.gpr .lr (by simp),
      r7.gpr .lr (by simp), r6.gpr .lr (by simp), h5.other .lr (by decide), r4.gpr .lr (by simp),
      h3.other .lr (by decide), r2.gpr .lr (by simp), h1.other .lr (by decide), count, Nat.sub_zero]
    exact BitVec.ofNat_sub_ofNat_of_le n 2 (by decide) (by omega_arith)
  · rw [carries, t7, t8, t5, t11, q0t, q1t]
    simp only [val32, Nat.zero_add, Nat.mul_zero, Nat.add_zero, show 32 * 2 = 64 from rfl]
    rw [show b + 4 = b + 4 from rfl] -- keep the offsets as `total` states them
    simpa only [Nat.mul_comm (w32 s.mem (State.addr base) b) (s.gpr .r9).toNat,
      Nat.mul_comm (w32 s.mem (State.addr base) mod) (s9.gpr .r10).toNat] using total

end VG.Proof.Bignum.Arm.Fios2
