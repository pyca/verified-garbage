module

public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.First
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Loop
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Top
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Value
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState

/-! The two-row scan: both rows' products and quotients, divided by `2⁶⁴`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

/-- Three words stored at `d`, read back as a number below the words at `o`. -/
theorem three_words {m : Mem} {base : BitVec 32} {size o d k : Nat} (v0 v1 v2 : BitVec 32)
    (nowrap : base.toNat + size ≤ 2 ^ 32) (fit : d + 12 ≤ size) (hd : d = o + 4 * k) :
    val32 (((m.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1).writeW
        (off (State.addr base) (d + 8)) v2) (State.addr base) o (k + 3) =
      val32 m (State.addr base) o k + 2 ^ (32 * k) * (v0.toNat + 2 ^ 32 * (v1.toNat + 2 ^ 32 * v2.toNat)) := by
  have nb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  have w0 := writeW32_outside m (State.addr base) (d := d) v0 (by omega)
  have w1 := writeW32_outside (m.writeW (off (State.addr base) d) v0) (State.addr base) (d := d + 4) v1 (by omega)
  have w2 := writeW32_outside ((m.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1)
    (State.addr base) (d := d + 8) v2 (by omega)
  have all : Outside (State.addr base) d 12 m _ :=
    (w0.mono (by omega) (by omega)).trans ((w1.mono (by omega) (by omega)).trans (w2.mono (by omega) (by omega)))
  rw [val32_append, all.val32 (by omega) (by omega), ← hd]
  congr 2
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  rw [w32_write_ne nb (by omega) (by omega) (by omega), w32_write_ne nb (by omega) (by omega) (by omega),
    w32_write_self, w32_write_ne nb (by omega) (by omega) (by omega), w32_write_self, w32_write_self]

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4 ≤ n) (even : n % 2 = 0)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 acc)
    (source : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (modulus : s.gpr .r4 = base + BitVec.ofNat 32 mod)
    (count : s.gpr .lr = BitVec.ofNat 32 n)
    (inv2 : s.gpr .r10 = s.gpr .r2)
    (c7 : s.gpr .r7 = 0) (c8 : s.gpr .r8 = 0) (c5 : s.gpr .r5 = 0) (c11 : s.gpr .r11 = 0)
    (inverse : (w32 s.mem (State.addr base) mod * (s.gpr .r2).toNat + 1) % 2 ^ 32 = 0)
    (high : w32 s.mem (State.addr base) (acc + 4 * (n + 1)) = 0) :
    WP isa VG.Impl.Bignum.Arm.Fios2.code s fun t =>
      (∃ q0 q1 : BitVec 32, 2 ^ 64 * val32 t.mem (State.addr base) acc (n + 1) =
        val32 s.mem (State.addr base) acc (n + 2) +
        ((s.gpr .r1).toNat + 2 ^ 32 * (s.gpr .r9).toNat) * val32 s.mem (State.addr base) b n +
        (q0.toNat + 2 ^ 32 * q1.toNat) * val32 s.mem (State.addr base) mod n) ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (acc + 4 * (n + 1)) ∧
      Outside (State.addr base) acc (4 * (n + 1)) s.mem t.mem ∧
      Rest roundClobbers s t := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  rw [VG.Impl.Bignum.Arm.Fios2.code, WP.seq_iff]
  refine WP.mono (first_ok s ctx positive ptr source modulus count inv2 c7 c8 c5 c11 inverse) fun u iu => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx iu positive even) fun v iv => ?_
  let d := acc + 4 * (n - 2)
  have ws := ctx.workspace.congr iv.rest.wr
  have oldT0 := iv.outside.w32 (d := acc + 4 * n) (by omega) (by omega)
  have oldT1 := iv.outside.w32 (d := acc + 4 * (n + 1)) (by omega) (by omega)
  have oldB := iv.outside.w32 (d := b + 4 * (n - 1)) (by rcases ctx.accB with h | h <;> omega) (by omega)
  have oldM := iv.outside.w32 (d := mod + 4 * (n - 1)) (by rcases ctx.accM with h | h <;> omega) (by omega)
  have e8 : d + 8 = acc + 4 * n := by omega
  have e12 : d + 12 = acc + 4 * (n + 1) := by omega
  have eb : b + 4 * (n - 2) + 4 = b + 4 * (n - 1) := by omega
  have em : mod + 4 * (n - 2) + 4 = mod + 4 * (n - 1) := by omega
  have bound : w32 v.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 v.mem (State.addr base) (d + 12) +
      (v.gpr .r7).toNat + (v.gpr .r8).toNat < 2 ^ 64 := by
    rw [e8, e12, oldT0, oldT1]
    have := (v.gpr .r7).isLt; have := (v.gpr .r8).isLt
    have := (s.mem.readW (off (State.addr base) (acc + 4 * n)) 32).isLt
    rw [high]
    simp only [w32] at *
    omega
  refine WP.mono (top_ok v ws (d := d) (by omega) (by omega) (by omega) iv.outPtr iv.bPtr iv.mPtr bound) ?_
  rintro t ⟨v0, v1, v2, mem, value, pt, rest⟩
  refine ⟨⟨u.gpr .r2, u.gpr .r10, ?_⟩, ?_, ?_, iv.rest.trans (rest.mono (by simp [roundClobbers]))⟩
  · rw [e8, e12, oldT0, oldT1, eb, em, oldB, oldM, iv.scalar1, iv.quotient1] at value
    have stored := three_words (m := v.mem) (o := acc) (k := n - 2) v0 v1 v2 nowrap (by omega) rfl
    rw [← mem, show n - 2 + 3 = n + 1 by omega] at stored
    have prior := iv.value
    -- the old numbers, split at their last words
    have eT : val32 s.mem (State.addr base) acc (n + 2) = val32 s.mem (State.addr base) acc n +
        2 ^ 64 * 2 ^ (32 * (n - 2)) * (w32 s.mem (State.addr base) (acc + 4 * n) +
          2 ^ 32 * w32 s.mem (State.addr base) (acc + 4 * (n + 1))) := by
      rw [val32_append s.mem _ acc n 2]
      congr 1
      rw [show 2 ^ 64 * 2 ^ (32 * (n - 2)) = 2 ^ (32 * n) by
        rw [← Nat.pow_add]; congr 1; omega]
      simp only [val32, Nat.mul_zero, Nat.add_zero, show acc + 4 * n + 4 = acc + 4 * (n + 1) by omega]
    have eB : val32 s.mem (State.addr base) b n = val32 s.mem (State.addr base) b (n - 2 + 1) +
        2 ^ 32 * 2 ^ (32 * (n - 2)) * w32 s.mem (State.addr base) (b + 4 * (n - 1)) := by
      rw [show n = (n - 2 + 1) + 1 by omega, val32_succ, ← pow32_succ]
      congr 3 <;> omega
    have eM : val32 s.mem (State.addr base) mod n = val32 s.mem (State.addr base) mod (n - 2 + 1) +
        2 ^ 32 * 2 ^ (32 * (n - 2)) * w32 s.mem (State.addr base) (mod + 4 * (n - 1)) := by
      rw [show n = (n - 2 + 1) + 1 by omega, val32_succ, ← pow32_succ]
      congr 3 <;> omega
    rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at prior
    rw [show n - 2 + 1 = n - 1 by omega] at eB eM
    rw [show 2 ^ (32 * n) = 2 ^ 64 * 2 ^ (32 * (n - 2)) by rw [← Nat.pow_add]; congr 1; omega, eB, eM] at prior
    rw [stored, eT, eB, eM]
    unfold carries at prior value
    exact top_value prior value rfl
  · rw [pt, show d + 12 = acc + 4 * (n + 1) by omega]
  · have nb : (State.addr base).toNat + size ≤ 2 ^ 32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
    rw [mem]
    have w0 := writeW32_outside v.mem (State.addr base) (d := d) v0 (by omega)
    have w1 := writeW32_outside (v.mem.writeW (off (State.addr base) d) v0) (State.addr base) (d := d + 4) v1
      (by omega)
    have w2 := writeW32_outside ((v.mem.writeW (off (State.addr base) d) v0).writeW
      (off (State.addr base) (d + 4)) v1) (State.addr base) (d := d + 8) v2 (by omega)
    exact (iv.outside.mono (Nat.le_refl _) (by omega)).trans ((w0.mono (by omega) (by omega)).trans
      ((w1.mono (by omega) (by omega)).trans (w2.mono (by omega) (by omega))))

end VG.Proof.Bignum.Arm.Fios2
