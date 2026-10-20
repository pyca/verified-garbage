module
public import VerifiedGarbage.Proof.Bignum.Arm.SquareInit

import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! # The square's cross products doubled -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov op2_imm op2_reg op2_lsl dpVal)

/-- After the doubling: `T`'s `2n` words are twice the cross products, its top two words zero. -/
structure DblInv (m0 : Mem) (base : BitVec 32) (size out a mod M n : Nat) (inv : BitVec 32)
    (s : State) : Prop where
  env : SqEnv m0 base size out a mod M n inv s
  md : SqMeta s.mem base out a M n
  value : val32 s.mem (State.addr base) (M + 24) (2 * n) = 2 * sqCross m0 (State.addr base) a n (n - 1)
  top : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0

/-- Twice the cross products are below `2^(64 n)`. -/
theorem sqCross_double_lt (m : Mem) (base : Addr) (a n : Nat) (hn : 0 < n) :
    2 * sqCross m base a n (n - 1) < 2 ^ (32 * (2 * n)) := by
  have e := sq_eq m base a n
  rw [sqCross_last m base a n hn] at e
  have lt := val32_lt m base a n
  have sq : val32 m base a n * val32 m base a n < 2 ^ (32 * n) * 2 ^ (32 * n) :=
    Nat.mul_lt_mul'' lt lt
  rw [← Nat.pow_add, show 32 * n + 32 * n = 32 * (2 * n) by omega] at sq
  omega

theorem sqDoubleArgs_ok (s : State) {base : BitVec 32} {size M n : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (big : 2 * n < 2 ^ 32) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n) :
    WP isa (.block sqDoubleArgs) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (2 * n) ∧ t.gpr .r0 = base + BitVec.ofNat 32 (M + 24) ∧
      t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r11, .lr] s t := by
  have nowrap := ws.nowrap
  unfold sqDoubleArgs
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega))
    (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.gpr, hn, ofNat_shl (by omega),
      Nat.mul_comm, Nat.pow_one]
  · rw [u4.other .r0 (by decide), u3.gpr, dpVal, u2.other .r0 (by decide), u1.other .r0 (by decide), p0]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
    rw [Offset.add_add]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqDouble_ok (s : State) (h : CrossInv m0 base size out a mod M n inv (n - 1) s) :
    WP isa sqDouble s fun t => DblInv m0 base size out a mod M n inv t ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header
  -- The words above the `2n` are zero.
  have topS : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0 := by
    have z := h.top
    rw [show n - 1 + n = 2 * n - 1 by omega, show n + 2 - (n - 1) = 1 + 2 by omega] at z
    have z' := val32_zero_tail z
    rwa [show M + 24 + 4 * (2 * n - 1) + 4 * 1 = M + 24 + 8 * n by omega] at z'
  have lowS : val32 s.mem (State.addr base) (M + 24) (2 * n) = sqCross m0 (State.addr base) a n (n - 1) := by
    have v := h.value
    rw [val32_append s.mem (State.addr base) (M + 24) (2 * n) 2, show M + 24 + 4 * (2 * n) = M + 24 + 8 * n by omega,
      topS, Nat.mul_zero, Nat.add_zero] at v
    exact v
  rw [sqDouble, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqDoubleArgs_ok s1 (M := M) (n := n) e1.workspace (by omega) (by omega) p1
    (by rw [m1]; exact h.md.count)) ?_
  rintro s2 ⟨plr, p0, p11, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  have ctx : ShiftLeftCtx s2 base size (M + 24) (2 * n) := ⟨nowrap, by omega, e2.workspace.writable⟩
  refine WP.mono (shiftLeft_ok s2 ctx (by omega) p0 plr (by rw [p11]; decide)) ?_
  intro t sh
  have et := e2.next (Outs.of_outside (sh.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega)
    (by omega)) (by simp)) sh.rest
  have ms : s2.mem = s.mem := m2.trans m1
  refine ⟨⟨et, ?_, ?_, ?_⟩, ?_⟩
  · refine h.md.congr fun d hd => ?_
    rw [outside_read32 sh.outside (by omega) (by omega), ms]
  · rw [sh.result.1, ms, lowS, p11]
    exact Nat.mod_eq_of_lt (sqCross_double_lt m0 (State.addr base) a n (by omega))
  · rw [sh.outside.val32 (by omega) (by omega), ms]; exact topS
  · exact (r1.mono (by simp [roundClobbers])).trans ((r2.mono (by simp [roundClobbers])).trans
      (sh.rest.mono (by simp [roundClobbers])))

end

end VG.Proof.Bignum.Arm
