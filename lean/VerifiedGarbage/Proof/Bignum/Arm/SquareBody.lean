module

import VerifiedGarbage.Proof.Bignum.Arm.SquareFinish
public import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.Csub
import VerifiedGarbage.Proof.Bignum.Arm.CsubValue
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.Row

/-! ### `Bignum.Arm.SquareReduce`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.SquareDiag`, which only this module used -/

section

/-! ### `Bignum.Arm.SquareDouble`, which only this module used -/

section

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
  obtain e := sq_eq m base a n
  rw [sqCross_last m base a n hn] at e
  obtain lt := val32_lt m base a n
  obtain sq : val32 m base a n * val32 m base a n < 2 ^ (32 * n) * 2 ^ (32 * n) :=
    Nat.mul_lt_mul'' lt lt
  rw [← Nat.pow_add, show 32 * n + 32 * n = 32 * (2 * n) by omega_using []] at sq
  omega_using [e, sq]

theorem sqDoubleArgs_ok (s : State) {base : BitVec 32} {size M n : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (big : 2 * n < 2 ^ 32) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n) :
    WP isa (.block sqDoubleArgs) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (2 * n) ∧ t.gpr .r0 = base + BitVec.ofNat 32 (M + 24) ∧
      t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r11, .lr] s t := by
  have nowrap := ws.nowrap
  unfold sqDoubleArgs
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_using [fit]))
    (ws.read (by omega_using [fit])) fun s1 u1 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.gpr, hn, ofNat_shl (by omega_using [big]),
      Nat.mul_comm, Nat.pow_one]
  · rw [u4.other .r0 (by decide), u3.gpr, dpVal, u2.other .r0 (by decide), u1.other .r0 (by decide), p0]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
    rw [Offset.add_add]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqDouble_ok (s : State) (h : CrossInv m0 base size out a mod M n inv (n - 1) s) :
    WP isa sqDouble s fun t => DblInv m0 base size out a mod M n inv t ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header
  -- The words above the `2n` are zero.
  obtain topS : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0 := by
    have z := h.top
    rw [show n - 1 + n = 2 * n - 1 by omega_using [], show n + 2 - (n - 1) = 1 + 2 by omega_arith] at z
    obtain z' := val32_zero_tail z
    rwa [show M + 24 + 4 * (2 * n - 1) + 4 * 1 = M + 24 + 8 * n by omega_arith] at z'
  obtain lowS : val32 s.mem (State.addr base) (M + 24) (2 * n) = sqCross m0 (State.addr base) a n (n - 1) := by
    have v := h.value
    rw [val32_append s.mem (State.addr base) (M + 24) (2 * n) 2, show M + 24 + 4 * (2 * n) = M + 24 + 8 * n by omega_using [],
      topS, Nat.mul_zero, Nat.add_zero] at v
    exact v
  rw [sqDouble, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  obtain e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqDoubleArgs_ok s1 (M := M) (n := n) e1.workspace (by omega_arith) (by omega_arith) p1
    (by rw [m1]; exact h.md.count)) ?_
  rintro s2 ⟨plr, p0, p11, m2, r2⟩
  obtain e2 := e1.of_mem m2 r2
  obtain ctx : ShiftLeftCtx s2 base size (M + 24) (2 * n) := ⟨nowrap, by omega_arith, e2.workspace.writable⟩
  refine WP.mono (shiftLeft_ok s2 ctx (by omega_arith) p0 plr (by rw [p11]; decide)) ?_
  intro t sh
  obtain et := e2.next (Outs.of_outside (sh.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_using [])
    (by omega_using [])) (by simp)) sh.rest
  obtain ms : s2.mem = s.mem := m2.trans m1
  refine ⟨⟨et, ?_, ?_, ?_⟩, ?_⟩
  · refine h.md.congr fun d hd => ?_
    rw [outside_read32 sh.outside (by omega_using [hd]) (by omega_arith), ms]
  · rw [sh.result.1, ms, lowS, p11]
    exact Nat.mod_eq_of_lt (sqCross_double_lt m0 (State.addr base) a n (by omega_arith))
  · rw [sh.outside.val32 (by omega_using []) (by omega_arith), ms]; exact topS
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      (sh.rest.mono (by decide)))

end

end VG.Proof.Bignum.Arm

end

end


/-! # The squares of the operand's words added to the doubled cross products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg dpVal ofNat_beq_zero)

theorem sqDiag_congr {m m' : Mem} {base : Addr} {a : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (a + 4 * j) = w32 m base (a + 4 * j)) →
      diagSum m' base a k = diagSum m base a k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [diagSum]
    rw [sqDiag_congr fun j hj => h j (by omega_arith), h k (by omega_arith)]

/-- `T[2i], T[2i+1] += a_i² + r11`, the carry out in `r11`. -/
theorem diagStep_ok (s : State) {base : BitVec 32} {size A T : Nat} (ws : Workspace s base size)
    (fitA : A + 4 ≤ size) (fitT : T + 8 ≤ size)
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 A) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 T) :
    WP isa diagStep s fun t =>
      w32 t.mem (State.addr base) T + 2 ^ 32 * w32 t.mem (State.addr base) (T + 4) +
          2 ^ 64 * (t.gpr .r11).toNat =
        w32 s.mem (State.addr base) A * w32 s.mem (State.addr base) A + w32 s.mem (State.addr base) T +
          2 ^ 32 * w32 s.mem (State.addr base) (T + 4) + (s.gpr .r11).toNat ∧
      Outside (State.addr base) T 8 s.mem t.mem ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r12 = s.gpr .r12 ∧
      t.gpr .lr = s.gpr .lr ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  rw [diagStep, WP.seq_iff]
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p12 (imm := 0) (by omega_arith))
    (ws.read fitA) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_ldr (a := off (State.addr base) T) (by decide) (by
      rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]
      simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun s3 u3 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (mac_ok s3) ?_
  rintro s4 ⟨mac4, f4⟩
  obtain q0 : s4.gpr .r0 = s.gpr .r0 := by
    rw [f4.regs .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide),
      u1.other .r0 (by decide)]
  obtain mem4 : s4.mem = s.mem := by rw [f4.mem, u3.mem, u2.mem, u1.mem]
  obtain wr4 : s4.wr = s.wr := by rw [f4.wr, u3.wr, u2.wr, u1.wr]
  obtain rd4 : s4.rd = s.rd := by rw [f4.rd, u3.rd, u2.rd, u1.rd]
  obtain ea0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) T := by
    rw [q0]; simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith)
  have ea4 {u : State} (hu : u.gpr .r0 = s.gpr .r0) :
      State.addr (u.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr base) (T + 4) := by
    rw [hu]; exact sq_ea nowrap p0 (by omega_arith)
  refine wp_str (by decide) ea0 (by rw [wr4]; exact ws.write (by omega_arith)) fun s5 u5 => ?_
  refine wp_ldr (by decide) (ea4 (by rw [u5.gpr, q0])) (by rw [u5.rd, u5.wr, rd4, wr4]; exact ws.read (by omega_arith))
    fun s6 u6 => ?_
  refine wp_adds (op2_reg _ _) fun s7 u7 c7 => ?_
  refine wp_mov_c (op2_imm (by decide)) fun s8 u8 c8 => ?_
  refine wp_adc (op2_imm (by decide)) fun s9 u9 _ => ?_
  refine wp_str (by decide) (ea4 (by rw [u9.other .r0 (by decide), u8.other .r0 (by decide),
      u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, q0]))
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, wr4]; exact ws.write (by omega_arith)) fun t u10 => WP.block_nil ?_
  -- Values.
  obtain x : s3.gpr .r10 = s.mem.readW (off (State.addr base) T) 32 := by rw [u3.gpr, u2.mem, u1.mem]
  obtain w1 : s3.gpr .r1 = s.mem.readW (off (State.addr base) A) 32 := by
    rw [u3.other .r1 (by decide), u2.other .r1 (by decide), u1.gpr]
  obtain w2 : s3.gpr .r2 = s.mem.readW (off (State.addr base) A) 32 := by
    rw [u3.other .r2 (by decide), u2.gpr, u1.gpr]
  obtain y : s6.gpr .r10 = s.mem.readW (off (State.addr base) (T + 4)) 32 := by
    rw [u6.gpr, u5.mem, mem4, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith)]
  obtain lo : s9.gpr .r3 = s4.gpr .r3 := by
    rw [u9.other .r3 (by decide), u8.other .r3 (by decide), u7.other .r3 (by decide),
      u6.other .r3 (by decide), u5.gpr]
  obtain hi : s9.gpr .r4 = s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32 := by
    rw [u9.other .r4 (by decide), u8.other .r4 (by decide), u7.gpr, u6.other .r4 (by decide), u5.gpr, y]
  obtain c1 : (s9.gpr .r11).toNat = (if 2 ^ 32 ≤ (s4.gpr .r4).toNat +
      (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat then 1 else 0) := by
    rw [u9.gpr, c8, c7, u8.gpr, u6.other .r4 (by decide), u5.gpr, y]
    by_cases hc : 2 ^ 32 ≤ (s4.gpr .r4).toNat + (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte] <;> rfl
  obtain memT : t.mem = (s.mem.writeW (off (State.addr base) T) (s4.gpr .r3)).writeW
      (off (State.addr base) (T + 4)) (s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32) := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, mem4, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [w32]
    rw [u10.gpr, c1, memT, rd_other (d := T + 4) (e := T) _ (by omega_arith) (by omega_arith) (by omega_arith), rd_self, rd_self]
    obtain ac := add_carry (s4.gpr .r4) (s.mem.readW (off (State.addr base) (T + 4)) 32)
    rw [x, w1, w2] at mac4
    change _ = (s.mem.readW (off (State.addr base) A) 32).toNat * (s.mem.readW (off (State.addr base) A) 32).toNat +
      (s.mem.readW (off (State.addr base) T) 32).toNat + 2 ^ 32 * (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat +
      (s.gpr .r11).toNat
    rw [u3.other .r11 (by decide), u2.other .r11 (by decide), u1.other .r11 (by decide)] at mac4
    generalize (s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32).toNat = h4 at *
    generalize (if 2 ^ 32 ≤ (s4.gpr .r4).toNat + (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat
      then 1 else 0) = cc at *
    omega_arith
  · rw [memT]
    exact ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [u10.gpr, u9.other .r0 (by decide), u8.other .r0 (by decide), u7.other .r0 (by decide),
      u6.other .r0 (by decide), u5.gpr, q0]
  · rw [u10.gpr, u9.other .r12 (by decide), u8.other .r12 (by decide), u7.other .r12 (by decide),
      u6.other .r12 (by decide), u5.gpr, f4.regs .r12 (by decide), u3.other .r12 (by decide),
      u2.other .r12 (by decide), u1.other .r12 (by decide)]
  · rw [u10.gpr, u9.other .lr (by decide), u8.other .lr (by decide), u7.other .lr (by decide),
      u6.other .lr (by decide), u5.gpr, f4.regs .lr (by decide), u3.other .lr (by decide),
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · have k4 : Rest roundClobbers s3 s4 := ⟨fun r hr => f4.regs r (by revert hr; cases r <;> decide),
      f4.rd, f4.wr, f4.sp⟩
    exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (k4.trans
      ((u5.rest _).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans
      ((u9.rest (by decide)).trans (u10.rest _)))))))))

theorem diagAdvance_ok (s : State) :
    WP isa (.block diagAdvance) s fun t =>
      t.gpr .r0 = s.gpr .r0 + 8 ∧ t.gpr .r12 = s.gpr .r12 + 4 ∧ t.gpr .lr = s.gpr .lr - 1 ∧
      t.z = (s.gpr .lr - 1 == 0) ∧ t.mem = s.mem ∧ Rest [.r0, .r12, .lr] s t := by
  unfold diagAdvance
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u3 hz => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.gpr]; rfl
  · rw [u3.other .r12 (by decide), u2.gpr, u1.other .r12 (by decide)]; rfl
  · rw [u3.gpr, u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [hz, u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))

structure DiagCtx (s : State) (base : BitVec 32) (size T A n : Nat) : Prop where
  workspace : Workspace s base size
  tFits : T + 8 * n ≤ size
  aFits : A + 4 * n ≤ size
  sep : T + 8 * n ≤ A ∨ A + 4 * n ≤ T

structure DiagLoopInv (s0 : State) (base : BitVec 32) (T A n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (T + 8 * i)
  aptr : s.gpr .r12 = base + BitVec.ofNat 32 (A + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) T (8 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) T (2 * i) + 2 ^ (64 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) T (2 * i) + diagSum s0.mem (State.addr base) A i + (s0.gpr .r11).toNat
  rest : Rest roundClobbers s0 s

theorem diagLoopBody_ok {s0 s : State} {base : BitVec 32} {size T A n i : Nat}
    (ctx : DiagCtx s0 base size T A n) (inv : DiagLoopInv s0 base T A n i s) (hi : i < n) :
    WP isa (.seq diagStep (.block diagAdvance)) s fun t => DiagLoopInv s0 base T A n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have nowrap := ctx.workspace.nowrap
  have := ctx.tFits; have := ctx.aFits; have := ctx.sep
  obtain ws := ctx.workspace.congr inv.rest.wr
  rw [WP.seq_iff]
  refine WP.mono (diagStep_ok s (A := A + 4 * i) (T := T + 8 * i) ws (by omega_arith) (by omega_arith) inv.aptr inv.ptr) ?_
  rintro s1 ⟨v1, o1, p0, p12, plr, r1⟩
  refine WP.mono (diagAdvance_ok s1) ?_
  rintro t ⟨q0, q12, qlr, z, mem, r2⟩
  obtain aw : w32 s.mem (State.addr base) (A + 4 * i) = w32 s0.mem (State.addr base) (A + 4 * i) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  obtain tw0 : w32 s.mem (State.addr base) (T + 8 * i) = w32 s0.mem (State.addr base) (T + 8 * i) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  obtain tw1 : w32 s.mem (State.addr base) (T + 8 * i + 4) = w32 s0.mem (State.addr base) (T + 8 * i + 4) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  obtain low : val32 s1.mem (State.addr base) T (2 * i) = val32 s.mem (State.addr base) T (2 * i) :=
    o1.val32 (by omega_arith) (by omega_arith)
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q0, p0, inv.ptr]
    change base + BitVec.ofNat 32 (T + 8 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show T + 8 * i + 8 = T + 8 * (i + 1) by omega_arith]
  · rw [q12, p12, inv.aptr]
    change base + BitVec.ofNat 32 (A + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add, show A + 4 * i + 4 = A + 4 * (i + 1) by omega_arith]
  · rw [qlr, plr, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  · rw [mem]
    exact (inv.outside.mono (Nat.le_refl _) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))
  · rw [mem, r2.gpr .r11 (by decide), show 2 * (i + 1) = 2 * i + 2 by omega_arith, val32_append s1.mem _ T (2 * i) 2,
      val32_append s0.mem _ T (2 * i) 2, show T + 4 * (2 * i) = T + 8 * i by omega_arith]
    simp only [val32, diagSum, Nat.mul_zero, Nat.add_zero]
    rw [show T + 8 * i + 4 = T + 8 * i + 4 from rfl, low, ← tw0, ← tw1, ← aw,
      show 32 * (2 * i) = 64 * i by omega_arith, show 64 * (i + 1) = 64 * i + 64 by omega_arith, Nat.pow_add]
    have e1 := inv.value
    have e2 := v1
    generalize 2 ^ (64 * i) = P at *
    grind
  · exact inv.rest.trans (r1.trans (r2.mono (by decide)))
  · rw [z, plr, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

theorem diagLoop_ok (s : State) {base : BitVec 32} {size T A n : Nat}
    (ctx : DiagCtx s base size T A n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 T) (p12 : s.gpr .r12 = base + BitVec.ofNat 32 A)
    (plr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa diagLoop s (DiagLoopInv s base T A n n) := by
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ DiagLoopInv s base T A n i t
  unfold diagLoop
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (diagLoopBody_ok ctx hi (by omega_arith)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_arith, hn, ?_⟩
    refine ⟨by omega_arith, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using p0
    · simpa only [Nat.mul_zero, Nat.add_zero] using p12
    · simpa only [Nat.sub_zero] using plr
    · simp only [val32, diagSum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

/-- After the squares of the words: `T`'s `2n` words are the square. -/
structure ProdInv (m0 : Mem) (base : BitVec 32) (size out a mod M n : Nat) (inv : BitVec 32)
    (s : State) : Prop where
  env : SqEnv m0 base size out a mod M n inv s
  md : SqMeta s.mem base out a M n
  value : val32 s.mem (State.addr base) (M + 24) (2 * n) =
    val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n
  top : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0

theorem sqDiagArgs_ok (s : State) {base : BitVec 32} {size M n a : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n)
    (ha : s.mem.readW (off (State.addr base) (M + 8)) 32 = base + BitVec.ofNat 32 a) :
    WP isa (.block sqDiagArgs) s fun t =>
      t.gpr .r12 = base + BitVec.ofNat 32 a ∧ t.gpr .lr = BitVec.ofNat 32 n ∧
      t.gpr .r0 = base + BitVec.ofNat 32 (M + 24) ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧
      Rest [.r0, .r11, .r12, .lr] s t := by
  have nowrap := ws.nowrap
  unfold sqDiagArgs
  refine wp_ldr (by decide) (sq_ea nowrap p0 (by omega_arith)) (ws.read (by omega_arith)) fun s1 u1 => ?_
  obtain ea1 := sq_ea nowrap ((u1.other .r0 (by decide)).trans p0) (imm := 0) (by omega_arith)
  rw [Nat.add_zero] at ea1
  refine wp_ldr (by decide) ea1 (by rw [u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u4 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, u4.gpr, ?_, ?_⟩
  · rw [u4.other .r12 (by decide), u3.other .r12 (by decide), u2.other .r12 (by decide), u1.gpr, ha]
  · rw [u4.other .lr (by decide), u3.other .lr (by decide), u2.gpr, u1.mem, hn]
  · rw [u4.other .r0 (by decide), u3.gpr, dpVal, u2.other .r0 (by decide), u1.other .r0 (by decide), p0]
    change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
    rw [Offset.add_add]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqDiagPhase_ok (s : State) (h : DblInv m0 base size out a mod M n inv s) :
    WP isa sqDiag s fun t => ProdInv m0 base size out a mod M n inv t ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepA; have := env.aFits
  rw [sqDiag, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  obtain e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqDiagArgs_ok s1 (M := M) (n := n) (a := a) e1.workspace (by omega_arith) p1
    (by rw [m1]; exact h.md.count) (by rw [m1]; exact h.md.aPtr)) ?_
  rintro s2 ⟨p12, plr, p0, p11, m2, r2⟩
  obtain e2 := e1.of_mem m2 r2
  obtain ctx : DiagCtx s2 base size (M + 24) a n := ⟨e2.workspace, by omega_arith, by omega_arith, by omega_arith⟩
  refine WP.mono (diagLoop_ok s2 ctx (by omega_arith) p0 p12 plr) ?_
  intro t di
  obtain ms : s2.mem = s.mem := m2.trans m1
  obtain et := e2.next (Outs.of_outside (di.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith)
    (by omega_arith)) (by simp)) di.rest
  obtain dg : diagSum s2.mem (State.addr base) a n = diagSum m0 (State.addr base) a n :=
    sqDiag_congr fun j hj => e2.aWord hj
  have v := di.value
  rw [p11, dg, ms, h.value] at v
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at v
  obtain sq := sq_eq m0 (State.addr base) a n
  rw [sqCross_last m0 (State.addr base) a n (by omega_arith)] at sq
  obtain lt := val32_lt m0 (State.addr base) a n
  obtain big : val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n < 2 ^ (64 * n) := by
    have := Nat.mul_lt_mul'' lt lt
    rwa [← Nat.pow_add, show 32 * n + 32 * n = 64 * n by omega_arith] at this
  obtain c0 : (t.gpr .r11).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (t.gpr .r11).toNat with c | c
    · exact c
    · have : 2 ^ (64 * n) * 1 ≤ 2 ^ (64 * n) * (t.gpr .r11).toNat := Nat.mul_le_mul_left _ c
      omega_arith
  refine ⟨⟨et, ?_, ?_, ?_⟩, ?_⟩
  · refine h.md.congr fun d hd => ?_
    rw [outside_read32 di.outside (by omega_arith) (by omega_arith), ms]
  · rw [c0, Nat.mul_zero, Nat.add_zero] at v
    rw [show 2 * n = 2 * n from rfl, v]
    omega_arith
  · rw [di.outside.val32 (by omega_arith) (by omega_arith), ms]; exact h.top
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans di.rest)

end

end VG.Proof.Bignum.Arm

end

end


/-! # The square's Montgomery reduction, in place

Round `k` adds `T[k] m' mod 2³²` times the modulus at word `k` of `T`, which
clears that word, and the row's carry with the carry `c` of the round before
into `T[k+n]`, whose own carry is the next `c` (at `M + 12`). -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_mul op2_imm op2_reg dpVal)

/-- After `k` reductions: `T` with the carry `c` at word `k + n` is the square
plus a multiple `Q < 2^(32 k)` of the modulus, its low `k` words zero. -/
structure RedInv (m0 : Mem) (base : BitVec 32) (size out a mod M n : Nat) (inv : BitVec 32)
    (k : Nat) (s : State) : Prop where
  env : SqEnv m0 base size out a mod M n inv s
  md : SqMeta s.mem base out a M n
  index : k ≤ n
  cnt : s.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - k)
  tptr : s.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 (M + 24 + 4 * k)
  value : ∃ Q < 2 ^ (32 * k), val32 s.mem (State.addr base) (M + 24) (2 * n) +
      2 ^ (32 * (k + n)) * (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat =
    val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n + Q * val32 m0 (State.addr base) mod n
  low : val32 s.mem (State.addr base) (M + 24) k = 0
  top : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0

theorem redInit_ok (s : State) {base : BitVec 32} {size M n : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n) :
    WP isa (.block redInit) s fun t =>
      t.mem = ((s.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 n)).writeW
        (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (M + 24))).writeW
        (off (State.addr base) (M + 12)) (0 : BitVec 32) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  unfold redInit
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith))
    (ws.read (by omega_arith)) fun s1 u1 => ?_
  obtain p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_str (by decide) (sq_ea nowrap p1 (by omega_arith)) (by rw [u1.wr]; exact ws.write (by omega_arith))
    fun s2 u2 => ?_
  obtain p2 : s2.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u2.gpr]; exact p1
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_str (by decide) (sq_ea nowrap p3 (by omega_arith)) (by rw [u3.wr, u2.wr, u1.wr]; exact ws.write (by omega_arith))
    fun s4 u4 => ?_
  obtain p4 : s4.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u4.gpr]; exact p3
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain p5 := (u5.other .r0 (by decide)).trans p4
  refine wp_str (by decide) (sq_ea nowrap p5 (by omega_arith))
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega_arith)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · have v3 : s3.gpr .r1 = base + BitVec.ofNat 32 (M + 24) := by
      rw [u3.gpr, dpVal, p2]
      change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
      rw [Offset.add_add]
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr, v3, u1.gpr, hn]
  · exact (u1.rest (by decide)).trans ((u2.rest _).trans ((u3.rest (by decide)).trans ((u4.rest _).trans
      ((u5.rest (by decide)).trans (u6.rest _)))))

theorem redHeader_ok (s : State) {base : BitVec 32} {size mod M : Nat} {inv : BitVec 32}
    (ws : Workspace s base size) (fit : 84 ≤ size) (p0 : s.gpr .r0 = base)
    (hm : s.mem.readW (off (State.addr base) 64) 32 = base + BitVec.ofNat 32 mod)
    (hi : s.mem.readW (off (State.addr base) 56) 32 = inv)
    (hM : s.mem.readW (off (State.addr base) 80) 32 = base + BitVec.ofNat 32 M) :
    WP isa (.block redHeader) s fun t =>
      t.gpr .r12 = base + BitVec.ofNat 32 mod ∧ t.gpr .r1 = inv ∧ t.gpr .r0 = base + BitVec.ofNat 32 M ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r12] s t := by
  have nowrap := ws.nowrap
  unfold redHeader
  refine wp_ldr (by decide) (sq_ea0 nowrap p0 (by omega_arith)) (ws.read (by omega_arith)) fun s1 u1 => ?_
  refine wp_ldr (by decide) (sq_ea0 nowrap ((u1.other .r0 (by decide)).trans p0) (by omega_arith))
    (by rw [u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun s2 u2 => ?_
  refine wp_ldr (by decide) (sq_ea0 nowrap ((u2.other .r0 (by decide)).trans ((u1.other .r0 (by decide)).trans p0))
    (by omega_arith)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.other .r12 (by decide), u2.other .r12 (by decide), u1.gpr, hm]
  · rw [u3.other .r1 (by decide), u2.gpr, u1.mem, hi]
  · rw [u3.gpr, u2.mem, u1.mem, hM]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))

theorem redArgs_ok (s : State) {base : BitVec 32} {size M n P : Nat} (ws : Workspace s base size)
    (fit : M + 24 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 M)
    (hn : s.mem.readW (off (State.addr base) M) 32 = BitVec.ofNat 32 n)
    (ht : s.mem.readW (off (State.addr base) (M + 20)) 32 = base + BitVec.ofNat 32 P) :
    WP isa (.block redArgs) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r0 = base + BitVec.ofNat 32 P ∧
      t.mem = s.mem.writeW (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (P + 4)) ∧
      Rest [.r0, .r2, .r3, .lr] s t := by
  have nowrap := ws.nowrap
  unfold redArgs
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith))
    (ws.read (by omega_arith)) fun s1 u1 => ?_
  obtain p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_ldr (by decide) (sq_ea nowrap p1 (by omega_arith)) (by rw [u1.rd, u1.wr]; exact ws.read (by omega_arith))
    fun s2 u2 => ?_
  obtain p2 := (u2.other .r0 (by decide)).trans p1
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_str (by decide) (sq_ea nowrap p3 (by omega_arith)) (by rw [u3.wr, u2.wr, u1.wr]; exact ws.write (by omega_arith))
    fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun t u5 => WP.block_nil ?_
  obtain g2 : s2.gpr .r2 = base + BitVec.ofNat 32 P := by rw [u2.gpr, u1.mem, ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u5.other .lr (by decide), u4.gpr, u3.other .lr (by decide), u2.other .lr (by decide), u1.gpr, hn]
  · rw [u5.gpr, u4.gpr, u3.other .r2 (by decide), g2]
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, dpVal, g2]
    change _ = s.mem.writeW _ (base + BitVec.ofNat 32 (P + 4))
    rw [← Offset.add_add]; rfl
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest _).trans
      (u5.rest (by decide)))))

theorem redScalar_ok (s : State) {base : BitVec 32} {size D : Nat} (ws : Workspace s base size)
    (fit : D + 4 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 D) :
    WP isa (.block redScalar) s fun t =>
      t.gpr .r1 = s.gpr .r1 * s.mem.readW (off (State.addr base) D) 32 ∧ t.gpr .r11 = 0 ∧
      t.gpr .r0 = s.gpr .r0 ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r11] s t := by
  unfold redScalar
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p0 (imm := 0) (by omega_arith))
    (ws.read fit) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, u3.gpr, ?_, ?_, ?_⟩
  · rw [u3.other .r1 (by decide), u2.gpr, u1.other .r1 (by decide), u1.gpr]
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))

/-- `T[k+n] += r11 + c`, the carry the next `c`. -/
theorem redCarry_ok (s : State) {base : BitVec 32} {size D M : Nat} (ws : Workspace s base size)
    (fitD : D + 4 ≤ size) (fitM : M + 16 ≤ size)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 D) (p2 : s.gpr .r2 = base + BitVec.ofNat 32 M) :
    WP isa (.block redCarry) s fun t => ∃ lo hi : BitVec 32,
      lo.toNat + 2 ^ 32 * hi.toNat = (s.mem.readW (off (State.addr base) D) 32).toNat + (s.gpr .r11).toNat +
        (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat ∧
      t.mem = (s.mem.writeW (off (State.addr base) D) lo).writeW (off (State.addr base) (M + 12)) hi ∧
      t.gpr .r0 = base + BitVec.ofNat 32 M ∧ Rest [.r0, .r3, .r4, .r5] s t := by
  have nowrap := ws.nowrap
  unfold redCarry
  obtain ea0 := sq_ea nowrap p0 (imm := 0) (by omega_arith)
  rw [Nat.add_zero] at ea0
  refine wp_ldr (by decide) ea0 (ws.read fitD) fun s1 u1 => ?_
  refine wp_ldr (by decide) (sq_ea nowrap ((u1.other .r2 (by decide)).trans p2) (by omega_arith))
    (by rw [u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun s2 u2 => ?_
  refine wp_adds (op2_reg _ _) fun s3 u3 c3 => ?_
  refine wp_mov_c (op2_imm (by decide)) fun s4 u4 c4 => ?_
  refine wp_adc (op2_imm (by decide)) fun s5 u5 c5 => ?_
  refine wp_adds (op2_reg _ _) fun s6 u6 c6 => ?_
  refine wp_adc (op2_imm (by decide)) fun s7 u7 _ => ?_
  obtain q0 : s7.gpr .r0 = s.gpr .r0 := by
    rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.other .r0 (by decide), u4.other .r0 (by decide),
      u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  obtain q2 : s7.gpr .r2 = s.gpr .r2 := by
    rw [u7.other .r2 (by decide), u6.other .r2 (by decide), u5.other .r2 (by decide), u4.other .r2 (by decide),
      u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide)]
  obtain w7 : s7.wr = s.wr := by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  obtain m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine wp_str (a := off (State.addr base) D) (by decide) (by rw [q0]; exact ea0) (by rw [w7]; exact ws.write fitD)
    fun s8 u8 => ?_
  refine wp_str (by decide) (sq_ea nowrap (by rw [u8.gpr, q2]; exact p2) (by omega_arith))
    (by rw [u8.wr, w7]; exact ws.write (by omega_arith)) fun s9 u9 => ?_
  refine wp_mov (op2_reg _ _) fun t u10 => WP.block_nil ?_
  -- The values.
  have x : s1.gpr .r3 = s.mem.readW (off (State.addr base) D) 32 := u1.gpr
  obtain c : s2.gpr .r4 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by rw [u2.gpr, u1.mem]
  obtain r : s2.gpr .r11 = s.gpr .r11 := by rw [u2.other .r11 (by decide), u1.other .r11 (by decide)]
  obtain v3 : s3.gpr .r3 = s.mem.readW (off (State.addr base) D) 32 + s.gpr .r11 := by
    rw [u3.gpr, u2.other .r3 (by decide), x, r]
  obtain v6 : s6.gpr .r3 = s3.gpr .r3 + s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [u6.gpr, u5.other .r3 (by decide), u4.other .r3 (by decide), u5.other .r4 (by decide),
      u4.other .r4 (by decide), u3.other .r4 (by decide), c]
  obtain h5 : (s5.gpr .r5).toNat = (if s4.c then 1 else 0) := by
    rw [u5.gpr, u4.gpr]
    have := adc_zero 0 s4.c (by decide)
    simpa only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add] using this
  obtain h7 : (s7.gpr .r5).toNat = (s5.gpr .r5).toNat + (if s6.c then 1 else 0) := by
    rw [u7.gpr, u6.other .r5 (by decide)]
    exact adc_zero _ _ (by rw [h5]; split <;> decide)
  obtain e3 := add_carry (s.mem.readW (off (State.addr base) D) 32) (s.gpr .r11)
  obtain e6 := add_carry (s3.gpr .r3) (s.mem.readW (off (State.addr base) (M + 12)) 32)
  rw [← v3] at e3
  rw [← v6] at e6
  obtain cc4 : s4.c = decide (2 ^ 32 ≤ (s.mem.readW (off (State.addr base) D) 32).toNat + (s.gpr .r11).toNat) := by
    rw [c4, c3, u2.other .r3 (by decide), x, r]
  obtain cc6 : s6.c = decide (2 ^ 32 ≤ (s3.gpr .r3).toNat +
      (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat) := by
    rw [c6, u5.other .r3 (by decide), u4.other .r3 (by decide), u5.other .r4 (by decide),
      u4.other .r4 (by decide), u3.other .r4 (by decide), c]
  refine ⟨s6.gpr .r3, s7.gpr .r5, ?_, ?_, ?_, ?_⟩
  · rw [h7, h5, cc4, cc6]
    simp only [decide_eq_true_eq]
    omega_arith
  · rw [u10.mem, u9.mem, u8.mem, m7, u8.gpr, u7.other .r3 (by decide)]
  · rw [u10.gpr, u9.gpr, u8.gpr, q2, p2]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest _).trans ((u9.rest _).trans (u10.rest (by decide))))))))))

/-- A round's value step. -/
theorem red_value {VT VT' P Wn W X X' win win' lo hi x r c m N : Nat}
    (hrep : VT' + P * X = VT + P * X') (hX : X = win + Wn * x) (hX' : X' = win' + Wn * lo)
    (hrow : win' + Wn * r = win + m * N) (hcar : lo + W * hi = x + r + c) :
    VT' + P * Wn * W * hi = VT + P * Wn * c + P * (m * N) := by
  subst hX hX'
  obtain e1 : P * (win' + Wn * r) = P * (win + m * N) := by rw [hrow]
  obtain e2 : P * Wn * (lo + W * hi) = P * Wn * (x + r + c) := by rw [hcar]
  grind

theorem red_q {Q P m W : Nat} (hQ : Q < P) (hm : m < W) : Q + P * m < P * W := by
  have := Nat.mul_le_mul_left P (show m + 1 ≤ W by omega_arith)
  rw [Nat.mul_succ] at this
  omega_arith

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqReduceInit_ok (s : State) (h : ProdInv m0 base size out a mod M n inv s) :
    WP isa (.seq sqAnchor (.block redInit)) s fun t => RedInv m0 base size out a mod M n inv 0 t ∧
      Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header
  rw [WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  obtain e1 := env.of_mem m1 r1
  refine WP.mono (redInit_ok s1 (M := M) (n := n) e1.workspace (by omega_arith) p1 (by rw [m1]; exact h.md.count)) ?_
  rintro t ⟨mt, rt⟩
  obtain o1 := writeW32_outside s1.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 n) (by omega_arith)
  obtain o2 := writeW32_outside (s1.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 n))
    (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (M + 24)) (by omega_arith)
  obtain o3 := writeW32_outside ((s1.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 n)).writeW
      (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (M + 24))) (State.addr base) (d := M + 12)
    (0 : BitVec 32) (by omega_arith)
  rw [← mt] at o3
  obtain O : Outside (State.addr base) (M + 12) 12 s1.mem t.mem :=
    (o1.mono (by omega_arith) (by omega_arith)).trans ((o2.mono (by omega_arith) (by omega_arith)).trans (o3.mono (by omega_arith) (by omega_arith)))
  obtain et := e1.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) rt
  refine ⟨⟨et, h.md.congr fun d hd => ?_, by omega_arith, ?_, ?_, ⟨0, by simp, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [outside_read32 O (by omega_arith) (by omega_arith), m1]
  · rw [mt, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_self,
      Nat.sub_zero]
  · rw [mt, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_self, Nat.mul_zero, Nat.add_zero]
  · rw [O.val32 (by omega_arith) (by omega_arith), mt, rd_self, m1, h.value]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  · rfl
  · rw [O.val32 (by omega_arith) (by omega_arith), m1]; exact h.top
  · exact (r1.mono (by decide)).trans (rt.mono (by decide))

theorem redRound_ok (s : State) {k : Nat} (h : RedInv m0 base size out a mod M n inv k s) (hk : k < n) :
    WP isa redRound s fun t => RedInv m0 base size out a mod M n inv (k + 1) t ∧
      t.z = decide (k + 1 = n) ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepM; have := env.mFits
  obtain ⟨o, ho⟩ : ∃ o, o = M + 24 + 4 * k := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = o + 4 * n := ⟨_, rfl⟩
  rw [redRound, WP.seq_iff]
  refine WP.mono (sqBase_ok s env .r0) ?_
  rintro s1 ⟨p1, m1, r1⟩
  obtain e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (redHeader_ok s1 e1.workspace (by omega_arith) p1 e1.modNow e1.invNow e1.metaNow) ?_
  rintro s2 ⟨q12, q1, q0, m2, r2⟩
  obtain e2 := e1.of_mem m2 r2
  rw [WP.seq_iff]
  refine WP.mono (redArgs_ok s2 (P := o) e2.workspace (by omega_arith) q0 (by rw [m2, m1]; exact h.md.count)
    (by rw [m2, m1, ho]; exact h.tptr)) ?_
  rintro s3 ⟨g3lr, g30, m3, r3⟩
  obtain o3 := writeW32_outside s2.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 4)) (by omega_arith)
  rw [← m3] at o3
  obtain e3 := e2.next (Outs.of_outside (o3.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r3
  rw [WP.seq_iff]
  refine WP.mono (redScalar_ok s3 e3.workspace (D := o) (by omega_arith) g30) ?_
  rintro s4 ⟨g41, g411, g40, m4, r4⟩
  obtain e4 := e3.of_mem m4 r4
  obtain ctx : RowCtx s4 base size o mod n := ⟨nowrap, by omega_arith, by omega_arith, by omega_arith, e4.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (row_ok s4 ctx (by omega_arith) (g40.trans g30)
    (by rw [r4.gpr .r12 (by decide), r3.gpr .r12 (by decide)]; exact q12)
    (by rw [r4.gpr .lr (by decide)]; exact g3lr)) ?_
  intro s5 ri
  obtain e5 := e4.next (Outs.of_outside (ri.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith)
    (by omega_arith)) (by simp)) ri.rest
  rw [WP.seq_iff]
  refine WP.mono (sqBase_ok s5 e5 .r2) ?_
  rintro s6 ⟨p6, m6, r6⟩
  obtain e6 := e5.of_mem m6 r6
  rw [WP.seq_iff]
  refine wp_ldr (by decide) (sq_ea0 nowrap p6 (by omega_arith)) (e6.read (by omega_arith)) fun s7 u7 => WP.block_nil ?_
  obtain e7 := e6.of_mem u7.mem (u7.rest (ws := [.r2]) (by decide))
  obtain p72 : s7.gpr .r2 = base + BitVec.ofNat 32 M := u7.gpr.trans e6.metaNow
  obtain p70 : s7.gpr .r0 = base + BitVec.ofNat 32 D := by
    rw [u7.other .r0 (by decide), r6.gpr .r0 (by decide), ri.outPtr, hD]
  rw [WP.seq_iff]
  refine WP.mono (redCarry_ok s7 e7.workspace (D := D) (M := M) (by omega_arith) (by omega_arith) p70 p72) ?_
  rintro s8 ⟨lo, hi, car, m8, p80, r8⟩
  obtain o8a := writeW32_outside s7.mem (State.addr base) (d := D) lo (by omega_arith)
  obtain o8b := writeW32_outside (s7.mem.writeW (off (State.addr base) D) lo) (State.addr base) (d := M + 12) hi
    (by omega_arith)
  rw [← m8] at o8b
  obtain e8 := e7.next (Outs.of_outside ((o8a.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)).trans
    (o8b.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))) (by simp)) r8
  obtain cnt8 : s8.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - k) := by
    rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), u7.mem, m6,
      outside_read32 ri.outside (by omega_arith) (by omega_arith), m4, m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m2, m1]
    exact h.cnt
  refine WP.mono (sqCount_ok s8 e8.workspace (by omega_arith) p80 cnt8 (by omega_arith) (by omega_arith)) ?_
  rintro t ⟨m9, z9, r9⟩
  obtain o9 := writeW32_outside s8.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 (n - k - 1)) (by omega_arith)
  rw [← m9] at o9
  obtain et := e8.next (Outs.of_outside (o9.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r9
  -- Where memory changed.
  obtain ⟨w, hw⟩ : ∃ w, w = s7.mem.writeW (off (State.addr base) D) lo := ⟨_, rfl⟩
  rw [← hw] at o8a o8b m8
  obtain hw7 : s7.mem = s5.mem := u7.mem.trans m6
  obtain o8a' : Outside (State.addr base) D 4 s5.mem w := by rw [← hw7]; exact o8a
  obtain OW : Outside (State.addr base) o (4 * n + 4) s4.mem w :=
    (ri.outside.mono (by omega_arith) (by omega_arith)).trans (o8a'.mono (by omega_arith) (by omega_arith))
  obtain all : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s.mem t.mem := by
    obtain A1 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s2.mem s3.mem :=
      Outs.of_outside (o3.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    obtain A2 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s4.mem w := Outs.of_outside OW (by simp)
    obtain A4 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] w s8.mem :=
      Outs.of_outside (o8b.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    obtain A5 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s8.mem t.mem :=
      Outs.of_outside (o9.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    rw [m2, m1] at A1
    rw [m4] at A2
    exact A1.trans (A2.trans (A4.trans A5))
  -- The carry in, and the old values.
  obtain c4 : s4.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [m4, m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m2, m1]
  obtain c7 : s7.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega_arith) (by omega_arith), c4]
  obtain x7 : s7.mem.readW (off (State.addr base) D) 32 = s4.mem.readW (off (State.addr base) D) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega_arith) (by omega_arith)]
  obtain r7 : s7.gpr .r11 = s5.gpr .r11 := by rw [u7.other .r11 (by decide), r6.gpr .r11 (by decide)]
  obtain VT : val32 s4.mem (State.addr base) (M + 24) (2 * n) = val32 s.mem (State.addr base) (M + 24) (2 * n) := by
    rw [m4, o3.val32 (by omega_arith) (by omega_arith), m2, m1]
  obtain inv4 : s4.gpr .r1 = inv * s4.mem.readW (off (State.addr base) o) 32 := by
    rw [g41, r3.gpr .r1 (by decide), q1, m4]
  have N4 : val32 s4.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := e4.modVal
  have row := ri.value
  rw [g411, inv4, N4] at row
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at row
  rw [x7, r7, c7] at car
  obtain rep := val32_replace (m := s4.mem) (m' := w) (base := State.addr base) (d := M + 24) (i := k) (j := n + 1)
    (k := n - k - 1) (OW.val32 (by omega_arith) (by omega_arith)) (OW.val32 (by omega_arith) (by omega_arith))
  rw [show k + (n + 1) + (n - k - 1) = 2 * n by omega_arith, show M + 24 + 4 * k = o by omega_arith] at rep
  obtain hX := val32_succ s4.mem (State.addr base) o n
  obtain hX' := val32_succ w (State.addr base) o n
  rw [o8a'.val32 (d := o) (k := n) (by omega_arith) (by omega_arith), ← hD, hw, w32_write_self, ← hw] at hX'
  rw [← hD] at hX
  obtain step := red_value (W := 2 ^ 32) rep (by rw [hX, Nat.mul_comm]) (by rw [hX', Nat.mul_comm]) row car
  obtain ⟨Q, hQ, value⟩ := h.value
  obtain pk : 2 ^ (32 * (k + 1 + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) * 2 ^ 32 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
  obtain pk' : 2 ^ (32 * (k + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  obtain mlt := (inv * s4.mem.readW (off (State.addr base) o) 32).isLt
  -- The cleared word.
  obtain hu : (inv * s4.mem.readW (off (State.addr base) o) 32).toNat =
      val32 s4.mem (State.addr base) o n * inv.toNat % 2 ^ 32 := by
    have := coefficient_value inv s4.mem (State.addr base) o (n - 1)
    rw [show n - 1 + 1 = n by omega_arith] at this
    exact this
  obtain cancel := round_cancel (T := val32 s4.mem (State.addr base) o n)
    (T' := val32 s5.mem (State.addr base) o n + 2 ^ (32 * n) * (s5.gpr .r11).toNat) e4.invOk hu row
  rw [show 32 * n = 32 + 32 * (n - 1) by omega_arith, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
    show n = n - 1 + 1 by omega_arith, val32_mod_low] at cancel
  refine ⟨⟨et, h.md.of_outs all (by simp; omega_arith) (by omega_arith), by omega_arith, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [m9, rd_self, show n - k - 1 = n - (k + 1) by omega_arith]
  · rw [m9, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith),
      outside_read32 o8a' (by omega_arith) (by omega_arith), outside_read32 ri.outside (by omega_arith) (by omega_arith), m4, m3, rd_self,
      ho, show M + 24 + 4 * k + 4 = M + 24 + 4 * (k + 1) by omega_arith]
  · refine ⟨Q + 2 ^ (32 * k) * (inv * s4.mem.readW (off (State.addr base) o) 32).toNat, ?_, ?_⟩
    · rw [show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add]
      exact red_q hQ mlt
    · rw [o9.val32 (by omega_arith) (by omega_arith), o8b.val32 (by omega_arith) (by omega_arith), m9,
        rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m8, rd_self, pk]
      rw [VT] at step
      rw [step, ← pk', value]
      grind
  · rw [val32_succ, all.val32 (by simp; omega_arith) (by omega_arith), h.low, o9.w32 (by omega_arith) (by omega_arith),
      o8b.w32 (by omega_arith) (by omega_arith), o8a'.w32 (by omega_arith) (by omega_arith), show M + 24 + 4 * k = o by omega_arith, cancel,
      Nat.mul_zero]
  · rw [all.val32 (by simp; omega_arith) (by omega_arith)]; exact h.top
  · rw [z9]; simp only [show n - k = 1 ↔ k + 1 = n by omega_arith]
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans
      ((ri.rest.mono (by decide)).trans ((r6.mono (by decide)).trans
      ((u7.rest (by decide)).trans ((r8.mono (by decide)).trans
      (r9.mono (by decide)))))))))

theorem redRounds_ok (s : State) (h : RedInv m0 base size out a mod M n inv 0 s) :
    WP isa redRounds s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  have hn := h.env.count
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧
    RedInv m0 base size out a mod M n inv i t ∧ Rest roundClobbers s t
  unfold redRounds
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t hk
    obtain ⟨i, hik, hk, hi, rest⟩ := hk
    refine WP.mono (redRound_ok t hi (by omega_arith)) ?_
    rintro u ⟨hu, hz, ru⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu, rest.trans ru⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, hu, rest.trans ru⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, by omega_arith, by omega_arith, h, Rest.refl _ _⟩

theorem sqReduce_ok (s : State) (h : ProdInv m0 base size out a mod M n inv s) :
    WP isa sqReduce s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  rw [sqReduce, WP.seq_iff]
  refine WP.mono (sqReduceInit_ok s h) ?_
  rintro u ⟨hu, ru⟩
  exact WP.mono (redRounds_ok u hu) fun t ⟨ht, rt⟩ => ⟨ht, ru.trans rt⟩

end

end VG.Proof.Bignum.Arm

end

end

/-! # The whole ARMv7 Montgomery square: `a² R⁻¹ mod m`, canonical -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqFinish_ok (s : State) (h : RedInv m0 base size out a mod M n inv n s) :
    WP isa sqFinish s fun t =>
      val32 t.mem (State.addr base) out n < val32 m0 (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 m0 (State.addr base) mod n =
        val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n % val32 m0 (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepM; have := env.mFits
  have := env.sepO; have := env.outFits
  rw [sqFinish, WP.seq_iff]
  refine WP.mono (sqBase_ok s env .r0) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqFinishHeader_ok s1 e1.workspace (by omega_arith) p1 e1.modNow e1.metaNow) ?_
  rintro s2 ⟨q12, q0, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  rw [WP.seq_iff]
  refine WP.mono (sqFinishLoad_ok s2 (n := n) (out := out) e2.workspace (by omega_arith) q0
    (by rw [m2, m1]; exact h.md.count) (by rw [m2, m1]; exact h.md.outPtr)) ?_
  rintro s3 ⟨g7, g9, g3, g0, m3, r3⟩
  have e3 := e2.of_mem m3 r3
  rw [WP.seq_iff]
  refine WP.mono (sqFinishArgs_ok s3 e3.workspace (by omega_arith) (g0.trans q0) g7) ?_
  rintro s4 ⟨m4, g10, glr, g11, r4⟩
  have o4 := writeW32_outside s3.mem (State.addr base) (d := M + 8 * n + 24) (s3.gpr .r3) (by omega_arith)
  rw [← m4] at o4
  have e4 := e3.next (Outs.of_outside (o4.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r4
  -- The number to reduce: `T[n …]` with the carry `c` above it.
  obtain ⟨Q, hQ, value⟩ := h.value
  have ms3 : s3.mem = s.mem := m3.trans (m2.trans m1)
  have hi : val32 s4.mem (State.addr base) (M + 24 + 4 * n) (n + 2) =
      val32 s.mem (State.addr base) (M + 24 + 4 * n) n +
        2 ^ (32 * n) * (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat := by
    rw [val32_top2, show M + 24 + 4 * n + 4 * n = M + 8 * n + 24 by omega_arith, o4.val32 (by omega_arith) (by omega_arith),
      o4.w32 (d := M + 8 * n + 24 + 4) (by omega_arith) (by omega_arith), m4, w32_write_self, g3, m2, m1, ms3]
    have z := h.top
    rw [show M + 24 + 8 * n = M + 8 * n + 24 by omega_arith] at z
    have z' := val32_zero_tail (i := 1) (j := 1) z
    rw [val32, val32, Nat.mul_zero, Nat.add_zero] at z'
    rw [show M + 8 * n + 24 + 4 = M + 8 * n + 24 + 4 * 1 by omega_arith, z']
    simp only [Nat.mul_zero, Nat.add_zero]
  have whole : 2 ^ (32 * n) * val32 s4.mem (State.addr base) (M + 24 + 4 * n) (n + 2) =
      val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n + Q * val32 m0 (State.addr base) mod n := by
    rw [hi, ← value, show 2 * n = n + n by omega_arith, val32_append, h.low, Nat.zero_add,
      show 32 * (n + n) = 32 * n + 32 * n by omega_arith, Nat.pow_add, Nat.mul_add, Nat.mul_assoc]
  have N4 : val32 s4.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := e4.modVal
  have bound := sq_red_bound env.operand (Nat.le_of_lt (val32_lt m0 (State.addr base) mod n)) hQ whole
  have ctx : CsubCtx s4 base size out (M + 24 + 4 * n) mod M n :=
    ⟨⟨nowrap, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, e4.workspace.writable⟩,
      by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have p0 : s4.gpr .r0 = base + BitVec.ofNat 32 M := by rw [r4.gpr .r0 (by decide), g0, q0]
  have p12 : s4.gpr .r12 = base + BitVec.ofNat 32 mod := by
    rw [r4.gpr .r12 (by decide), r3.gpr .r12 (by decide), q12]
  have p9 : s4.gpr .r9 = base + BitVec.ofNat 32 out := by rw [r4.gpr .r9 (by decide), g9]
  have p7 : s4.gpr .r7 = BitVec.ofNat 32 n := by rw [r4.gpr .r7 (by decide), g7]
  refine WP.mono (csub_ok s4 ctx (by omega_arith) p0 g10 p12 p9 glr p7 g11 (by rw [N4]; exact bound)) ?_
  rintro t ⟨result, outs, rest⟩
  have hpos : 0 < val32 m0 (State.addr base) mod n := Nat.lt_of_le_of_lt (Nat.zero_le _) env.operand
  rw [N4] at result
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [result]; exact Nat.mod_lt _ hpos
  · rw [result, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, whole, Nat.add_mul_mod_self_right]
  · have A : Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s3.mem s4.mem :=
      Outs.of_outside (o4.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)) (by simp)
    have B : Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s4.mem t.mem := fun x hx =>
      outs x fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h1 := hx (M, 4 * (2 * n + 8)) (by simp)
        have h2 := hx (out, 4 * n) (by simp)
        rcases hr with rfl | rfl <;> simp only at h1 h2 ⊢ <;> omega_arith
    rw [ms3] at A
    exact A.trans B
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans
      (rest.mono (by decide)))))

/-- The square from `MontFn.bases`' registers. -/
theorem sqBody_ok (s : State) (h : SqEnv s.mem base size out a mod M n inv s)
    (p6 : s.gpr .r6 = base + BitVec.ofNat 32 M) (p7 : s.gpr .r7 = BitVec.ofNat 32 n)
    (p8 : s.gpr .r8 = base + BitVec.ofNat 32 a) (p10 : s.gpr .r10 = base + BitVec.ofNat 32 out) :
    WP isa sqBody s fun t =>
      val32 t.mem (State.addr base) out n < val32 s.mem (State.addr base) mod n ∧
      2 ^ (32 * n) * val32 t.mem (State.addr base) out n % val32 s.mem (State.addr base) mod n =
        val32 s.mem (State.addr base) a n * val32 s.mem (State.addr base) a n %
          val32 s.mem (State.addr base) mod n ∧
      Outs (State.addr base) [(M, 4 * (2 * n + 8)), (out, 4 * n)] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [sqBody, WP.seq_iff]
  refine WP.mono (sqInit_ok s h p6 p7 p8 p10) ?_
  rintro s1 ⟨h1, r1⟩
  rw [WP.seq_iff]
  refine WP.mono (crossRows_ok s1 h1) ?_
  rintro s2 ⟨h2, r2⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDouble_ok s2 h2) ?_
  rintro s3 ⟨h3, r3⟩
  rw [WP.seq_iff]
  refine WP.mono (sqDiagPhase_ok s3 h3) ?_
  rintro s4 ⟨h4, r4⟩
  rw [WP.seq_iff]
  refine WP.mono (sqReduce_ok s4 h4) ?_
  rintro s5 ⟨h5, r5⟩
  refine WP.mono (sqFinish_ok s5 h5) ?_
  rintro t ⟨lt, value, outs, r6⟩
  refine ⟨lt, value, ?_, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  exact (h5.env.frame.mono (by simp)).trans outs

end

end VG.Proof.Bignum.Arm
