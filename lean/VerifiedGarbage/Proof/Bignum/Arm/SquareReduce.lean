module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareDiag
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

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
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega))
    (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_str (by decide) (sq_ea nowrap p1 (by omega)) (by rw [u1.wr]; exact ws.write (by omega))
    fun s2 u2 => ?_
  have p2 : s2.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u2.gpr]; exact p1
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_str (by decide) (sq_ea nowrap p3 (by omega)) (by rw [u3.wr, u2.wr, u1.wr]; exact ws.write (by omega))
    fun s4 u4 => ?_
  have p4 : s4.gpr .r0 = base + BitVec.ofNat 32 M := by rw [u4.gpr]; exact p3
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have p5 := (u5.other .r0 (by decide)).trans p4
  refine wp_str (by decide) (sq_ea nowrap p5 (by omega))
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write (by omega)) fun t u6 => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · have v3 : s3.gpr .r1 = base + BitVec.ofNat 32 (M + 24) := by
      rw [u3.gpr, dpVal, p2]
      change base + BitVec.ofNat 32 M + BitVec.ofNat 32 24 = _
      rw [Offset.add_add]
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr, v3, u1.gpr, hn]
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans ((u3.rest (by simp)).trans ((u4.rest _).trans
      ((u5.rest (by simp)).trans (u6.rest _)))))

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
  refine wp_ldr (by decide) (sq_ea0 nowrap p0 (by omega)) (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_ldr (by decide) (sq_ea0 nowrap ((u1.other .r0 (by decide)).trans p0) (by omega))
    (by rw [u1.rd, u1.wr]; exact ws.read (by omega)) fun s2 u2 => ?_
  refine wp_ldr (by decide) (sq_ea0 nowrap ((u2.other .r0 (by decide)).trans ((u1.other .r0 (by decide)).trans p0))
    (by omega)) (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u3.other .r12 (by decide), u2.other .r12 (by decide), u1.gpr, hm]
  · rw [u3.other .r1 (by decide), u2.gpr, u1.mem, hi]
  · rw [u3.gpr, u2.mem, u1.mem, hM]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

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
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega))
    (ws.read (by omega)) fun s1 u1 => ?_
  have p1 := (u1.other .r0 (by decide)).trans p0
  refine wp_ldr (by decide) (sq_ea nowrap p1 (by omega)) (by rw [u1.rd, u1.wr]; exact ws.read (by omega))
    fun s2 u2 => ?_
  have p2 := (u2.other .r0 (by decide)).trans p1
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have p3 := (u3.other .r0 (by decide)).trans p2
  refine wp_str (by decide) (sq_ea nowrap p3 (by omega)) (by rw [u3.wr, u2.wr, u1.wr]; exact ws.write (by omega))
    fun s4 u4 => ?_
  refine wp_mov (op2_reg _ _) fun t u5 => WP.block_nil ?_
  have g2 : s2.gpr .r2 = base + BitVec.ofNat 32 P := by rw [u2.gpr, u1.mem, ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u5.other .lr (by decide), u4.gpr, u3.other .lr (by decide), u2.other .lr (by decide), u1.gpr, hn]
  · rw [u5.gpr, u4.gpr, u3.other .r2 (by decide), g2]
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, dpVal, g2]
    change _ = s.mem.writeW _ (base + BitVec.ofNat 32 (P + 4))
    rw [← Offset.add_add]; rfl
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest _).trans
      (u5.rest (by simp)))))

theorem redScalar_ok (s : State) {base : BitVec 32} {size D : Nat} (ws : Workspace s base size)
    (fit : D + 4 ≤ size) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 D) :
    WP isa (.block redScalar) s fun t =>
      t.gpr .r1 = s.gpr .r1 * s.mem.readW (off (State.addr base) D) 32 ∧ t.gpr .r11 = 0 ∧
      t.gpr .r0 = s.gpr .r0 ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r11] s t := by
  unfold redScalar
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea ws.nowrap p0 (imm := 0) (by omega))
    (ws.read fit) fun s1 u1 => ?_
  refine wp_mul fun s2 u2 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, u3.gpr, ?_, ?_, ?_⟩
  · rw [u3.other .r1 (by decide), u2.gpr, u1.other .r1 (by decide), u1.gpr]
  · rw [u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u3.mem, u2.mem, u1.mem]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest (by simp)))

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
  have ea0 := sq_ea nowrap p0 (imm := 0) (by omega)
  rw [Nat.add_zero] at ea0
  refine wp_ldr (by decide) ea0 (ws.read fitD) fun s1 u1 => ?_
  refine wp_ldr (by decide) (sq_ea nowrap ((u1.other .r2 (by decide)).trans p2) (by omega))
    (by rw [u1.rd, u1.wr]; exact ws.read (by omega)) fun s2 u2 => ?_
  refine wp_adds (op2_reg _ _) fun s3 u3 c3 => ?_
  refine wp_mov_c (op2_imm (by decide)) fun s4 u4 c4 => ?_
  refine wp_adc (op2_imm (by decide)) fun s5 u5 c5 => ?_
  refine wp_adds (op2_reg _ _) fun s6 u6 c6 => ?_
  refine wp_adc (op2_imm (by decide)) fun s7 u7 _ => ?_
  have q0 : s7.gpr .r0 = s.gpr .r0 := by
    rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.other .r0 (by decide), u4.other .r0 (by decide),
      u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  have q2 : s7.gpr .r2 = s.gpr .r2 := by
    rw [u7.other .r2 (by decide), u6.other .r2 (by decide), u5.other .r2 (by decide), u4.other .r2 (by decide),
      u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide)]
  have w7 : s7.wr = s.wr := by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine wp_str (a := off (State.addr base) D) (by decide) (by rw [q0]; exact ea0) (by rw [w7]; exact ws.write fitD)
    fun s8 u8 => ?_
  refine wp_str (by decide) (sq_ea nowrap (by rw [u8.gpr, q2]; exact p2) (by omega))
    (by rw [u8.wr, w7]; exact ws.write (by omega)) fun s9 u9 => ?_
  refine wp_mov (op2_reg _ _) fun t u10 => WP.block_nil ?_
  -- The values.
  have x : s1.gpr .r3 = s.mem.readW (off (State.addr base) D) 32 := u1.gpr
  have c : s2.gpr .r4 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by rw [u2.gpr, u1.mem]
  have r : s2.gpr .r11 = s.gpr .r11 := by rw [u2.other .r11 (by decide), u1.other .r11 (by decide)]
  have v3 : s3.gpr .r3 = s.mem.readW (off (State.addr base) D) 32 + s.gpr .r11 := by
    rw [u3.gpr, u2.other .r3 (by decide), x, r]
  have v6 : s6.gpr .r3 = s3.gpr .r3 + s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [u6.gpr, u5.other .r3 (by decide), u4.other .r3 (by decide), u5.other .r4 (by decide),
      u4.other .r4 (by decide), u3.other .r4 (by decide), c]
  have h5 : (s5.gpr .r5).toNat = (if s4.c then 1 else 0) := by
    rw [u5.gpr, u4.gpr]
    have := adc_zero 0 s4.c (by decide)
    simpa only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add] using this
  have h7 : (s7.gpr .r5).toNat = (s5.gpr .r5).toNat + (if s6.c then 1 else 0) := by
    rw [u7.gpr, u6.other .r5 (by decide)]
    exact adc_zero _ _ (by rw [h5]; split <;> decide)
  have e3 := add_carry (s.mem.readW (off (State.addr base) D) 32) (s.gpr .r11)
  have e6 := add_carry (s3.gpr .r3) (s.mem.readW (off (State.addr base) (M + 12)) 32)
  rw [← v3] at e3
  rw [← v6] at e6
  have cc4 : s4.c = decide (2 ^ 32 ≤ (s.mem.readW (off (State.addr base) D) 32).toNat + (s.gpr .r11).toNat) := by
    rw [c4, c3, u2.other .r3 (by decide), x, r]
  have cc6 : s6.c = decide (2 ^ 32 ≤ (s3.gpr .r3).toNat +
      (s.mem.readW (off (State.addr base) (M + 12)) 32).toNat) := by
    rw [c6, u5.other .r3 (by decide), u4.other .r3 (by decide), u5.other .r4 (by decide),
      u4.other .r4 (by decide), u3.other .r4 (by decide), c]
  refine ⟨s6.gpr .r3, s7.gpr .r5, ?_, ?_, ?_, ?_⟩
  · rw [h7, h5, cc4, cc6]
    simp only [decide_eq_true_eq]
    omega
  · rw [u10.mem, u9.mem, u8.mem, m7, u8.gpr, u7.other .r3 (by decide)]
  · rw [u10.gpr, u9.gpr, u8.gpr, q2, p2]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans
      ((u8.rest _).trans ((u9.rest _).trans (u10.rest (by simp))))))))))

/-- A round's value step. -/
theorem red_value {VT VT' P Wn W X X' win win' lo hi x r c m N : Nat}
    (hrep : VT' + P * X = VT + P * X') (hX : X = win + Wn * x) (hX' : X' = win' + Wn * lo)
    (hrow : win' + Wn * r = win + m * N) (hcar : lo + W * hi = x + r + c) :
    VT' + P * Wn * W * hi = VT + P * Wn * c + P * (m * N) := by
  subst hX hX'
  have e1 : P * (win' + Wn * r) = P * (win + m * N) := by rw [hrow]
  have e2 : P * Wn * (lo + W * hi) = P * Wn * (x + r + c) := by rw [hcar]
  grind

theorem red_q {Q P m W : Nat} (hQ : Q < P) (hm : m < W) : Q + P * m < P * W := by
  have := Nat.mul_le_mul_left P (show m + 1 ≤ W by omega)
  rw [Nat.mul_succ] at this
  omega

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
  have e1 := env.of_mem m1 r1
  refine WP.mono (redInit_ok s1 (M := M) (n := n) e1.workspace (by omega) p1 (by rw [m1]; exact h.md.count)) ?_
  rintro t ⟨mt, rt⟩
  have o1 := writeW32_outside s1.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 n) (by omega)
  have o2 := writeW32_outside (s1.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 n))
    (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (M + 24)) (by omega)
  have o3 := writeW32_outside ((s1.mem.writeW (off (State.addr base) (M + 16)) (BitVec.ofNat 32 n)).writeW
      (off (State.addr base) (M + 20)) (base + BitVec.ofNat 32 (M + 24))) (State.addr base) (d := M + 12)
    (0 : BitVec 32) (by omega)
  rw [← mt] at o3
  have O : Outside (State.addr base) (M + 12) 12 s1.mem t.mem :=
    (o1.mono (by omega) (by omega)).trans ((o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega)))
  have et := e1.next (Outs.of_outside (O.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) rt
  refine ⟨⟨et, h.md.congr fun d hd => ?_, by omega, ?_, ?_, ⟨0, by simp, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [outside_read32 O (by omega) (by omega), m1]
  · rw [mt, rd_other _ (by omega) (by omega) (by omega), rd_other _ (by omega) (by omega) (by omega), rd_self,
      Nat.sub_zero]
  · rw [mt, rd_other _ (by omega) (by omega) (by omega), rd_self, Nat.mul_zero, Nat.add_zero]
  · rw [O.val32 (by omega) (by omega), mt, rd_self, m1, h.value]
    simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  · rfl
  · rw [O.val32 (by omega) (by omega), m1]; exact h.top
  · exact (r1.mono (by simp [roundClobbers])).trans (rt.mono (by simp [roundClobbers]))

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
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (redHeader_ok s1 e1.workspace (by omega_arith) p1 e1.modNow e1.invNow e1.metaNow) ?_
  rintro s2 ⟨q12, q1, q0, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  rw [WP.seq_iff]
  refine WP.mono (redArgs_ok s2 (P := o) e2.workspace (by omega_arith) q0 (by rw [m2, m1]; exact h.md.count)
    (by rw [m2, m1, ho]; exact h.tptr)) ?_
  rintro s3 ⟨g3lr, g30, m3, r3⟩
  have o3 := writeW32_outside s2.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 4)) (by omega_arith)
  rw [← m3] at o3
  have e3 := e2.next (Outs.of_outside (o3.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r3
  rw [WP.seq_iff]
  refine WP.mono (redScalar_ok s3 e3.workspace (D := o) (by omega_arith) g30) ?_
  rintro s4 ⟨g41, g411, g40, m4, r4⟩
  have e4 := e3.of_mem m4 r4
  have ctx : RowCtx s4 base size o mod n := ⟨nowrap, by omega_arith, by omega_arith, by omega_arith, e4.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (row_ok s4 ctx (by omega_arith) (g40.trans g30)
    (by rw [r4.gpr .r12 (by simp), r3.gpr .r12 (by simp)]; exact q12)
    (by rw [r4.gpr .lr (by simp)]; exact g3lr)) ?_
  intro s5 ri
  have e5 := e4.next (Outs.of_outside (ri.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith)
    (by omega_arith)) (by simp)) ri.rest
  rw [WP.seq_iff]
  refine WP.mono (sqBase_ok s5 e5 .r2) ?_
  rintro s6 ⟨p6, m6, r6⟩
  have e6 := e5.of_mem m6 r6
  rw [WP.seq_iff]
  refine wp_ldr (by decide) (sq_ea0 nowrap p6 (by omega_arith)) (e6.read (by omega_arith)) fun s7 u7 => WP.block_nil ?_
  have e7 := e6.of_mem u7.mem (u7.rest (ws := [.r2]) (by simp))
  have p72 : s7.gpr .r2 = base + BitVec.ofNat 32 M := u7.gpr.trans e6.metaNow
  have p70 : s7.gpr .r0 = base + BitVec.ofNat 32 D := by
    rw [u7.other .r0 (by decide), r6.gpr .r0 (by simp), ri.outPtr, hD]
  rw [WP.seq_iff]
  refine WP.mono (redCarry_ok s7 e7.workspace (D := D) (M := M) (by omega_arith) (by omega_arith) p70 p72) ?_
  rintro s8 ⟨lo, hi, car, m8, p80, r8⟩
  have o8a := writeW32_outside s7.mem (State.addr base) (d := D) lo (by omega_arith)
  have o8b := writeW32_outside (s7.mem.writeW (off (State.addr base) D) lo) (State.addr base) (d := M + 12) hi
    (by omega_arith)
  rw [← m8] at o8b
  have e8 := e7.next (Outs.of_outside ((o8a.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith)).trans
    (o8b.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))) (by simp)) r8
  have cnt8 : s8.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - k) := by
    rw [m8, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), u7.mem, m6,
      outside_read32 ri.outside (by omega_arith) (by omega_arith), m4, m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m2, m1]
    exact h.cnt
  refine WP.mono (sqCount_ok s8 e8.workspace (by omega_arith) p80 cnt8 (by omega_arith) (by omega_arith)) ?_
  rintro t ⟨m9, z9, r9⟩
  have o9 := writeW32_outside s8.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 (n - k - 1)) (by omega_arith)
  rw [← m9] at o9
  have et := e8.next (Outs.of_outside (o9.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith) (by omega_arith))
    (by simp)) r9
  -- Where memory changed.
  obtain ⟨w, hw⟩ : ∃ w, w = s7.mem.writeW (off (State.addr base) D) lo := ⟨_, rfl⟩
  rw [← hw] at o8a o8b m8
  have hw7 : s7.mem = s5.mem := u7.mem.trans m6
  have o8a' : Outside (State.addr base) D 4 s5.mem w := by rw [← hw7]; exact o8a
  have OW : Outside (State.addr base) o (4 * n + 4) s4.mem w :=
    (ri.outside.mono (by omega_arith) (by omega_arith)).trans (o8a'.mono (by omega_arith) (by omega_arith))
  have all : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s.mem t.mem := by
    have A1 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s2.mem s3.mem :=
      Outs.of_outside (o3.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    have A2 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s4.mem w := Outs.of_outside OW (by simp)
    have A4 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] w s8.mem :=
      Outs.of_outside (o8b.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    have A5 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s8.mem t.mem :=
      Outs.of_outside (o9.mono (o' := M + 12) (n' := 12) (by omega_arith) (by omega_arith)) (by simp)
    rw [m2, m1] at A1
    rw [m4] at A2
    exact A1.trans (A2.trans (A4.trans A5))
  -- The carry in, and the old values.
  have c4 : s4.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [m4, m3, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith), m2, m1]
  have c7 : s7.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega_arith) (by omega_arith), c4]
  have x7 : s7.mem.readW (off (State.addr base) D) 32 = s4.mem.readW (off (State.addr base) D) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega_arith) (by omega_arith)]
  have r7 : s7.gpr .r11 = s5.gpr .r11 := by rw [u7.other .r11 (by decide), r6.gpr .r11 (by simp)]
  have VT : val32 s4.mem (State.addr base) (M + 24) (2 * n) = val32 s.mem (State.addr base) (M + 24) (2 * n) := by
    rw [m4, o3.val32 (by omega_arith) (by omega_arith), m2, m1]
  have inv4 : s4.gpr .r1 = inv * s4.mem.readW (off (State.addr base) o) 32 := by
    rw [g41, r3.gpr .r1 (by simp), q1, m4]
  have N4 : val32 s4.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := e4.modVal
  have row := ri.value
  rw [g411, inv4, N4] at row
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at row
  rw [x7, r7, c7] at car
  have rep := val32_replace (m := s4.mem) (m' := w) (base := State.addr base) (d := M + 24) (i := k) (j := n + 1)
    (k := n - k - 1) (OW.val32 (by omega_arith) (by omega_arith)) (OW.val32 (by omega_arith) (by omega_arith))
  rw [show k + (n + 1) + (n - k - 1) = 2 * n by omega_arith, show M + 24 + 4 * k = o by omega_arith] at rep
  have hX := val32_succ s4.mem (State.addr base) o n
  have hX' := val32_succ w (State.addr base) o n
  rw [o8a'.val32 (d := o) (k := n) (by omega_arith) (by omega_arith), ← hD, hw, w32_write_self, ← hw] at hX'
  rw [← hD] at hX
  have step := red_value (W := 2 ^ 32) rep (by rw [hX, Nat.mul_comm]) (by rw [hX', Nat.mul_comm]) row car
  obtain ⟨Q, hQ, value⟩ := h.value
  have pk : 2 ^ (32 * (k + 1 + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) * 2 ^ 32 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
  have pk' : 2 ^ (32 * (k + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) := by
    rw [← Nat.pow_add]; congr 1; omega_arith
  have mlt := (inv * s4.mem.readW (off (State.addr base) o) 32).isLt
  -- The cleared word.
  have hu : (inv * s4.mem.readW (off (State.addr base) o) 32).toNat =
      val32 s4.mem (State.addr base) o n * inv.toNat % 2 ^ 32 := by
    have := coefficient_value inv s4.mem (State.addr base) o (n - 1)
    rw [show n - 1 + 1 = n by omega_arith] at this
    exact this
  have cancel := round_cancel (T := val32 s4.mem (State.addr base) o n)
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
  · exact (r1.mono (by simp [roundClobbers])).trans ((r2.mono (by simp [roundClobbers])).trans
      ((r3.mono (by simp [roundClobbers])).trans ((r4.mono (by simp [roundClobbers])).trans
      ((ri.rest.mono (by simp [loopClobbers, roundClobbers])).trans ((r6.mono (by simp [roundClobbers])).trans
      ((u7.rest (by simp [roundClobbers])).trans ((r8.mono (by simp [roundClobbers])).trans
      (r9.mono (by simp [roundClobbers])))))))))

theorem redRounds_ok (s : State) (h : RedInv m0 base size out a mod M n inv 0 s) :
    WP isa redRounds s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  have hn := h.env.count
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧
    RedInv m0 base size out a mod M n inv i t ∧ Rest roundClobbers s t
  unfold redRounds
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t hk
    obtain ⟨i, hik, hk, hi, rest⟩ := hk
    refine WP.mono (redRound_ok t hi (by omega)) ?_
    rintro u ⟨hu, hz, ru⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu, rest.trans ru⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu, rest.trans ru⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, by omega, by omega, h, Rest.refl _ _⟩

theorem sqReduce_ok (s : State) (h : ProdInv m0 base size out a mod M n inv s) :
    WP isa sqReduce s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  rw [sqReduce, WP.seq_iff]
  refine WP.mono (sqReduceInit_ok s h) ?_
  rintro u ⟨hu, ru⟩
  exact WP.mono (redRounds_ok u hu) fun t ⟨ht, rt⟩ => ⟨ht, ru.trans rt⟩

end

end VG.Proof.Bignum.Arm
