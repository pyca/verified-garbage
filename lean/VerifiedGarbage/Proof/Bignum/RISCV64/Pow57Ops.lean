module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Pow57Rect
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Radix `2⁵⁷` on RISC-V: the operations
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pow57

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Pow57

/-! ## The working space -/

/-- `A`'s offset, for `M` at `dM`. -/
abbrev oA (q dM : Nat) : Nat := dM + 72 * q + 24
/-- `T`'s offset. -/
abbrev oT (q dM : Nat) : Nat := dM + 144 * q + 48
/-- `E`'s offset. -/
abbrev oE (q dM : Nat) : Nat := dM + 288 * q + 48

/-- The registers and the space of an operation, for `n = 9 q` limbs. -/
structure In (s : State) (B : Addr) (Z q dM : Nat) : Prop where
  scr : Scr s B Z
  q1 : 1 ≤ q
  q6 : q ≤ 6
  dM8 : dM % 8 = 0
  fit : dM + 360 * q + 48 < Z
  a7 : s.gpr .a7 = off B (oA q dM)
  s5 : s.gpr .s5 = off B (oT q dM)

theorem In.of {s t : State} {B : Addr} {Z q dM : Nat} {rs : List Reg} (h : In s B Z q dM) (k : Keep rs s t)
    (h7 : Reg.a7 ∉ rs) (h5 : Reg.s5 ∉ rs) : In t B Z q dM :=
  ⟨h.scr.congr k.2.2, h.q1, h.q6, h.dM8, h.fit, (k.gpr h7).trans h.a7, (k.gpr h5).trans h.s5⟩

/-- The modulus `N` in `M`, and its inverse. -/
structure ModIn (s : State) (B : Addr) (q dM N : Nat) : Prop where
  val : lv s.mem B dM (9 * q) = N
  lim : Lim s.mem B dM (9 * q) L57
  pad : lv s.mem B (dM + 72 * q) 3 = 0
  inv : ((word s.mem B dM).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 57 = 0

theorem sub_off (B : Addr) {a b : Nat} (h : a ≤ b) : off B b - off B a = BitVec.ofNat 64 (b - a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, off, off, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel]

theorem limbs_ok {s : State} {B : Addr} {Z q dM : Nat} (h : In s B Z q dM) :
    WP isa (.block limbs) s fun t => (t.gpr .t2 = BitVec.ofNat 64 (72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold limbs
  brun [h.a7, h.s5, sub_off B (show oA q dM ≤ oT q dM by unfold oA oT; omega_arith)]
  rw [show oT q dM - oA q dM = 72 * q + 24 by unfold oA oT; omega_arith, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The mask of a limb. -/
abbrev m57 : BitVec 64 := BitVec.ofNat 64 (2 ^ 57 - 1)

theorem mask57_ok (s : State) :
    WP isa (.block mask57) s fun t => (t.gpr .t6 = m57 ∧ t.mem = s.mem) ∧ Keep [.t6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold mask57
  brun [exec_li]
  rfl

theorem and_m57 (x : BitVec 64) : (x &&& m57).toNat = x.toNat % 2 ^ 57 := by
  rw [BitVec.toNat_and, show m57.toNat = 2 ^ 57 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem srl57 (x : BitVec 64) : (x >>> 57).toNat = x.toNat / 2 ^ 57 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shl7_and (x : BitVec 64) : x <<< 7 = (x &&& m57) <<< 7 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, and_m57, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega_arith

/-! ## Products and quotients -/

theorem mul57_val {x y : BitVec 64} (hx : x.toNat ≤ L57) :
    (x * y - mh (x <<< 7) y <<< 57).toNat = lo57 x y ∧ (mh (x <<< 7) y).toNat = hi57 x y := by
  obtain hy := y.isLt
  obtain bd : hi57 x y < 2 ^ 64 := by
    unfold hi57 L57 at *
    obtain a := Nat.mul_le_mul hx (Nat.le_of_lt hy)
    omega_using [a]
  obtain e := Nat.div_add_mod (x.toNat * y.toNat) (2 ^ 57)
  obtain b := Nat.mod_lt (x.toNat * y.toNat) (show 2 ^ 57 > 0 by decide)
  unfold mh
  rw [shl7_mul hx]
  refine ⟨?_, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bd]⟩
  obtain key : x * y - BitVec.ofNat 64 (hi57 x y) <<< 57 = BitVec.ofNat 64 (lo57 x y) := by
    rw [BitVec.sub_eq_iff_eq_add, ofNat_shl57, ← BitVec.ofNat_add, mul_ofNat]
    refine congrArg _ ?_
    unfold hi57 lo57
    omega_using [e]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold lo57; omega_using [b])]

theorem mul57_ok {rl rh x xp y tmp : Reg} (s : State) (h1 : rh ≠ x) (h2 : rh ≠ y) (h3 : rl ≠ rh) (h4 : tmp ≠ rl)
    (h5 : tmp ≠ rh) (hp : s.gpr xp = s.gpr x <<< 7) (hx : (s.gpr x).toNat ≤ L57)
    (hw : writesOnly [rl, rh, tmp] (.block (mul57 rl rh x xp y tmp)) = true) :
    WP isa (.block (mul57 rl rh x xp y tmp)) s fun t =>
      ((t.gpr rl).toNat = lo57 (s.gpr x) (s.gpr y) ∧ (t.gpr rh).toNat = hi57 (s.gpr x) (s.gpr y) ∧ t.mem = s.mem) ∧
        Keep [rl, rh, tmp] s t := by
  refine WP.keep _ ?_ hw (by rfl)
  unfold mul57
  brun [↓exec_mh, hp, h1, h2, h3, h4, h5, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  exact mul57_val hx

theorem quot_ok {u up : Reg} (hu : (u = .s2 ∧ up = .t2) ∨ (u = .s3 ∧ up = .t3) ∨ (u = .s4 ∧ up = .t4)) (s : State)
    (h6 : s.gpr .t6 = m57) (hv : (s.gpr .s0).toNat + 2 ^ 57 ≤ 2 ^ 64) :
    WP isa (.block (quot u up .s0)) s fun t =>
      ((t.gpr u).toNat = (s.gpr .s0).toNat * (s.gpr .t1).toNat % 2 ^ 57 ∧ t.gpr up = t.gpr u <<< 7 ∧
        (t.gpr .s0).toNat = ((s.gpr .s0).toNat + (2 ^ 57 - 1)) / 2 ^ 57 ∧ t.mem = s.mem) ∧ Keep [u, up, .s0] s t := by
  obtain a : (s.gpr .s0 * s.gpr .t1 &&& m57).toNat = (s.gpr .s0).toNat * (s.gpr .t1).toNat % 2 ^ 57 := by
    rw [and_m57, BitVec.toNat_mul]
    omega_arith
  obtain b : ((s.gpr .s0 + m57) >>> 57).toNat = ((s.gpr .s0).toNat + (2 ^ 57 - 1)) / 2 ^ 57 := by
    rw [srl57, BitVec.toNat_add, show m57.toNat = 2 ^ 57 - 1 from rfl, Nat.mod_eq_of_lt (by omega_arith)]
  rcases hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold quot
    brun [h6]
    exact ⟨a, shl7_and _, b⟩

/-- The carry of a column `v` that a multiple of the modulus clears. -/
theorem carry_up {v u m mi c : Nat} (hm : (m * mi + 1) % 2 ^ 57 = 0) (hu : u = v * mi % 2 ^ 57)
    (hc : c = (v + (2 ^ 57 - 1)) / 2 ^ 57) : 2 ^ 57 * (c + u * m / 2 ^ 57) = v + u * m := by
  obtain z : (v + u * m) % 2 ^ 57 = 0 := by
    rw [Nat.add_mod, hu, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.mul_assoc, Nat.mul_comm mi m,
      show v + v * (m * mi) = v * (m * mi + 1) by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm], Nat.mul_mod, hm,
      Nat.mul_zero, Nat.zero_mod]
  generalize u * m = p at z ⊢
  subst hc
  omega_arith

/-! ## The reduction -/

theorem toNat_add_lt {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) : (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem red_sum {t₀ t₁ t₂ m₀ m₁ m₂ mi u₀ u₁ u₂ c₀ c₁ c₂ v₁ v₂ h : Nat} (hm : (m₀ * mi + 1) % 2 ^ 57 = 0)
    (eu₀ : u₀ = t₀ * mi % 2 ^ 57) (ec₀ : c₀ = (t₀ + (2 ^ 57 - 1)) / 2 ^ 57)
    (ev₁ : v₁ = c₀ + u₀ * m₀ / 2 ^ 57 + t₁ + u₀ * m₁ % 2 ^ 57)
    (eu₁ : u₁ = v₁ * mi % 2 ^ 57) (ec₁ : c₁ = (v₁ + (2 ^ 57 - 1)) / 2 ^ 57)
    (ev₂ : v₂ = c₁ + u₀ * m₁ / 2 ^ 57 + t₂ + u₁ * m₀ / 2 ^ 57 + u₀ * m₂ % 2 ^ 57 + u₁ * m₁ % 2 ^ 57)
    (eu₂ : u₂ = v₂ * mi % 2 ^ 57) (ec₂ : c₂ = (v₂ + (2 ^ 57 - 1)) / 2 ^ 57)
    (eh : h = u₀ * m₂ / 2 ^ 57 + u₁ * m₁ / 2 ^ 57 + c₂ + u₂ * m₀ / 2 ^ 57) :
    2 ^ 171 * (h + u₁ * m₂ + u₂ * m₁ + 2 ^ 57 * (u₂ * m₂)) =
      t₀ + 2 ^ 57 * t₁ + 2 ^ 114 * t₂ + (u₀ + 2 ^ 57 * u₁ + 2 ^ 114 * u₂) * (m₀ + 2 ^ 57 * m₁ + 2 ^ 114 * m₂) := by
  obtain e₀ := carry_up hm eu₀ ec₀
  obtain e₁ := carry_up hm eu₁ ec₁
  obtain e₂ := carry_up hm eu₂ ec₂
  obtain d₁ := Nat.div_add_mod (u₀ * m₁) (2 ^ 57)
  obtain d₂ := Nat.div_add_mod (u₀ * m₂) (2 ^ 57)
  obtain d₃ := Nat.div_add_mod (u₁ * m₁) (2 ^ 57)
  clear eu₀ eu₁ eu₂ ec₀ ec₁ ec₂ hm
  subst ev₁ ev₂ eh
  obtain x : (u₀ + 2 ^ 57 * u₁ + 2 ^ 114 * u₂) * (m₀ + 2 ^ 57 * m₁ + 2 ^ 114 * m₂) =
      u₀ * m₀ + 2 ^ 57 * (u₀ * m₁ + u₁ * m₀) + 2 ^ 114 * (u₀ * m₂ + u₁ * m₁ + u₂ * m₀) +
        2 ^ 171 * (u₁ * m₂ + u₂ * m₁ + 2 ^ 57 * (u₂ * m₂)) := by
    grind
  rw [x]
  clear x
  grind

/-- The registers the head of a block of the reduction writes. -/
def redHeadRegs : List Reg := [.t2, .a1, .a4, .a5, .a6, .t6, .s0, .s2, .a3, .s1, .a2, .t0, .s3, .t3, .t5, .s7, .s4, .t4, .a0]

theorem redHead_ok {s : State} {B : Addr} {Z q dM N d g : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (ha0 : s.gpr .a0 = off B d) (hd8 : d % 8 = 0) (hd : d + 24 ≤ Z) (lT : Lim s.mem B d 3 g)
    (hg : g + 6 * L57 + 2 ^ 10 < 2 ^ 64) :
    WP isa (.block redHead) s fun t =>
      ((Mult t ∧ t.gpr .a0 = off B (d + 24) ∧ t.gpr .a1 = off B (dM + 24) ∧ (t.gpr .s7).toNat ≤ 3 * L57 + 2 ^ 10 ∧
        (t.gpr .t5).toNat ≤ L57 ∧ (t.gpr .t6).toNat ≤ L57 ∧ t.mem = s.mem ∧
        2 ^ 171 * cVal t = lv s.mem B d 3 + xVal t * lv s.mem B dM 3) ∧ Keep redHeadRegs s t) := by
  obtain q1 := h.q1
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain l0 := lT 0 (by decide)
  obtain l1 := lT 1 (by decide)
  obtain l2 := lT 2 (by decide)
  obtain n0 := hm.lim 0 (by omega_using [q1])
  obtain n1 := hm.lim 1 (by omega_using [q1])
  obtain n2 := hm.lim 2 (by omega_using [q1])
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at l0 l1 l2 n0 n1 n2
  obtain inv := hm.inv
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  rw [lv_three, lv_three]
  generalize eT0 : word s.mem B d = T0 at l0 ⊢
  generalize eT1 : word s.mem B (d + 8) = T1 at l1 ⊢
  generalize eT2 : word s.mem B (d + 16) = T2 at l2 ⊢
  generalize eM0 : word s.mem B dM = M0 at n0 inv ⊢
  generalize eM1 : word s.mem B (dM + 8) = M1 at n1 ⊢
  generalize eM2 : word s.mem B (dM + 16) = M2 at n2 ⊢
  unfold redHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  obtain r2 : WP isa (.block [.sub .t2 .a7 .t2, .addi .a1 .t2 (-24), .load .d .a4 .a1 0, .load .d .a5 .a1 8,
      .load .d .a6 .a1 16]) s₁ fun t => (t.gpr .a1 = off B dM ∧ t.gpr .a4 = M0 ∧ t.gpr .a5 = M1 ∧ t.gpr .a6 = M2 ∧
        t.mem = s₁.mem) ∧ Keep [.t2, .a1, .a4, .a5, .a6] s₁ t := by
    obtain hs := h.scr.congr k1.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(k1.gpr (r := .a7) (by decide)).trans h.a7, x2, m1, off_sub B (show 72 * q ≤ oA q dM by unfold oA; omega_arith),
      show oA q dM - 72 * q = dM + 24 by unfold oA; omega_arith, off_sub B (show 24 ≤ dM + 24 by omega_arith),
      Nat.add_sub_cancel, hs.ld (show dM + 8 ≤ Z by omega_arith), hs.ld (show dM + 8 + 8 ≤ Z by omega_arith),
      hs.ld (show dM + 16 + 8 ≤ Z by omega_arith), hs.al8 (show dM + 8 ≤ Z by omega_arith) dM8,
      hs.al8 (show dM + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs.al8 (show dM + 16 + 8 ≤ Z by omega_arith) (by omega_arith)]
    exact ⟨eM0, eM1, eM2⟩
  refine WP.mono r2 fun s₂ ⟨⟨a1, a4, a5, a6, m2⟩, k2⟩ => ?_
  obtain K2 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (mask57_ok s₂) fun s₃ ⟨⟨t6, m3⟩, k3⟩ => ?_
  obtain K3 := K2.trans k3
  obtain M3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  rw [WP.block_append_iff]
  obtain hs := h.scr.congr K3.2.2
  obtain r4 : WP isa (.block [.load .d .s0 .a0 0]) s₃ fun t => (t.gpr .s0 = T0 ∧ t.mem = s₃.mem) ∧ Keep [.s0] s₃ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [(K3.gpr (r := .a0) (by decide)).trans ha0, M3, hs.ld (show d + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 8 ≤ Z by omega_arith) hd8]
    exact eT0
  refine WP.mono r4 fun s₄ ⟨⟨x0, m4⟩, k4⟩ => ?_
  obtain K4 := K3.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s2) (up := .t2) (.inl ⟨rfl, rfl⟩) s₄ ((k4.gpr (by decide)).trans t6)
    (by rw [x0]; omega_arith)) fun s₅ ⟨⟨u0, p0, c0, m5⟩, k5⟩ => ?_
  obtain K5 := K4.trans k5
  rw [x0, K4.gpr (r := .t1) (by decide)] at u0
  rw [x0] at c0
  obtain bu0 : (s₅.gpr .s2).toNat ≤ L57 := by rw [u0]; unfold L57; omega_arith
  obtain A4₅ : s₅.gpr .a4 = M0 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a4]
  rw [WP.block_append_iff]
  obtain M5 : s₅.mem = s.mem := by rw [m5, m4, M3]
  obtain r6 : WP isa (.block [.mulhu .a3 .t2 .a4, .load .d .s1 .a0 8, .add .s0 .s0 .a3, .add .s0 .s0 .s1]) s₅ fun t =>
      (t.gpr .s0 = s₅.gpr .s0 + mh (s₅.gpr .s2 <<< 7) M0 + T1 ∧ t.mem = s₅.mem) ∧ Keep [.a3, .s1, .s0] s₅ t := by
    obtain hs := h.scr.congr K5.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, (K5.gpr (r := .a0) (by decide)).trans ha0, M5, A4₅, p0, hs.ld (show d + 8 + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 8 + 8 ≤ Z by omega_arith) (by omega_arith), show s.mem.readW (off B (d + 8)) 64 = T1 from eT1]
  refine WP.mono r6 fun s₆ ⟨⟨x6, m6⟩, k6⟩ => ?_
  obtain K6 := K5.trans k6
  obtain H0 := (mul57_val (y := M0) bu0).2
  obtain bH0 := hi57_le bu0 n0
  obtain n6 : (s₆.gpr .s0).toNat = (s₅.gpr .s0).toNat + hi57 (s₅.gpr .s2) M0 + T1.toNat := by
    rw [x6, toNat_add_lt (by rw [toNat_add_lt (by rw [H0, c0]; omega_arith), H0, c0]; omega_arith),
      toNat_add_lt (by rw [H0, c0]; omega_arith), H0]
  rw [WP.block_append_iff]
  obtain g6 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₆.gpr r = s₅.gpr r := fun r hr => k6.gpr (by revert r hr; decide)
  refine WP.mono (mul57_ok (rl := .a2) (rh := .a3) (x := .s2) (xp := .t2) (y := .a5) (tmp := .t0) s₆ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g6 .t2 (by decide), g6 .s2 (by decide), p0])
    (by rw [g6 .s2 (by decide)]; exact bu0) (by rfl)) fun s₇ ⟨⟨lo01, hi01, m7⟩, k7⟩ => ?_
  obtain K7 := K6.trans k7
  obtain A5₆ : s₆.gpr .a5 = M1 := by rw [k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a5]
  rw [g6 .s2 (by decide), A5₆] at lo01 hi01
  obtain bl01 := lo57_le (s₅.gpr .s2) M1
  obtain bh01 := hi57_le bu0 n1
  obtain r8 : WP isa (.block [.add .s0 .s0 .a2]) s₇ fun t => (t.gpr .s0 = s₇.gpr .s0 + s₇.gpr .a2 ∧ t.mem = s₇.mem) ∧
      Keep [.s0] s₇ t := WP.keep _ (by brun) (by rfl) (by rfl)
  rw [WP.block_append_iff]
  refine WP.mono r8 fun s₈ ⟨⟨x8, m8⟩, k8⟩ => ?_
  obtain K8 := K7.trans k8
  obtain n8 : (s₈.gpr .s0).toNat = (s₅.gpr .s0).toNat + hi57 (s₅.gpr .s2) M0 + T1.toNat + lo57 (s₅.gpr .s2) M1 := by
    rw [x8, k7.gpr (by decide), toNat_add_lt (by rw [n6, lo01, c0]; omega_arith), n6, lo01]
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s3) (up := .t3) (.inr (.inl ⟨rfl, rfl⟩)) s₈
    (by rw [k8.gpr (by decide), k7.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), t6])
    (by rw [n8, c0]; omega_arith)) fun s₉ ⟨⟨u1, p1, c1, m9⟩, k9⟩ => ?_
  obtain K9 := K8.trans k9
  rw [K8.gpr (r := .t1) (by decide)] at u1
  obtain bu1 : (s₉.gpr .s3).toNat ≤ L57 := by rw [u1]; omega_arith
  obtain k69 := (k6.trans k7).trans (k8.trans k9)
  obtain g9 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₉.gpr r = s₅.gpr r := fun r hr => k69.gpr (by revert r hr; decide)
  obtain M9 : s₉.mem = s.mem := by rw [m9, m8, m7, m6, M5]
  obtain r10 : WP isa (.block [.mulhu .s1 .t3 .a4, .load .d .t5 .a0 16, .add .s0 .s0 .a3, .add .s0 .s0 .t5,
      .add .s0 .s0 .s1]) s₉ fun t => (t.gpr .s0 = s₉.gpr .s0 + s₇.gpr .a3 + T2 + mh (s₉.gpr .s3 <<< 7) M0 ∧
        t.mem = s₉.mem) ∧ Keep [.s1, .t5, .s0] s₉ t := by
    obtain hs := h.scr.congr K9.2.2
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, (K9.gpr (r := .a0) (by decide)).trans ha0, M9, (g9 .a4 (by decide)).trans A4₅, p1,
      (k9.gpr (r := .a3) (by decide)).trans (k8.gpr (by decide)), hs.ld (show d + 16 + 8 ≤ Z by omega_arith),
      hs.al8 (show d + 16 + 8 ≤ Z by omega_arith) (by omega_arith), show s.mem.readW (off B (d + 16)) 64 = T2 from eT2]
  rw [WP.block_append_iff]
  refine WP.mono r10 fun s₁₀ ⟨⟨x10, m10⟩, k10⟩ => ?_
  obtain K10 := K9.trans k10
  obtain H1 := (mul57_val (y := M0) bu1).2
  obtain bH1 := hi57_le bu1 n0
  obtain n10 : (s₁₀.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 := by
    obtain y1 : (s₉.gpr .s0 + s₇.gpr .a3).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 := by
      rw [toNat_add_lt (by rw [hi01, c1, n8, c0]; omega_arith), hi01]
    obtain y2 : (s₉.gpr .s0 + s₇.gpr .a3 + T2).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat := by
      rw [toNat_add_lt (by rw [y1, c1, n8, c0]; omega_arith), y1]
    rw [x10, toNat_add_lt (by rw [y2, H1, c1, n8, c0]; omega_arith), y2, H1]
  obtain g10 : ∀ r ∈ [Reg.s2, .t2, .a4, .a5, .a6, .t6], s₁₀.gpr r = s₅.gpr r := fun r hr =>
    (k10.gpr (by revert r hr; decide)).trans (g9 r hr)
  obtain A6₅ : s₅.gpr .a6 = M2 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a6]
  obtain A5₅ : s₅.gpr .a5 = M1 := by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), a5]
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a2) (rh := .s7) (x := .s2) (xp := .t2) (y := .a6) (tmp := .t0) s₁₀ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g10 .t2 (by decide), g10 .s2 (by decide), p0])
    (by rw [g10 .s2 (by decide)]; exact bu0) (by rfl)) fun s₁₁ ⟨⟨lo02, hi02, m11⟩, k11⟩ => ?_
  obtain K11 := K10.trans k11
  rw [g10 .s2 (by decide), g10 .a6 (by decide), A6₅] at lo02 hi02
  obtain bl02 := lo57_le (s₅.gpr .s2) M2
  obtain bh02 := hi57_le bu0 n2
  rw [WP.block_append_iff]
  obtain r12 : WP isa (.block [.add .s0 .s0 .a2]) s₁₁ fun t => (t.gpr .s0 = s₁₁.gpr .s0 + s₁₁.gpr .a2 ∧ t.mem = s₁₁.mem) ∧
      Keep [.s0] s₁₁ t := WP.keep _ (by brun) (by rfl) (by rfl)
  refine WP.mono r12 fun s₁₂ ⟨⟨x12, m12⟩, k12⟩ => ?_
  obtain K12 := K11.trans k12
  obtain n12 : (s₁₂.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 +
      lo57 (s₅.gpr .s2) M2 := by
    rw [x12, k11.gpr (by decide), toNat_add_lt (by rw [n10, lo02, c1, n8, c0]; omega_arith), n10, lo02]
  obtain k912 := (k10.trans k11).trans k12
  obtain g12 : ∀ r ∈ [Reg.s3, .t3, .s2, .t2, .a4, .a5, .a6, .t6], s₁₂.gpr r = s₉.gpr r := fun r hr =>
    k912.gpr (by revert r hr; decide)
  rw [WP.block_append_iff]
  refine WP.mono (mul57_ok (rl := .a2) (rh := .a3) (x := .s3) (xp := .t3) (y := .a5) (tmp := .t0) s₁₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [g12 .t3 (by decide), g12 .s3 (by decide), p1])
    (by rw [g12 .s3 (by decide)]; exact bu1) (by rfl)) fun s₁₃ ⟨⟨lo11, hi11, m13⟩, k13⟩ => ?_
  obtain K13 := K12.trans k13
  rw [g12 .s3 (by decide), g12 .a5 (by decide), g9 .a5 (by decide), A5₅] at lo11 hi11
  obtain bl11 := lo57_le (s₉.gpr .s3) M1
  obtain bh11 := hi57_le bu1 n1
  rw [WP.block_append_iff]
  obtain r14 : WP isa (.block [.add .s0 .s0 .a2, .add .s7 .s7 .a3]) s₁₃ fun t => (t.gpr .s0 = s₁₃.gpr .s0 + s₁₃.gpr .a2 ∧
      t.gpr .s7 = s₁₃.gpr .s7 + s₁₃.gpr .a3 ∧ t.mem = s₁₃.mem) ∧
      Keep [.s0, .s7] s₁₃ t := WP.keep _ (by brun) (by rfl) (by rfl)
  refine WP.mono r14 fun s₁₄ ⟨⟨x14, h14, m14⟩, k14⟩ => ?_
  obtain K14 := K13.trans k14
  obtain n14 : (s₁₄.gpr .s0).toNat = (s₉.gpr .s0).toNat + hi57 (s₅.gpr .s2) M1 + T2.toNat + hi57 (s₉.gpr .s3) M0 +
      lo57 (s₅.gpr .s2) M2 + lo57 (s₉.gpr .s3) M1 := by
    rw [x14, k13.gpr (by decide), toNat_add_lt (by rw [n12, lo11, c1, n8, c0]; omega_arith), n12, lo11]
  obtain h14' : (s₁₄.gpr .s7).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 := by
    rw [h14, k13.gpr (by decide), k12.gpr (by decide), toNat_add_lt (by rw [hi02, hi11]; omega_arith), hi02, hi11]
  rw [WP.block_append_iff]
  refine WP.mono (quot_ok (u := .s4) (up := .t4) (.inr (.inr ⟨rfl, rfl⟩)) s₁₄
    (by rw [k14.gpr (by decide), k13.gpr (by decide), g12 .t6 (by decide), g9 .t6 (by decide), k5.gpr (by decide),
      k4.gpr (by decide), t6])
    (by rw [n14, c1, n8, c0]; omega_arith)) fun s₁₅ ⟨⟨u2, p2, c2, m15⟩, k15⟩ => ?_
  obtain K15 := K14.trans k15
  rw [K14.gpr (r := .t1) (by decide)] at u2
  obtain bu2 : (s₁₅.gpr .s4).toNat ≤ L57 := by rw [u2]; omega_arith
  obtain H2 := (mul57_val (y := M0) bu2).2
  obtain bH2 := hi57_le bu2 n0
  obtain k1215 := (k13.trans k14).trans k15
  obtain g15 : ∀ r ∈ [Reg.s3, .t3, .s2, .t2, .a4, .a5, .a6], s₁₅.gpr r = s₉.gpr r := fun r hr =>
    (k1215.gpr (by revert r hr; decide)).trans (g12 r (by revert r hr; decide))
  obtain r16 : WP isa (.block [.mulhu .a3 .t4 .a4, .add .s7 .s7 .s0, .add .s7 .s7 .a3,
      .addi .t5 .a6 0, .addi .t6 .a5 0, .addi .a0 .a0 24, .addi .a1 .a1 24]) s₁₅ fun t =>
      (t.gpr .s7 = s₁₅.gpr .s7 + s₁₅.gpr .s0 + mh (s₁₅.gpr .s4 <<< 7) M0 ∧ t.gpr .t5 = M2 ∧ t.gpr .t6 = M1 ∧
        t.gpr .a0 = off B (d + 24) ∧ t.gpr .a1 = off B (dM + 24) ∧ t.mem = s₁₅.mem) ∧
      Keep [.a3, .s7, .t5, .t6, .a0, .a1] s₁₅ t := by
    obtain e1 : s₁₅.gpr .a1 = off B dM := by
      rw [k1215.gpr (by decide), k912.gpr (by decide), k69.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide),
        k3.gpr (by decide), a1]
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [↓exec_mh, p2, (g15 .a4 (by decide)).trans ((g9 .a4 (by decide)).trans A4₅),
      (g15 .a6 (by decide)).trans ((g9 .a6 (by decide)).trans A6₅),
      (g15 .a5 (by decide)).trans ((g9 .a5 (by decide)).trans A5₅), (K15.gpr (r := .a0) (by decide)).trans ha0, e1,
      BitVec.add_zero]
  refine WP.mono r16 fun t ⟨⟨h7, y5, y6, b0, b1, m16⟩, k16⟩ => ?_
  obtain h7' : (t.gpr .s7).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 + (s₁₅.gpr .s0).toNat + hi57 (s₁₅.gpr .s4) M0 := by
    obtain y : (s₁₅.gpr .s7 + s₁₅.gpr .s0).toNat = hi57 (s₅.gpr .s2) M2 + hi57 (s₉.gpr .s3) M1 + (s₁₅.gpr .s0).toNat := by
      rw [k15.gpr (by decide), toNat_add_lt (by rw [h14', c2, n14, c1, n8, c0]; omega_arith), h14']
    rw [h7, toNat_add_lt (by rw [y, H2, c2, n14, c1, n8, c0]; omega_arith), y, H2]
  obtain gs2 : t.gpr .s2 = s₅.gpr .s2 := by rw [k16.gpr (by decide), g15 .s2 (by decide), g9 .s2 (by decide)]
  obtain gs3 : t.gpr .s3 = s₉.gpr .s3 := by rw [k16.gpr (by decide), g15 .s3 (by decide)]
  obtain gs4 : t.gpr .s4 = s₁₅.gpr .s4 := by rw [k16.gpr (by decide)]
  refine ⟨⟨⟨?_, ?_, ?_, by rw [gs2]; exact bu0, by rw [gs3]; exact bu1, by rw [gs4]; exact bu2⟩, b0, b1, ?_, by rw [y5]; exact n2,
    by rw [y6]; exact n1, ?_, ?_⟩, (K15.trans k16).mono (by decide)⟩
  · rw [gs2, k16.gpr (by decide), g15 .t2 (by decide), g9 .t2 (by decide), p0]
  · rw [gs3, k16.gpr (by decide), g15 .t3 (by decide), p1]
  · rw [gs4, k16.gpr (by decide), p2]
  · rw [h7', c2, n14, c1, n8, c0]; omega_arith
  · rw [m16, m15, m14, m13, m12, m11, m10, M9]
  · unfold cVal xVal
    rw [y5, y6, gs2, gs3, gs4]
    exact red_sum inv u0 c0 n8 u1 c1 n14 u2 c2 h7'

/-- The registers an operation writes. -/
def opRegs : List Reg :=
  [.t0, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .s0, .s1, .s2, .s3, .s4, .s7]

theorem ModIn.of {s t : State} {B : Addr} {q dM N o n Z : Nat} {rs : List Reg} (h : ModIn s B q dM N)
    (k : Keep rs s t) (h1 : Reg.t1 ∉ rs) (out : Outside B o n s.mem t.mem) (ho : dM + 72 * q + 24 ≤ o)
    (hs : Scr s B Z) (hZ : dM + 72 * q + 24 ≤ Z) (hq : 1 ≤ q) : ModIn t B q dM N := by
  have hn := hs.nowrap
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [out.lv (by omega_arith) (by omega_arith)]; exact h.val
  · exact out.lim (by omega_arith) (by omega_arith) h.lim
  · rw [out.lv (by omega_arith) (by omega_arith)]; exact h.pad
  · rw [k.gpr h1, out.word (by omega_arith) (by omega_arith)]; exact h.inv

theorem rowNext_ok {s : State} {B : Addr} {Z q dM d : Nat} (h : In s B Z q dM) (ha0 : s.gpr .a0 = off B (d + 72 * q)) :
    WP isa (.block rowNext) s fun t =>
      (t.gpr .a0 = off B d ∧ t.gpr .t3 = off B (oT q dM + 72 * q) ∧ t.mem = s.mem) ∧ Keep [.t2, .a0, .t3] s t := by
  unfold rowNext
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  obtain r : WP isa (.block [.sub .a0 .a0 .t2, .add .t3 .s5 .t2]) s₁ fun t =>
      (t.gpr .a0 = off B d ∧ t.gpr .t3 = off B (oT q dM + 72 * q) ∧ t.mem = s₁.mem) ∧ Keep [.a0, .t3] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, (k1.gpr (r := .a0) (by decide)).trans ha0, (k1.gpr (r := .s5) (by decide)).trans h.s5,
      off_sub B (show 72 * q ≤ d + 72 * q by omega_arith), Nat.add_sub_cancel]
  refine WP.mono r fun t ⟨⟨a0, t3, m2⟩, k2⟩ => ⟨⟨a0, t3, m2.trans m1⟩, (k1.trans k2).mono (by decide)⟩

theorem LimF.append {m : Mem} {B : Addr} {d j k : Nat} {f : Nat → Nat} (h : LimF m B d j f)
    (h' : LimF m B (d + 8 * j) k fun i => f (j + i)) : LimF m B d (j + k) f := fun i hi => by
  by_cases hj : i < j
  · exact h i hj
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hj)
    obtain l := h' c (by omega_arith)
    rw [Nat.mul_add, ← Nat.add_assoc]
    exact l

theorem xVal_lt {s : State} (h : Mult s) : xVal s < 2 ^ 171 := by
  obtain a := h.x0
  obtain b := h.x1
  obtain c := h.x2
  unfold L57 at a b c
  unfold xVal
  omega_using [a, b, c]

theorem lv_split3 (m : Mem) (B : Addr) (d k : Nat) : lv m B d (3 + k) = lv m B d 3 + 2 ^ 171 * lv m B (d + 24) k :=
  lv_append m B d 3 k

/-- After `b` blocks of the reduction of `T` from `s₀`. -/
structure Red (s₀ s : State) (B : Addr) (Z q dM N b : Nat) : Prop where
  ctx : In s B Z q dM
  mod : ModIn s B q dM N
  a0 : s.gpr .a0 = off B (oT q dM + 24 * b)
  out : Outside B (oT q dM) (144 * q) s₀.mem s.mem
  val : ∃ W, W < 2 ^ (171 * b) ∧ 2 ^ (171 * b) * lv s.mem B (oT q dM + 24 * b) (18 * q - 3 * b) =
    lv s₀.mem B (oT q dM) (18 * q) + W * N
  lim : Lim s.mem B (oT q dM + 24 * b) (18 * q - 3 * b) (L57 + b * rowMax)
  keep : Keep opRegs s₀ s

theorem red_step {P V V' T₀ W X N : Nat} (e : P * V = T₀ + W * N) (e' : 2 ^ 171 * V' = V + X * N) :
    P * 2 ^ 171 * V' = T₀ + (W + P * X) * N := by
  rw [Nat.mul_assoc, e', Nat.mul_add, e]
  grind

theorem redRows_ok {s : State} {B : Addr} {Z q dM N : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (lT : Lim s.mem B (oT q dM) (18 * q) L57) :
    WP isa redRows s fun t => Red s t B Z q dM N (3 * q) := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
  unfold redRows
  obtain r0 : WP isa (.block [.addi .a0 .s5 0]) s fun t => (t.gpr .a0 = off B (oT q dM) ∧ t.mem = s.mem) ∧ Keep [.a0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s5, BitVec.add_zero]
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  obtain hm1 : ModIn s₁ B q dM N := ⟨by rw [m1]; exact hm.val, by rw [m1]; exact hm.lim, by rw [m1]; exact hm.pad,
    by rw [m1, k1.gpr (by decide)]; exact hm.inv⟩
  refine ptr_loop (n := 3 * q) (by omega_using [q1]) (fun b t => Red s t B Z q dM N b) (fun b hb t ht => ?_)
    ⟨h.of k1 (by decide) (by decide), hm1, a0, by rw [m1]; exact Outside.refl _ _ _ _,
      ⟨0, Nat.one_pos, by rw [m1]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_mul, Nat.sub_zero]⟩,
      by rw [m1, Nat.zero_mul, Nat.mul_zero, Nat.sub_zero, Nat.add_zero, Nat.add_zero]; exact lT, k1.mono (by decide)⟩
  obtain hbm : b * rowMax ≤ 17 * rowMax := Nat.mul_le_mul_right _ (by omega_using [hb, q6])
  obtain sp : 18 * q - 3 * b = 3 + (9 * q + (9 * q - 3 * (b + 1))) := by omega_using [hb]
  obtain sp' : 18 * q - 3 * (b + 1) = 9 * q + (9 * q - 3 * (b + 1)) := by omega_using [hb]
  refine WP.seq (WP.mono (redHead_ok (d := oT q dM + 24 * b) (g := L57 + b * rowMax) ht.ctx ht.mod ht.a0
    (by unfold oT; omega_using [dM8]) (by unfold oT; omega_using [fit, hb]) (fun i hi => ht.lim i (by omega_using [hi, sp]))
    (by omega_using [hbm, hL, hR])) fun u ⟨⟨mu, ua0, ua1, u7, u5, u6, um, uv⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (rect_ok (e := .a7) (.inl rfl) (k := 3 * q) (f := fun _ => L57 + b * rowMax) (dT := oT q dM + 24 * b + 24)
    (dY := dM + 24) (ht.ctx.scr.congr ku.2.2) ua0 ua1
    (by rw [ku.gpr (by decide), ht.ctx.a7, show oA q dM = dM + 24 + 24 * (3 * q) by unfold oA; omega_using []])
    (by omega_using [q1]) (by unfold oT; omega_using [fit, hb]) (by omega_using [fit]) (by unfold oT; omega_using [dM8])
    (by omega_using [dM8]) (by unfold oT; omega_using []) mu u5 u6 ?_ ?_ u7 (fun i _ => by omega_using [hbm, hL, hR]))
    fun v hv => ?_)
  · intro i hi
    rw [um]
    by_cases hi' : i + 3 < 9 * q
    · rw [show dM + 24 + 8 * i = dM + 8 * (i + 3) by omega_using []]; exact ht.mod.lim _ hi'
    · obtain ⟨z0, z1, z2⟩ := lv_three_zero ht.mod.pad
      rcases (show i = 9 * q - 3 ∨ i = 9 * q - 2 ∨ i = 9 * q - 1 by omega_using [hi, hi']) with rfl | rfl | rfl
      · rw [show dM + 24 + 8 * (9 * q - 3) = dM + 72 * q by omega_using [q1], z0]; exact Nat.zero_le _
      · rw [show dM + 24 + 8 * (9 * q - 2) = dM + 72 * q + 8 by omega_using [q1], z1]; exact Nat.zero_le _
      · rw [show dM + 24 + 8 * (9 * q - 1) = dM + 72 * q + 16 by omega_using [q1], z2]; exact Nat.zero_le _
  · intro i hi
    rw [um, show oT q dM + 24 * b + 24 + 8 * i = oT q dM + 24 * b + 8 * (i + 3) by omega_using []]
    exact ht.lim _ (by omega_using [hi, hb])
  obtain kv := ku.trans hv.keep
  obtain cv := ht.ctx.of kv (by decide) (by decide)
  refine WP.mono (rowNext_ok (d := oT q dM + 24 * b + 24) cv (by rw [hv.a0, show oT q dM + 24 * b + 24 + 24 * (3 * q) =
    oT q dM + 24 * b + 24 + 72 * q by omega_using []])) fun w ⟨⟨wa0, wt3, wm⟩, kw⟩ => ?_
  obtain ov : Outside B (oT q dM + 24 * b + 24) (72 * q) t.mem w.mem := by
    rw [wm, ← um]; exact hv.out.mono (Nat.le_refl _) (by omega_using [])
  obtain ov' : Outside B (oT q dM) (144 * q) t.mem w.mem := ov.mono (by omega_using []) (by omega_using [hb])
  obtain kt := kv.trans kw
  obtain zc : cVal v = 0 := hv.zero (by omega_using [q1]) (by
    rw [um, show dM + 24 + 24 * (3 * q - 1) = dM + 72 * q by omega_using [q1]]; exact ht.mod.pad)
  obtain hMv : lv t.mem B dM 3 + 2 ^ 171 * lv t.mem B (dM + 24) (9 * q) = N := by
    rw [← lv_split3, Nat.add_comm, lv_append, show dM + 8 * (9 * q) = dM + 72 * q by omega_using [], ht.mod.pad, Nat.mul_zero,
      Nat.add_zero, ht.mod.val]
  obtain ev := hv.val
  rw [zc, Nat.mul_zero, Nat.add_zero, um, show 3 * (3 * q) = 9 * q by omega_using []] at ev
  obtain rest : lv w.mem B (oT q dM + 24 * b + 24 + 72 * q) (9 * q - 3 * (b + 1)) =
      lv t.mem B (oT q dM + 24 * b + 24 + 72 * q) (9 * q - 3 * (b + 1)) :=
    ov.lv (by omega_using []) (by unfold oT; omega_using [hn, fit, hb])
  obtain key : 2 ^ 171 * lv w.mem B (oT q dM + 24 * (b + 1)) (18 * q - 3 * (b + 1)) =
      lv t.mem B (oT q dM + 24 * b) (18 * q - 3 * b) + xVal u * N := by
    rw [sp, sp', lv_split3, show oT q dM + 24 * (b + 1) = oT q dM + 24 * b + 24 by omega_using [], lv_append, lv_append,
      show oT q dM + 24 * b + 24 + 8 * (9 * q) = oT q dM + 24 * b + 24 + 72 * q by omega_using [], rest, wm, ev, ← hMv]
    grind
  refine ⟨⟨cv.of kw (by decide) (by decide), ht.mod.of kt (by decide) ov' (by unfold oT; omega_using []) ht.ctx.scr
    (by omega_using [fit]) q1, by rw [wa0, show oT q dM + 24 * b + 24 = oT q dM + 24 * (b + 1) by omega_using []], ht.out.trans ov', ?_, ?_, Keep.trans' ht.keep (kt.mono (by decide))⟩, ?_⟩
  · obtain ⟨W, hW, eW⟩ := ht.val
    refine ⟨W + 2 ^ (171 * b) * xVal u, ?_, ?_⟩
    · rw [Nat.mul_succ, Nat.pow_add]
      obtain l := Nat.mul_le_mul_left (2 ^ (171 * b)) (xVal_lt mu)
      rw [Nat.mul_succ] at l
      omega_using [l, hW]
    · rw [Nat.mul_succ, Nat.pow_add]
      exact red_step eW key
  · refine (?_ : LimF w.mem B (oT q dM + 24 * (b + 1)) (18 * q - 3 * (b + 1)) fun _ => L57 + (b + 1) * rowMax)
    obtain es : L57 + (b + 1) * rowMax = L57 + b * rowMax + rowMax := by rw [Nat.succ_mul, Nat.add_assoc]
    rw [es, show oT q dM + 24 * (b + 1) = oT q dM + 24 * b + 24 by omega_using [], sp']
    refine LimF.append (by rw [wm]; exact (show 9 * q = 3 * (3 * q) by omega_using []) ▸ hv.lim) ?_
    intro i hi
    rw [ov.word (by omega_using []) (by unfold oT; omega_using [hn, fit, hb, hi]),
      show oT q dM + 24 * b + 24 + 8 * (9 * q) + 8 * i = oT q dM + 24 * b + 8 * (9 * q + i + 3) by omega_using []]
    exact Nat.le_trans (ht.lim _ (by omega_using [hi, hb])) (Nat.le_add_right _ _)
  · rw [wa0, wt3, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

end VG.Proof.Bignum.RISCV64.Pow57
