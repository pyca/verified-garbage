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

/-! ## The carry pass -/

/-- After `i` limbs of a carry pass from `dS` to `dD`, from `s₀`. -/
structure Norm (s₀ s : State) (B : Addr) (dS dD i : Nat) : Prop where
  out : Outside B dD (8 * i) s₀.mem s.mem
  val : lv s.mem B dD i + 2 ^ (57 * i) * (s.gpr .t5).toNat = lv s₀.mem B dS i
  lim : Lim s.mem B dD i L57
  cy : (s.gpr .t5).toNat ≤ 2 ^ 10
  t6 : s.gpr .t6 = m57

/-- The registers a step of the carry pass writes. -/
def normRegs : List Reg := [.s0, .s1, .t5]

theorem norm_arith {x c : BitVec 64} (h : x.toNat + c.toNat < 2 ^ 64) :
    ((x + c) &&& m57).toNat ≤ L57 ∧ ((x + c) >>> 57).toNat ≤ 2 ^ 10 ∧
      ((x + c) &&& m57).toNat + 2 ^ 57 * ((x + c) >>> 57).toNat = x.toNat + c.toNat := by
  obtain e := toNat_add_lt h
  rw [and_m57, srl57, e]
  unfold L57
  omega_using [h]

theorem normStep_ok {s₀ s : State} {B : Addr} {Z dS dD i pS pD k n : Nat} (hs : Scr s B Z) (h : Norm s₀ s B dS dD i)
    (ha0 : s.gpr .a0 = off B pS) (ha1 : s.gpr .a1 = off B pD) (eS : pS + k = dS + 8 * i) (eD : pD + k = dD + 8 * i)
    (hi : i < n) (hk : k < 2048) (hS : dS + 8 * n ≤ Z) (hD : dD + 8 * n ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS = dD ∨ dS + 8 * n ≤ dD ∨ dD + 8 * n ≤ dS) (lS : LimF s₀.mem B dS n fun _ => 2 ^ 64 - 2 ^ 10 - 1) :
    WP isa (.block (normStep k)) s fun t => Norm s₀ t B dS dD (i + 1) ∧ Keep normRegs s t := by
  have hn := hs.nowrap
  obtain l : (word s₀.mem B (dS + 8 * i)).toNat ≤ 2 ^ 64 - 2 ^ 10 - 1 := lS i hi
  obtain cy := h.cy
  obtain rd : word s.mem B (dS + 8 * i) = word s₀.mem B (dS + 8 * i) :=
    h.out.word (by omega_using [sep, hi]) (by omega_using [hn, hS, hi])
  obtain ⟨a1, a2, a3⟩ := norm_arith (x := word s₀.mem B (dS + 8 * i)) (c := s.gpr .t5) (by omega_using [l, cy])
  obtain r : WP isa (.block (normStep k)) s fun t =>
      (t.mem = s.mem.writeW (off B (dD + 8 * i)) ((word s₀.mem B (dS + 8 * i) + s.gpr .t5) &&& m57) ∧
        t.gpr .t5 = (word s₀.mem B (dS + 8 * i) + s.gpr .t5) >>> 57) ∧ Keep normRegs s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold normStep
    brun [ha0, ha1, eS, eD, hk, h.t6, hs.ld (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]),
      hs.st (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]),
      hs.al8 (show dS + 8 * i + 8 ≤ Z by omega_using [hS, hi]) (by omega_using [hS8]),
      hs.al8 (show dD + 8 * i + 8 ≤ Z by omega_using [hD, hi]) (by omega_using [hD8]),
      show s.mem.readW (off B (dS + 8 * i)) 64 = word s₀.mem B (dS + 8 * i) from rd]
  refine WP.mono r fun t ⟨⟨mt, t5⟩, k⟩ => ⟨⟨?_, ?_, ?_, by rw [t5]; exact a2, (k.gpr (by decide)).trans h.t6⟩, k⟩
  · rw [mt]
    exact (h.out.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hn, hD, hi])).mono (by omega_using []) (by omega_using []))
  · obtain v := h.val
    rw [lv, lv, (show lv t.mem B dD i = lv s.mem B dD i by
      rw [mt]; exact (writeW_outside _ B _ (by omega_using [hn, hD, hi])).lv (by omega_using []) (by omega_using [hn, hD, hi])),
      mt, word_writeW_self, t5, ← v, Nat.mul_succ, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_assoc, ← Nat.mul_add,
      ← Nat.mul_add, a3, Nat.add_comm (s.gpr .t5).toNat]
  · refine LimF.append (j := i) (k := 1) ?_ ?_
    · rw [mt]
      exact (writeW_outside _ B _ (by omega_using [hn, hD, hi])).lim (by omega_using []) (by omega_using [hn, hD, hi]) h.lim
    · intro c hc
      obtain rfl : c = 0 := by omega_using [hc]
      rw [Nat.mul_zero, Nat.add_zero, mt, word_writeW_self]
      exact a1

theorem norm_ok {s : State} {B : Addr} {Z dS dD c : Nat} (hs : Scr s B Z) (ha0 : s.gpr .a0 = off B dS)
    (ha1 : s.gpr .a1 = off B dD) (h3 : s.gpr .t3 = off B (dS + 24 * c)) (hc : 0 < c) (hS : dS + 24 * c < Z)
    (hD : dD + 24 * c ≤ Z) (hS8 : dS % 8 = 0) (hD8 : dD % 8 = 0)
    (sep : dS = dD ∨ dS + 24 * c ≤ dD ∨ dD + 24 * c ≤ dS) (lS : LimF s.mem B dS (3 * c) fun _ => 2 ^ 64 - 2 ^ 10 - 1) :
    WP isa norm s fun t => (Outside B dD (24 * c) s.mem t.mem ∧
      (∃ k, lv t.mem B dD (3 * c) + 2 ^ (171 * c) * k = lv s.mem B dS (3 * c)) ∧ Lim t.mem B dD (3 * c) L57) ∧
        Keep ([.t6, .a0, .a1] ++ normRegs) s t := by
  have hn := hs.nowrap
  unfold norm
  obtain r0 : WP isa (.block (mask57 ++ ([.li .t5 0] : List Instr))) s fun t =>
      (t.gpr .t6 = m57 ∧ t.gpr .t5 = 0#64 ∧ t.mem = s.mem) ∧ Keep [.t6, .t5] s t := by
    rw [WP.block_append_iff]
    refine WP.mono (mask57_ok s) fun u ⟨⟨u6, um⟩, ku⟩ => ?_
    obtain r : WP isa (.block [.li .t5 0]) u fun t => (t.gpr .t5 = 0#64 ∧ t.mem = u.mem) ∧ Keep [.t5] u t :=
      WP.keep _ (by brun [exec_li]) (by rfl) (by rfl)
    exact WP.mono r fun t ⟨⟨t5, tm⟩, k⟩ => ⟨⟨(k.gpr (by decide)).trans u6, t5, tm.trans um⟩, (ku.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨t6, t5, m1⟩, k1⟩ => ?_)
  refine WP.mono (ptr_loop (a := .a0) (e := .t3) (n := c) hc (fun b t => Norm s t B dS dD (3 * b) ∧ t.gpr .a0 = off B (dS + 24 * b) ∧
      t.gpr .a1 = off B (dD + 24 * b) ∧ Keep ([.t6, .a0, .a1] ++ normRegs) s t) (fun b hb t ⟨ht, t0, t1, kt⟩ => ?_)
    ⟨⟨by rw [m1]; exact Outside.refl _ _ _ _, by rw [t5, m1]; rfl, fun i hi => absurd hi (by omega_using []), by rw [t5]; decide, t6⟩,
      (k1.gpr (by decide)).trans ha0, (k1.gpr (by decide)).trans ha1, k1.mono (by decide)⟩)
    fun t ⟨ht, _, _, kt⟩ => ⟨⟨ht.out.mono (Nat.le_refl _) (by omega_using []), ⟨(t.gpr .t5).toNat, ?_⟩, ht.lim⟩, kt⟩
  · rw [show (List.range 3).flatMap (fun k => normStep (8 * k)) = normStep 0 ++ (normStep 8 ++ normStep 16) by rfl]
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr kt.2.2) ht t0 t1 (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun u ⟨hu, ku⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr (kt.trans ku).2.2) hu ((ku.gpr (by decide)).trans t0)
      ((ku.gpr (by decide)).trans t1) (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun v ⟨hv, kv⟩ => ?_
    obtain kuv := ku.trans kv
    rw [WP.block_append_iff]
    refine WP.mono (normStep_ok (n := 3 * c) (hs.congr (kt.trans kuv).2.2) hv ((kuv.gpr (by decide)).trans t0)
      ((kuv.gpr (by decide)).trans t1) (by omega_using []) (by omega_using []) (by omega_using [hb]) (by decide)
      (by omega_using [hS]) (by omega_using [hD]) hS8 hD8 (by omega_using [sep]) lS) fun w ⟨hw, kw⟩ => ?_
    obtain kuw := kuv.trans kw
    obtain fin : WP isa (.block [.addi .a0 .a0 24, .addi .a1 .a1 24]) w fun v =>
        (v.gpr .a0 = off B (dS + 24 * b + 24) ∧ v.gpr .a1 = off B (dD + 24 * b + 24) ∧ v.mem = w.mem) ∧
          Keep [.a0, .a1] w v := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [(kuw.gpr (r := .a0) (by decide)).trans t0, (kuw.gpr (r := .a1) (by decide)).trans t1]
    refine WP.mono fin fun x ⟨⟨x0, x1, xm⟩, kx⟩ => ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    · rw [xm]; exact hw.out
    · rw [xm, kx.gpr (by decide)]; exact hw.val
    · rw [xm]; exact hw.lim
    · rw [kx.gpr (by decide)]; exact hw.cy
    · rw [kx.gpr (by decide)]; exact hw.t6
    · rw [x0, Nat.mul_succ, Nat.add_assoc]
    · rw [x1, Nat.mul_succ, Nat.add_assoc]
    · exact Keep.trans' kt ((kuw.trans kx).mono (by decide))
    · rw [x0, kx.gpr (by decide), kuw.gpr (by decide), kt.gpr (by decide), h3,
        off_inj (by omega_using [hn, hS, hb]) (by omega_using [hn, hS])]
      omega_using []
  · rw [← ht.val, show 57 * (3 * c) = 171 * c by omega_using []]

/-! ## Zeroing `T` -/

theorem lv_zero {m : Mem} {B : Addr} {d k : Nat} (h : Lim m B d k 0) : lv m B d k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lv, ih fun i hi => h i (by omega_using [hi]), Nat.eq_zero_of_le_zero (h k (Nat.lt_succ_self k))]
    rfl

theorem zeroT57_ok {s : State} {B : Addr} {Z q dM : Nat} (h : In s B Z q dM) :
    WP isa zeroT57 s fun t => (Outside B (oT q dM) (144 * q) s.mem t.mem ∧ Lim t.mem B (oT q dM) (18 * q) 0) ∧
      Keep [.t2, .t3, .t4, .s0] s t := by
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain q6 := h.q6
  have hn := h.scr.nowrap
  unfold zeroT57
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  obtain r : WP isa (.block [.shift .sll .d .t2 .t2 1, .add .t4 .s5 .t2, .addi .t3 .s5 0, .li .s0 0]) s₁ fun t =>
      (t.gpr .t4 = off B (oT q dM + 144 * q) ∧ t.gpr .t3 = off B (oT q dM) ∧ t.gpr .s0 = 0#64 ∧ t.mem = s₁.mem) ∧
        Keep [.t2, .t3, .t4, .s0] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    obtain e : BitVec.ofNat 64 (72 * q) <<< 1 = BitVec.ofNat 64 (144 * q) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_using []
    brun [x2, (k1.gpr (r := .s5) (by decide)).trans h.s5, e, exec_li, BitVec.add_zero]
  refine WP.mono r fun s₂ ⟨⟨t4, t3, s0, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (ptr_loop (a := .t3) (e := .t4) (n := 6 * q) (by have := h.q1; omega_using [this]) (fun b t => t.gpr .t3 = off B (oT q dM + 24 * b) ∧
      Outside B (oT q dM) (24 * b) s.mem t.mem ∧ Lim t.mem B (oT q dM) (3 * b) 0 ∧ t.gpr .s0 = 0#64 ∧
      t.gpr .t4 = off B (oT q dM + 144 * q) ∧
      Keep [.t2, .t3, .t4, .s0] s t) (fun b hb t ⟨h3, ho, hl, h0, h4, kt⟩ => ?_)
    ⟨t3, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun i hi => absurd hi (by omega_using []), s0, t4, k12.mono (by decide)⟩)
    fun t ⟨_, ho, hl, _, _, kt⟩ => ⟨⟨ho.mono (Nat.le_refl _) (by omega_using []), (show 18 * q = 3 * (6 * q) by omega_using []) ▸ hl⟩, kt⟩
  obtain hs := h.scr.congr kt.2.2
  obtain b1 : oT q dM + 24 * b + 24 ≤ Z := by unfold oT; omega_using [fit, hb]
  obtain b8 : (oT q dM + 24 * b) % 8 = 0 := by unfold oT; omega_using [dM8]
  obtain r : WP isa (.block [.store .d .s0 .t3 0, .store .d .s0 .t3 8, .store .d .s0 .t3 16, .addi .t3 .t3 24]) t fun u =>
      (u.mem = ((t.mem.writeW (off B (oT q dM + 24 * b)) 0#64).writeW (off B (oT q dM + 24 * b + 8)) 0#64).writeW
        (off B (oT q dM + 24 * b + 16)) 0#64 ∧ u.gpr .t3 = off B (oT q dM + 24 * b + 24)) ∧ Keep [.t3] t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3, h0, hs.st (show oT q dM + 24 * b + 8 ≤ Z by omega_using [b1]),
      hs.st (show oT q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]),
      hs.st (show oT q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]),
      hs.al8 (show oT q dM + 24 * b + 8 ≤ Z by omega_using [b1]) b8,
      hs.al8 (show oT q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8]),
      hs.al8 (show oT q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8])]
  refine WP.mono r fun u ⟨⟨um, u3⟩, ku⟩ => ?_
  obtain ou : Outside B (oT q dM + 24 * b) 24 t.mem u.mem := by
    rw [um]
    exact (((writeW_outside _ B _ (by omega_using [hn, b1])).mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW_outside _ B _ (by omega_using [hn, b1])).mono (by omega_using []) (by omega_using []))).trans
      ((writeW_outside _ B _ (by omega_using [hn, b1])).mono (by omega_using []) (by omega_using []))
  refine ⟨⟨by rw [u3, Nat.mul_succ, Nat.add_assoc], (ho.mono (Nat.le_refl _) (by omega_using [])).trans
    (ou.mono (by omega_using []) (by omega_using [])), ?_, (ku.gpr (by decide)).trans h0, (ku.gpr (by decide)).trans h4,
    Keep.trans' kt (ku.mono (by decide))⟩, ?_⟩
  · refine LimF.append (j := 3 * b) (k := 3) (ou.lim (by omega_using []) (by omega_using [hn, b1]) hl) ?_
    rw [show oT q dM + 8 * (3 * b) = oT q dM + 24 * b by omega_using []]
    intro i hi
    rw [um]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
    · rw [show oT q dM + 24 * b + 8 * 0 = oT q dM + 24 * b by omega_using [], wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]),
        wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]), word_writeW_self]
      exact Nat.le_refl 0
    · rw [Nat.mul_one, wd_ne _ B _ (by omega_using []) (by omega_using [hn, b1]) (by omega_using [hn, b1]), word_writeW_self]
      exact Nat.le_refl 0
    · rw [word_writeW_self]
      exact Nat.le_refl 0
  · rw [u3, ku.gpr (by decide), h4, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

/-! ## The whole reduction -/

/-- The number `a` in `A`. -/
structure AIn (m : Mem) (B : Addr) (q dM a : Nat) : Prop where
  val : lv m B (oA q dM) (9 * q) = a
  lim : Lim m B (oA q dM) (9 * q) L57
  pad : lv m B (oA q dM + 72 * q) 3 = 0

/-- What the reduction writes: `A` and `T`. -/
abbrev OutAT (B : Addr) (q dM : Nat) (m m' : Mem) : Prop := Outside B (oA q dM) (216 * q + 24) m m'

theorem outT {B : Addr} {q dM : Nat} {m m' : Mem} (h : Outside B (oT q dM) (144 * q) m m') : OutAT B q dM m m' :=
  Outside.mono h (by unfold oA oT; omega_using []) (by unfold oA oT; omega_using [])

theorem reduce57_ok {s : State} {B : Addr} {Z q dM N V : Nat} (h : In s B Z q dM) (hm : ModIn s B q dM N)
    (lT : Lim s.mem B (oT q dM) (18 * q) L57) (eV : lv s.mem B (oT q dM) (18 * q) = V)
    (hV : V + 2 ^ (513 * q) * N ≤ 2 ^ (513 * q) * 2 ^ (513 * q)) (hN : 0 < N)
    (pad : lv s.mem B (oA q dM + 72 * q) 3 = 0) :
    WP isa reduce57 s fun t => (In t B Z q dM ∧ ModIn t B q dM N ∧ OutAT B q dM s.mem t.mem ∧
      ∃ a W, AIn t.mem B q dM a ∧ W < 2 ^ (513 * q) ∧ 2 ^ (513 * q) * a = V + W * N) ∧ Keep opRegs s t := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  unfold reduce57
  refine WP.seq (WP.mono (redRows_ok h hm lT) fun s₁ hr => ?_)
  obtain ⟨W, hW, eW⟩ := hr.val
  rw [eV, show 171 * (3 * q) = 513 * q by omega_using [], show 18 * q - 3 * (3 * q) = 9 * q by omega_using [],
    show oT q dM + 24 * (3 * q) = oT q dM + 72 * q by omega_using []] at eW
  rw [show 171 * (3 * q) = 513 * q by omega_using []] at hW
  obtain rl := hr.lim
  rw [show 18 * q - 3 * (3 * q) = 9 * q by omega_using [], show oT q dM + 24 * (3 * q) = oT q dM + 72 * q by omega_using []] at rl
  obtain X : lv s₁.mem B (oT q dM + 72 * q) (9 * q) < 2 ^ (513 * q) := by
    obtain l := (Nat.mul_lt_mul_right hN).mpr hW
    exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ (513 * q)) (by rw [eW]; omega_using [l, hV])
  obtain r : WP isa (.block (limbs ++ [.add .a0 .s5 .t2, .addi .a1 .a7 0, .add .t3 .a0 .t2])) s₁ fun t =>
      (t.gpr .a0 = off B (oT q dM + 72 * q) ∧ t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oT q dM + 72 * q + 72 * q) ∧ t.mem = s₁.mem) ∧ Keep [.t2, .a0, .a1, .t3] s₁ t := by
    rw [WP.block_append_iff]
    refine WP.mono (limbs_ok hr.ctx) fun u ⟨⟨x2, um⟩, ku⟩ => ?_
    obtain r : WP isa (.block [.add .a0 .s5 .t2, .addi .a1 .a7 0, .add .t3 .a0 .t2]) u fun t =>
      (t.gpr .a0 = off B (oT q dM + 72 * q) ∧ t.gpr .a1 = off B (oA q dM) ∧
        t.gpr .t3 = off B (oT q dM + 72 * q + 72 * q) ∧ t.mem = u.mem) ∧ Keep [.a0, .a1, .t3] u t := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [x2, (ku.gpr (r := .s5) (by decide)).trans hr.ctx.s5, (ku.gpr (r := .a7) (by decide)).trans hr.ctx.a7, BitVec.add_zero]
    exact WP.mono r fun t ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c, d.trans um⟩, (ku.trans k).mono (by decide)⟩
  refine WP.seq (WP.mono r fun s₂ ⟨⟨a0, a1, t3, m2⟩, k2⟩ => ?_)
  obtain K2 := hr.keep.trans k2
  refine WP.mono (norm_ok (c := 3 * q) (dS := oT q dM + 72 * q) (dD := oA q dM) (h.scr.congr K2.2.2) a0 a1
    (by rw [t3, show 24 * (3 * q) = 72 * q by omega_using []]) (by omega_using [q1]) (by unfold oT; omega_using [fit])
    (by unfold oA; omega_using [fit]) (by unfold oT; omega_using [dM8]) (by unfold oA; omega_using [dM8])
    (by unfold oA oT; omega_using []) (by
      rw [m2, show 3 * (3 * q) = 9 * q by omega_using []]
      intro i hi
      refine Nat.le_trans (rl i hi) ?_
      obtain b : 3 * q * rowMax ≤ 18 * rowMax := Nat.mul_le_mul_right _ (by omega_using [q6])
      obtain hL : L57 = 2 ^ 57 - 1 := rfl
      obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
      show L57 + 3 * q * rowMax ≤ 2 ^ 64 - 2 ^ 10 - 1
      omega_using [b, hL, hR])) fun t ⟨⟨ot, ⟨k, et⟩, lt⟩, kt⟩ => ?_
  rw [m2] at ot et
  rw [show 3 * (3 * q) = 9 * q by omega_using [], show 171 * (3 * q) = 513 * q by omega_using []] at et
  rw [show 3 * (3 * q) = 9 * q by omega_using []] at lt
  rw [show 24 * (3 * q) = 72 * q by omega_using []] at ot
  obtain hk : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · obtain l := Nat.le_mul_of_pos_right (2 ^ (513 * q)) h
      omega_using [l, et, X]
  subst hk
  rw [Nat.mul_zero, Nat.add_zero] at et
  obtain KT := K2.trans kt
  refine ⟨⟨h.of (KT.mono (rs' := opRegs) (by decide)) (by decide) (by decide), ?_, ?_, _, W, ⟨rfl, lt, ?_⟩, hW, by rw [et]; exact eW⟩, KT.mono (by decide)⟩
  · exact hr.mod.of (k2.trans kt) (by decide) ot (by unfold oA; omega_using []) (h.scr.congr hr.keep.2.2)
      (by omega_using [fit]) q1
  · exact (outT hr.out).trans (ot.mono (Nat.le_refl _) (by omega_using []))
  · rw [ot.lv (by omega_using []) (by unfold oA; omega_using [hn, fit]),
      hr.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit])]
    exact pad

/-! ## The product -/

theorem lv_seg {m m' : Mem} {B : Addr} {d j k r δ : Nat} (out : Outside B (d + 8 * j) (8 * k) m m')
    (e : lv m' B (d + 8 * j) k = lv m B (d + 8 * j) k + δ) (hd : d + 8 * (j + k + r) ≤ 2 ^ 64) :
    lv m' B d (j + k + r) = lv m B d (j + k + r) + 2 ^ (57 * j) * δ := by
  rw [lv_append, lv_append m', lv_append m, lv_append m, e,
    out.lv (d := d) (by omega_using []) (by omega_using [hd]),
    out.lv (d := d + 8 * (j + k)) (by omega_using []) (by omega_using [hd]), Nat.mul_add]
  omega_using []

theorem lim_seg {m m' : Mem} {B : Addr} {d j k r : Nat} {f g : Nat → Nat} (out : Outside B (d + 8 * j) (8 * k) m m')
    (h : LimF m B d (j + k + r) f) (h' : LimF m' B (d + 8 * j) k fun i => g (j + i)) (hfg : ∀ i, f i ≤ g i)
    (hd : d + 8 * (j + k + r) ≤ 2 ^ 64) : LimF m' B d (j + k + r) g := by
  refine LimF.append (LimF.append ?_ h') ?_
  · intro i hi
    rw [out.word (by omega_using [hi]) (by omega_using [hi, hd])]
    exact Nat.le_trans (h i (by omega_using [hi])) (hfg i)
  · intro i hi
    rw [out.word (by omega_using []) (by omega_using [hi, hd]), show d + 8 * (j + k) + 8 * i = d + 8 * (j + k + i) by omega_using []]
    exact Nat.le_trans (h (j + k + i) (by omega_using [hi])) (hfg _)

theorem zeros (s : State) : WP isa (.block [.li .t5 0, .li .t6 0, .li .s7 0, .addi .a1 .a7 0]) s fun t =>
    (t.gpr .t5 = 0#64 ∧ t.gpr .t6 = 0#64 ∧ t.gpr .s7 = 0#64 ∧ t.gpr .a1 = s.gpr .a7 ∧ t.mem = s.mem) ∧
      Keep [.t5, .t6, .s7, .a1] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [exec_li, BitVec.add_zero]

theorem rectX_ok (s : State) : WP isa (.block rectX) s fun t => (t.gpr .t2 = s.gpr .s2 <<< 7 ∧ t.gpr .t3 = s.gpr .s3 <<< 7 ∧
    t.gpr .t4 = s.gpr .s4 <<< 7 ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .t4] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold rectX
  brun

theorem shl1 (n : Nat) (h : n < 2 ^ 63) : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using [h]

def mulHeadRegs : List Reg := [.t2, .a2, .s2, .s3, .s4, .t3, .t4, .t5, .t6, .s7, .a1]

theorem mulHead_ok {s : State} {B : Addr} {Z q dM b : Nat} (h : In s B Z q dM) (ha0 : s.gpr .a0 = off B (oT q dM + 24 * b))
    (hb : b < 3 * q) (lE : Lim s.mem B (oE q dM) (9 * q) L57) :
    WP isa (.block mulHead) s fun t =>
      (Mult t ∧ t.gpr .a1 = off B (oA q dM) ∧ t.gpr .s7 = 0#64 ∧ t.gpr .t5 = 0#64 ∧ t.gpr .t6 = 0#64 ∧
        xVal t = lv s.mem B (oE q dM + 24 * b) 3 ∧ t.mem = s.mem) ∧ Keep mulHeadRegs s t := by
  obtain fit := h.fit
  obtain dM8 := h.dM8
  obtain q6 := h.q6
  unfold mulHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (limbs_ok h) fun s₁ ⟨⟨x2, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  obtain hs := h.scr.congr k1.2.2
  obtain b1 : oE q dM + 24 * b + 24 ≤ Z := by unfold oE; omega_using [fit, hb]
  obtain b8 : (oE q dM + 24 * b) % 8 = 0 := by unfold oE; omega_using [dM8]
  obtain r : WP isa (.block [.shift .sll .d .t2 .t2 1, .add .a2 .a0 .t2, .load .d .s2 .a2 0, .load .d .s3 .a2 8,
      .load .d .s4 .a2 16]) s₁ fun t => (t.gpr .s2 = word s.mem B (oE q dM + 24 * b) ∧
        t.gpr .s3 = word s.mem B (oE q dM + 24 * b + 8) ∧ t.gpr .s4 = word s.mem B (oE q dM + 24 * b + 16) ∧ t.mem = s₁.mem) ∧
      Keep [.t2, .a2, .s2, .s3, .s4] s₁ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [x2, shl1 (72 * q) (by omega_using [q6]), (k1.gpr (r := .a0) (by decide)).trans ha0,
      show oT q dM + 24 * b + 2 * (72 * q) = oE q dM + 24 * b by unfold oT oE; omega_using [], m1,
      hs.ld (show oE q dM + 24 * b + 8 ≤ Z by omega_using [b1]), hs.ld (show oE q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]),
      hs.ld (show oE q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]), hs.al8 (show oE q dM + 24 * b + 8 ≤ Z by omega_using [b1]) b8,
      hs.al8 (show oE q dM + 24 * b + 8 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8]),
      hs.al8 (show oE q dM + 24 * b + 16 + 8 ≤ Z by omega_using [b1]) (by omega_using [b8])]
  refine WP.mono r fun s₂ ⟨⟨x0, x1, x2', m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rectX_ok s₂) fun s₃ ⟨⟨p0, p1, p2, m3⟩, k3⟩ => ?_
  refine WP.mono (zeros s₃) fun t ⟨⟨t5, t6, t7, a1, m4⟩, k4⟩ => ?_
  obtain K4 := ((k1.trans k2).trans k3).trans k4
  obtain g : ∀ r ∈ [Reg.s2, .s3, .s4], t.gpr r = s₂.gpr r := fun r hr => (k3.trans k4).gpr (by revert r hr; decide)
  obtain l0 := lE (3 * b) (by omega_using [hb])
  obtain l1 := lE (3 * b + 1) (by omega_using [hb])
  obtain l2 := lE (3 * b + 2) (by omega_using [hb])
  rw [show oE q dM + 8 * (3 * b) = oE q dM + 24 * b by omega_using []] at l0
  rw [show oE q dM + 8 * (3 * b + 1) = oE q dM + 24 * b + 8 by omega_using []] at l1
  rw [show oE q dM + 8 * (3 * b + 2) = oE q dM + 24 * b + 16 by omega_using []] at l2
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, t7, t5, t6, ?_, by rw [m4, m3, m2, m1]⟩, K4.mono (by decide)⟩
  · rw [k4.gpr (by decide), p0, g .s2 (by decide)]
  · rw [k4.gpr (by decide), p1, g .s3 (by decide)]
  · rw [k4.gpr (by decide), p2, g .s4 (by decide)]
  · rw [g .s2 (by decide), x0]; exact l0
  · rw [g .s3 (by decide), x1]; exact l1
  · rw [g .s4 (by decide), x2']; exact l2
  · rw [a1, k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), h.a7]
  · unfold xVal
    rw [g .s2 (by decide), g .s3 (by decide), g .s4 (by decide), x0, x1, x2', lv_three]

/-- After `b` blocks of the product `T = A E`, from `s₀`. -/
structure MulI (s₀ s : State) (B : Addr) (Z q dM b : Nat) : Prop where
  ctx : In s B Z q dM
  a0 : s.gpr .a0 = off B (oT q dM + 24 * b)
  out : Outside B (oT q dM) (144 * q) s₀.mem s.mem
  val : lv s.mem B (oT q dM) (18 * q) = lv s₀.mem B (oA q dM) (9 * q) * lv s₀.mem B (oE q dM) (3 * b)
  lim : Lim s.mem B (oT q dM) (18 * q) (b * rowMax)
  keep : Keep opRegs s₀ s

theorem cVal_zero {s : State} (h7 : s.gpr .s7 = 0#64) (h5 : s.gpr .t5 = 0#64) (h6 : s.gpr .t6 = 0#64) : cVal s = 0 := by
  unfold cVal
  rw [h7, h5, h6]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]

theorem AIn.pads {m : Mem} {B : Addr} {q dM a : Nat} (h : AIn m B q dM a) : lv m B (oA q dM) (9 * q + 3) = a := by
  rw [lv_append, show oA q dM + 8 * (9 * q) = oA q dM + 72 * q by omega_using [], h.pad, h.val, Nat.mul_zero, Nat.add_zero]

theorem pad_lim {m : Mem} {B : Addr} {d k : Nat} (h : Lim m B d k L57) (p : lv m B (d + 8 * k) 3 = 0) : Lim m B d (k + 3) L57 := by
  refine LimF.append h fun i hi => ?_
  obtain ⟨z0, z1, z2⟩ := lv_three_zero p
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero, z0]; exact Nat.zero_le _
  · rw [Nat.mul_one, z1]; exact Nat.zero_le _
  · rw [z2]; exact Nat.zero_le _

theorem mulRows_ok {s : State} {B : Addr} {Z q dM a : Nat} (h : In s B Z q dM) (hA : AIn s.mem B q dM a)
    (lE : Lim s.mem B (oE q dM) (9 * q) L57) (lT : Lim s.mem B (oT q dM) (18 * q) 0) :
    WP isa mulRows s fun t => MulI s t B Z q dM (3 * q) := by
  obtain q1 := h.q1
  obtain q6 := h.q6
  obtain fit := h.fit
  obtain dM8 := h.dM8
  have hn := h.scr.nowrap
  obtain hL : L57 = 2 ^ 57 - 1 := rfl
  obtain hR : rowMax = 6 * L57 + 2 ^ 10 := rfl
  unfold mulRows
  obtain r0 : WP isa (.block [.addi .a0 .s5 0]) s fun t => (t.gpr .a0 = off B (oT q dM) ∧ t.mem = s.mem) ∧ Keep [.a0] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h.s5, BitVec.add_zero]
  refine WP.seq (WP.mono r0 fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  refine ptr_loop (n := 3 * q) (by omega_using [q1]) (fun b t => MulI s t B Z q dM b) (fun b hb t ht => ?_)
    ⟨h.of k1 (by decide) (by decide), a0, by rw [m1]; exact Outside.refl _ _ _ _, by
      rw [m1, lv_zero lT]; rfl, by rw [m1, Nat.zero_mul]; exact lT, k1.mono (by decide)⟩
  obtain hbm : b * rowMax ≤ 17 * rowMax := Nat.mul_le_mul_right _ (by omega_using [hb, q6])
  obtain sp : 18 * q = 3 * b + (9 * q + 3) + (9 * q - 3 * (b + 1)) := by omega_using [hb]
  obtain ht18 := ht.lim
  refine WP.seq (WP.mono (mulHead_ok ht.ctx ht.a0 hb (ht.out.lim (by unfold oE oT; omega_using []) (by unfold oE; omega_using [hn, fit]) lE))
    fun u ⟨⟨mu, ua1, u7, u5, u6, ux, um⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (rect_ok (e := .s5) (.inr rfl) (k := 3 * q + 1) (f := fun _ => b * rowMax) (dT := oT q dM + 24 * b)
    (dY := oA q dM) (ht.ctx.scr.congr ku.2.2) ((ku.gpr (by decide)).trans ht.a0) ua1
    (by rw [ku.gpr (by decide), ht.ctx.s5, show oT q dM = oA q dM + 24 * (3 * q + 1) by unfold oA oT; omega_using []])
    (by omega_using []) (by unfold oT; omega_using [fit, hb]) (by unfold oA; omega_using [fit, q1]) (by unfold oT; omega_using [dM8])
    (by unfold oA; omega_using [dM8]) (by unfold oA oT; omega_using []) mu (by rw [u5]; decide) (by rw [u6]; decide) ?_ ?_
    (by rw [u7]; decide) (fun i _ => by omega_using [hbm, hL, hR]))
    fun v hv => ?_)
  · rw [um, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using []]
    exact ht.out.lim (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])
      (pad_lim hA.lim (by rw [show oA q dM + 8 * (9 * q) = oA q dM + 72 * q by omega_using []]; exact hA.pad))
  · intro i hi
    rw [um, show oT q dM + 24 * b + 8 * i = oT q dM + 8 * (3 * b + i) by omega_using []]
    exact ht18 (3 * b + i) (by omega_using [hi, hb])
  obtain kv := ku.trans hv.keep
  obtain cv := ht.ctx.of kv (by decide) (by decide)
  refine WP.mono (rowNext_ok (d := oT q dM + 24 * b + 24) cv (by rw [hv.a0, show oT q dM + 24 * b + 24 * (3 * q + 1) =
    oT q dM + 24 * b + 24 + 72 * q by omega_using []])) fun w ⟨⟨wa0, wt3, wm⟩, kw⟩ => ?_
  obtain ov : Outside B (oT q dM + 8 * (3 * b)) (8 * (9 * q + 3)) t.mem w.mem := by
    rw [wm, ← um]; exact hv.out.mono (by omega_using []) (by omega_using [])
  obtain ov' : Outside B (oT q dM) (144 * q) t.mem w.mem := ov.mono (by omega_using []) (by omega_using [hb])
  obtain kt := kv.trans kw
  obtain eA : lv t.mem B (oA q dM) (9 * q + 3) = a := by
    rw [ht.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])]; exact hA.pads
  obtain zc : cVal v = 0 := hv.zero (by omega_using []) (by
    rw [um, show oA q dM + 24 * (3 * q + 1 - 1) = oA q dM + 72 * q by omega_using [],
      ht.out.lv (by unfold oA oT; omega_using []) (by unfold oA; omega_using [hn, fit, q1])]
    exact hA.pad)
  obtain ev := hv.val
  rw [zc, Nat.mul_zero, Nat.add_zero, um, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using [], cVal_zero u7 u5 u6, Nat.add_zero, eA, ux,
    show oT q dM + 24 * b = oT q dM + 8 * (3 * b) by omega_using [], ← wm,
    ht.out.lv (d := oE q dM + 24 * b) (by unfold oE oT; omega_using []) (by unfold oE; omega_using [hn, fit, hb])] at ev
  obtain bd : oT q dM + 8 * (3 * b + (9 * q + 3) + (9 * q - 3 * (b + 1))) ≤ 2 ^ 64 := by
    rw [← sp]; unfold oT; omega_using [hn, fit]
  refine ⟨⟨cv.of kw (by decide) (by decide), by rw [wa0, show oT q dM + 24 * b + 24 = oT q dM + 24 * (b + 1) by omega_using []],
    ht.out.trans ov', ?_, ?_, Keep.trans' ht.keep (kt.mono (by decide))⟩, ?_⟩
  · rw [sp, lv_seg ov ev bd, ← sp, ht.val, hA.val, show 3 * (b + 1) = 3 * b + 3 from rfl, lv_append,
      show oE q dM + 8 * (3 * b) = oE q dM + 24 * b by omega_using []]
    grind
  · rw [sp] at ht18 ⊢
    refine lim_seg ov ht18 ?_ (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ b)) bd
    obtain l := hv.lim
    rw [← wm, show 3 * (3 * q + 1) = 9 * q + 3 by omega_using [], show oT q dM + 24 * b = oT q dM + 8 * (3 * b) by omega_using [],
      ← Nat.succ_mul] at l
    exact l
  · rw [wa0, wt3, off_inj (by unfold oT; omega_using [hn, fit, hb]) (by unfold oT; omega_using [hn, fit])]
    omega_using []

end VG.Proof.Bignum.RISCV64.Pow57
