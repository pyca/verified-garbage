module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Bignum.Fios32
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

/-- The arithmetic of digit 0, on bit vectors: `x = t + a b`, `u = (x mod 2³²)
m' mod 2³²`, `y = x mod 2³² + u m`. -/
theorem head_arith (t a b m : BitVec 32) (m' : BitVec 64) (hm' : m'.toNat < 2 ^ 32) :
    let X := t.setWidth 64 + a.setWidth 64 * b.setWidth 64
    let L := (X.setWidth 32 >>> 0).setWidth 64
    let U := ((L * m').setWidth 32 >>> 0).setWidth 64
    let Y := L + U * m.setWidth 64
    let x := t.toNat + a.toNat * b.toNat
    let u := x % 2 ^ 32 * m'.toNat % 2 ^ 32
    (X >>> 32).toNat = x / 2 ^ 32 ∧ U.toNat = u ∧ (Y >>> 32).toNat = (x % 2 ^ 32 + u * m.toNat) / 2 ^ 32 := by
  intro X L U Y x u
  have ht := t.isLt
  have ha := a.isLt
  have hb := b.isLt
  have hm := m.isLt
  have e1 := Fios32.mac_lt ha hb ht (show 0 < 2 ^ 32 by decide)
  have hx := Nat.mod_lt x (show 0 < 2 ^ 32 by decide)
  have hu : u < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have e2 := Fios32.mac_lt hu hm hx (show 0 < 2 ^ 32 by decide)
  have p1 : (a.setWidth 64 * b.setWidth 64).toNat = a.toNat * b.toNat := by
    rw [toNat_mul_lt] <;> rw [toNat_ext32, toNat_ext32]; omega
  have vx : X.toNat = x := by
    simp only [X, x]
    rw [toNat_add_lt (by rw [toNat_ext32, p1]; omega), toNat_ext32, p1]
  have vl : L.toNat = x % 2 ^ 32 := by
    simp only [L]; rw [BitVec.ushiftRight_zero, toNat_lo32, vx]
  have vu : U.toNat = u := by
    simp only [U, u]
    rw [BitVec.ushiftRight_zero, toNat_lo32, toNat_mul_lt] <;> rw [vl]
    have : x % 2 ^ 32 * m'.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hm'
    omega
  have p2 : (U * m.setWidth 64).toNat = u * m.toNat := by
    rw [toNat_mul_lt] <;> rw [vu, toNat_ext32]; omega
  have vy : Y.toNat = x % 2 ^ 32 + u * m.toNat := by
    simp only [Y]
    rw [toNat_add_lt (by rw [vl, p2]; omega), vl, p2]
  exact ⟨by rw [toNat_shr32, vx], vu, by rw [toNat_shr32, vy]⟩

theorem ofNat_sub_one {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The registers `head` writes. -/
def headRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- Digit 0 of a round (`head`): `aᵢ` (at `da`) and the pointer past it, the
carries of digit 0 and `u`, the pointers at digit 0 and `n - 1` digits left. -/
theorem head_ok {s : State} {B : Addr} {Z da dA dB dM n : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h8 : s.gpr .r8 = off B dA) (h7 : s.gpr .r7 = off B dB)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 n)
    (h12 : (s.gpr .r12).toNat < 2 ^ 32) (hn : 1 ≤ n) (hn' : n < 2 ^ 64)
    (ha : da + 4 ≤ Z) (hA : dA + 4 ≤ Z) (hB : dB + 4 ≤ Z) (hM : dM + 4 ≤ Z) :
    WP isa (.block head) s fun s' =>
      let x := w32 s.mem B dA + w32 s.mem B da * w32 s.mem B dB
      let u := x % 2 ^ 32 * (s.gpr .r12).toNat % 2 ^ 32
      ((s'.gpr .r18).toNat = w32 s.mem B da ∧ s'.gpr .r6 = off B (da + 4) ∧
        (s'.gpr .r20).toNat = x / 2 ^ 32 ∧ (s'.gpr .r19).toNat = u ∧
        (s'.gpr .r22).toNat = (x % 2 ^ 32 + u * w32 s.mem B dM) / 2 ^ 32 ∧
        s'.gpr .r14 = off B dA ∧ s'.gpr .r15 = off B dB ∧ s'.gpr .r16 = off B dM ∧
        s'.gpr .r17 = BitVec.ofNat 64 (n - 1) ∧ s'.mem = s.mem) ∧ Keep headRegs s s' := by
  refine WP.keep headRegs ?_ (by decide)
  unfold head
  prun [h6, h8, h7, h10, h11, hs.ld ha, hs.ld hA, hs.ld hB, hs.ld hM]
  obtain ⟨k1, k2, k3⟩ := head_arith (s.mem.readW (off B dA) 32) (s.mem.readW (off B da) 32)
    (s.mem.readW (off B dB) 32) (s.mem.readW (off B dM) 32) _ h12
  refine ⟨toNat_ext32 _, k1, k2, k3, ?_⟩
  exact ofNat_sub_one hn hn'

/-- The arithmetic of the top digit, on bit vectors: `x = t + c₁`, `y = x mod
2³² + c₂`. -/
theorem top_arith (t : BitVec 32) (c₁ c₂ : BitVec 64) (hc1 : c₁.toNat < 2 ^ 32)
    (hc2 : c₂.toNat < 2 ^ 32) :
    let X := t.setWidth 64 + c₁
    let Y := (X.setWidth 32 >>> 0).setWidth 64 + c₂
    let x := t.toNat + c₁.toNat
    let y := x % 2 ^ 32 + c₂.toNat
    Y.setWidth 32 = BitVec.ofNat 32 y ∧
      (Y >>> 32 + X >>> 32).setWidth 32 = BitVec.ofNat 32 (x / 2 ^ 32 + y / 2 ^ 32) := by
  intro X Y x y
  have ht := t.isLt
  have hx := Nat.mod_lt x (show 0 < 2 ^ 32 by decide)
  have vx : X.toNat = x := by
    simp only [X, x]; rw [toNat_add_lt (by rw [toNat_ext32]; omega), toNat_ext32]
  have vy : Y.toNat = y := by
    simp only [Y, y]
    rw [BitVec.ushiftRight_zero, toNat_add_lt (by rw [toNat_lo32, vx]; omega), toNat_lo32, vx]
  refine ⟨by rw [lo32_ofNat, vy], ?_⟩
  rw [lo32_ofNat, toNat_add_lt (by rw [toNat_shr32, toNat_shr32, vx, vy]; omega), toNat_shr32,
    toNat_shr32, vx, vy, Nat.add_comm (y / 2 ^ 32)]

/-- The top digit of a round (`top`), the accumulator's pointer at digit `n -
1` (offset `dT`): `x = tₙ + c₁`, `y = x mod 2³² + c₂`, `y mod 2³²` stored at
digit `n - 1` and `x / 2³² + y / 2³²` at digit `n`. -/
theorem top_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (hT : dT + 8 ≤ Z) (hc1 : (s.gpr .r20).toNat < 2 ^ 32) (hc2 : (s.gpr .r22).toNat < 2 ^ 32) :
    WP isa (.block top) s fun s' =>
      let x := w32 s.mem B (dT + 4) + (s.gpr .r20).toNat
      let y := x % 2 ^ 32 + (s.gpr .r22).toNat
      s'.mem = (s.mem.writeW (off B dT) (BitVec.ofNat 32 y)).writeW (off B (dT + 4))
        (BitVec.ofNat 32 (x / 2 ^ 32 + y / 2 ^ 32)) ∧ Keep [.r0, .r20] s s' := by
  refine WP.keep [.r0, .r20] ?_ (by decide)
  unfold top
  prun [h14, hs.ld (show dT + 4 + 4 ≤ Z by omega), hs.st (show dT + 4 ≤ Z by omega),
    hs.st (show dT + 4 + 4 ≤ Z by omega)]
  obtain ⟨k1, k2⟩ := top_arith (s.mem.readW (off B (dT + 4)) 32) _ _ hc1 hc2
  rw [k1, k2]

/-- `cnt -= 1`. -/
theorem subi_ok (s : State) (r : Reg) (hr : r ≠ .r0) :
    WP isa (.block [.subi r r 1]) s fun s' => s' = s.write r (s.gpr r - BitVec.ofNat 64 1) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_subi (imm := 1) hr (by decide), runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-- A store of digit `j` of a number of `j + 1` digits. -/
theorem val32_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 32) (h : d + 4 * j + 4 ≤ 2 ^ 64) :
    val32 (m.writeW (off B (d + 4 * j)) v) B d (j + 1) = val32 m B d j + 2 ^ (32 * j) * v.toNat := by
  rw [val32_succ, (writeW32_outside m B v (by omega)).val32 (by omega) (by omega), w32_write_self]

/-- A digit `j + 1` of the accumulator's low digits is the `j + 1`-th. -/
theorem off_succ (dA j : Nat) : dA + 4 * j + 4 = dA + 4 * (j + 1) := by omega

theorem pow32_mul (j : Nat) : 2 ^ 32 * 2 ^ (32 * j) = 2 ^ (32 * (j + 1)) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- The pass of a round over digits `1` to `n - 1` (`countLoop .r17 step`),
from the pointers at digit 0 with the carries of digit 0: the low `n` digits
of `T + aᵢ b + u m` are `2³²` times the `n - 1` digits stored, from the
accumulator's offset `dA` on, plus the carries, at `2^(32 n)`. -/
theorem inner_ok {s₀ : State} {B : Addr} {Z dA dB dM n : Nat} (hs : Scr s₀ B Z)
    (h14 : s₀.gpr .r14 = off B dA) (h15 : s₀.gpr .r15 = off B dB) (h16 : s₀.gpr .r16 = off B dM)
    (h17 : s₀.gpr .r17 = BitVec.ofNat 64 (n - 1)) (hn : 2 ≤ n) (hn' : n < 2 ^ 64)
    (hA : dA + 4 * n ≤ Z) (hB : dB + 4 * n ≤ Z) (hM : dM + 4 * n ≤ Z)
    (dBA : dB + 4 * n ≤ dA ∨ dA + 4 * n ≤ dB) (dMA : dM + 4 * n ≤ dA ∨ dA + 4 * n ≤ dM)
    (ha : (s₀.gpr .r18).toNat < 2 ^ 32) (hu : (s₀.gpr .r19).toNat < 2 ^ 32)
    (hc1 : (s₀.gpr .r20).toNat < 2 ^ 32) (hc2 : (s₀.gpr .r22).toNat < 2 ^ 32)
    (h0 : w32 s₀.mem B dA + (s₀.gpr .r18).toNat * w32 s₀.mem B dB + (s₀.gpr .r19).toNat * w32 s₀.mem B dM =
      2 ^ 32 * ((s₀.gpr .r20).toNat + (s₀.gpr .r22).toNat)) :
    WP isa (countLoop .r17 step) s₀ fun s =>
      s.gpr .r14 = off B (dA + 4 * (n - 1)) ∧ (s.gpr .r20).toNat < 2 ^ 32 ∧
      (s.gpr .r22).toNat < 2 ^ 32 ∧ Outside B dA (4 * (n - 1)) s₀.mem s.mem ∧
      val32 s₀.mem B dA n + (s₀.gpr .r18).toNat * val32 s₀.mem B dB n +
        (s₀.gpr .r19).toNat * val32 s₀.mem B dM n =
        2 ^ 32 * val32 s.mem B dA (n - 1) + 2 ^ (32 * n) * ((s.gpr .r20).toNat + (s.gpr .r22).toNat) ∧
      Keep (stepRegs ++ ([.r17] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let ai := (s₀.gpr .r18).toNat
  let u := (s₀.gpr .r19).toNat
  let Inv : Nat → State → Prop := fun j s =>
    s.gpr .r14 = off B (dA + 4 * j) ∧ s.gpr .r15 = off B (dB + 4 * j) ∧
    s.gpr .r16 = off B (dM + 4 * j) ∧ (s.gpr .r20).toNat < 2 ^ 32 ∧ (s.gpr .r22).toNat < 2 ^ 32 ∧
    Outside B dA (4 * j) s₀.mem s.mem ∧
    val32 s₀.mem B dA (j + 1) + ai * val32 s₀.mem B dB (j + 1) + u * val32 s₀.mem B dM (j + 1) =
      2 ^ 32 * val32 s.mem B dA j + 2 ^ (32 * (j + 1)) * ((s.gpr .r20).toNat + (s.gpr .r22).toNat) ∧
    Keep (stepRegs ++ ([.r17] : List Reg)) s₀ s
  have hinv0 : Inv 0 s₀ := by
    refine ⟨by rw [h14]; rfl, by rw [h15]; rfl, by rw [h16]; rfl, hc1, hc2, Outside.refl _ _ _ _, ?_,
      Keep.refl _ _⟩
    simp only [val32, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
    exact h0
  have hfin := wp_countdown (body := .block (step ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := n - 1) (by omega) (by omega) Inv (fun j hj s hI hc => ?_) hinv0 h17
  · refine WP.mono hfin fun s ⟨i14, _, _, i20, i22, iout, ieq, ik⟩ => ⟨i14, i20, i22, iout, ?_, ik⟩
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at ieq
  obtain ⟨i14, i15, i16, i20, i22, iout, ieq, ik⟩ := hI
  have r18 : s.gpr .r18 = s₀.gpr .r18 := ik.gpr _ (by decide)
  have r19 : s.gpr .r19 = s₀.gpr .r19 := ik.gpr _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (step_ok (hs.congr ik.wr) i14 i15 i16 (by omega) (by omega) (by omega)
    (by rw [r18]; exact ha) (by rw [r19]; exact hu) i20 i22)
    fun s₁ ⟨⟨j14, j15, j16, j20, j22, jm⟩, k₁⟩ => ?_
  refine WP.mono (subi_ok s₁ .r17 (by decide)) fun s₂ e => ?_
  subst e
  -- The digits read are those on entry.
  have wt : w32 s.mem B (dA + 4 * j + 4) = w32 s₀.mem B (dA + 4 * j + 4) :=
    iout.w32 (by omega) (by omega)
  have wb : w32 s.mem B (dB + 4 * j + 4) = w32 s₀.mem B (dB + 4 * j + 4) :=
    iout.w32 (by omega) (by omega)
  have wm : w32 s.mem B (dM + 4 * j + 4) = w32 s₀.mem B (dM + 4 * j + 4) :=
    iout.w32 (by omega) (by omega)
  simp only [r18, r19, wt, wb, wm] at j20 j22 jm
  have hw := writeW32_outside s.mem B (d := dA + 4 * j)
    (BitVec.ofNat 32 ((w32 s₀.mem B (dA + 4 * j + 4) + ai * w32 s₀.mem B (dB + 4 * j + 4) +
      (s.gpr .r20).toNat) % 2 ^ 32 + u * w32 s₀.mem B (dM + 4 * j + 4) + (s.gpr .r22).toNat))
    (by omega)
  refine ⟨⟨by gsimp; rw [j14, off_succ], by gsimp; rw [j15, off_succ],
    by gsimp; rw [j16, off_succ], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · gsimp; rw [j20]
    exact Fios32.mac_div_lt ha (by exact (s₀.mem.readW _ 32).isLt)
      (by exact (s₀.mem.readW _ 32).isLt) i20
  · gsimp; rw [j22]
    exact Fios32.mac_div_lt (by exact hu) (by exact (s₀.mem.readW _ 32).isLt)
      (Nat.mod_lt _ (by decide)) i22
  · gsimp; rw [jm]
    exact (iout.mono (Nat.le_refl _) (by omega)).trans (hw.mono (by omega) (by omega))
  · gsimp
    rw [jm, j20, j22]
    rw [val32_write_top _ _ _ _ _ (by omega), BitVec.toNat_ofNat, val32_succ s₀.mem B dA (j + 1), val32_succ s₀.mem B dB (j + 1),
      val32_succ s₀.mem B dM (j + 1), ← off_succ, ← off_succ, ← off_succ, show 32 * (j + 1 + 1) = 32 * (j + 1) + 32 by omega,
      Nat.pow_add]
    exact Fios32.row_step (pow32_mul j) ieq (Fios32.step_eq _ _ _ _ _ _ _)
  · have k₂ : Keep [.r17] s₁ (s₁.write .r17 (s₁.gpr .r17 - BitVec.ofNat 64 1)) :=
      ⟨fun r hr => by
        simp only [gpr_write]
        exact ite_eq_right_iff.mpr fun h => absurd h fun h => hr (by simp [h]), rfl, rfl, rfl, rfl⟩
    exact ik.trans' ((k₁.mono (by decide)).trans' (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr _ (by decide)]

end VG.Proof.Bignum.PPC64LE
