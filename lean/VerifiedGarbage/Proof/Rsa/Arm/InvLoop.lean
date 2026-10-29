module

public import VerifiedGarbage.Proof.Rsa.Arm.InvStep
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath
import Batteries.Tactic.Alias

/-! # `inverse` on ARMv7: `32 w` iterations of two steps

`inverse_ok`: from `(a, m, 1, 0)` in arrays 0–3, for an odd `m > 1`, array 1
ends as `gcd(a, m)` and array 3 as `x < m` with `x a ≡ gcd(a, m) (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (invIter InvI)

alias invI_start' := VG.Proof.Rsa.invI_start'

/-- The arrays and header words `inverse` writes. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]

/-- The state after `i` iterations. -/
structure InvLoopI (s0 : State) (B : BitVec 32) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Keep B w invArrs invSlots s0.mem t.mem
  rest : Rest (.r6 :: opRegs) s0 t
  count : t.gpr .r6 = BitVec.ofNat 32 (32 * w - i)
  value : num s0.mem B w aNM + num s0.mem B w aM = 2 ^ (32 * w) → num s0.mem B w aZero = 0 →
    num s0.mem B w aM % 2 = 1 → 1 < num s0.mem B w aM →
    bank s0.mem B w 0 = (num s0.mem B w 0, num s0.mem B w aM, 1, 0) →
    bank t.mem B w 0 = invIter (num s0.mem B w aM) (2 * i) (bank s0.mem B w 0)

theorem inverseBody_ok {s0 t : State} {B : BitVec 32} {Z w N i : Nat} (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (inv : InvLoopI s0 B Z w N i t) (hi : i < 32 * w) :
    WP isa (.seq (VG.Impl.Rsa.Arm.Keys.invStep 0 4) (.seq (VG.Impl.Rsa.Arm.Keys.invStep 4 0)
      (.block [.subs .r6 .r6 (.imm 1)]))) t fun u =>
      InvLoopI s0 B Z w N (i + 1) u ∧ u.z = decide (i + 1 = 32 * w) := by
  have h := inv.ws
  have fM := h.fit64 (j := aM) (by idx)
  have fNM := h.fit64 (j := aNM) (by idx)
  have fZ := h.fit64 (j := aZero) (by idx)
  have f0 := h.fit64 (j := 0) (by idx)
  have keepM : ∀ {m m' : Mem} {js ds : List Nat}, Keep B w js ds m m' → (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) →
      (∀ d ∈ ds, d + 4 ≤ hdr) → num m' B w aM = num m B w aM ∧ num m' B w aNM = num m B w aNM ∧
        num m' B w aZero = num m B w aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 hN (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 hN (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine wp_subs (op2_imm (by decide)) fun u u3 hz => WP.block_nil ?_
  have r6 : t2.gpr .r6 = t.gpr .r6 := (r2.gpr _ (by decide)).trans (r1.gpr _ (by decide))
  have m2 : u.mem = t2.mem := u3.mem
  refine ⟨⟨h2.of_upd u3 (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (u3.rest (by simp))))
  · rw [u3.gpr, r6, inv.count]
    change BitVec.ofNat 32 (32 * w - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by have := h.wle; omega_arith)]
    congr 1
  · intro hNM hZ hodd h1M hst
    have prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by idx)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by idx)
    have I := VG.Proof.Rsa.invIter_inv hodd (invI_start' (a := num s0.mem B w 0) hodd h1M) (2 * i)
    rw [← hst, ← prev] at I
    have s1 := e1 (by rw [n0, m0]; exact hNM) (by rw [z0]; exact hZ)
      (by rw [m0]; exact I.x₁_lt) (by rw [m0]; exact I.x₂_lt)
    rw [m0] at s1
    have I1 := VG.Proof.Rsa.invStep_inv hodd I
    rw [← s1] at I1
    have s2 := e2 (by rw [n1, m1, n0, m0]; exact hNM) (by rw [z1, z0]; exact hZ)
      (by rw [m1, m0]; exact I1.x₁_lt) (by rw [m1, m0]; exact I1.x₂_lt)
    rw [m1, m0, s1, prev] at s2
    rw [m2, s2, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    rfl
  · rw [hz, r6, inv.count]
    change (BitVec.ofNat 32 (32 * w - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by have := h.wle; omega_arith), ofNat_beq_zero (by have := h.wle; omega_arith)]
    simp only [show 32 * w - i - 1 = 0 ↔ i + 1 = 32 * w by omega_arith]

theorem inverse_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256) :
    WP isa VG.Impl.Rsa.Arm.Keys.inverse s fun t => Ws t B Z w N ∧ Keep B w invArrs invSlots s.mem t.mem ∧
      Rest (.r6 :: opRegs) s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        num t.mem B w 1 = Nat.gcd (num s.mem B w 0) (num s.mem B w aM) ∧
        (num s.mem B w aM : Int) ∣ (num t.mem B w 3 : Int) * num s.mem B w 0 - num t.mem B w 1 ∧
        num t.mem B w 3 < num s.mem B w aM) := by
  rw [inverse, WP.seq_iff]
  refine wp_mov (op2_lsl (by decide)) fun s1 u1 => WP.block_nil ?_
  have h1 := h.of_upd u1 (by decide) (by decide) (by decide)
  have wp := h.wpos
  have wl := h.wle
  have start : InvLoopI s B Z w N 0 s1 := ⟨h1, by rw [u1.mem]; exact Keep.refl _ _ _ _ _, u1.rest (by simp),
    by rw [u1.gpr, h.r9]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; simp; omega_arith,
    fun _ _ _ _ _ => by rw [u1.mem]; rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * w ∧ 0 < k ∧ InvLoopI s B Z w N i t) ?_ (32 * w) s1
    ⟨0, by omega_arith, by omega_arith, start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (inverseBody_ok hN15 hN inv (by omega_arith)) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * w
    · left
      refine ⟨by change some (!u.z) = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hNM hZ hodd h1M hst
      have v := iu.value hNM hZ hodd h1M hst
      rw [e, hst] at v
      have hm : 1 % num s.mem B w aM = 1 := Nat.mod_eq_of_lt h1M
      have D := VG.Proof.Rsa.invIter_done (a := num s.mem B w 0) (K := 2 * (32 * w)) hodd (by
        have := val32_lt s.mem (State.addr B) (arr w 0) w
        have := val32_lt s.mem (State.addr B) (arr w aM) w
        calc num s.mem B w 0 * num s.mem B w aM < 2 ^ (32 * w) * 2 ^ (32 * w) :=
              Nat.mul_lt_mul'' (by assumption) (by assumption)
          _ = 2 ^ (2 * (32 * w)) := by rw [← Nat.pow_add]; congr 1; omega_arith)
      rw [hm] at D
      dsimp only at D
      rw [← v] at D
      exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩
    · right
      exact ⟨by change some (!u.z) = some true; simp [hz, e], k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end VG.Proof.Rsa.Arm.Keys
