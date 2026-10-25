module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `inverse` on PPC64LE: `32 w` iterations of two steps

As on ARMv7 (`Proof/Rsa/Arm/InvLoop.lean`): `inverse_ok`: from
`(a, m, 1, 0)` in arrays 0–3, for an odd `m > 1`, array 1 ends as
`gcd(a, m)` and array 3 as `x < m` with `x a ≡ gcd(a, m) (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (inverse aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)
open VG.Proof.Rsa (invIter InvI invI_start')

/-- The arrays and header words `inverse` writes. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]

/-- The registers `inverse` changes. -/
abbrev invRegs : List Reg := .r4 :: opRegs

/-- The state after `i` iterations, from `s0`. -/
structure InvLoopI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : KeyWorkspace.Keep B w invArrs invSlots s0.mem t.mem
  regs : Keep invRegs s0 t
  value : num s0.mem B w aNM + num s0.mem B w aM = 2 ^ (32 * w) → num s0.mem B w aZero = 0 →
    num s0.mem B w aM % 2 = 1 → 1 < num s0.mem B w aM →
    bank s0.mem B w 0 = (num s0.mem B w 0, num s0.mem B w aM, 1, 0) →
    bank t.mem B w 0 = invIter (num s0.mem B w aM) (2 * i) (bank s0.mem B w 0)

theorem inverseBody_ok {s0 t : State} {B : Addr} {Z w N i : Nat} (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (inv : InvLoopI s0 B Z w N i t) :
    WP isa (.seq (VG.Impl.Rsa.PPC64LE.Keys.invStep 0 4) (.seq (VG.Impl.Rsa.PPC64LE.Keys.invStep 4 0) (.block [.subi .r4 .r4 1]))) t fun u =>
      InvLoopI s0 B Z w N (i + 1) u ∧ u.gpr .r4 = t.gpr .r4 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  have fM := h.fit64 (j := aM) (by idx)
  have fNM := h.fit64 (j := aNM) (by idx)
  have fZ := h.fit64 (j := aZero) (by idx)
  have keepM : ∀ {m m' : Mem} {js ds : List Nat}, KeyWorkspace.Keep B w js ds m m' →
      (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) → (∀ d ∈ ds, d + 4 ≤ KeyWorkspace.hdr) →
        num m' B w aM = num m B w aM ∧ num m' B w aNM = num m B w aNM ∧
        num m' B w aZero = num m B w aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 hN (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 hN (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have hs : WP isa (.block [.subi .r4 .r4 1]) t2 fun u =>
      (u.gpr .r4 = t2.gpr .r4 - BitVec.ofNat 64 1 ∧ u.mem = t2.mem) ∧ Keep [.r4] t2 u := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hs fun u ⟨⟨u4, m2⟩, k3⟩ => ?_
  have r4 : t2.gpr .r4 = t.gpr .r4 := (r2.gpr _ (by decide)).trans (r1.gpr _ (by decide))
  refine ⟨⟨h2.of_keep k3, ?_, ?_, ?_⟩, by rw [u4, r4]⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.regs.trans' (((r1.trans r2).trans k3).mono)
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

theorem inverse_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N)
    (hN : N ≤ 256) :
    WP isa inverse s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs invSlots s.mem t.mem ∧
      Keep invRegs s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        num t.mem B w 1 = Nat.gcd (num s.mem B w 0) (num s.mem B w aM) ∧
        (num s.mem B w aM : Int) ∣ (num t.mem B w 3 : Int) * num s.mem B w 0 - num t.mem B w 1 ∧
        num t.mem B w 3 < num s.mem B w aM) := by
  have wp := h.wpos
  have wl := h.wle
  rw [inverse, WP.seq_iff]
  have hl : WP isa (.block [.lsl .r4 .r29 5]) s fun x =>
      (x.gpr .r4 = BitVec.ofNat 64 (32 * w) ∧ x.mem = s.mem) ∧ Keep [.r4] s x := by
    refine WP.keep _ ?_ (by decide)
    have e : BitVec.ofNat 64 w <<< 5 = BitVec.ofNat 64 (32 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega_arith
    prun [h.r29, e]
  refine WP.mono hl fun s1 ⟨⟨u4, m1⟩, k1⟩ => ?_
  have h1 := h.of_keep k1
  have start : InvLoopI s B Z w N 0 s1 :=
    ⟨h1, by rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _, k1.mono, fun _ _ _ _ _ => by rw [m1]; rfl⟩
  refine WP.mono (wp_countdown (body := .seq (VG.Impl.Rsa.PPC64LE.Keys.invStep 0 4) (.seq (VG.Impl.Rsa.PPC64LE.Keys.invStep 4 0) (.block [.subi .r4 .r4 1])))
    (cnt := .r4) (N := 32 * w) (by omega_arith) (by omega_arith) (InvLoopI s B Z w N)
    (fun i _ t inv _ => inverseBody_ok hN15 hN inv) start u4) fun t inv => ?_
  refine ⟨inv.ws, inv.keep, inv.regs, fun hNM hZ hodd h1M hst => ?_⟩
  have v := inv.value hNM hZ hodd h1M hst
  rw [hst] at v
  have hm : 1 % num s.mem B w aM = 1 := Nat.mod_eq_of_lt h1M
  have hlt : num s.mem B w 0 * num s.mem B w aM < 2 ^ (2 * (32 * w)) := by
    have a0 := val32_lt s.mem B (arr w 0) w
    have aM' := val32_lt s.mem B (arr w aM) w
    rw [show 2 * (32 * w) = 32 * w + 32 * w by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul'' a0 aM'
  have D := VG.Proof.Rsa.invIter_done (a := num s.mem B w 0) (K := 2 * (32 * w)) hodd hlt
  rw [hm] at D
  dsimp only at D
  rw [← v] at D
  exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩

end VG.Proof.Rsa.PPC64LE.Keys
