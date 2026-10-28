module

public import VerifiedGarbage.Proof.Rsa.X86.InvStep
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Widget.Calc
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `inverse` on i686: `32 w` iterations of two steps

`inverse_ok`: from `(a, m, 1, 0)` in arrays 0–3, for an odd `m > 1`, array 1
ends as `gcd(a, m)` and array 3 as `x < m` with `x a ≡ gcd(a, m) (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa (invIter InvI)

/-- The arrays and header words `inverse` writes. -/
abbrev invArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, aT1, aT2, aT3, aT4]
abbrev invSlots : List Nat := [sOdd, sB, sC]
/-- The header words from 16 to 96 that the batched inverse also uses as scratch. -/
abbrev rtSlots : List Nat := [16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96]

/-- The state after `i` iterations. -/
structure InvLoopI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Keep B w invArrs invSlots s0.mem t.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 t
  count : t.gpr .esi = BitVec.ofNat 32 (32 * w - i)
  value : num s0.mem B w aNM + num s0.mem B w aM = 2 ^ (32 * w) → num s0.mem B w aZero = 0 →
    num s0.mem B w aM % 2 = 1 → 1 < num s0.mem B w aM →
    bank s0.mem B w 0 = (num s0.mem B w 0, num s0.mem B w aM, 1, 0) →
    bank t.mem B w 0 = invIter (num s0.mem B w aM) (2 * i) (bank s0.mem B w 0)

theorem inverseBody_ok {s0 t : State} {B : Addr} {Z w N i : Nat} (hN15 : 15 ≤ N) 
    (inv : InvLoopI s0 B Z w N i t) (hi : i < 32 * w) :
    WP isa (.seq (VG.Impl.Rsa.X86.Keys.invStep w 0 4) (.seq (VG.Impl.Rsa.X86.Keys.invStep w 4 0)
      (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) t fun u =>
      InvLoopI s0 B Z w N (i + 1) u ∧ u.zf = some (decide (i + 1 = 32 * w)) := by
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
  refine WP.mono (invStep_ok h hN15 (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine WP.mono (Div.count_ok t2) fun u ⟨countU, hz, m2, r3⟩ => ?_
  have r6 : t2.gpr .esi = t.gpr .esi := (r2.1 _ (by decide)).trans (r1.1 _ (by decide))
  refine ⟨⟨h2.rest r3 (by decide) (by decide), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))))
  · rw [countU, r6, inv.count]
    change BitVec.ofNat 32 (32 * w - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by have := h.wle; omega)]
    congr 1
  · intro hNM hZ hodd h1M hst
    have prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by idx)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by idx)
    have I := VG.Proof.Rsa.invIter_inv hodd (VG.Proof.Rsa.invI_start' (a := num s0.mem B w 0) hodd h1M) (2 * i)
    rw [← hst, ← prev] at I
    have s1 := e1 (by rw [n0, m0]; exact hNM) (by rw [z0]; exact hZ)
      (by rw [m0]; exact I.x₁_lt) (by rw [m0]; exact I.x₂_lt)
    rw [m0] at s1
    have I1 := VG.Proof.Rsa.invStep_inv hodd I
    rw [← s1] at I1
    have s2 := e2 (by rw [n1, m1, n0, m0]; exact hNM) (by rw [z1, z0]; exact hZ)
      (by rw [m1, m0]; exact I1.x₁_lt) (by rw [m1, m0]; exact I1.x₂_lt)
    rw [m1, m0, s1, prev] at s2
    rw [m2, s2, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    rfl
  · rw [hz, r6, inv.count]
    change some (BitVec.ofNat 32 (32 * w - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by have := h.wle; omega), ofNat_beq_zero (by have := h.wle; omega)]
    simp only [show 32 * w - i - 1 = 0 ↔ i + 1 = 32 * w by omega]

theorem inverse_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N)  :
    WP isa (VG.Impl.Rsa.X86.Keys.inverse w) s fun t => Ws t B Z w N ∧ Keep B w invArrs invSlots s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num s.mem B w aM % 2 = 1 → 1 < num s.mem B w aM →
        bank s.mem B w 0 = (num s.mem B w 0, num s.mem B w aM, 1, 0) →
        num t.mem B w 1 = Nat.gcd (num s.mem B w 0) (num s.mem B w aM) ∧
        (num s.mem B w aM : Int) ∣ (num t.mem B w 3 : Int) * num s.mem B w 0 - num t.mem B w 1 ∧
        num t.mem B w 3 < num s.mem B w aM) := by
  rw [inverse, WP.seq_iff]
  refine wp_movS rfl fun s1 u1 _ => WP.block_nil ?_
  have h1 := h.rest u1.keeps (by decide) (by decide)
  have wp := h.wpos
  have wl := h.wle
  have start : InvLoopI s B Z w N 0 s1 := ⟨h1, by rw [u1.mem]; exact Keep.refl _ _ _ _ _,
    u1.keeps.mono (by decide), by rw [u1.gpr]; rfl, fun _ _ _ _ _ => by rw [u1.mem]; rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * w ∧ 0 < k ∧ InvLoopI s B Z w N i t) ?_ (32 * w) s1
    ⟨0, by omega, by omega, start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (inverseBody_ok hN15 inv (by omega)) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * w
    · left
      refine ⟨by change u.zf.map not = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hNM hZ hodd h1M hst
      have v := iu.value hNM hZ hodd h1M hst
      rw [e, hst] at v
      have hm : 1 % num s.mem B w aM = 1 := Nat.mod_eq_of_lt h1M
      have D := VG.Proof.Rsa.invIter_done (a := num s.mem B w 0) (K := 2 * (32 * w)) hodd (by
        have := val32_lt s.mem B (arr w 0) w
        have := val32_lt s.mem B (arr w aM) w
        calc num s.mem B w 0 * num s.mem B w aM < 2 ^ (32 * w) * 2 ^ (32 * w) :=
              Nat.mul_lt_mul'' (by assumption) (by assumption)
          _ = 2 ^ (2 * (32 * w)) := by rw [← Nat.pow_add]; congr 1; omega)
      rw [hm] at D
      dsimp only at D
      rw [← v] at D
      exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩
    · right
      exact ⟨by change u.zf.map not = some true; simp [hz, e], k - 1, by omega, i + 1, by omega, by omega, iu⟩

end VG.Proof.Rsa.X86.Keys
