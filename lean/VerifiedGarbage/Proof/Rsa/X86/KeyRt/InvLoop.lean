module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvStep
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import Mathlib.Tactic.Widget.Calc
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass

/-! # The inverse at a run-time width: `32 w` iterations of two steps

`inverse_ok` states what `Keys.inverse_ok` does, for the run-time width's
`inverse` on `RtWs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot bank invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr)
open VG.Proof.Rsa (invIter InvI)

variable {L : Lay}

/-- The state after `i` iterations. -/
structure InvLoopI (L : Lay) (s0 : State) (B : Addr) (Z len N : Nat) (i : Nat) (t : State) : Prop where
  ws : RtWs L t B Z len N
  keep : Keep B (kw len) invArrs invSlots s0.mem t.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 t
  count : t.gpr .esi = BitVec.ofNat 32 (32 * kw len - i)
  value : num s0.mem B (kw len) aNM + num s0.mem B (kw len) aM = 2 ^ (32 * kw len) → num s0.mem B (kw len) aZero = 0 →
    num s0.mem B (kw len) aM % 2 = 1 → 1 < num s0.mem B (kw len) aM →
    bank s0.mem B (kw len) 0 = (num s0.mem B (kw len) 0, num s0.mem B (kw len) aM, 1, 0) →
    bank t.mem B (kw len) 0 = invIter (num s0.mem B (kw len) aM) (2 * i) (bank s0.mem B (kw len) 0)

theorem inverseBody_ok {s0 t : State} {B : Addr} {Z len N i : Nat} (hN15 : 15 ≤ N) 
    (inv : InvLoopI L s0 B Z len N i t) (hi : i < 32 * kw len) :
    WP isa (.seq (VG.Impl.Rsa.X86.KeyRt.invStep L 0 4) (.seq (VG.Impl.Rsa.X86.KeyRt.invStep L 4 0)
      (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) t fun u =>
      InvLoopI L s0 B Z len N (i + 1) u ∧ u.zf = some (decide (i + 1 = 32 * kw len)) := by
  have h := inv.ws
  have wle := h.ws.wle
  have fM := h.ws.fit64 (j := aM) (by idx)
  have fNM := h.ws.fit64 (j := aNM) (by idx)
  have fZ := h.ws.fit64 (j := aZero) (by idx)
  have f0 := h.ws.fit64 (j := 0) (by idx)
  have keepM : ∀ {m m' : Mem} {js ds : List Nat}, Keep B (kw len) js ds m m' → (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) →
      (∀ d ∈ ds, d + 4 ≤ hdr) → num m' B (kw len) aM = num m B (kw len) aM ∧ num m' B (kw len) aNM = num m B (kw len) aNM ∧
        num m' B (kw len) aZero = num m B (kw len) aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine WP.mono (Div.count_ok t2) fun u ⟨countU, hz, m2, r3⟩ => ?_
  have r6 : t2.gpr .esi = t.gpr .esi := (r2.1 _ (by decide)).trans (r1.1 _ (by decide))
  refine ⟨⟨h2.keep r3 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))))
  · rw [countU, r6, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro hNM hZ hodd h1M hst
    have prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by idx)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by idx)
    have I := VG.Proof.Rsa.invIter_inv hodd (VG.Proof.Rsa.invI_start' (a := num s0.mem B (kw len) 0) hodd h1M) (2 * i)
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
    change some (BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * kw len - i - 1 = 0 ↔ i + 1 = 32 * kw len by omega]

theorem inverse_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs L s B Z len N) (hN15 : 15 ≤ N) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.inverse L) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) invArrs invSlots s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (num s.mem B (kw len) aNM + num s.mem B (kw len) aM = 2 ^ (32 * kw len) → num s.mem B (kw len) aZero = 0 →
        num s.mem B (kw len) aM % 2 = 1 → 1 < num s.mem B (kw len) aM →
        bank s.mem B (kw len) 0 = (num s.mem B (kw len) 0, num s.mem B (kw len) aM, 1, 0) →
        num t.mem B (kw len) 1 = Nat.gcd (num s.mem B (kw len) 0) (num s.mem B (kw len) aM) ∧
        (num s.mem B (kw len) aM : Int) ∣ (num t.mem B (kw len) 3 : Int) * num s.mem B (kw len) 0 - num t.mem B (kw len) 1 ∧
        num t.mem B (kw len) 3 < num s.mem B (kw len) aM) := by
  unfold VG.Impl.Rsa.X86.KeyRt.inverse
  refine WP.seq ?_
  rw [show bits L = bits L ++ [] from (List.append_nil _).symm]
  refine bits_ok h fun s1 u1 m1 e1 => WP.block_nil ?_
  have h1 := h.keep u1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  have wp := h.kw_pos
  have wl := h.ws.wle
  have start : InvLoopI L s B Z len N 0 s1 := ⟨h1, by rw [m1]; exact Keep.refl _ _ _ _ _,
    u1.mono (by decide), by rw [e1]; rfl, fun _ _ _ _ _ => by rw [m1]; rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ InvLoopI L s B Z len N i t) ?_
    (32 * kw len) s1 ⟨0, by omega, by omega, start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (inverseBody_ok hN15 inv (by omega)) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * kw len
    · left
      refine ⟨by change u.zf.map not = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hNM hZ hodd h1M hst
      have v := iu.value hNM hZ hodd h1M hst
      rw [e, hst] at v
      have hm : 1 % num s.mem B (kw len) aM = 1 := Nat.mod_eq_of_lt h1M
      have D := VG.Proof.Rsa.invIter_done (a := num s.mem B (kw len) 0) (K := 2 * (32 * kw len)) hodd (by
        have := val32_lt s.mem B (arr (kw len) 0) (kw len)
        have := val32_lt s.mem B (arr (kw len) aM) (kw len)
        calc num s.mem B (kw len) 0 * num s.mem B (kw len) aM < 2 ^ (32 * kw len) * 2 ^ (32 * kw len) :=
              Nat.mul_lt_mul'' (by assumption) (by assumption)
          _ = 2 ^ (2 * (32 * kw len)) := by rw [← Nat.pow_add]; congr 1; omega)
      rw [hm] at D
      dsimp only at D
      rw [← v] at D
      exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩
    · right
      exact ⟨by change u.zf.map not = some true; simp [hz, e], k - 1, by omega, i + 1, by omega, by omega, iu⟩

end VG.Proof.Rsa.X86.KeyRt
