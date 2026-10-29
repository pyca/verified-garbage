module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvU
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.ToAdditive

/-! # Binary GCD without inverse coefficients

The machine retains only the first two coordinates of the existing, terminating
binary inverse algorithm. Its coefficient coordinates are ghosts in this proof.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM)
open VG.Proof.Rsa (invIter)

variable {L : Lay}

/-- Only the `u` and `v` coordinates are materialized. -/
structure GcdLoopI (L : Lay) (s0 : State) (B : Addr) (Z len N : Nat) (i : Nat) (t : State) : Prop where
  ws : RtWs L t B Z len N
  keep : Keep B (kw len) invArrs invSlots s0.mem t.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 t
  count : t.gpr .esi = BitVec.ofNat 32 (32 * kw len - i)
  value :
    let st : Nat × Nat × Nat × Nat := invIter (num s0.mem B (kw len) aM) (2 * i)
      (num s0.mem B (kw len) 0, num s0.mem B (kw len) 1, 1, 0)
    num t.mem B (kw len) 0 = st.1 ∧ num t.mem B (kw len) 1 = st.2.1

private theorem uv_step {s : State} {B : Addr} {Z len N A D : Nat}
    (h : RtWs L s B Z len N) (hN15 : 15 ≤ N)
    (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) (m x y : Nat) :
    WP isa (gcdStep L A D) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [D, D + 1, VG.Impl.Rsa.X86.Keys.aT1, VG.Impl.Rsa.X86.Keys.aT2, VG.Impl.Rsa.X86.Keys.aT3]
        [VG.Impl.Rsa.X86.Keys.sOdd, VG.Impl.Rsa.X86.Keys.sB, VG.Impl.Rsa.X86.Keys.sC] s.mem t.mem ∧
      (num t.mem B (kw len) D, num t.mem B (kw len) (D + 1)) =
        ((VG.Proof.Rsa.invStep m (num s.mem B (kw len) A, num s.mem B (kw len) (A + 1), x, y)).1,
         (VG.Proof.Rsa.invStep m (num s.mem B (kw len) A, num s.mem B (kw len) (A + 1), x, y)).2.1) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  refine WP.mono (invU_ok h hN15 hb) fun t ⟨ht, k, _, _, v, u, r⟩ => ⟨ht, k, ?_, r⟩
  rw [u, v]
  dsimp only [VG.Proof.Rsa.invStep]
  split_ifs <;> simp_all

private theorem gcdBody_ok {s0 t : State} {B : Addr} {Z len N i : Nat} (hN15 : 15 ≤ N)
    (inv : GcdLoopI L s0 B Z len N i t) (hi : i < 32 * kw len) :
    WP isa (.seq (gcdStep L 0 4) (.seq (gcdStep L 4 0)
      (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) t fun u =>
      GcdLoopI L s0 B Z len N (i + 1) u ∧ u.zf = some (decide (i + 1 = 32 * kw len)) := by
  have wle := inv.ws.ws.wle
  let st := invIter (num s0.mem B (kw len) aM) (2 * i)
    (num s0.mem B (kw len) 0, num s0.mem B (kw len) 1, 1, 0)
  let next := VG.Proof.Rsa.invStep (num s0.mem B (kw len) aM) st
  rw [WP.seq_iff]
  refine WP.mono (uv_step inv.ws hN15 (.inl ⟨rfl, rfl⟩)
    (num s0.mem B (kw len) aM) st.2.2.1 st.2.2.2) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (uv_step h1 hN15 (.inr ⟨rfl, rfl⟩)
    (num s0.mem B (kw len) aM) next.2.2.1 next.2.2.2) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine WP.mono (Div.count_ok t2) fun u ⟨countU, hz, m2, r3⟩ => ?_
  have r6 : t2.gpr .esi = t.gpr .esi := (r2.1 _ (by decide)).trans (r1.1 _ (by decide))
  refine ⟨⟨h2.keep r3 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))))
  · rw [countU, r6, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  · have prev := inv.value
    change num t.mem B (kw len) 0 = st.1 ∧ num t.mem B (kw len) 1 = st.2.1 at prev
    rw [prev.1, prev.2] at e1
    have n1 : num t1.mem B (kw len) 4 = next.1 := congrArg Prod.fst e1
    have n2 : num t1.mem B (kw len) 5 = next.2.1 := congrArg Prod.snd e1
    rw [n1, n2] at e2
    rw [m2]
    change num t2.mem B (kw len) 0 = _ ∧ num t2.mem B (kw len) 1 = _
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith]
    exact ⟨congrArg Prod.fst e2, congrArg Prod.snd e2⟩
  · rw [hz, r6, inv.count]
    change some (BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show 32 * kw len - i - 1 = 0 ↔ i + 1 = 32 * kw len by omega_arith]

/-- Same fixed iteration bound and memory footprint, without computing coefficients. -/
theorem gcd_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs L s B Z len N) (hN15 : 15 ≤ N) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.gcd L) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) invArrs invSlots s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (num s.mem B (kw len) aM % 2 = 1 → 1 < num s.mem B (kw len) aM →
        num s.mem B (kw len) 1 = num s.mem B (kw len) aM →
        num t.mem B (kw len) 1 = Nat.gcd (num s.mem B (kw len) 0) (num s.mem B (kw len) aM)) := by
  unfold VG.Impl.Rsa.X86.KeyRt.gcd
  refine WP.seq ?_
  rw [show bits L = bits L ++ [] from (List.append_nil _).symm]
  refine bits_ok h fun s1 u1 m1 e1 => WP.block_nil ?_
  have h1 := h.keep u1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  have wp := h.kw_pos
  have wl := h.ws.wle
  have start : GcdLoopI L s B Z len N 0 s1 := ⟨h1, by rw [m1]; exact Keep.refl _ _ _ _ _,
    u1.mono (by decide), by rw [e1]; rfl, by rw [m1]; exact ⟨rfl, rfl⟩⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ GcdLoopI L s B Z len N i t) ?_
    (32 * kw len) s1 ⟨0, by omega_arith, by omega_arith, start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (gcdBody_ok hN15 inv (by omega_arith)) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * kw len
    · left
      refine ⟨by change u.zf.map not = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hodd h1M hv
      have v := iu.value.2
      rw [e, hv] at v
      have hm : 1 % num s.mem B (kw len) aM = 1 := Nat.mod_eq_of_lt h1M
      have D := VG.Proof.Rsa.invIter_done (a := num s.mem B (kw len) 0) (K := 2 * (32 * kw len)) hodd (by
        have := val32_lt s.mem B (arr (kw len) 0) (kw len)
        have := val32_lt s.mem B (arr (kw len) aM) (kw len)
        calc num s.mem B (kw len) 0 * num s.mem B (kw len) aM < 2 ^ (32 * kw len) * 2 ^ (32 * kw len) :=
              Nat.mul_lt_mul'' (by assumption) (by assumption)
          _ = 2 ^ (2 * (32 * kw len)) := by rw [← Nat.pow_add]; congr 1; omega_arith)
      rw [hm] at D
      exact v.trans D.2.1
    · right
      exact ⟨by change u.zf.map not = some true; simp [hz, e], k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, iu⟩

end VG.Proof.Rsa.X86.KeyRt
