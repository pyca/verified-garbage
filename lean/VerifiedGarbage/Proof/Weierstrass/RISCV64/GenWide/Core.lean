module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Csub
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Init
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Adc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the operations on aligned pointers

`mulCore`, `addCore` and `subCore` (`Impl/Weierstrass/RISCV64/GenWide.lean`)
from a state with `a3 = b`, `t4`, `t5` and `t2` pointing to `[a]`, `[b]` and
`[o]` (`CoreOk`): `[o]` becomes `[a] [b] R⁻¹`, `[a] + [b]` or `[a] - [b]`
modulo `m` (`mulCore_ok`, `addCore_ok`, `subCore_ok`), and only `[o]` and the
own working space at `b + T` are written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_frame al8 colsV sd_ok dw_write_self dw_write_other)

/-- The registers the operations write. -/
abbrev clobW : List Reg := [.t0, .t3, .t6, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The own working space used: `T` and `N`. -/
abbrev ownR (k : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (T k), 8 * (2 * k + 2)⟩

/-- What the operations need. -/
structure CoreOk (k : Nat) (b A B O : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  b' : s.gpr .t5 = B
  o : s.gpr .t2 = O
  aal : A.toNat % 8 = 0
  bal : B.toNat % 8 = 0
  oal : O.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  bin : ∀ i < k, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  ow : ∀ i < k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8
  onw : O.toNat + 8 * k ≤ 2 ^ 64
  adis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownR k b)
  bdis : ∀ i < k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (ownR k b)
  odis : Region.Disjoint ⟨O, 8 * k⟩ (ownR k b)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem own_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) : T k + 8 * (2 * k + 2) ≤ 2048 ∧ N k + 8 * k = T k + 8 * (2 * k + 2) := by
  unfold N T; omega

/-- A part of the own working space within it. -/
theorem own_sub {k : Nat} {b : Addr} {d n : Nat} (hd : T k ≤ d)
    (hn : d + n ≤ T k + 8 * (2 * k + 2)) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (ownR k b) :=
  Offset.sub b hd hn

theorem disj_sub {r r₁ r₂ : Region} (h : Region.Disjoint r r₂) (hs : Region.Sub r₁ r₂) : Region.Disjoint r r₁ :=
  fun x h₁ h₂ => h x h₁ (hs x h₂)

theorem disj_symm {r₁ r₂ : Region} (h : Region.Disjoint r₁ r₂) : Region.Disjoint r₂ r₁ :=
  fun x h₁ h₂ => h x h₂ h₁

theorem mont_nat {V a Bv Q M R : Nat} (hinv : V * R = a * Bv + Q * M) (ha : a < R) (hB : Bv < M) (hQ : Q < R) :
    V < 2 * M ∧ V % M * R % M = a * Bv % M := by
  have hR : 0 < R := by omega
  refine ⟨?_, ?_⟩
  · apply Nat.lt_of_mul_lt_mul_right (a := R)
    have h1 : a * Bv < R * M := Nat.mul_lt_mul_of_lt_of_le ha (by omega) (by omega)
    have h2 : Q * M ≤ R * M := Nat.mul_le_mul_right _ (by omega)
    rw [hinv, Nat.mul_assoc, Nat.two_mul]
    rw [Nat.mul_comm R M] at h1 h2
    omega
  · rw [Nat.mod_mul_mod, hinv, Nat.add_mul_mod_self_right]

/-- `[o] = [a] [b] R⁻¹ mod m`, below `m`. -/
theorem mulCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1)
    (hB : xv s.mem B k < m) :
    WP isa (.block (mulCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k < m ∧ ov s'.mem O k * 2 ^ (64 * k) % m = xv s.mem A k * xv s.mem B k % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  unfold mulCore
  rw [List.append_assoc, List.append_assoc]
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine WP.block_append (WP.mono (mulInit_ok (m := m) hc1 (by omega) k30) fun s2 ⟨g2, rd2, wr2, sp2, f2, z2, t6⟩ => ?_)
  -- The rounds.
  have hc2 : Ctx b s2 := ctx_of hc1 (g2 _ (by decide)) wr2
  have m02 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s2.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f2 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (Nat.le_refl _) (by omega)),
      dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hN2 : ∀ i < k, dw s2.mem b (N k + 8 * i) = dw s1.mem b (N k + 8 * i) := fun i hi =>
    dw_frame f2 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  have hL : LoopOk k b A B (negInv m) s2 :=
    { mo := ⟨hc2, hb, by rw [g2 _ (by decide), g1 _ (by decide), hC.a], hC.aal,
        by rw [rd2, wr2, rd1, wr1]; exact hC.ain,
        fun i hi j hj => disj_sub (hC.adis i hi) (own_sub (Nat.le_refl _) (by omega)), k7, k30⟩
      t5 := by rw [g2 _ (by decide), g1 _ (by decide), hC.b']
      bal := hC.bal
      bin := by rw [rd2, wr2, rd1, wr1]; exact hC.bin
      bdis := fun i hi => disj_sub (hC.bdis i hi) (own_sub (Nat.le_refl _) (by omega))
      t6 := t6
      m'lt := Nat.mod_lt _ (by decide)
      inv := by
        rw [show N k = N k + 8 * 0 by rfl, hN2 0 (by omega), w1 0 (by omega)]
        unfold negInv at hinv ⊢; exact hinv
      zero := z2 }
  refine WP.block_append (WP.mono (loop_ok hL k (Nat.le_refl _)) fun s3 h3 => ?_)
  -- The final subtraction.
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  have hA : xv s2.mem A k = xv s.mem A k := colsV_congr fun i hi => m02 (hC.adis i hi)
  have hBv : bv s2.mem B k = xv s.mem B k := colsV_congr fun i hi => m02 (hC.bdis i hi)
  have hNv : nv k s2.mem b = m := by
    rw [← nv1]; exact colsV_congr fun i hi => hN2 i hi
  obtain ⟨Q, hQ, hv⟩ := h3.val
  rw [hA, hBv, hNv] at hv
  have hNv3 : nv k s3.mem b = m := by
    rw [← hNv]
    exact colsV_congr fun i hi => frame_dw h3.frame (Offset.disjoint b (.inr (by omega)) (by omega) (by omega))
  have hR : (2 ^ 64) ^ k = 2 ^ (64 * k) := (Nat.pow_mul ..).symm
  rw [hR] at hv hQ
  obtain ⟨hV2, hVm⟩ := mont_nat hv (by rw [← hR]; exact colsV_lt _ (fun _ => dw_lt _ _ _) k) hB hQ
  have hCs : CsubOk k b O s3 :=
    { ctx := hc3
      nowrap := hb
      t2 := by rw [h3.gpr _ (by decide), g2 _ (by decide), g1 _ (by decide), hC.o]
      oal := hC.oal
      onw := hC.onw
      ow := by rw [h3.wr, wr2, wr1]; exact hC.ow
      tdis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      ndis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      k7 := k7
      k30 := k30 }
  refine WP.mono (csub_ok hCs (by rw [hNv3]; exact hV2)) fun s4 ⟨g4, rd4, wr4, sp4, f4, v4⟩ => ?_
  rw [hNv3] at v4
  refine ⟨fun r hr => ?_, by rw [rd4, h3.rd, rd2, rd1], by rw [wr4, h3.wr, wr2, wr1],
    by rw [sp4, h3.sp, sp2, sp1], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]), g2 r (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g1 r (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · have sub1 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩], Region.Sub r r' :=
      fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
    have subT : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
    have sub4 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region), ⟨O, 8 * k⟩], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun x h => h⟩
    exact (((f1.sub sub1).trans (f2.sub subT)).trans (h3.frame.sub subT)).trans (f4.sub sub4)
  · rw [v4]; exact Nat.mod_lt _ (by omega)
  · rw [v4]; exact hVm

theorem colsV_yw_false (M : BitVec 64) (f : Nat → Nat) (n : Nat) :
    colsV (fun i => yw false M (f i)) n = colsV f n := by simp [yw]

theorem add_zero_addr (O : Addr) : O + BitVec.ofNat 64 0 = O := by simp

/-- The own working space's frames within it. -/
theorem sub_own {k : Nat} {b O : Addr} (hk : 1 ≤ k) (hk' : k ≤ 30) {d n : Nat} (hd : T k ≤ d)
    (hn : d + n ≤ T k + 8 * (2 * k + 2)) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 d, n⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩], Region.Sub r r' :=
  fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    have := own_facts k hk hk'
    exact ⟨_, List.mem_cons_self .., own_sub hd hn⟩

/-- `[o] = [a] + [b] mod m`, for `[a] + [b] < 2 m`. -/
theorem addCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hAB : xv s.mem A k + xv s.mem B k < 2 * m) :
    WP isa (.block (addCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k = (xv s.mem A k + xv s.mem B k) % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  unfold addCore addSum
  rw [List.append_assoc]
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ctx_of hc1 (u2.other _ (by decide)) u2.wr
  have g2 : ∀ r, r ∉ [.a5, .a6, .a7] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.1, g1 r (by simp [hr.2.1, hr.2.2])]
  have m2 : s2.mem = s1.mem := u2.mem
  have hD : DstOk b .a3 (T k) k s2 :=
    ⟨hc2.a3, by decide, hc2.al, t8, by omega, by omega, fun j hj => hc2.inW (by omega)⟩
  have hXo : OpOk b A .t4 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.a], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.aal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.ain j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.adis j hj) (own_sub (by omega) (by omega))⟩
  have hYo : OpOk b B .t5 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.b'], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.bal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.bin j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.bdis j hj) (own_sub (by omega) (by omega))⟩
  show WP isa (.block (((List.range k).flatMap (adcStep (mkOf false) .t4 0 .t5 0 .a3 (T k)) ++
    [.store .d .a5 .a3 (T k + 8 * k)]) ++ csub k)) s2 _
  refine WP.block_append (WP.block_append (WP.mono (adcRow_ok hD hXo hYo (by rw [u2.gpr]; decide) k
    (Nat.le_refl _)) fun s3 h3 => ?_))
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have hc4 : Ctx b s4 := ctx_of hc3 (by rw [u4.gpr]) u4.wr
  -- The sum.
  have m01 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s1.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hv := h3.val
  rw [colsV_yw_false, m2, u2.gpr] at hv
  have hA : colsV (fun i => dw s1.mem A (0 + 8 * i)) k = xv s.mem A k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.adis i hi)
  have hB : colsV (fun i => dw s1.mem B (0 + 8 * i)) k = xv s.mem B k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.bdis i hi)
  rw [hA, hB] at hv
  have hm4 : s4.mem = s3.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * k)) (s3.gpr .a5) := u4.mem
  have hT4 : tv k s4.mem b (k + 1) = xv s.mem A k + xv s.mem B k := by
    show colsV _ k + (2 ^ 64) ^ k * dw s4.mem b (T k + 8 * k) = _
    rw [colsV_congr (g := fun i => dw s3.mem b (T k + 8 * i)) fun i hi => by
      rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)], hm4, dw_write_self]
    have : (BitVec.ofNat 64 0).toNat = 0 := rfl
    rw [this, Nat.add_zero] at hv
    exact hv
  have hNv4 : nv k s4.mem b = m := by
    rw [← nv1]
    refine colsV_congr fun i hi => ?_
    rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m2]
  have hCs : CsubOk k b O s4 :=
    { ctx := hc4
      nowrap := hb
      t2 := by rw [u4.gpr, h3.gpr _ (by decide), g2 _ (by decide), hC.o]
      oal := hC.oal
      onw := hC.onw
      ow := by rw [u4.wr, h3.wr, u2.wr, wr1]; exact hC.ow
      tdis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      ndis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      k7 := k7
      k30 := k30 }
  refine WP.mono (csub_ok hCs (by rw [hT4, hNv4]; exact hAB)) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_
  rw [hT4, hNv4] at v5
  refine ⟨fun r hr => ?_, by rw [rd5, u4.rd, h3.rd, u2.rd, rd1], by rw [wr5, u4.wr, h3.wr, u2.wr, wr1],
    by rw [sp5, u4.sp, h3.sp, u2.sp, sp1], ?_, v5⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g5 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]), u4.gpr,
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g2 r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · have fT : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 1)⟩] s1.mem s4.mem := by
      rw [hm4, ← m2]
      refine (h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by omega)
    have sub5 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region), ⟨O, 8 * k⟩], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun x h => h⟩
    exact ((f1.sub (sub_own (by omega) k30 (by omega) (by omega))).trans
      (fT.sub (sub_own (by omega) k30 (Nat.le_refl _) (by omega)))).trans (f5.sub sub5)

theorem sub_nat {D a b m E c c' ov Y : Nat} (hs : D + b + 0 = a + E * c) (hc : c ≤ 1) (hc' : c' ≤ 1)
    (hY : Y = if c = 1 then m else 0) (hadd : ov + E * c' = D + Y + 0) (hD : D < E) (hov : ov < E)
    (ha : a < m) (hb : b < m) : ov = (a + m - b) % m := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc' with rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, show (0 : Nat) = 1 ↔ False by decide,
      ↓reduceIte] at hs hadd hY <;> subst hY
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · omega
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem colsV_mask (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) {c : BitVec 64} (hc : c.toNat ≤ 1) (n : Nat) :
    colsV (fun i => yw true (BitVec.ofNat 64 0 - c) (f i)) n = if c.toNat = 1 then colsV f n else 0 := by
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  rcases hc' with rfl | rfl
  · simp only [yw, ↓reduceIte, show (BitVec.ofNat 64 0 - 0 : BitVec 64) = 0 by decide,
      show ((0 : BitVec 64).toNat = 1) = False by decide]
    induction n with
    | zero => rfl
    | succ n ih => rw [colsV_succ, ih]; simp
  · have e : (BitVec.ofNat 64 0 - 1 : BitVec 64) = BitVec.allOnes 64 := by decide
    simp only [yw, ↓reduceIte, e, BitVec.and_allOnes, BitVec.toNat_ofNat, show ((1 : BitVec 64).toNat = 1) = True by decide]
    exact colsV_congr fun i _ => Nat.mod_eq_of_lt (hf i)

/-- `[o] = [a] - [b] mod m`, for `[a]` and `[b]` below `m`. -/
theorem subCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hA : xv s.mem A k < m) (hB : xv s.mem B k < m) :
    WP isa (.block (subCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k = (xv s.mem A k + m - xv s.mem B k) % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  have honw := hC.onw
  unfold subCore subDiff
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ctx_of hc1 (u2.other _ (by decide)) u2.wr
  have g2 : ∀ r, r ∉ [.a5, .a6, .a7] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.1, g1 r (by simp [hr.2.1, hr.2.2])]
  have m2 : s2.mem = s1.mem := u2.mem
  have hXo : OpOk b A .t4 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.a], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.aal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.ain j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.adis j hj) (own_sub (by omega) (by omega))⟩
  have hYo : OpOk b B .t5 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.b'], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.bal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.bin j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.bdis j hj) (own_sub (by omega) (by omega))⟩
  show WP isa (.block (((List.range k).flatMap (sbbStep .t4 0 .t5 0 (T k)) ++
    [.li .a2 0, .sub .a2 .a2 .a5, .li .a5 0]) ++
    (List.range k).flatMap (adcStep (mkOf true) .a3 (T k) .a3 (N k) .t2 0))) s2 _
  refine WP.block_append (WP.block_append (WP.mono (sbbRow_ok hc2 (by omega) t8 hXo hYo
    (by rw [u2.gpr]; decide) k (Nat.le_refl _)) fun s3 h3 => ?_))
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => wp_li (by decide) fun s6 u6 => WP.block_nil ?_
  have g6 : ∀ r, r ∉ clobW → s6.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.other r hr.2.2.2.2.2.2.1, u5.other r hr.2.2.2.2.1, u4.other r hr.2.2.2.2.1,
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g2 r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have wr6 : s6.wr = s.wr := by rw [u6.wr, u5.wr, u4.wr, h3.wr, u2.wr, wr1]
  have rd6 : s6.rd = s.rd := by rw [u6.rd, u5.rd, u4.rd, h3.rd, u2.rd, rd1]
  have hc6 : Ctx b s6 := ctx_of hC.ctx (g6 _ (by decide)) wr6
  have a2v : s6.gpr .a2 = BitVec.ofNat 64 0 - s3.gpr .a5 := by
    rw [u6.other _ (by decide), u5.gpr, u4.gpr, u4.other _ (by decide)]
  have hD : DstOk O .t2 0 k s6 :=
    ⟨by rw [g6 _ (by decide), hC.o], by decide, hC.oal, by decide, by omega, by omega,
      fun j hj => by rw [Nat.zero_add, wr6]; exact hC.ow j hj⟩
  have osub : ∀ j ≤ k, Region.Sub ⟨O + BitVec.ofNat 64 0, 8 * j⟩ ⟨O, 8 * k⟩ := fun j hj => Offset.sub_base O (by omega)
  have hTo : OpOk O b .a3 (T k) 0 k s6 :=
    ⟨hc6.a3, by decide, fun j hj => by omega, fun j _ => al8 hc6.al (by omega), fun j _ => hc6.inR (by omega),
      fun j hj => disj_sub (disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))) (osub j (by omega))⟩
  have hNo : OpOk O b .a3 (N k) 0 k s6 :=
    ⟨hc6.a3, by decide, fun j hj => by omega, fun j _ => al8 hc6.al (by omega), fun j _ => hc6.inR (by omega),
      fun j hj => disj_sub (disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))) (osub j (by omega))⟩
  refine WP.mono (adcRow_ok hD hTo hNo (by rw [u6.gpr]; decide) k (Nat.le_refl _)) fun s7 h7 => ?_
  -- The numbers.
  have m01 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s1.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hsv := h3.val
  rw [m2, u2.gpr] at hsv
  have hAv : colsV (fun i => dw s1.mem A (0 + 8 * i)) k = xv s.mem A k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.adis i hi)
  have hBv : colsV (fun i => dw s1.mem B (0 + 8 * i)) k = xv s.mem B k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.bdis i hi)
  rw [hAv, hBv, show (BitVec.ofNat 64 0).toNat = 0 from rfl] at hsv
  have hav := h7.val
  rw [a2v, u6.gpr, show (BitVec.ofNat 64 0).toNat = 0 from rfl, m6,
    colsV_mask _ (fun _ => dw_lt _ _ _) h3.cy] at hav
  have hNv : colsV (fun i => dw s3.mem b (N k + 8 * i)) k = m := by
    rw [← nv1]
    refine colsV_congr fun i hi => ?_
    rw [dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m2]
  rw [hNv] at hav
  have hov : ov s7.mem O k = colsV (fun i => dw s7.mem O (0 + 8 * i)) k :=
    colsV_congr fun i _ => by rw [Nat.zero_add]
  have hE : (2 ^ 64) ^ k = 2 ^ (64 * k) := (Nat.pow_mul ..).symm
  have hres := sub_nat hsv h3.cy h7.cy rfl hav (colsV_lt _ (fun _ => dw_lt _ _ _) k)
    (by rw [← hov]; exact colsV_lt _ (fun _ => dw_lt _ _ _) k) hA hB
  refine ⟨fun r hr => by
      rw [h7.gpr r (fun h' => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
        rcases h' with h | h | h | h | h | h <;> simp [h])), g6 r hr],
    by rw [h7.rd, rd6], by rw [h7.wr, wr6], by rw [h7.sp, u6.sp, u5.sp, u4.sp, h3.sp, u2.sp, sp1], ?_,
    by rw [hov]; exact hres⟩
  · have sub3 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (T k), 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := sub_own (by omega) k30 (Nat.le_refl _) (by omega)
    have sub7 : ∀ r ∈ [(⟨O + BitVec.ofNat 64 0, 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), osub k (Nat.le_refl _)⟩
    have f3 : Frame [ownR k b, ⟨O, 8 * k⟩] s1.mem s3.mem := by rw [← m2]; exact h3.frame.sub sub3
    have f7 : Frame [ownR k b, ⟨O, 8 * k⟩] s3.mem s7.mem := by rw [← m6]; exact h7.frame.sub sub7
    exact ((f1.sub (sub_own (by omega) k30 (by omega) (by omega))).trans f3).trans f7

end VG.Proof.Weierstrass.RISCV64.GenWide
