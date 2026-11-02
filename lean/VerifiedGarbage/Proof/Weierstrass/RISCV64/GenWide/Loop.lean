module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Red
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Arithmetic modulo a wide modulus on RISC-V: the rounds of the multiplication

The `k` rounds of `mulCore` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from
`T = 0`: after round `i`, the `k + 1` words of `T` are `V` with
`V 2^(64 i) = a (b mod 2^(64 i)) + Q m` for some `Q < 2^(64 i)`, and
`V < 2^(64 k) + m` (`loop_ok`), Montgomery's operand scanning (CIOS).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_frame al8 colsV)

theorem cios_step {V a Bi Bc Q M q E W : Nat} (hinv : V * E = a * Bc + Q * M)
    (hW : 2 ^ 64 * W = V + a * Bi + q * M) :
    W * (E * 2 ^ 64) = a * (Bc + E * Bi) + (Q + E * q) * M := by
  have h1 : W * (E * 2 ^ 64) = (V + a * Bi + q * M) * E := by
    rw [← hW, Nat.mul_comm (2 ^ 64) W, Nat.mul_comm E, Nat.mul_assoc]
  rw [h1, Nat.add_mul, Nat.add_mul, hinv, Nat.mul_add, Nat.add_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem cios_bound {V a Bc Q M E R : Nat} (hinv : V * E = a * Bc + Q * M) (ha : a < R) (hB : Bc < E)
    (hQ : Q < E) : V < R + M := by
  have hE : 0 < E := by omega
  apply Nat.lt_of_mul_lt_mul_right (a := E)
  have h1 : a * Bc ≤ a * E := Nat.mul_le_mul_left _ (by omega)
  have h2 : a * E < R * E := Nat.mul_lt_mul_of_pos_right ha hE
  have h3 : Q * M ≤ E * M := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, hinv]
  rw [Nat.mul_comm E M] at h3
  omega

theorem colsV_lt (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) : ∀ n, colsV f n < (2 ^ 64) ^ n
  | 0 => by simp [colsV]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 := Nat.pow_succ ..
    rw [colsV_succ, e]
    have := colsV_lt f hf n
    have := hf n
    have : (2 ^ 64) ^ n * f n ≤ (2 ^ 64) ^ n * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega

/-- The words of `b`'s operand, `B`. -/
abbrev bv (m : Mem) (B : Addr) (i : Nat) : Nat := colsV (fun j => dw m B (8 * j)) i

/-- What the rounds need. -/
structure LoopOk (k : Nat) (b A B : Addr) (m' : Nat) (s0 : State) : Prop where
  mo : MulOk k b A s0
  t5 : s0.gpr .t5 = B
  bal : B.toNat % 8 = 0
  bin : ∀ i < k, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  bdis : ∀ i < k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩
  t6 : s0.gpr .t6 = BitVec.ofNat 64 m'
  m'lt : m' < 2 ^ 64
  inv : dw s0.mem b (N k) * m' % 2 ^ 64 = 2 ^ 64 - 1
  zero : tv k s0.mem b (k + 1) = 0

/-- After round `i`. -/
structure LoopInv (k : Nat) (b A B : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ .a4 :: clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s.mem
  val : ∃ Q < (2 ^ 64) ^ i, tv k s.mem b (k + 1) * (2 ^ 64) ^ i = xv s0.mem A k * bv s0.mem B i + Q * nv k s0.mem b
  lt : tv k s.mem b (k + 1) < 2 ^ (64 * k) + nv k s0.mem b

/-- The words outside `T` are as they were. -/
theorem frame_dw {k : Nat} {b : Addr} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] m m')
    {P : Addr} {d : Nat} (hd : Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩) :
    dw m' P d = dw m P d :=
  dw_frame hf fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd

theorem nv_frame {k : Nat} {b : Addr} {m m' : Mem} (hk : 1 ≤ k) (hk' : k ≤ 30)
    (hf : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] m m') {d : Nat} (hd : N k ≤ d) (hd' : d + 8 ≤ 2048) :
    dw m' b d = dw m b d := by
  obtain ⟨hNT, -, -⟩ := N_facts k hk hk'
  exact frame_dw hf (Offset.disjoint b (.inr (by omega)) (by omega) (by omega))

/-- Round `i`. -/
theorem loopStep_ok {k : Nat} {b A B : Addr} {m' : Nat} {s0 : State} (hL : LoopOk k b A B m' s0) {i : Nat}
    (hi : i < k) {s : State} (h : LoopInv k b A B s0 i s) :
    WP isa (.block (mulRound k i ++ redRound k)) s (LoopInv k b A B s0 (i + 1)) := by
  have k7 := hL.mo.k7
  have k30 := hL.mo.k32
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  have hb := hL.mo.nowrap
  have hmo : MulOk k b A s := hL.mo.of (h.gpr _ (by decide)) (h.gpr _ (by decide)) h.rd h.wr
  refine WP.block_append (WP.mono (mulRound_ok hmo (B := B) (i := i) (by rw [h.gpr _ (by decide), hL.t5])
    (al8 hL.bal (by omega)) (by omega) (by rw [h.rd, h.wr]; exact hL.bin i hi)) fun s1 ⟨g1, rd1, wr1, sp1, f1, v1⟩ => ?_)
  have hred : RedOk k b m' s1 :=
    { ctx := ctx_of hmo.ctx (g1 _ (by decide)) wr1
      nowrap := hb
      t6 := by rw [g1 _ (by decide), h.gpr _ (by decide), hL.t6]
      m'lt := hL.m'lt
      inv := by
        rw [nv_frame (by omega) k30 f1 (Nat.le_refl _) (by omega),
          nv_frame (by omega) k30 h.frame (Nat.le_refl _) (by omega)]
        exact hL.inv
      k7 := k7
      k30 := k30 }
  refine WP.mono (redRound_ok hred) fun s2 ⟨g2, rd2, wr2, sp2, f2, w, v2⟩ => ?_
  -- The numbers, all as in `s0`.
  have fT : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s2.mem :=
    (h.frame.trans f1).trans (f2.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩)
  have hA : xv s.mem A k = xv s0.mem A k :=
    colsV_congr fun j hj => frame_dw h.frame (hL.mo.adis j hj (k + 2) (Nat.le_refl _))
  have hB : dw s.mem B (8 * i) = dw s0.mem B (8 * i) := frame_dw h.frame (hL.bdis i hi)
  have hN1 : nv k s1.mem b = nv k s0.mem b :=
    colsV_congr fun j hj => by
      rw [nv_frame (by omega) k30 f1 (by omega) (by omega),
        nv_frame (by omega) k30 h.frame (by omega) (by omega)]
  rw [hA, hB] at v1
  rw [hN1] at v2
  obtain ⟨Q, hQ, hv⟩ := h.val
  generalize hq : dw s1.mem b (T k) * m' % 2 ^ 64 = q at v2
  have hq64 : q < 2 ^ 64 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
  -- The top word does not carry.
  have hw : w = 0 := by
    by_contra hw0
    have hw1 : (2 ^ 64) ^ (k + 1) ≤ (2 ^ 64) ^ (k + 1) * w := Nat.le_mul_of_pos_right _ (by omega)
    have hAk : xv s0.mem A k < (2 ^ 64) ^ k := colsV_lt _ (fun j => dw_lt _ _ _) k
    have hNk : nv k s0.mem b < (2 ^ 64) ^ k := colsV_lt _ (fun j => dw_lt _ _ _) k
    have hp : xv s0.mem A k * dw s0.mem B (8 * i) ≤ (2 ^ 64) ^ k * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by have := dw_lt s0.mem B (8 * i); omega)
    have hqN : q * nv k s0.mem b ≤ (2 ^ 64 - 1) * (2 ^ 64) ^ k := Nat.mul_le_mul (by omega) (by omega)
    have hlt := h.lt
    rw [show 2 ^ (64 * k) = (2 ^ 64) ^ k from Nat.pow_mul ..] at hlt
    rw [Nat.mul_sub, Nat.mul_one] at hp
    rw [Nat.sub_mul, Nat.one_mul] at hqN
    have e1 : (2 ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 := Nat.pow_succ ..
    have e2 : (2 ^ 64) ^ k * 2 ^ 64 = 2 ^ 64 * (2 ^ 64) ^ k := Nat.mul_comm ..
    rw [v1] at v2
    generalize (2 ^ 64) ^ k = E at *
    generalize (2 ^ 64) ^ (k + 1) = F at *
    omega
  subst hw
  rw [Nat.mul_zero, Nat.add_zero, v1] at v2
  obtain ⟨Q', hQ', hv'⟩ : ∃ Q' < (2 ^ 64) ^ (i + 1),
      tv k s2.mem b (k + 1) * (2 ^ 64) ^ (i + 1) =
        xv s0.mem A k * bv s0.mem B (i + 1) + Q' * nv k s0.mem b := by
    have inv' := cios_step hv v2
    have e : ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 := Nat.pow_succ ..
    refine ⟨Q + (2 ^ 64) ^ i * q, ?_, ?_⟩
    · rw [e]
      have : (2 ^ 64) ^ i * q ≤ (2 ^ 64) ^ i * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_sub, Nat.mul_one] at this
      omega
    · rw [e]
      show _ = xv s0.mem A k * colsV _ (i + 1) + _
      rw [colsV_succ]
      exact inv'
  refine ⟨fun r hr => by rw [g2 r hr, g1 r hr, h.gpr r hr], by rw [rd2, rd1, h.rd], by rw [wr2, wr1, h.wr],
    by rw [sp2, sp1, h.sp], fT, ⟨Q', hQ', hv'⟩, ?_⟩
  rw [Nat.pow_mul]
  exact cios_bound hv' (colsV_lt _ (fun j => dw_lt _ _ _) k) (colsV_lt _ (fun j => dw_lt _ _ _) _) hQ'

/-- The rounds. -/
theorem loop_ok {k : Nat} {b A B : Addr} {m' : Nat} {s0 : State} (hL : LoopOk k b A B m' s0) :
    ∀ i ≤ k, WP isa (.block ((List.range i).flatMap fun i => mulRound k i ++ redRound k)) s0
      (LoopInv k b A B s0 i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      ⟨0, by decide, by rw [hL.zero]; simp [bv, colsV]⟩, by rw [hL.zero]; exact Nat.add_pos_left (Nat.two_pow_pos _) _⟩
  | i + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (loop_ok hL i (by omega)) fun s h => loopStep_ok hL (i := i) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide
