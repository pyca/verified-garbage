module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.KeyMath
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyInv
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The halvings and the GCD of `vg_rsa_recover_primes_det` on RISC-V

* `twosInit_ok`, `twosBody_ok`, `twos_ok`: from `n` (narrow, `aN`) and `x = d e - 1`
  (wide, `wX`), `64 w` steps of `RecoverDet.twoStep` with `b = 64 W` on
  `(u, x, 2^k x)` (`twosSt`: narrow `aU`, narrow `aX2`, wide `wX3`), from
  `(n - 1, x mod 2^(64 w), x)`;
* `gcdStep_ok`, `gcd_ok`: the binary GCD on `([gU], [gV])` is `uvStep`, the
  `(u, v)` part of `KeyMath.invStep` (`invIter_uv`), so from `(x, u)`, `u`
  odd, it ends at `(0, gcd(x, u))` (`uv_done`), copied into the low half of
  the wide `wG`.
-/

@[expose] public section

namespace VG.Proof.Rsa

/-- `KeyMath.invStep`'s `(u, v)` part. -/
def uvStep (s : Nat × Nat) : Nat × Nat :=
  if s.1 % 2 = 1 then (if s.1 < s.2 then ((s.2 - s.1) / 2, s.1) else ((s.1 - s.2) / 2, s.2))
  else (s.1 / 2, s.2)

theorem invStep_uv (m : Nat) (st : Nat × Nat × Nat × Nat) :
    ((invStep m st).1, (invStep m st).2.1) = uvStep (st.1, st.2.1) := by
  obtain ⟨u, v, x₁, x₂⟩ := st
  simp only [invStep, uvStep]
  split <;> (try split) <;> rfl

/-- The `(u, v)` part of `invIter` ignores the cofactors. -/
theorem invIter_uv (m : Nat) (st : Nat × Nat × Nat × Nat) : ∀ k,
    ((invIter m k st).1, (invIter m k st).2.1) = uvStep^[k] (st.1, st.2.1)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', ← invIter_uv m st k]
    exact invStep_uv m _

/-- From `(a, m)` with `m` odd and `a m < 2^K`: `(0, gcd a m)`. -/
theorem uv_done {a m K : Nat} (hm : m % 2 = 1) (ha : a * m < 2 ^ K) :
    uvStep^[K] (a, m) = (0, Nat.gcd a m) := by
  have D := invIter_done (a := a) (K := K) hm ha
  dsimp only at D
  rw [← invIter_uv m (a, m, 1 % m, 0) K, D.1, D.2.1]

end VG.Proof.Rsa

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Rsa.RISCV64.Keys (seqs sub3 sel bitOf stBorrow andS half copy sOdd sB sC)
open VG.Impl.Rsa.RISCV64.RecoverDet (gcdStep gcd next gU gV gT1 gT2 gT3 aU aX2 wG)
open VG.Proof.Rsa (uvStep uv_done invU_arith borrow_iff)

/-- Index side conditions. -/
macro "rdidx" : tactic => `(tactic| ((try simp only [gU, gV, gT1, gT2, gT3, aU, aX2, wG, sOdd, sB, sC,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-! ## The GCD -/

/-- `gcdStep`: `uvStep` on `([gU], [gV])`. -/
theorem gcdStep_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) :
    WP isa gcdStep s fun t => Ws t B Z w N ∧
      Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t.mem ∧
      (num t.mem B w gU, num t.mem B w gV) = uvStep (num s.mem B w gU, num s.mem B w gV) ∧
      Keep opRegs s t := by
  have hsOdd : sOdd + 8 ≤ hdr := by decide
  have hsB : sB + 8 ≤ hdr := by decide
  have hsC : sC + 8 ≤ hdr := by decide
  have fU := h.fit64 (j := gU) (by rdidx)
  have fV := h.fit64 (j := gV) (by rdidx)
  have fT1 := h.fit64 (j := gT1) (by rdidx)
  have fT2 := h.fit64 (j := gT2) (by rdidx)
  generalize hu : num s.mem B w gU = u
  generalize hv : num s.mem B w gV = v
  unfold gcdStep
  -- 1: the low bit of `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by rdidx) hN' hsOdd (by decide)) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  rw [hu] at o1
  have u1 : num t1.mem B w gU = u := by rw [k1.num (by simp) (by decide) fU, hu]
  have v1 : num t1.mem B w gV = v := by rw [k1.num (by simp) (by decide) fV, hv]
  -- 2: `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (by rdidx) (by rdidx) (by rdidx) hN' (by rdidx) (by rdidx))
    fun t2 ⟨h2, k2, d2, b2, r2⟩ => ?_
  rw [u1, v1] at d2
  -- 3: the masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _), WP.block_append_iff]
  refine WP.mono (stBorrow_ok h2 hsB (by decide)) fun t3' ⟨h3', k3', sB3, r3'⟩ => ?_
  have o3 : slot t3'.mem B sOdd = u % 2 := by
    rw [k3'.slot hsOdd (by decide), k2.slot hsOdd (by simp), o1]
  refine WP.mono (andS_ok h3' hsC (by decide) hsOdd (by decide) hsB (by decide) (by rw [o3]; omega_arith)
    (by rw [sB3]; exact b2)) fun t3 ⟨h3, k3, c3, r3⟩ => ?_
  rw [o3, sB3] at c3
  have lt : (t2.gpr .t4).toNat = 1 ↔ u < v := by
    have := borrow_iff d2 (wordsVal_lt _ _ _ _) b2; omega_arith
  have c3' : slot t3.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [c3]
    rcases Nat.mod_two_eq_zero_or_one u with f | f
    · simp [f]
    · by_cases g : u < v
      · simp [f, g, lt.mpr g]
      · have : (t2.gpr .t4).toNat ≠ 1 := fun e => g (lt.mp e)
        simp only [f, g, and_false, ↓reduceIte, Nat.one_mul]
        omega_arith
  have K3 : Frame B w [] [sB, sC] t2.mem t3.mem := k3'.join k3
  have o3' : slot t3.mem B sOdd = u % 2 := by rw [k3.slot hsOdd (by decide), o3]
  have u3 : num t3.mem B w gU = u := by
    rw [K3.num (by simp) (by decide) fU, k2.num (by rdidx) (by simp) fU, u1]
  have v3 : num t3.mem B w gV = v := by
    rw [K3.num (by simp) (by decide) fV, k2.num (by rdidx) (by simp) fV, v1]
  -- 4: `v - u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by rdidx) (by rdidx) (by rdidx) hN' (by rdidx) (by rdidx))
    fun t4 ⟨h4, k4, d4, b4, r4⟩ => ?_
  rw [u3, v3] at d4
  have cs4 : slot t4.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [k4.slot hsC (by simp), c3']
  have cb4 : slot t4.mem B sC ≤ 1 := by rw [cs4]; split <;> omega_arith
  have u4 : num t4.mem B w gU = u := by rw [k4.num (by rdidx) (by simp) fU, u3]
  have v4 : num t4.mem B w gV = v := by rw [k4.num (by rdidx) (by simp) fV, v3]
  -- 5: `v' = c ? u : v`, in place.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_self_ok h4 (by rdidx) (by rdidx) hN' (by rdidx) hsC (by decide) cb4)
    fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  rw [u4, v4, cs4] at e5
  -- 6: `|u - v|`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (by rdidx) (by rdidx) (by rdidx) hN' (by rdidx) (by rdidx) hsC (by decide)
    (by rw [k5.slot hsC (by simp)]; exact cb4)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [k5.slot hsC (by simp), cs4, k5.num (by rdidx) (by simp) fT1, k5.num (by rdidx) (by simp) fT2,
    k4.num (by rdidx) (by simp) fT1, K3.num (by simp) (by decide) fT1] at e6
  -- 7: `u'` before the halving, in place.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have od6 : slot t6.mem B sOdd = u % 2 := by
    rw [k6.slot hsOdd (by simp), k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), o3']
  refine WP.mono (sel_self_ok h6 (by rdidx) (by rdidx) hN' (by rdidx) hsOdd (by decide)
    (by rw [od6]; omega_arith)) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [od6, e6, k6.num (by rdidx) (by simp) fU, k5.num (by rdidx) (by simp) fU, u4] at e7
  -- 8, 9: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hz : WP isa (.block [.li .t4 0]) t7 fun t8 =>
      (t8.gpr .t4 = 0 ∧ t8.mem = t7.mem) ∧ Keep [.t4] t7 t8 := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hz fun t8 ⟨⟨u9, u8⟩, k8⟩ => ?_
  have h8 := h7.of_keep k8
  refine WP.mono (half_ok h8 (by rdidx) hN' (by rw [u9]; decide)) fun t ⟨h9, k9, e9, _, r9⟩ => ?_
  rw [u9, u8] at e9
  rw [u8] at k9
  refine ⟨h9, ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
      (k7.mono.trans k9.mono))))))
  · have ev : num t.mem B w gV = (if u % 2 = 1 ∧ u < v then u else v) := by
      rw [k9.num (by rdidx) (by simp) fV, k7.num (by rdidx) (by simp) fV, k6.num (by rdidx) (by simp) fV, e5]
      by_cases c : u % 2 = 1 ∧ u < v <;> simp [c]
    have eu : num t.mem B w gU = (if u % 2 = 1 then (if u < v then (v - u) / 2 else (u - v) / 2)
        else u / 2) := by
      rw [e9, e7, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
      exact invU_arith d2 b2 (wordsVal_lt _ _ _ _) d4 b4 (wordsVal_lt _ _ _ _)
    rw [eu, ev]
    simp only [uvStep]
    by_cases f : u % 2 = 1 <;> by_cases g : u < v <;> simp [f, g]
  · exact Keep.trans' r1 (Keep.trans' r2 (Keep.trans' (Keep.mono r3' (by decide)) (Keep.trans' r3
      (Keep.trans' r4 (Keep.trans' r5 (Keep.trans' r6 (Keep.trans' r7 (Keep.trans' (Keep.mono k8 (by decide))
        r9))))))))

theorem shlk_ofNat (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.mul_mod_mod]

/-- The GCD's count: `s7 := 32 w + 4 L`. -/
theorem gcdCount_ok {s : State} {B : Addr} {Z w N L : Nat} (h : Ws s B Z w N)
    (hl : s.gpr .s2 = BitVec.ofNat 64 L) :
    WP isa (.block [.shift .sll .d .s7 .s9 5, .shift .sll .d .t5 .s2 2, .add .s7 .s7 .t5]) s fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (32 * w + 4 * L) ∧ t.mem = s.mem) ∧ Keep [.s7, .t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s9, hl, shlk_ofNat]
  exact (BitVec.ofNat_add _ _).symm

/-- The GCD's state after `i` iterations of two steps from `s0`. -/
structure GcdI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s0.mem t.mem
  regs : Keep (.s7 :: opRegs) s0 t
  value : (num t.mem B w gU, num t.mem B w gV) = uvStep^[2 * i] (num s0.mem B w gU, num s0.mem B w gV)

theorem gcdBody_ok {s0 t : State} {B : Addr} {Z w N i : Nat} (hN : 63 ≤ N) (hN' : N ≤ 2048)
    (inv : GcdI s0 B Z w N i t) :
    WP isa (seqs [gcdStep, gcdStep, .block next]) t fun u =>
      GcdI s0 B Z w N (i + 1) u ∧ u.gpr .s7 = t.gpr .s7 - BitVec.ofNat 64 1 := by
  have h := inv.ws
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcdStep_ok h hN hN') fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (gcdStep_ok h1 hN hN') fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  have hs : WP isa (.block next) t2 fun u =>
      (u.gpr .s7 = t2.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t2.mem) ∧ Keep [.s7] t2 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [next]
  refine WP.mono hs fun u ⟨⟨u7, m2⟩, k3⟩ => ?_
  have r7 : t2.gpr .s7 = t.gpr .s7 := (r2.gpr (by decide)).trans (r1.gpr (by decide))
  refine ⟨⟨h2.of_keep k3, ?_, ?_, ?_⟩, by rw [u7, r7]⟩
  · rw [m2]; exact inv.keep.trans (k1.trans k2)
  · exact Keep.trans' inv.regs (Keep.mono ((r1.trans r2).trans k3) (by decide))
  · rw [m2, e2, e1, inv.value, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_arith,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- `gcd`, narrow: `gcd(x, u)` from `x` in `aX2` and an odd `u` in `aU`, with
`x u < 2^(64 w + 8 L)` (`s2 = L = n_len`), into the low half of the wide `wG`,
its upper half kept (`hiW`, so a zero upper half makes the wide `wG` the GCD). -/
theorem gcd_ok {s : State} {B : Addr} {Z w N L : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) (hl : s.gpr .s2 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    WP isa gcd s fun t => Ws t B Z w N ∧
      Frame B w [gU, gV, gT1, gT2, gT3, 2 * wG] [sOdd, sB, sC] s.mem t.mem ∧
      hiW t.mem B w wG = hiW s.mem B w wG ∧
      (num s.mem B w aU % 2 = 1 →
        num s.mem B w aX2 * num s.mem B w aU < 2 ^ (64 * w + 8 * L) →
        num t.mem B w (2 * wG) = Nat.gcd (num s.mem B w aX2) (num s.mem B w aU)) ∧
      Keep (.s7 :: opRegs) s t := by
  have := h.wle
  have := h.wpos
  have hS : S w = 8 * (w + 2) := rfl
  have nw := h.nowrap
  have fit := h.fits
  have fX := h.fit64 (j := aX2) (by rdidx)
  have fU := h.fit64 (j := aU) (by rdidx)
  have fV := h.fit64 (j := gV) (by rdidx)
  have a34 : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ arr w gU := by
    simp only [arr, S, hdr_eq, wG, gU]; omega
  have fG : arr w (2 * wG) + 8 * w + 8 * (w + 2) ≤ 2 ^ 64 := by
    have := arr_mono (w := w) (show gU ≤ N by rdidx); omega
  generalize hx : num s.mem B w aX2 = x
  generalize hu : num s.mem B w aU = u
  unfold gcd
  -- The copies.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by rdidx) (by rdidx) hN' (by rdidx)) fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (by rdidx) (by rdidx) hN' (by rdidx)) fun t2 ⟨h2, k2, e2, r2, _⟩ => ?_
  rw [k1.num (by rdidx) (by simp) fU, hu] at e2
  rw [hx] at e1
  have e1' : num t2.mem B w gU = x := by rw [k2.num (by rdidx) (by simp) (h1.fit64 (by rdidx)), e1]
  -- The count.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hl2 : t2.gpr .s2 = BitVec.ofNat 64 L := by rw [r2.gpr (by decide), r1.gpr (by decide), hl]
  refine WP.mono (gcdCount_ok h2 hl2) fun t3 ⟨⟨c3, m3⟩, k3⟩ => ?_
  have h3 := h2.of_keep k3
  -- The loop.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hK : 32 * w + 4 * L < 2 ^ 64 := by omega_arith
  refine WP.mono (wp_countdown (body := seqs [gcdStep, gcdStep, .block next]) (cnt := .s7)
    (N := 32 * w + 4 * L) hK (by omega_arith) (GcdI t3 B Z w N)
    (fun i _ t inv _ => gcdBody_ok hN hN' inv)
    ⟨h3, Frame.refl _ _ _ _ _, Keep.refl _ _, rfl⟩ c3) fun t4 inv => ?_
  -- The copy into `wG`.
  refine WP.mono (copy_ok inv.ws (by rdidx) (by rdidx) hN' (by rdidx)) fun t ⟨h5, k5, e5, r5, o5⟩ => ?_
  have F4 : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t4.mem := by
    have F2 : Frame B w [gU, gV, gT1, gT2, gT3] [sOdd, sB, sC] s.mem t2.mem := Frame.join k1 k2
    have F3 := inv.keep
    rw [m3] at F3
    exact F2.trans F3
  refine ⟨h5, Frame.join F4 k5, ?_, fun hodd hlt => ?_, ?_⟩
  · simp only [hiW]
    rw [o5.wordsVal (.inr (by omega_arith)) fG]
    refine F4.words (fun j hj => ?_) (fun e he => ?_) fG
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have := arr_mono (w := w) (show gU ≤ j by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rdidx)
      omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      have := hdr_le_arr w (2 * wG)
      rcases he with rfl | rfl | rfl <;> simp only [sOdd, sB, sC, hdr_eq] at * <;> omega_arith
  · rw [e5]
    have v := inv.value
    rw [m3, e1', show num t2.mem B w gV = u from e2] at v
    have D := uv_done (a := x) (m := u) (K := 2 * (32 * w + 4 * L)) hodd
      (by rw [show 2 * (32 * w + 4 * L) = 64 * w + 8 * L by omega_arith]; exact hlt)
    rw [D] at v
    exact (Prod.mk.inj v).2
  · exact Keep.trans' (Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono r2 (by decide))
      (Keep.mono k3 (by decide)))) (Keep.trans' inv.regs (Keep.mono r5 (by decide)))

end VG.Proof.Rsa.RISCV64.Keys
