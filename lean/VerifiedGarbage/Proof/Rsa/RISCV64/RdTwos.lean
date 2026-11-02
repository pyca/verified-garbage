module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverDetModel
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

/-! ## The halvings -/

open VG.Impl.Rsa.RISCV64.RecoverDet (twosInit twosFlags halfIf twosBody twos ctxW ctxw aN aOne aT wX wX3 wT2
  sU sX sEven sBoth)

/-- The tail of `twosFlags`: `even := ¬u₀` and `both := ¬x₀ ∧ ¬u₀`, from the slots `sU`, `sX`. -/
theorem flagsTail_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block [.load .d .t5 .s11 sU, .load .d .t6 .s11 sX, .logicImm .xor .t5 .t5 1,
        .logicImm .xor .t6 .t6 1, .store .d .t5 .s11 sEven, .logic .and .t6 .t6 .t5, .store .d .t6 .s11 sBoth]) s
      fun u => (u.mem = (s.mem.writeW (off B sEven) (word s.mem B sU ^^^ 1#64)).writeW (off B sBoth)
        ((word s.mem B sX ^^^ 1#64) &&& (word s.mem B sU ^^^ 1#64))) ∧ Keep [.t5, .t6] s u := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s11, h.scr.st (d := sEven) (n := 8) (by simp only [sEven]; omega_arith),
    h.scr.al8 (d := sEven) (by simp only [sEven]; omega_arith) (by decide),
    h.scr.st (d := sBoth) (n := 8) (by simp only [sBoth]; omega_arith),
    h.scr.al8 (d := sBoth) (by simp only [sBoth]; omega_arith) (by decide),
    h.scr.ld (d := sU) (n := 8) (by simp only [sU]; omega_arith),
    h.scr.al8 (d := sU) (by simp only [sU]; omega_arith) (by decide),
    h.scr.ld (d := sX) (n := 8) (by simp only [sX]; omega_arith),
    h.scr.al8 (d := sX) (by simp only [sX]; omega_arith) (by decide),
    show sU < 2048 by decide, show sX < 2048 by decide, show sEven < 2048 by decide,
    show sBoth < 2048 by decide, add_ofNat_zero']

/-- Index side conditions of the halvings. -/
macro "twidx" : tactic => `(tactic| ((try simp only [aN, aOne, aT, aU, aX2, wX, wX3, wT2, sU, sX, sEven, sBoth,
  hdr_eq, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and,
  ne_eq]) <;> omega_arith))

/-- `twosFlags`: the low bits of `u` and `x`, `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
theorem twosFlags_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) :
    WP isa (.block twosFlags) s fun t => Ws t B Z w N ∧ Frame B w [] [sU, sX, sEven, sBoth] s.mem t.mem ∧
      slot t.mem B sEven = (if num s.mem B w aU % 2 = 0 then 1 else 0) ∧
      slot t.mem B sBoth = (if num s.mem B w aU % 2 = 0 ∧ num s.mem B w aX2 % 2 = 0 then 1 else 0) ∧
      Keep opRegs s t := by
  have hsU : sU + 8 ≤ hdr := by decide
  have hsX : sX + 8 ≤ hdr := by decide
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fX := h.fit64 (j := aX2) (by twidx)
  unfold twosFlags
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitOf_ok h (by twidx) hN' hsU (by decide)) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  refine WP.mono (bitOf_ok h1 (by twidx) hN' hsX (by decide)) fun t2 ⟨h2, k2, o2, r2⟩ => ?_
  rw [k1.num (by simp) (by decide) fX] at o2
  have o1' : slot t2.mem B sU = num s.mem B w aU % 2 := by rw [k2.slot hsU (by decide), o1]
  refine WP.mono (flagsTail_ok h2) fun t ⟨mt, kt⟩ => ?_
  have nw := h2.nowrap
  have hz := h2.hdr_le
  simp only [hdr_eq] at hz
  have sw1 := slot_write (m := t2.mem) (B := B) (w := w) (d := sEven) (word t2.mem B sU ^^^ 1#64)
    (by simp only [sEven]; omega_arith)
  have sw2 := slot_write (m := t2.mem.writeW (off B sEven) (word t2.mem B sU ^^^ 1#64)) (B := B) (w := w)
    (d := sBoth) ((word t2.mem B sX ^^^ 1#64) &&& (word t2.mem B sU ^^^ 1#64)) (by simp only [sBoth]; omega_arith)
  rw [← mt] at sw2
  have bU : (word t2.mem B sU).toNat ≤ 1 := by change slot t2.mem B sU ≤ 1; rw [o1']; omega_arith
  have bX : (word t2.mem B sX).toNat ≤ 1 := by change slot t2.mem B sX ≤ 1; rw [o2]; omega_arith
  have xU : (word t2.mem B sU ^^^ 1#64).toNat = (num s.mem B w aU % 2 + 1) % 2 := by
    rw [xor_bits bU (by decide)]; change (slot t2.mem B sU + 1) % 2 = _; rw [o1']
  have xX : (word t2.mem B sX ^^^ 1#64).toNat = (num s.mem B w aX2 % 2 + 1) % 2 := by
    rw [xor_bits bX (by decide)]; change (slot t2.mem B sX + 1) % 2 = _; rw [o2]
  refine ⟨h2.of_keep kt, (k1.join k2 (js := []) (ds := [sU, sX, sEven, sBoth])).join
    (sw1.1.join sw2.1 (js := []) (ds := [sU, sX, sEven, sBoth])) (js := []) (ds := [sU, sX, sEven, sBoth]), ?_, ?_,
    Keep.trans' r1 (Keep.trans' r2 (Keep.mono kt (by decide)))⟩
  · rw [sw2.1.slot hsE (by decide), sw1.2, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;> simp [e]
  · rw [sw2.2, and01 (by rw [xX]; omega_arith) (by rw [xU]; omega_arith), xX, xU]
    rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aU) with e | e <;>
      rcases Nat.mod_two_eq_zero_or_one (num s.mem B w aX2) with f | f <;> simp [e, f]

/-- `halfIf j sl`: `[j]` halved if the slot `sl` holds 1, through `aT`. -/
theorem halfIf_ok {s : State} {B : Addr} {Z w N j sl : Nat} (h : Ws s B Z w N) (hN : 63 ≤ N)
    (hN' : N ≤ 2048) (hj : j < N) (hjT : j ≠ aT) (hsl : sl + 8 ≤ hdr) (hsl8 : sl % 8 = 0)
    (bit : slot s.mem B sl ≤ 1) :
    WP isa (halfIf j sl) s fun t => Ws t B Z w N ∧ Frame B w [aT, j] [] s.mem t.mem ∧
      num t.mem B w j = (if slot s.mem B sl = 0 then num s.mem B w j else num s.mem B w j / 2) ∧
      Keep opRegs s t := by
  have fj := h.fit64 hj
  unfold halfIf
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by twidx) hj hN' (Ne.symm hjT)) fun t1 ⟨h1, k1, e1, r1, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have hz : WP isa (.block [.li .t4 0]) t1 fun t2 =>
      (t2.gpr .t4 = 0 ∧ t2.mem = t1.mem) ∧ Keep [.t4] t1 t2 := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero]
  refine WP.mono hz fun t2 ⟨⟨z2, m2⟩, k2⟩ => ?_
  have h2 := h1.of_keep k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (half_ok h2 (by twidx) hN' (by rw [z2]; decide)) fun t3 ⟨h3, k3, e3, _, r3⟩ => ?_
  rw [z2, m2, e1, show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at e3
  rw [m2] at k3
  have sl3 : slot t3.mem B sl = slot s.mem B sl := by
    rw [k3.slot hsl (by simp), k1.slot hsl (by simp)]
  have j3 : num t3.mem B w j = num s.mem B w j := by
    rw [k3.num (by simp; omega_arith) (by simp) fj, k1.num (by simp; omega_arith) (by simp) fj]
  refine WP.mono (sel_self_ok h3 hj (by twidx) hN' hjT hsl hsl8 (by rw [sl3]; exact bit))
    fun t ⟨h4, k4, e4, r4⟩ => ?_
  rw [sl3, j3, e3] at e4
  exact ⟨h4, (k1.join k3 (js := [aT, j]) (ds := [])).join k4 (js := [aT, j]) (ds := []), e4, Keep.trans' r1 (Keep.trans' (Keep.mono k2 (by decide))
    (Keep.trans' r3 r4))⟩

/-- The registers the halvings and the GCD change. -/
abbrev rdRegs : List Reg := .s7 :: .s9 :: .s10 :: opRegs

/-- The halvings' state: `(u, x, 2^k x)`, narrow, narrow, wide. -/
def twosSt (m : Mem) (B : Addr) (w : Nat) : Nat × Nat × Nat :=
  (num m B w aU, num m B w aX2, num m B (W2 w) wX3)

theorem Frame.toNarrow1 {B : Addr} {w j : Nat} {ds : List Nat} {m m' : Mem}
    (h : Frame B (W2 w) [j] ds m m') : Frame B w [2 * j, 2 * j + 1] ds m m' := by
  simpa only [halves, List.flatMap_cons, List.flatMap_nil, List.append_nil] using h.toNarrow

/-- `twosBody`, narrow view to narrow view: one `twoStep` with `b = 64 W`. -/
theorem twosBody_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z w N)
    (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) :
    WP isa twosBody s fun t => Ws t B Z w N ∧
      Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      twosSt t.mem B w = VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w) (twosSt s.mem B w) ∧
      t.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 1 ∧ Keep rdRegs s t := by
  have hsE : sEven + 8 ≤ hdr := by decide
  have hsB : sBoth + 8 ≤ hdr := by decide
  have fU := h.fit64 (j := aU) (by twidx)
  have fX := h.fit64 (j := aX2) (by twidx)
  have hM' : M ≤ 2048 := by omega_arith
  generalize hu : num s.mem B w aU = u
  generalize hx : num s.mem B w aX2 = x
  generalize hX : num s.mem B (W2 w) wX3 = X
  unfold twosBody
  -- 1: the flags.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosFlags_ok h hN hN') fun t1 ⟨h1, k1, f1, g1, r1⟩ => ?_
  try simp only [hu, hx] at f1 g1
  -- 2: `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h1 hN hN' (by twidx) (by twidx) hsE (by decide) (by rw [f1]; split <;> omega_arith))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [f1, k1.num (by simp) (by decide) fU, hu] at e2
  have g2 : slot t2.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k2.slot hsB (by simp), g1]
  -- 3: `x`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (halfIf_ok h2 hN hN' (by twidx) (by twidx) hsB (by decide) (by rw [g2]; split <;> omega_arith))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [g2, k2.num (by simp [aT, aU, aX2]) (by simp) fX, k1.num (by simp) (by decide) fX, hx] at e3
  have g3 : slot t3.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k3.slot hsB (by simp), g2]
  have u3 : num t3.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
    rw [k3.num (by simp [aT, aU, aX2]) (by simp) fU, e2]
  -- 4: the wide view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxW_ok h3 hW hMN) fun t4 ⟨⟨h4, m4⟩, k4⟩ => ?_
  have fX3 := h4.fit64 (j := wX3) (by twidx)
  have fT2 := h4.fit64 (j := wT2) (by twidx)
  have X4 : num t4.mem B (W2 w) wX3 = X := by
    rw [m4, k3.toWide.num (by decide) (by simp) fX3, k2.toWide.num (by decide) (by simp) fX3,
      k1.toWide.num (by simp) (by decide) fX3, hX]
  -- 5: `2^k x` copied, 6: doubled.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hM' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [X4] at e5
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shl_ok h5 (by twidx) hM') fun t6 ⟨h6, k6, _, e6, b6, r6⟩ => ?_
  rw [e5] at e6
  -- 7: the selection.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have g6 : slot t6.mem B sBoth = (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) := by
    rw [k6.slot hsB (by simp), k5.slot hsB (by simp), m4, g3]
  refine WP.mono (sel_self_ok h6 (by twidx) (by twidx) hM' (by twidx) hsB (by decide)
    (by rw [g6]; split <;> omega_arith)) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [g6, k6.num (by simp [wT2, wX3]) (by simp) fX3, k5.num (by simp [wT2, wX3]) (by simp) fX3, X4] at e7
  -- 8: the narrow view, a step less.
  show WP isa (.block (ctxw ++ next)) t7 _
  rw [WP.block_append_iff]
  refine WP.mono (ctxw_ok h7 h.wpos h.fits) fun t8 ⟨⟨h8, m8⟩, k8⟩ => ?_
  have hs : WP isa (.block next) t8 fun u =>
      (u.gpr .s7 = t8.gpr .s7 - BitVec.ofNat 64 1 ∧ u.mem = t8.mem) ∧ Keep [.s7] t8 u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [next]
  refine WP.mono hs fun t ⟨⟨u7, m9⟩, k9⟩ => ?_
  have W8 : Frame B w [2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [] t4.mem t7.mem :=
    (k5.toNarrow1.join k6.toNarrow1 (js := [2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1]) (ds := [])).join
      k7.toNarrow1 (js := [2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1]) (ds := [])
  have fU' := h8.fit64 (j := aU) (by twidx)
  have fX' := h8.fit64 (j := aX2) (by twidx)
  refine ⟨h8.of_keep k9, ?_, ?_, ?_, ?_⟩
  · rw [m9, m8]
    have A : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
        s.mem t3.mem :=
      (k1.join k2 (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1])
        (ds := [sU, sX, sEven, sBoth])).join k3
        (js := [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1]) (ds := [sU, sX, sEven, sBoth])
    rw [← m4] at A
    exact A.join W8
  · have eU : num t.mem B w aU = (if (if u % 2 = 0 then 1 else 0) = 0 then u else u / 2) := by
      rw [m9, m8, W8.num (by simp [aU, wT2, wX3]) (by simp) fU', m4, u3]
    have eX : num t.mem B w aX2 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then x else x / 2) := by
      rw [m9, m8, W8.num (by simp [aX2, wT2, wX3]) (by simp) fX', m4, e3]
    have eW : num t.mem B (W2 w) wX3 = (if (if u % 2 = 0 ∧ x % 2 = 0 then 1 else 0) = 0 then X
        else 2 * X % 2 ^ (64 * W2 w)) := by
      rw [m9, m8, e7]
      congr 1
      rw [← e6, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _)]
    simp only [twosSt, eU, eX, eW, hu, hx, hX, VG.Proof.Rsa.RecoverDet.twoStep]
    rcases Nat.mod_two_eq_zero_or_one u with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one x with b | b <;> simp [a, b]
  · have r7 : t8.gpr .s7 = s.gpr .s7 := by
      rw [k8.gpr (by decide), r7.gpr (by decide), r6.gpr (by decide), r5.gpr (by decide), k4.gpr (by decide),
        r3.gpr (by decide), r2.gpr (by decide), r1.gpr (by decide)]
    rw [u7, r7]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono r2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono k4 (by decide))
        (Keep.trans' (Keep.mono r5 (by decide)) (Keep.trans' (Keep.mono r6 (by decide))
          (Keep.trans' (Keep.mono r7 (by decide)) (Keep.trans' (Keep.mono k8 (by decide))
            (Keep.mono k9 (by decide)))))))))

/-- A subtraction with its borrow is `wsub`. -/
theorem sub_eq_wsub {b x a c β : Nat} (e : x + c = a + 2 ^ b * β) (hx : x < 2 ^ b) (ha : a < 2 ^ b)
    (hc : c < 2 ^ b) (hβ : β ≤ 1) : x = VG.Proof.Rsa.RecoverDet.wsub b a c := by
  unfold VG.Proof.Rsa.RecoverDet.wsub
  rcases (show β = 0 ∨ β = 1 by omega_arith) with rfl | rfl
  · rw [show a + 2 ^ b - c = (a - c) + 2 ^ b by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- `twosInit`, from the wide view: `2^k x := x`; `u := n - 1` and `x := x mod 2^(64 w)` (narrow);
`s7 := 64 w`; the narrow view after. -/
theorem twosInit_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M) (hMN : 2 * M ≤ N)
    (h1 : num s.mem B w aOne = 0) :
    WP isa twosInit s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2] [] s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
        num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ Keep rdRegs s t := by
  have hM' : M ≤ 2048 := by omega_arith
  have fXw := h.fit64 (j := wX) (by twidx)
  unfold twosInit
  -- 1: `2^k x := x` (wide).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h (by twidx) (by twidx) hM' (by twidx)) fun t1 ⟨h1', k1, e1, r1, _⟩ => ?_
  -- 2: the narrow view.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok h1' hw hNZ) fun t2 ⟨⟨h2, m2⟩, k2⟩ => ?_
  have fO := h2.fit64 (j := aOne) (by twidx)
  have fN := h2.fit64 (j := aN) (by twidx)
  have fX := h2.fit64 (j := 2 * wX) (by twidx)
  have fU := h2.fit64 (j := aU) (by twidx)
  have K1 := k1.toNarrow1
  -- 3: one.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setOne_ok h2 (by twidx) hN') fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [m2, K1.num (by simp [aOne, wX3]) (by simp) fO, h1] at e3
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero] at e3
  -- 4: `u = n - 1`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by twidx) (by twidx) (by twidx) hN' (by twidx) (by twidx))
    fun t4 ⟨h4, k4, e4, b4, r4⟩ => ?_
  rw [e3, k3.num (by simp [aOne, aN]) (by simp) fN, m2, K1.num (by simp [aN, wX3]) (by simp) fN] at e4
  have u4 : num t4.mem B w aU = VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1 :=
    sub_eq_wsub e4 (wordsVal_lt _ _ _ _) (wordsVal_lt _ _ _ _) (Nat.one_lt_two_pow (by omega_arith)) b4
  -- 5: `x` (narrow).
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h4 (by twidx) (by twidx) hN' (by twidx)) fun t5 ⟨h5, k5, e5, r5, _⟩ => ?_
  rw [k4.num (by simp [aU, wX]) (by simp) fX, k3.num (by simp [aOne, wX]) (by simp) fX, m2,
    K1.num (by simp [wX, wX3]) (by simp) fX, num_low] at e5
  -- 6: the count.
  have hc : WP isa (.block [.shift .sll .d .s7 .s9 6]) t5 fun t =>
      (t.gpr .s7 = BitVec.ofNat 64 (64 * w) ∧ t.mem = t5.mem) ∧ Keep [.s7] t5 t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5.s9, shlk_ofNat]
  refine WP.mono hc fun t ⟨⟨c6, m6⟩, k6⟩ => ?_
  have fX3 := h1'.fit64 (j := wX3) (by twidx)
  have fA := h5.fit64 (j := aX2) (by twidx)
  refine ⟨h5.of_keep k6, ?_, ?_, ?_, c6, ?_⟩
  · rw [m6]
    have A := K1
    rw [← m2] at A
    exact (A.join k3 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])).join
      (k4.join k5 (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := []))
      (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2]) (ds := [])
  · rw [m6, k5.num (by simp [aOne, aX2]) (by simp) fO, k4.num (by simp [aOne, aU]) (by simp) fO, e3]
  · simp only [twosSt]
    rw [m6, k5.num (by simp [aU, aX2]) (by simp) fU, u4, e5,
      k5.toWide.num (by decide) (by simp) fX3, k4.toWide.num (by decide) (by simp) fX3,
      k3.toWide.num (by decide) (by simp) fX3, m2, e1]
  · exact Keep.trans' (Keep.mono r1 (by decide)) (Keep.trans' (Keep.mono k2 (by decide))
      (Keep.trans' (Keep.mono r3 (by decide)) (Keep.trans' (Keep.mono r4 (by decide))
        (Keep.trans' (Keep.mono r5 (by decide)) (Keep.mono k6 (by decide))))))

/-- The halvings' state after `i` steps from `s0`. -/
structure TwosI (s0 : State) (B : Addr) (Z w N : Nat) (i : Nat) (t : State) : Prop where
  ws : Ws t B Z w N
  keep : Frame B w [aU, aX2, aT, 2 * wT2, 2 * wT2 + 1, 2 * wX3, 2 * wX3 + 1] [sU, sX, sEven, sBoth]
    s0.mem t.mem
  regs : Keep rdRegs s0 t
  value : twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[i] (twosSt s0.mem B w)

/-- `twos`, from the wide view after `d e - 1`: `64 w` steps from `(n - 1, x mod 2^(64 w), x)`,
`n` narrow in `aN` and `x` wide in `wX`; the narrow view after. -/
theorem twos_ok {s : State} {B : Addr} {Z w N M : Nat} (h : Ws s B Z (W2 w) M)
    (hw : 0 < w) (hNZ : arr w N ≤ Z) (hN : 63 ≤ N) (hN' : N ≤ 2048) (hM : 20 ≤ M)
    (hMN : 2 * M ≤ N) (hW : W2 w ≤ 1024) (h1 : num s.mem B w aOne = 0) :
    WP isa twos s fun t => Ws t B Z w N ∧
      Frame B w [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1] [sU, sX, sEven, sBoth]
        s.mem t.mem ∧
      num t.mem B w aOne = 1 ∧
      twosSt t.mem B w = (VG.Proof.Rsa.RecoverDet.twoStep (64 * W2 w))^[64 * w]
        (VG.Proof.Rsa.RecoverDet.wsub (64 * w) (num s.mem B w aN) 1,
          num s.mem B (W2 w) wX % 2 ^ (64 * w), num s.mem B (W2 w) wX) ∧
      Keep rdRegs s t := by
  unfold twos
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (twosInit_ok h hw hNZ hN hN' hM hMN h1) fun t0 ⟨h0, k0, o0, e0, c0, r0⟩ => ?_
  have hK : 64 * w < 2 ^ 64 := by have := h0.wle; omega_arith
  refine WP.mono (wp_countdown (body := twosBody) (cnt := .s7) (N := 64 * w) hK (by omega_arith)
    (TwosI t0 B Z w N)
    (fun i _ t inv _ => WP.mono (twosBody_ok inv.ws hN hN' hM hMN hW) fun u ⟨hu, ku, eu, cu, ru⟩ =>
      ⟨⟨hu, inv.keep.trans ku, Keep.trans' inv.regs ru, by
        rw [eu, inv.value, Function.iterate_succ_apply']⟩, cu⟩)
    ⟨h0, Frame.refl _ _ _ _ _, Keep.refl _ _, rfl⟩ c0) fun t inv => ?_
  have fO := h0.fit64 (j := aOne) (by twidx)
  refine ⟨inv.ws, ?_, ?_, ?_, Keep.trans' r0 inv.regs⟩
  · exact k0.join inv.keep (js := [2 * wX3, 2 * wX3 + 1, aOne, aU, aX2, aT, 2 * wT2, 2 * wT2 + 1])
      (ds := [sU, sX, sEven, sBoth])
  · rw [inv.keep.num (by simp [aOne, aU, aX2, aT, wT2, wX3]) (by decide) fO, o0]
  · rw [inv.value, e0]

end VG.Proof.Rsa.RISCV64.Keys
