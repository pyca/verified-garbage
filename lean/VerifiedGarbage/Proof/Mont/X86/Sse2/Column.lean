module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Fold
public import VerifiedGarbage.Proof.Mont.X86.Sse2.CarryMath
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! # The columns

`ColsI`: after the columns `j < k`, from the state `s0` the columns started
in, the carry `c` (at `S + 16`), the quotient digits `q` and the result's
words (`rvalT`), both in reverse at `S + 24`, the result's word `j`
replacing the digit `q_j`, dead, satisfy

`2^(32 k) c + 2^(32 N) T = Σ_(i+j<k) A_i B_j 2^(32 (i+j)) + Σ_(i+j<k) q_i M_j 2^(32 (i+j))`,

`A'` (`A` in reverse) is at `S + 24 + 4 N`, the two latest digits are in
`xmm6` while `k < N`, and only the function's scratch has changed. A column
keeps it (`column_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- The numbers' offsets in the working space of `L` bytes: `A`, `B`, `M`
and the result `O` of `N ≥ 2` words, `-M⁻¹ mod 2³²` at `inv`, the scratch of
`8 N + 28` bytes at `S`, apart from the others, and `O` apart from `M` and
`inv`. -/
structure Lay (L N S mo inv o a b : Nat) : Prop where
  hN : 0 < N
  hN2 : 2 ≤ N
  hN28 : N < 2 ^ 29
  a_le : a + 4 * N ≤ L
  b_le : b + 4 * N ≤ L
  mo_le : mo + 4 * N ≤ L
  inv_le : inv + 4 ≤ L
  o_le : o + 4 * N ≤ L
  s_le : S + 8 * N + 28 ≤ L
  sa : a + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ a
  sb : b + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ b
  smo : mo + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ mo
  sinv : inv + 4 ≤ S ∨ S + 8 * N + 28 ≤ inv
  so : o + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ o

/-- The result's words stored so far, word `j` at word `N - 1 - j` of `S + 24`. -/
def rvalT (m : Mem) (W : Addr) (N S : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rvalT m W N S n + 2 ^ (32 * n) * w32 m W (S + 24 + 4 * (N - 1 - n))

theorem rvalT_congr {m m' : Mem} {W : Addr} {N S : Nat} :
    ∀ {n : Nat}, (∀ j < n, w32 m' W (S + 24 + 4 * (N - 1 - j)) = w32 m W (S + 24 + 4 * (N - 1 - j))) →
      rvalT m' W N S n = rvalT m W N S n
  | 0, _ => rfl
  | n + 1, h => by
    rw [rvalT, rvalT, rvalT_congr fun j hj => h j (by omega_arith), h n (by omega_arith)]

/-- After the columns `j < k`. -/
structure ColsI (s0 : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c : Nat) (q : Nat → Nat)
    (t : State) : Prop where
  ws : Ws t W L
  prm : Params t W L V 12
  out : Outs W [(S, 8 * N + 28)] s0.mem t.mem
  ecx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)
  mcdt : t.mcdt = s0.mcdt
  carry : w32 t.mem W (S + 16) + 2 ^ 32 * w32 t.mem W (S + 20) = c
  bound : c ≤ (2 * N + 2) * 2 ^ 32
  revA : ∀ i < N, w32 t.mem W (S + 24 + 4 * N + 4 * (N - 1 - i)) = digits s0.mem W a i
  qlt : ∀ j, q j ≤ 2 ^ 32 - 1
  qs : RevQ t.mem W N S q (k - N) (min k N)
  win : k < N → Window t W N mo k q
  eq : (2 ^ 32) ^ k * c + (2 ^ 32) ^ N * rvalT t.mem W N S (k - N) =
    Column.partSum (2 ^ 32) (digits s0.mem W a) (digits s0.mem W b) N k +
    Column.partSum (2 ^ 32) (Column.prefixDigits q k) (digits s0.mem W mo) N k
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s0 t

theorem digits_lt (m : Mem) (W : Addr) (x i : Nat) : digits m W x i ≤ 2 ^ 32 - 1 := by
  have := (m.readW (off W (x + 4 * i)) 32).isLt; simp only [digits, w32]; omega_arith

theorem coeff_le (m : Mem) (W : Addr) (y : Nat) {N k : Nat} (q : Nat → Nat) (hq : ∀ i, q i ≤ 2 ^ 32 - 1) :
    Column.coeff q (digits m W y) N k ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
  Column.coeff_bound (fun i _ => hq i) (fun _ _ => digits_lt _ _ _ _)

/-- A word apart from every range that changed. -/
theorem Outs.w32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have := h.val32 (k := 1) (by simpa using hd) (by simpa using hd')
  simpa [val32] using this

/-- The scratch's changes keep a number apart from it. -/
theorem digits_out {m m' : Mem} {W : Addr} {L N S x : Nat} (hn : W.toNat + L ≤ 2 ^ 32)
    (O : Outs W [(S, 8 * N + 28)] m m') (hx : x + 4 * N ≤ L) (sep : x + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ x) :
    ∀ i < N, digits m' W x i = digits m W x i := fun i hi =>
  Outs.w32 O (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)

theorem outs_widen {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    Outs base rs' m₁ m₂ :=
  fun x hx => h x (hr _ hx)

/-- Changes within ranges each inside one of `rs'`. -/
theorem outs_sub {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m₁ m₂ :=
  outs_widen h fun y hy r h' => by
    obtain ⟨r', hr', h1, h2⟩ := hr r h'
    have := hy r' hr'
    omega_arith

theorem outs_sub1 {base : Addr} {rs' : List (Nat × Nat)} {m₁ m₂ : Mem} {a n : Nat} (h : Outs base [(a, n)] m₁ m₂)
    {r : Nat × Nat} (hr : r ∈ rs') (h1 : r.1 ≤ a) (h2 : a + n ≤ r.1 + r.2) : Outs base rs' m₁ m₂ :=
  outs_sub h fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨r, hr, h1, h2⟩

theorem outs_sub2 {base : Addr} {rs' : List (Nat × Nat)} {m₁ m₂ : Mem} {a n b p : Nat}
    (h : Outs base [(a, n), (b, p)] m₁ m₂) {r q : Nat × Nat} (hr : r ∈ rs') (h1 : r.1 ≤ a) (h2 : a + n ≤ r.1 + r.2)
    (hq : q ∈ rs') (h3 : q.1 ≤ b) (h4 : b + p ≤ q.1 + q.2) : Outs base rs' m₁ m₂ :=
  outs_sub h fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨r, hr, h1, h2⟩
    · exact ⟨q, hq, h3, h4⟩

theorem coeff_congr {a b a' b' : Nat → Nat} {N k : Nat} (ha : ∀ i < N, a i = a' i) (hb : ∀ i < N, b i = b' i) :
    Column.coeff a b N k = Column.coeff a' b' N k := by
  unfold Column.coeff
  apply NatSum.congr
  intro i hi
  apply NatSum.congr
  intro j hj
  rw [ha i hi, hb j hj]

/-- The word a column stores: the digit's while `k < N`, else the result's. -/
def slot (N k : Nat) : Nat := if k < N then N - 1 - k else 2 * N - 1 - k

/-- The invariant after column `k`, from the column's word (`residue`, zero
while `k < N`, then stored over the dead digit `q_(k-N)`), its quotient digit
`qk` (stored while `k < N`, then zero), the digits `q'` (`q` with `q'_k = qk`
while `k < N`) and the carry `c'`, with `residue + 2³² c'` the column's sum. -/
theorem cols_next {s0 t u : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q q' : Nat → Nat} (Ly : Lay L N S mo inv o a b) (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N)
    (ws : Ws u W L) (prm : Params u W L V 12) (ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)))
    (mc : u.mcdt = s0.mcdt) (K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t u)
    (O : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem)
    {qk residue c' : Nat} (hw : w32 u.mem W (S + 24 + 4 * slot N k) = if k < N then qk else residue)
    (hq' : ∀ j, j ≠ k → q' j = q j) (hqk : k < N → q' k = qk) (hqz : N ≤ k → q' = q ∧ qk = 0)
    (hqlt : qk ≤ 2 ^ 32 - 1) (hres0 : k < N → residue = 0)
    (hcar : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c')
    (heq : residue + 2 ^ 32 * c' = c + Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + qk * digits s0.mem W mo 0)
    (hb : c' ≤ (2 * N + 2) * 2 ^ 32) (win : k + 1 < N → Window u W N mo (k + 1) q') :
    ColsI s0 W L V N S mo a b (k + 1) c' q' u := by
  have hn := ws.nowrap
  have hs := Ly.s_le
  have hsl : slot N k < N := by unfold slot; split <;> omega_arith
  have Ow : Outs W [(S, 8 * N + 28)] t.mem u.mem := outs_widen O fun y hy r hr => by
    have := hy _ (List.mem_singleton_self _)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega_arith
  -- The digits.
  have qkk : ∀ j, j ≠ k → q' j = q j := hq'
  have qs : Column.partSum (2 ^ 32) (Column.prefixDigits q' (k + 1)) (digits s0.mem W mo) N (k + 1) =
      Column.partSum (2 ^ 32) (Column.prefixDigits q k) (digits s0.mem W mo) N k +
        (Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + qk * digits s0.mem W mo 0) *
          (2 ^ 32) ^ k :=
    Column.qPart_step (2 ^ 32) q q' (digits s0.mem W mo) N k qk (fun i _ hik => hq' i (by omega_arith)) hqk
      (fun h => (hqz h).2)
  -- The result's words.
  have keepSlot : ∀ j, j ≠ slot N k → j < N → w32 u.mem W (S + 24 + 4 * j) = w32 t.mem W (S + 24 + 4 * j) :=
    fun j hj hjN => Outs.w32 O (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith) (by omega_arith)
  have out : (2 ^ 32) ^ N * rvalT u.mem W N S (k + 1 - N) =
      (2 ^ 32) ^ N * rvalT t.mem W N S (k - N) + (2 ^ 32) ^ k * residue := by
    by_cases hkN : k < N
    · rw [show k + 1 - N = 0 by omega_arith, show k - N = 0 by omega_arith, hres0 hkN]; simp [rvalT]
    · have hs' : slot N k = N - 1 - (k - N) := by unfold slot; rw [ite_eq_right hkN]; omega_arith
      rw [show k + 1 - N = (k - N) + 1 by omega_arith, rvalT, ← hs', hw, ite_eq_right hkN,
        rvalT_congr fun j hj => keepSlot _ (by rw [hs']; omega_arith) (by omega_arith),
        Nat.mul_add, ← Nat.mul_assoc, ← VG.Proof.Mont.X86.Square.pow32 (k - N), ← Nat.pow_add,
        show N + (k - N) = k by omega_arith]
  refine ⟨ws, prm, I.out.trans Ow, ecx, mc, hcar, hb, fun i hi => ?_, fun j => ?_, fun j h1 h2 => ?_, win, ?_,
    I.keep.trans K⟩
  · rw [Outs.w32 O (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)]
    exact I.revA i hi
  · by_cases hj : j = k
    · subst hj
      by_cases hkN : j < N
      · rw [hqk hkN]; exact hqlt
      · rw [(hqz (by omega_arith)).1]; exact I.qlt j
    · rw [hq' j hj]; exact I.qlt j
  · -- The digits still stored.
    by_cases hkN : k < N
    · by_cases hj : j = k
      · subst hj
        have hs' : slot N j = N - 1 - j := by unfold slot; rw [ite_eq_left hkN]
        rw [← hs', hw, ite_eq_left hkN, hqk hkN]
      · rw [keepSlot _ (by unfold slot; rw [ite_eq_left hkN]; omega_arith) (by omega_arith), hq' j hj]
        exact I.qs j (by omega_arith) (by omega_arith)
    · rw [keepSlot _ (by unfold slot; rw [ite_eq_right hkN]; omega_arith) (by omega_arith), (hqz (by omega_arith)).1]
      exact I.qs j (by omega_arith) (by omega_arith)
  · exact VG.Proof.Mont.X86.Square.advance (2 ^ 32) N k c c' residue _ _ _ _ _ _ _ _ _ I.eq
      (by rw [heq]) out (Column.partSum_succ _ _ _ _ _) qs

theorem pxor_run (s : State) :
    runBlock isa [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)] s =
      some ((s.setXmm .xmm0 (XBinOp.eval .pxor (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .pxor (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

theorem pxor_ex (s : State) :
    ∃ u, runBlock isa [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)] s = some u ∧
      u.gpr = s.gpr ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 ∧ u.xmm .xmm7 = s.xmm .xmm7 ∧ Acc (u.xmm .xmm0) (u.xmm .xmm1) 0 0 0 :=
  ⟨_, pxor_run s, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte]; exact Acc.zero⟩

/-- What the column has after `fold`: `edx:eax = (P + c) mod 2⁶⁴` for the
column's sum `P` of the products, the sum `H` of their high words at `S + 8`,
`P - 2³² H` at most `2 N + 3` low words. -/
structure Folded (s0 t : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c : Nat) (q : Nat → Nat)
    (H : Nat) (u : State) : Prop where
  ws : Ws u W L
  prm : Params u W L V 12
  z : (u.gpr .eax).toNat + 2 ^ 32 * (u.gpr .edx).toNat =
    (Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + c) % 2 ^ 64
  ebx : PtrAt u W .ebx S
  ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * k)
  hw : w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) = H
  carry : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c
  le : 2 ^ 32 * H ≤ Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k
  low : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k - 2 ^ 32 * H ≤
      (2 * N + 3) * (2 ^ 32 - 1)
  out : Outs W [(S, 16)] t.mem u.mem
  keep : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t u
  mcdt : u.mcdt = t.mcdt
  x6 : u.xmm .xmm6 = t.xmm .xmm6
  x7 : u.xmm .xmm7 = t.xmm .xmm7

/-- The column's products, then `fold`. -/
theorem sums_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) {rest : Prog isa} {Q : State → Prop}
    (K : ∀ u H, Folded s0 t W L V N S mo a b k c q H u → WP isa rest u Q) :
    WP isa (.seq (.block [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)])
      (.seq (input sq hi) (.seq (reduce hi) (.seq (.block fold) rest)))) t Q := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  obtain ⟨t0, run0, g0, m0, rd0, wr0, mc0, x60, x70, A0⟩ := pxor_ex t
  refine WP.seq (WP.of_runBlock ⟨t0, run0, ?_⟩)
  have K0 : Keeps [] t t0 := ⟨fun r _ => by rw [g0], rd0, wr0⟩
  have C0 : ColEnv t0 W L V N k := ⟨I.ws.of_keeps K0, I.prm.keep (by rw [m0]; exact Outs.refl _ _ _) (by rw [g0])
    rd0 wr0, PV.n4, hk, hN28, by rw [g0]; exact I.ecx, by rw [mc0, I.mcdt]; exact hm0⟩
  -- The numbers, as they were.
  have aT := digits_out hn I.out Ly.a_le Ly.sa
  have bT := digits_out hn I.out Ly.b_le Ly.sb
  have moT := digits_out hn I.out Ly.mo_le Ly.smo
  have RA : RevA t0.mem W N S a := fun i hi => by rw [m0, I.revA i hi, aT i hi]
  refine WP.seq (WP.mono (input_ok C0 PV sq hi hsq hhi Ly.a_le Ly.b_le hs RA A0) fun t1 P1 => ?_)
  obtain ⟨H1, n1, A1, hn1, hH1⟩ := P1.acc
  have C1 := C0.of_keeps P1.keep P1.mem P1.mcdt
  have mem1 : t1.mem = t.mem := by rw [P1.mem, m0]
  have eAB : Column.coeff (digits t0.mem W a) (digits t0.mem W b) N k =
      Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k := by rw [m0]; exact coeff_congr aT bT
  rw [eAB] at A1
  have hQ : ∀ {lo hi'}, lo ≥ k - N → hi' ≤ min k N → RevQ t1.mem W N S q lo hi' := fun h1 h2 j hj1 hj2 => by
    rw [mem1]; exact I.qs j (by omega_arith) (by omega_arith)
  have eM : ∀ k', Column.coeff (Column.prefixDigits q k') (digits t1.mem W mo) N k' =
      Column.coeff (Column.prefixDigits q k') (digits s0.mem W mo) N k' := fun _ => by
    rw [mem1]; exact coeff_congr (fun _ _ => rfl) moT
  have post2 : ∀ t2, RedPost t1 N (Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits t1.mem W mo) N k) H1 n1 t2 →
      WP isa (.seq (.block fold) rest) t2 Q := fun t2 R2 => by
    obtain ⟨H2, n2, A2, hn2, hH2⟩ := R2.acc
    rw [eM] at A2
    have C2 := C1.of_keeps R2.keep R2.mem R2.mcdt
    have mem2 : t2.mem = t.mem := by rw [R2.mem, mem1]
    have hc2 : w32 t2.mem W (S + 16) + 2 ^ 32 * w32 t2.mem W (S + 20) = c := by rw [mem2]; exact I.carry
    refine WP.seq (WP.mono (fold_ok C2 PV.s (by omega_arith) A2 (by omega_arith) hc2)
      fun t3 ⟨z3, b3, h3, c3, O3, K3, mc3, x63, x73⟩ => K t3 H2 ?_)
    have Kt3 : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t t3 :=
      ((((K0.mono (by decide)).trans (P1.keep.mono (by decide))).trans (R2.keep.mono (by decide))).trans
        (K3.mono (by decide)))
    have O3' : Outs W [(0, L)] t2.mem t3.mem := outs_widen O3 fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega_arith
    have := A2.le
    have := A2.low
    exact ⟨C2.ws.of_keeps K3, C2.prm.keep O3' (K3.1 _ (by decide)) K3.2.1 K3.2.2, z3, b3,
      by rw [K3.1 _ (by decide)]; exact C2.ecx, h3, c3, A2.le,
      Nat.le_trans A2.low (Nat.mul_le_mul_right _ (by omega_arith)), by rw [← mem2]; exact O3, Kt3,
      by rw [mc3, R2.mcdt, P1.mcdt, mc0], by rw [x63, R2.x6, P1.x6, x60], by rw [x73, R2.x7, P1.x7, x70]⟩
  cases hi with
  | true =>
    have hkN := hhi.mp rfl
    exact WP.seq (WP.mono (reduceHi_ok C1 PV hkN Ly.mo_le hs (hQ (by omega_arith) (by omega_arith)) (by omega_arith) A1) post2)
  | false =>
    have hkN : k < N := by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
    have Wd : Window t1 W N mo k q := by
      have Wt := I.win hkN
      refine ⟨by rw [P1.x6, x60]; exact Wt.q1, by rw [P1.x6, x60]; exact Wt.q2, ?_, ?_⟩
      · rw [P1.x7, x70, Wt.m1, mem1]
      · rw [P1.x7, x70, Wt.m2, mem1]
    exact WP.seq (WP.mono (reduceLo_ok C1 PV hkN Ly.mo_le hs (hQ (by omega_arith) (by omega_arith)) Wd (by omega_arith) A1) post2)

/-- What a column's last block takes from `fold`'s state: the memory as at
the column's start but the sums, the modulus and the inverse as they were. -/
theorem folded_facts {s0 t t4 : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} {H : Nat} (Ly : Lay L N S mo inv o a b) (I : ColsI s0 W L V N S mo a b k c q t)
    (F : Folded s0 t W L V N S mo a b k c q H t4) :
    Outs W [(S, 8 * N + 28)] s0.mem t4.mem ∧ w32 t4.mem W inv = w32 s0.mem W inv ∧
      w32 t4.mem W mo = digits s0.mem W mo 0 ∧ (∀ i < N, digits t4.mem W mo i = digits s0.mem W mo i) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have O5 : Outs W [(S, 8 * N + 28)] s0.mem t4.mem :=
    I.out.trans (outs_widen F.out fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega_arith)
  refine ⟨O5, Outs.w32 O5 (by have := Ly.sinv; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.inv_le; omega_arith), ?_, digits_out hn O5 Ly.mo_le Ly.smo⟩
  rw [digits, Nat.mul_zero, Nat.add_zero]
  exact Outs.w32 O5 (by have := Ly.smo; simp only [List.mem_singleton, forall_eq]; omega_arith)
    (by have := Ly.mo_le; omega_arith)

/-- A column's last block while `k < N`: the digit stored and into the window,
the carry stored, `ecx` up a word. -/
theorem digitBlock_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv Z H : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hkN : k < N)
    (hN4 : (V pN4).toNat = 4 * N) (hN28 : N < 2 ^ 29)
    (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32) (hI : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 ≤ L) (hi : inv + 4 ≤ L)
    (sep : mo + 4 ≤ S + 24 + 4 * (N - 1 - k) ∨ S + 24 + 4 * (N - 1 - k) + 4 ≤ mo)
    (hb : PtrAt t W .ebx S) (hz : (t.gpr .eax).toNat + 2 ^ 32 * (t.gpr .edx).toNat = Z)
    (hH : w32 t.mem W (S + 8) + 2 ^ 32 * w32 t.mem W (S + 12) = H) :
    WP isa (.block (digit ++ (carry ++ (([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] : List Instr) ++
      ((if false then ([.alu .add .eax (.reg .eax)] : List Instr) else []) ++ ([.alu .cmp .ecx (.reg .eax)] : List Instr)))))) t fun u =>
      ∃ Hl Hh, Hl < 2 ^ 32 ∧ Hl + 2 ^ 32 * Hh =
          (H + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo / 2 ^ 32) % 2 ^ 64 ∧
        w32 u.mem W (S + 16) =
          (Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) % 2 ^ 64 / 2 ^ 32 ∧
        w32 u.mem W (S + 20) = (Hh + (decide ((Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) %
          2 ^ 64 / 2 ^ 32 < Hl)).toNat) % 2 ^ 32 ∧
        w32 u.mem W (S + 24 + 4 * (N - 1 - k)) = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
        Outs W [(S + 8, 16), (S + 24 + 4 * (N - 1 - k), 4)] t.mem u.mem ∧
        Ws u W L ∧ Params u W L V 12 ∧ u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧
        u.zf = some (decide (k + 1 = N)) ∧ Keeps [.eax, .ecx, .edx, .esi, .edi] t u ∧ u.mcdt = t.mcdt ∧
        (dword (u.xmm .xmm6) 0).toNat = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
        dword (u.xmm .xmm6) 2 = dword (t.xmm .xmm6) 0 ∧ u.xmm .xmm7 = t.xmm .xmm7 := by
  have hn := hw.nowrap
  have hk : k < 2 * N := by omega_arith
  refine WP.block_append (WP.mono (digit_ok hw P hcx hkN hN4 hM hI hs hm hi sep hb hz hH)
    fun t6 ⟨d6, q6, hh6, O6, K6, mc6, w60, w62, w67⟩ => ?_)
  have hw6 := hw.of_keeps K6
  have O6' : Outs W [(0, L)] t.mem t6.mem := outs_sub2 O6 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith) (List.mem_singleton_self _) (Nat.zero_le _) (by simp only; omega_arith)
  have P6 : Params t6 W L V 12 := P.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
  have b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact hb
  have ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact hcx
  refine WP.block_append (WP.mono (carry_ok hw6 (by omega_arith) b6) fun t7 ⟨cl, ch, O7, K7, mc7, x7⟩ => ?_)
  have hw7 := hw6.of_keeps K7
  have O7' : Outs W [(0, L)] t6.mem t7.mem := outs_sub1 O7 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  have P7 : Params t7 W L V 12 := P6.keep O7' (K7.1 _ (by decide)) K7.2.1 K7.2.2
  have ecx7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K7.1 _ (by decide)]; exact ecx6
  refine WP.mono (step_ok P7 hN4 ecx7 hk hN28 false) fun u ⟨ecxu, zfu, Ku, mu, mcu, xu⟩ => ?_
  obtain ⟨e8, e12⟩ := words_split (t6.mem.readW (off W (S + 8)) 32).isLt hh6
  refine ⟨_, _, (t6.mem.readW (off W (S + 8)) 32).isLt, hh6, ?_, ?_, ?_, ?_, hw7.of_keeps Ku,
    P7.keep (by rw [mu]; exact Outs.refl _ _ _) (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2, ecxu,
    by rw [zfu]; simp, ((K6.mono (by decide)).trans (K7.mono (by decide))).trans (Ku.mono (by decide)),
    by rw [mcu, mc7, mc6], by rw [xu, x7]; exact w60, by rw [xu, x7]; exact w62, by rw [xu, x7, w67]⟩
  · rw [mu, cl, d6]
  · rw [mu, ch, d6]
  · rw [mu, Outs.w32 O7 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith), q6]
  · rw [mu]
    refine (outs_sub2 O6 (r := (S + 8, 16)) (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)).trans
      (outs_sub1 O7 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith))

/-- A column while `k < N`: its digit stored and into the window. -/
theorem columnLo_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hkN : k < N) (sq : Bool) (hsq : sq = true → a = b) :
    WP isa (column sq false) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧ u.zf = some (decide (k + 1 = N)) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  have hcb := I.bound
  have hk : k < 2 * N := by omega_arith
  unfold column
  simp only [seqs]
  rw [show (if false = true then VG.Impl.Mont.X86.Sse2.word else digit) = digit from rfl]
  simp only [List.append_assoc]
  refine sums_ok Ly PV hm0 I hk sq false hsq (by simp; omega_arith) fun t4 H F => ?_
  obtain ⟨O4, iv4, m04, mo4⟩ := folded_facts Ly I F
  refine WP.mono (digitBlock_ok F.ws F.prm F.ecx hkN PV.n4 hN28 PV.mo PV.inv (by omega_arith)
    (by have := Ly.mo_le; omega_arith) Ly.inv_le (by have := Ly.smo; omega_arith) F.ebx F.z F.hw)
    fun u ⟨Hl, Hh, hHl, hHw, cl, ch, qw, Ou4, wsu, Pu, ecxu, zfu, Ku, mcu, w60, w62, w67⟩ => ?_
  rw [iv4, m04] at hHw cl ch
  rw [iv4] at qw w60
  have hsl : slot N k = N - 1 - k := by unfold slot; rw [ite_eq_left hkN]
  have Ou : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem := by
    rw [hsl]
    refine (outs_sub1 F.out (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)).trans
      (outs_sub2 Ou4 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _))
  have Owide : Outs W [(S, 8 * N + 28)] t.mem u.mem := by
    rw [hsl] at Ou
    exact outs_sub2 Ou (List.mem_singleton_self _) (Nat.le_refl _) (by simp only; omega_arith)
      (List.mem_singleton_self _) (by simp only; omega_arith) (by simp only; omega_arith)
  have hP := coeff_le s0.mem W b (N := N) (k := k) (digits s0.mem W a) (digits_lt _ _ _)
  have hQ := coeff_le s0.mem W mo (N := N) (k := k) (Column.prefixDigits q k) (fun i => by
      unfold Column.prefixDigits; split
      · exact I.qlt i
      · omega_arith)
  have fl := F.le
  have fw := F.low
  generalize hAB : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k = AB at fl fw hP hHw cl ch qw w60
  generalize hQM : Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k = QM at fl fw hQ hHw cl ch qw w60
  have hM0 := digits_lt s0.mem W mo 0
  generalize hq : ((AB + QM + c) % 2 ^ 64 % 2 ^ 32 * w32 s0.mem W inv) % 2 ^ 32 = qk at hHw cl ch qw w60
  have hq32 : qk < 2 ^ 32 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
  have hqm : qk * digits s0.mem W mo 0 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega_arith) hM0
  have h0 : digits s0.mem W mo 0 = w32 s0.mem W mo := by simp only [digits, Nat.mul_zero, Nat.add_zero]
  have cancel := cancel_digit (2 ^ 32) (AB + QM + c) (digits s0.mem W mo 0) (w32 s0.mem W inv)
    (by rw [h0]; exact hinv)
  have hq' := hq
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)] at hq'
  rw [hq'] at cancel
  generalize hqmv : qk * digits s0.mem W mo 0 = qm at hHw cl ch hqm cancel
  obtain ⟨b1, b2, b3, b4, b5'⟩ := column_bounds hN28 hP hQ fl fw hcb hqm
  rw [Nat.mod_eq_of_lt b1] at hHw
  obtain ⟨e8, e12⟩ := words_split hHl hHw
  rw [Nat.mod_add_mod] at cl ch
  have e : AB + QM + c + qm = AB + QM + qm + c := Nat.add_right_comm _ _ _
  rw [e] at cl ch
  have cc := col_carry (P := AB + QM + qm) (H := H + qm / 2 ^ 32) (c := c)
    (Zh := (AB + QM + qm + c) % 2 ^ 64 / 2 ^ 32) b2 b3 b4 rfl
  refine ⟨(AB + QM + qm + c) / 2 ^ 32, fun j => if j = k then qk else q j,
    cols_next (qk := qk) (residue := 0) Ly I hk wsu Pu ecxu (by rw [mcu, F.mcdt, I.mcdt])
      ((F.keep.mono (by decide)).trans (Ku.mono (by decide))) Ou ?_
      (fun j hj => by simp only [hj, ↓reduceIte]) (fun _ => by simp)
      (fun h => absurd h (by omega_using [h, hkN])) (by omega_using [hq32]) (fun _ => rfl) ?_ ?_ b5' ?_, zfu⟩
  · rw [hsl, qw, ite_eq_left hkN]
  · rw [cl, ch, e8, e12]
    exact cc
  · rw [hAB, hQM, hqmv]
    omega_using [cancel]
  · intro hk1
    have Wt := I.win hkN
    have mou : ∀ i < N, digits u.mem W mo i = digits t.mem W mo i :=
      digits_out hn Owide Ly.mo_le Ly.smo
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [w60, ite_eq_left (by omega_using [] : 1 ≤ k + 1), show k + 1 - 1 = k by omega_using []]; simp
    · rw [w62, F.x6, Wt.q1]
      by_cases h1 : 1 ≤ k
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1] : 2 ≤ k + 1), show k + 1 - 2 = k - 1 by omega_using [h1],
          ite_eq_right (by omega_using [h1] : k - 1 ≠ k)]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1])]
    · rw [w67, F.x7, Wt.m1, mou 1 (by omega_using [Ly.hN2])]
    · rw [w67, F.x7, Wt.m2]
      by_cases h3 : 3 ≤ N
      · rw [ite_eq_left h3, ite_eq_left h3, mou 2 (by omega_using [h3])]
      · rw [ite_eq_right h3, ite_eq_right h3]

/-- A column's last block from `k = N` on: the result's word stored over the
dead digit, the carry stored, `ecx` up a word. -/
theorem wordBlock_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : k < 2 * N)
    (hN4 : (V pN4).toNat = 4 * N) (hN28 : N < 2 ^ 29) (hs : S + 24 + 8 * N ≤ L) (hb : PtrAt t W .ebx S) :
    WP isa (.block (VG.Impl.Mont.X86.Sse2.word ++ (carry ++ (([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] : List Instr) ++
      ((if true then ([.alu .add .eax (.reg .eax)] : List Instr) else []) ++ ([.alu .cmp .ecx (.reg .eax)] : List Instr)))))) t fun u =>
      w32 u.mem W (S + 16) = (t.gpr .edx).toNat ∧
      w32 u.mem W (S + 20) = (w32 t.mem W (S + 12) +
        (decide ((t.gpr .edx).toNat < w32 t.mem W (S + 8))).toNat) % 2 ^ 32 ∧
      w32 u.mem W (S + 24 + 4 * (2 * N - 1 - k)) = (t.gpr .eax).toNat ∧
      Outs W [(S + 16, 8), (S + 24 + 4 * (2 * N - 1 - k), 4)] t.mem u.mem ∧
      Ws u W L ∧ Params u W L V 12 ∧ u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧
      u.zf = some (decide (k + 1 = 2 * N)) ∧ Keeps [.eax, .ecx, .esi] t u ∧ u.mcdt = t.mcdt := by
  have hn := hw.nowrap
  refine WP.block_append (WP.mono (word_ok hw P hN4 hcx hk hs hb) fun t6 ⟨w6, O6, K6, mc6, x6⟩ => ?_)
  have hw6 := hw.of_keeps K6
  have O6' : Outs W [(0, L)] t.mem t6.mem := outs_sub1 O6 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  have P6 : Params t6 W L V 12 := P.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
  have b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact hb
  have ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact hcx
  have r8 : w32 t6.mem W (S + 8) = w32 t.mem W (S + 8) :=
    Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  have r12 : w32 t6.mem W (S + 12) = w32 t.mem W (S + 12) :=
    Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  have edx6 : t6.gpr .edx = t.gpr .edx := K6.1 _ (by decide)
  refine WP.block_append (WP.mono (carry_ok hw6 (by omega_arith) b6) fun t7 ⟨cl, ch, O7, K7, mc7, x7⟩ => ?_)
  have hw7 := hw6.of_keeps K7
  have O7' : Outs W [(0, L)] t6.mem t7.mem := outs_sub1 O7 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  have P7 : Params t7 W L V 12 := P6.keep O7' (K7.1 _ (by decide)) K7.2.1 K7.2.2
  have ecx7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K7.1 _ (by decide)]; exact ecx6
  refine WP.mono (step_ok P7 hN4 ecx7 hk hN28 true) fun u ⟨ecxu, zfu, Ku, mu, mcu, xu⟩ => ?_
  refine ⟨by rw [mu, cl, edx6], by rw [mu, ch, r8, r12, edx6], ?_, ?_, hw7.of_keeps Ku,
    P7.keep (by rw [mu]; exact Outs.refl _ _ _) (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2, ecxu,
    by rw [zfu]; simp, ((K6.mono (by decide)).trans (K7.mono (by decide))).trans (Ku.mono (by decide)),
    by rw [mcu, mc7, mc6]⟩
  · rw [mu, Outs.w32 O7 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith), w6]
  · rw [mu]
    exact (outs_sub1 O6 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)).trans
      (outs_sub1 O7 (List.mem_cons_self ..) (Nat.le_refl _) (Nat.le_refl _))

/-- A column from `k = N` on: its word of the result stored. -/
theorem columnHi_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hkN : N ≤ k) (hk : k < 2 * N) (sq : Bool) (hsq : sq = true → a = b) :
    WP isa (column sq true) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧ u.zf = some (decide (k + 1 = 2 * N)) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  have hcb := I.bound
  unfold column
  simp only [seqs]
  simp only [↓reduceIte, List.append_assoc]
  refine sums_ok Ly PV hm0 I hk sq true hsq (by simp; omega_arith) fun t4 H F => ?_
  refine WP.mono (wordBlock_ok F.ws F.prm F.ecx hk PV.n4 hN28 (by omega_arith) F.ebx)
    fun u ⟨cl, ch, ww, Ou4, wsu, Pu, ecxu, zfu, Ku, mcu⟩ => ?_
  have hsl : slot N k = 2 * N - 1 - k := by unfold slot; rw [ite_eq_right (by omega_using [hkN])]
  have Ou : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem := by
    rw [hsl]
    refine (outs_sub1 F.out (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)).trans
      (outs_sub2 Ou4 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _))
  have hP := coeff_le s0.mem W b (N := N) (k := k) (digits s0.mem W a) (digits_lt _ _ _)
  have hQ := coeff_le s0.mem W mo (N := N) (k := k) (Column.prefixDigits q k) (fun i => by
      unfold Column.prefixDigits; split
      · exact I.qlt i
      · omega_arith)
  have fl := F.le
  have fw := F.low
  have fz := F.z
  have hH := F.hw
  generalize hAB : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k = AB at fl fw fz hP
  generalize hQM : Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k = QM at fl fw fz hQ
  obtain ⟨b1, b2, b3, b4⟩ := column_bounds0 hN28 hP hQ fl fw hcb
  obtain ⟨e8, e12⟩ := words_split (t4.mem.readW (off W (S + 8)) 32).isLt hH
  have hlo := (t4.gpr .eax).isLt
  obtain ⟨zl, zh⟩ := words_split hlo fz
  have cc := col_carry (P := AB + QM) (H := H) (c := c) fl b2 b3 zh
  refine ⟨(AB + QM + c) / 2 ^ 32, q,
    cols_next (qk := 0) (residue := (AB + QM + c) % 2 ^ 32) Ly I hk wsu Pu ecxu (by rw [mcu, F.mcdt, I.mcdt])
      ((F.keep.mono (by decide)).trans (Ku.mono (by decide))) Ou ?_ (fun _ _ => rfl)
      (fun h => absurd h (by omega_using [h, hkN])) (fun _ => ⟨rfl, rfl⟩) (Nat.zero_le _)
      (fun h => absurd h (by omega_using [h, hkN])) ?_ ?_ b4 (fun h => absurd h (by omega_using [h, hkN])), zfu⟩
  · rw [hsl, ww, ite_eq_right (by omega_using [hkN]), zl, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  · rw [cl, ch, show w32 t4.mem W (S + 8) = _ from e8, show w32 t4.mem W (S + 12) = _ from e12]
    exact cc
  · rw [hAB, hQM, Nat.zero_mul, Nat.add_zero]
    omega_using []

/-- A column keeps the invariant. -/
theorem column_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) :
    WP isa (column sq hi) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧
        u.zf = some (decide (k + 1 = if hi then 2 * N else N)) := by
  cases hi with
  | false =>
    have hkN : k < N := by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
    exact columnLo_ok Ly PV hinv hm0 I hkN sq hsq
  | true => exact columnHi_ok Ly PV hm0 I (hhi.mp rfl) hk sq hsq

end VG.Proof.Mont.X86.Sse2
