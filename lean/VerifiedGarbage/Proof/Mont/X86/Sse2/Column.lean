module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Fold
public import VerifiedGarbage.Proof.Mont.X86.Sse2.CarryMath
public import VerifiedGarbage.Proof.Mont.ColumnSquare
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! # The columns

`ColsI`: after the columns `j < k`, from the state `s0` the columns started
in, the carry `c` (at `S + 16`), the quotient digits (at `S + 24`) and the
result's words (from `S + 24 + 4 N`) satisfy

`2^(32 k) c + 2^(32 N) T = Σ_(i+j<k) A_i B_j 2^(32 (i+j)) + Σ_(i+j<k) Q_i M_j 2^(32 (i+j))`,

and only the function's scratch has changed. A column keeps it
(`column_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- The numbers' offsets in the working space of `L` bytes: `A`, `B`, `M`
and the result `O` of `N` words, `-M⁻¹ mod 2³²` at `inv`, the scratch of
`8 N + 28` bytes at `S`, apart from the others, and `O` apart from `M` and
`inv`. -/
structure Lay (L N S mo inv o a b : Nat) : Prop where
  hN : 0 < N
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

/-- The parameters' values: pointers into the working space and `4 N`. -/
structure PVals (V : Nat → BitVec 32) (W : Addr) (N S mo inv o a b : Nat) : Prop where
  a : (V pA).toNat = (W.toNat + a) % 2 ^ 32
  b : (V pB).toNat = (W.toNat + b) % 2 ^ 32
  mo : (V pM).toNat = (W.toNat + mo) % 2 ^ 32
  o : (V pO).toNat = (W.toNat + o) % 2 ^ 32
  s : (V pS).toNat = (W.toNat + S) % 2 ^ 32
  inv : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32
  n4 : (V pN4).toNat = 4 * N

/-- After the columns `j < k`. -/
structure ColsI (s0 : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c : Nat) (t : State) :
    Prop where
  ws : Ws t W L
  prm : Params t W L V 12
  out : Outs W [(S, 8 * N + 28)] s0.mem t.mem
  ecx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)
  mcdt : t.mcdt = s0.mcdt
  carry : w32 t.mem W (S + 16) + 2 ^ 32 * w32 t.mem W (S + 20) = c
  bound : c ≤ (2 * N + 2) * 2 ^ 32
  eq : (2 ^ 32) ^ k * c + (2 ^ 32) ^ N * val32 t.mem W (S + 24 + 4 * N) (k - N) =
    Column.partSum (2 ^ 32) (digits s0.mem W a) (digits s0.mem W b) N k +
    Column.partSum (2 ^ 32) (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s0 t

theorem digits_lt (m : Mem) (W : Addr) (x i : Nat) : digits m W x i ≤ 2 ^ 32 - 1 := by
  have := (m.readW (off W (x + 4 * i)) 32).isLt; simp only [digits, w32]; omega

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
  Outs.w32 O (by simp only [List.mem_singleton, forall_eq]; omega) (by omega)

theorem pxor_run (s : State) :
    runBlock isa [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)] s =
      some ((s.setXmm .xmm0 (XBinOp.eval .pxor (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .pxor (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

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
    omega

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

/-- The invariant after column `k`, from the column's word (`residue`, zero
while `k < N`, then stored at word `k`), its quotient digit `q` (stored at
word `k` while `k < N`) and the carry `c'`, with `residue + 2³² c'` the
column's sum. -/
theorem cols_next {s0 t u : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    (Ly : Lay L N S mo inv o a b) (I : ColsI s0 W L V N S mo a b k c t) (hk : k < 2 * N)
    (ws : Ws u W L) (prm : Params u W L V 12) (ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)))
    (mc : u.mcdt = s0.mcdt) (K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t u)
    (O : Outs W [(S, 24), (S + 24 + 4 * k, 4)] t.mem u.mem)
    {q residue c' : Nat} (hw : w32 u.mem W (S + 24 + 4 * k) = if k < N then q else residue)
    (hqz : N ≤ k → q = 0) (hres0 : k < N → residue = 0)
    (hcar : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c')
    (heq : residue + 2 ^ 32 * c' = c + Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k +
      q * digits s0.mem W mo 0)
    (hb : c' ≤ (2 * N + 2) * 2 ^ 32) :
    ColsI s0 W L V N S mo a b (k + 1) c' u := by
  have hn := ws.nowrap
  have hs := Ly.s_le
  have Ow : Outs W [(S, 8 * N + 28)] t.mem u.mem := outs_widen O fun y hy r hr => by
    have := hy _ (List.mem_singleton_self _)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega
  refine ⟨ws, prm, I.out.trans Ow, ecx, mc, hcar, hb, ?_, I.keep.trans K⟩
  -- The quotient digits.
  have qs := Column.qPart_step (2 ^ 32) (digits t.mem W (S + 24)) (digits u.mem W (S + 24))
    (digits s0.mem W mo) N k q
    (fun i hi hik => Outs.w32 O (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega) (by omega))
    (fun hkN => by simp only [digits]; rw [hw, ite_eq_left hkN]) hqz
  -- The result's words.
  have out : (2 ^ 32) ^ N * val32 u.mem W (S + 24 + 4 * N) (k + 1 - N) =
      (2 ^ 32) ^ N * val32 t.mem W (S + 24 + 4 * N) (k - N) + (2 ^ 32) ^ k * residue := by
    by_cases hkN : k < N
    · rw [show k + 1 - N = 0 by omega, show k - N = 0 by omega, hres0 hkN]; simp [val32]
    · rw [show k + 1 - N = (k - N) + 1 by omega, val32_succ,
        Outs.val32 O (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega)
          (by omega),
        show S + 24 + 4 * N + 4 * (k - N) = S + 24 + 4 * k by omega, hw, ite_eq_right hkN,
        Nat.mul_add, ← Nat.mul_assoc, ← VG.Proof.Mont.X86.Square.pow32 (k - N), ← Nat.pow_add,
        show N + (k - N) = k by omega]
  exact VG.Proof.Mont.X86.Square.advance (2 ^ 32) N k c c' residue _ _ _ _ _ _ _ _ _ I.eq
    (by rw [heq]) out (Column.partSum_succ _ _ _ _ _) qs

theorem pxor_ex (s : State) :
    ∃ u, runBlock isa [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)] s = some u ∧
      u.gpr = s.gpr ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mcdt = s.mcdt ∧
      Acc (u.xmm .xmm0) (u.xmm .xmm1) 0 0 0 :=
  ⟨_, pxor_run s, rfl, rfl, rfl, rfl, rfl, by simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte]; exact Acc.zero⟩

theorem coeff_congr {a b a' b' : Nat → Nat} {N k : Nat} (ha : ∀ i < N, a i = a' i) (hb : ∀ i < N, b i = b' i) :
    Column.coeff a b N k = Column.coeff a' b' N k := by
  unfold Column.coeff
  apply NatSum.congr
  intro i hi
  apply NatSum.congr
  intro j hj
  rw [ha i hi, hb j hj]

/-- What the column has after `fold`: `edx:eax = (P + c) mod 2⁶⁴` for the
column's sum `P` of the products, the sum `H` of their high words at `S + 8`,
`P - 2³² H` at most `2 N + 1` low words. -/
structure Folded (s0 t : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c H : Nat)
    (u : State) : Prop where
  ws : Ws u W L
  prm : Params u W L V 12
  z : (u.gpr .eax).toNat + 2 ^ 32 * (u.gpr .edx).toNat =
    (Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k + c) % 2 ^ 64
  ebx : PtrAt u W .ebx S
  ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * k)
  hw : w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) = H
  carry : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c
  le : 2 ^ 32 * H ≤ Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k
  low : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k - 2 ^ 32 * H ≤
      (2 * N + 1) * (2 ^ 32 - 1)
  out : Outs W [(S, 16)] t.mem u.mem
  keep : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t u
  mcdt : u.mcdt = t.mcdt

/-- The column's products, then `fold`. -/
theorem sums_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c t) (hk : k < 2 * N) {rest : Prog isa} {Q : State → Prop}
    (K : ∀ u H, Folded s0 t W L V N S mo a b k c H u → WP isa rest u Q) :
    WP isa (.seq (.block [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)])
      (.seq lowIdx (.seq input (.seq reduce (.seq (.block fold) rest))))) t Q := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  obtain ⟨t0, run0, g0, m0, rd0, wr0, mc0, A0⟩ := pxor_ex t
  refine WP.seq (WP.of_runBlock ⟨t0, run0, ?_⟩)
  have K0 : Keeps [] t t0 := ⟨fun r _ => by rw [g0], rd0, wr0⟩
  have P0 : Params t0 W L V 12 := I.prm.keep (by rw [m0]; exact Outs.refl _ _ _) (by rw [g0]) rd0 wr0
  have ecx0 : t0.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [g0]; exact I.ecx
  refine WP.seq (WP.mono (lowIdx_ok P0 PV.n4 ecx0 (by omega)) fun t1 ⟨e1, K1⟩ => ?_)
  have C1 : ColEnv t1 W L V N k := ⟨(I.ws.of_keeps K0).of_keeps K1.keep, P0.of_sk K1, PV.n4, hk, hN28,
    by rw [K1.keep.1 _ (by decide)]; exact ecx0, e1, by rw [K1.mcdt, mc0, I.mcdt]; exact hm0⟩
  have A1 : Acc (t1.xmm .xmm0) (t1.xmm .xmm1) 0 0 0 := by rw [K1.xmm]; exact A0
  have mem1 : t1.mem = t.mem := by rw [K1.mem, m0]
  refine WP.seq (WP.mono (input_ok C1 PV.a PV.b Ly.a_le Ly.b_le A1) fun t2 ⟨H2, n2, A2, hn2, K2, m2, c2⟩ => ?_)
  have C2 := C1.of_keeps K2 m2 c2
  have ab := coeff_le t1.mem W b (N := N) (k := k) (digits t1.mem W a) (digits_lt _ _ _)
  have := A2.le
  refine WP.seq (WP.mono (reduce_ok C2 PV.s PV.mo (by omega) Ly.mo_le (by omega) A2)
    fun t3 ⟨A3, K3, m3, c3⟩ => ?_)
  have C3 := C2.of_keeps K3 m3 c3
  have mem3 : t3.mem = t.mem := by rw [m3, m2, mem1]
  have qm := coeff_le t2.mem W mo (N := N) (k := k)
    (Column.prefixDigits (digits t2.mem W (S + 24)) k) (fun i => by
      unfold Column.prefixDigits; split
      · exact digits_lt _ _ _ _
      · omega)
  have l3 := A3.le
  have w3 := A3.low
  have hc3 : w32 t3.mem W (S + 16) + 2 ^ 32 * w32 t3.mem W (S + 20) = c := by rw [mem3]; exact I.carry
  refine WP.seq (WP.mono (fold_ok C3 PV.s (by omega) A3 (by omega) hc3)
    fun t4 ⟨z4, b4, h4, c4, O4, K4, mc4⟩ =>
      K t4 (H2 + highSum t2.mem W (S + 24) mo k (k + 1 - N) (min k N - (k + 1 - N))) ?_)
  -- The coefficients from the columns' first state.
  have aT := digits_out hn I.out Ly.a_le Ly.sa
  have bT := digits_out hn I.out Ly.b_le Ly.sb
  have moT := digits_out hn I.out Ly.mo_le Ly.smo
  have eAB : Column.coeff (digits t1.mem W a) (digits t1.mem W b) N k =
      Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k := by rw [mem1]; exact coeff_congr aT bT
  have eQM : Column.coeff (Column.prefixDigits (digits t2.mem W (S + 24)) k) (digits t2.mem W mo) N k =
      Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k := by
    rw [m2, mem1]; exact coeff_congr (fun _ _ => rfl) moT
  rw [eAB, eQM] at l3 w3 z4
  have K3t : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t t3 :=
    (((K0.mono (by decide)).trans (K1.keep.mono (by decide))).trans (K2.mono (by decide))).trans (K3.mono (by decide))
  have O4' : Outs W [(0, L)] t3.mem t4.mem := outs_widen O4 fun y hy r hr => by
    have := hy _ (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega
  refine ⟨C3.ws.of_keeps K4, C3.prm.keep O4' (K4.1 _ (by decide)) K4.2.1 K4.2.2, z4, b4,
    by rw [K4.1 _ (by decide)]; exact C3.ecx, h4, c4, l3,
    Nat.le_trans w3 (Nat.mul_le_mul_right _ (by omega)), by rw [← mem3]; exact O4,
    K3t.trans (K4.mono (by decide)), by rw [mc4, c3, c2, K1.mcdt, mc0]⟩

/-- A column keeps the invariant. -/
theorem column_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c t) (hk : k < 2 * N) :
    WP isa column t fun u =>
      ∃ c', ColsI s0 W L V N S mo a b (k + 1) c' u ∧ u.zf = some (decide (k + 1 = 2 * N)) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  have hcb := I.bound
  unfold column
  simp only [seqs]
  refine sums_ok Ly PV hm0 I hk fun t4 H F => ?_
  have hP := coeff_le s0.mem W b (N := N) (k := k) (digits s0.mem W a) (digits_lt _ _ _)
  have hQ := coeff_le s0.mem W mo (N := N) (k := k)
    (Column.prefixDigits (digits t.mem W (S + 24)) k) (fun i => by
      unfold Column.prefixDigits; split
      · exact digits_lt _ _ _ _
      · omega_arith)
  have fl := F.le
  have fw := F.low
  have fz := F.z
  generalize hAB : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k = AB at fl fw fz hP
  generalize hQM : Column.coeff (Column.prefixDigits (digits t.mem W (S + 24)) k) (digits s0.mem W mo) N k = QM
    at fl fw fz hQ
  have hw4 := F.ws
  refine WP.seq (WP.seq (wp_movX (F.prm.read pN4 (by decide)) fun t45 u45 m45 x45 =>
    wp_cmpX rfl fun t5 f5 c5 _ m5 x5 => WP.block_nil ?_))
  have K5 : Keeps [.ebp] t4 t5 := u45.keeps.trans (f5.keeps [.ebp])
  have hw5 := hw4.of_keeps K5
  have mem5 : t5.mem = t4.mem := by rw [f5.mem, u45.mem]
  have P5 : Params t5 W L V 12 := F.prm.keep (by rw [mem5]; exact Outs.refl _ _ _)
    (by rw [f5.gpr, u45.other _ (by decide)]) (f5.rd.trans u45.rd) (f5.wr.trans u45.wr)
  have b5 : PtrAt t5 W .ebx S := by rw [PtrAt, f5.gpr, u45.other _ (by decide)]; exact F.ebx
  have ecx5 : t5.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [f5.gpr, u45.other _ (by decide)]; exact F.ecx
  have hv := (V pN4).isLt
  have cf5 : t5.cf = some (decide (k < N)) := by
    rw [c5, u45.gpr, u45.other _ (by decide), F.ecx, PV.n4, toNat_ofNat_lt (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have z5 : (t5.gpr .eax).toNat + 2 ^ 32 * (t5.gpr .edx).toNat = (AB + QM + c) % 2 ^ 64 := by
    rw [f5.gpr, u45.other _ (by decide), u45.other _ (by decide)]; exact fz
  have hH5 : w32 t5.mem W (S + 8) + 2 ^ 32 * w32 t5.mem W (S + 12) = H := by rw [mem5]; exact F.hw
  -- The modulus and the inverse, as they were.
  have O5 : Outs W [(S, 8 * N + 28)] s0.mem t5.mem := by
    rw [mem5]
    exact I.out.trans (outs_widen F.out fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega_arith)
  have iv5 : w32 t5.mem W inv = w32 s0.mem W inv :=
    Outs.w32 O5 (by have := Ly.sinv; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.inv_le; omega_arith)
  have m05 : w32 t5.mem W mo = digits s0.mem W mo 0 := by
    rw [digits, Nat.mul_zero, Nat.add_zero]
    exact Outs.w32 O5 (by have := Ly.smo; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.mo_le; omega_arith)
  have Kt5 : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t t5 := F.keep.trans (K5.mono (by decide))
  have mc5 : t5.mcdt = s0.mcdt := by rw [m5, m45, F.mcdt, I.mcdt]
  have Ot5 : Outs W [(S, 16)] t.mem t5.mem := by rw [mem5]; exact F.out
  have hM0 := digits_lt s0.mem W mo 0
  by_cases hkN : k < N
  · refine WP.ite true (by show t5.cf = _; rw [cf5, decide_eq_true hkN]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (digit_ok hw5 P5 ecx5 hkN PV.mo PV.inv (by omega_using [hs]) (by have := Ly.mo_le; omega_using [this, hN])
      Ly.inv_le (by have := Ly.smo; omega_using [this, hkN]) b5 z5 hH5) fun t6 ⟨d6, q6, hh6, O6, K6, mc6⟩ => ?_
    rw [iv5, m05] at d6 hh6
    rw [iv5] at q6
    generalize hq : ((AB + QM + c) % 2 ^ 64 % 2 ^ 32 * w32 s0.mem W inv) % 2 ^ 32 = q at d6 q6 hh6
    have hq32 : q < 2 ^ 32 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
    have hqm : q * digits s0.mem W mo 0 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega_using [hq32]) hM0
    have hw6 := hw5.of_keeps K6
    have O6' : Outs W [(0, L)] t5.mem t6.mem := outs_sub2 O6 (List.mem_singleton_self _) (Nat.zero_le _)
      (by simp only; omega_using [hs]) (List.mem_singleton_self _) (Nat.zero_le _) (by simp only; omega_using [hs, hkN])
    have P6 : Params t6 W L V 12 := P5.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
    have b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact b5
    have ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact ecx5
    refine WP.mono (carry_ok hw6 P6 PV.n4 ecx6 hk hN28 (by omega_using [hs]) b6)
      fun u ⟨cl, ch, Ou, ecxu, zfu, Ku, mcu⟩ => ?_
    have h0 : digits s0.mem W mo 0 = w32 s0.mem W mo := by simp only [digits, Nat.mul_zero, Nat.add_zero]
    have cancel := cancel_digit (2 ^ 32) (AB + QM + c) (digits s0.mem W mo 0) (w32 s0.mem W inv)
      (by rw [h0]; exact hinv)
    have hq' := hq
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)] at hq'
    rw [hq'] at cancel
    generalize hqmv : q * digits s0.mem W mo 0 = qm at d6 hh6 hqm cancel
    obtain ⟨b1, b2, b3, b4, b5'⟩ := column_bounds hN28 hP hQ fl fw hcb hqm
    rw [Nat.mod_eq_of_lt b1] at hh6
    obtain ⟨e8, e12⟩ := words_split (t6.mem.readW (off W (S + 8)) 32).isLt hh6
    rw [Nat.mod_add_mod] at d6
    have cc := col_carry (P := AB + QM + qm) (H := H + qm / 2 ^ 32) (c := c) b2 b3 b4
      (d6.trans (by rw [show AB + QM + c + qm = AB + QM + qm + c by omega_using []]))
    refine ⟨(AB + QM + qm + c) / 2 ^ 32, cols_next (q := q) (residue := 0) Ly I hk (hw6.of_keeps Ku)
      (P6.keep ?_ (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2) ecxu (by rw [mcu, mc6, mc5])
      ((((Kt5.mono (by decide)).trans (K6.mono (by decide))).trans (Ku.mono (by decide)))) ?_ ?_
      (fun h => absurd h (by omega_using [h, hkN])) (fun _ => rfl) ?_ ?_ b5', zfu⟩
    · exact outs_sub1 Ou (List.mem_singleton_self _) (Nat.zero_le _) (by simp only; omega_using [hs])
    · refine (Outs.trans (m₃ := t6.mem) (outs_sub1 Ot5 (List.mem_cons_self ..) (Nat.le_refl _)
        (by simp only; omega_using [])) ?_).trans ?_
      · exact outs_sub2 O6 (List.mem_cons_self ..) (by simp only; omega_using []) (by simp only; omega_using [])
          (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)
      · exact outs_sub1 Ou (List.mem_cons_self ..) (by simp only; omega_using []) (by simp only; omega_using [])
    · rw [Outs.w32 Ou (by simp only [List.mem_singleton, forall_eq]; omega_using []) (by omega_using [hs, hn, hkN]),
        q6, ite_eq_left hkN]
    · rw [cl, ch, show w32 t6.mem W (S + 8) = _ from e8, show w32 t6.mem W (S + 12) = _ from e12]
      exact cc
    · rw [hAB, hQM, hqmv]
      omega_using [cancel]
  · refine WP.ite false (by show t5.cf = _; rw [cf5, decide_eq_false hkN]) (fun h => absurd h (by decide))
      (fun _ => ?_)
    refine WP.mono (word_ok hw5 ecx5 hk (by omega_using [hs]) b5) fun t6 ⟨w6, O6, K6, mc6⟩ => ?_
    have hw6 := hw5.of_keeps K6
    have O6' : Outs W [(0, L)] t5.mem t6.mem := outs_sub1 O6 (List.mem_singleton_self _) (Nat.zero_le _)
      (by simp only; omega_using [hs, hk])
    have P6 : Params t6 W L V 12 := P5.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
    have b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact b5
    have ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact ecx5
    refine WP.mono (carry_ok hw6 P6 PV.n4 ecx6 hk hN28 (by omega_using [hs]) b6)
      fun u ⟨cl, ch, Ou, ecxu, zfu, Ku, mcu⟩ => ?_
    obtain ⟨b1, b2, b3, b4⟩ := column_bounds0 hN28 hP hQ fl fw hcb
    have hH6 : w32 t6.mem W (S + 8) + 2 ^ 32 * w32 t6.mem W (S + 12) = H := by
      rw [Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_using [hkN]) (by omega_using [hs, hn]),
        Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_using [hkN]) (by omega_using [hs, hn])]
      exact hH5
    obtain ⟨e8, e12⟩ := words_split (t6.mem.readW (off W (S + 8)) 32).isLt hH6
    have hlo := (t5.gpr .eax).isLt
    obtain ⟨zl, zh⟩ := words_split hlo z5
    have edx6 : t6.gpr .edx = t5.gpr .edx := K6.1 _ (by decide)
    have cc := col_carry (P := AB + QM) (H := H) (c := c) fl b2 b3 ((congrArg BitVec.toNat edx6).trans zh)
    refine ⟨(AB + QM + c) / 2 ^ 32, cols_next (q := 0) (residue := (AB + QM + c) % 2 ^ 32) Ly I hk (hw6.of_keeps Ku)
      (P6.keep ?_ (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2) ecxu (by rw [mcu, mc6, mc5])
      ((((Kt5.mono (by decide)).trans (K6.mono (by decide))).trans (Ku.mono (by decide)))) ?_ ?_
      (fun _ => rfl) (fun h => absurd h hkN) ?_ ?_ b4, zfu⟩
    · exact outs_sub1 Ou (List.mem_singleton_self _) (Nat.zero_le _) (by simp only; omega_using [hs])
    · refine (Outs.trans (m₃ := t6.mem) (outs_sub1 Ot5 (List.mem_cons_self ..) (Nat.le_refl _)
        (by simp only; omega_using [])) ?_).trans ?_
      · exact outs_sub1 O6 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)
      · exact outs_sub1 Ou (List.mem_cons_self ..) (by simp only; omega_using []) (by simp only; omega_using [])
    · rw [Outs.w32 Ou (by simp only [List.mem_singleton, forall_eq]; omega_using []) (by omega_using [hs, hn, hk]),
        w6, ite_eq_right hkN, zl, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
    · rw [cl, ch, show w32 t6.mem W (S + 8) = _ from e8, show w32 t6.mem W (S + 12) = _ from e12]
      exact cc
    · rw [hAB, hQM, Nat.zero_mul, Nat.add_zero]
      omega_using []


end VG.Proof.Mont.X86.Sse2
