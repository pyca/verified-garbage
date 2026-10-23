module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Index
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Products
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! # A column's sums

`Acc`: the lanes hold a column's sum `P` modulo `2⁶⁴` and the sum `H` of
its products' high words, with `P - 2³² H` the sum of at most `n` low words.
`dot` adds its products (`Acc.dot`); a square's sum is doubled
(`Acc.double`) and gets the diagonal's product (`Acc.single`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- A column's sums: `P` and the high words' `H`, `P - 2³² H` at most `n` low words. -/
structure Acc (x0 x1 : BitVec 128) (P H n : Nat) : Prop where
  sums : Sums x0 x1 P H
  le : 2 ^ 32 * H ≤ P
  low : P - 2 ^ 32 * H ≤ n * (2 ^ 32 - 1)

theorem Acc.zero {x0 x1 : BitVec 128} : Acc (XBinOp.eval .pxor x0 x0) (XBinOp.eval .pxor x1 x1) 0 0 0 := by
  refine ⟨⟨?_, ?_⟩, Nat.le_refl _, Nat.le_refl _⟩ <;> simp only [pxor_self, qword_zero] <;> rfl

theorem Acc.dot {x0 x1 y0 y1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) {m : Mem} {W : Addr}
    {x y k i0 c : Nat} (D : Sums y0 y1 (P + lowSum m W x y k i0 c) (H + highSum m W x y k i0 c)) :
    Acc y0 y1 (P + lowSum m W x y k i0 c) (H + highSum m W x y k i0 c) (n + c) := by
  obtain ⟨e, l⟩ := lowSum_split m W x y k i0 c
  have := A.le
  have := A.low
  refine ⟨D, by omega, ?_⟩
  rw [Nat.add_mul]; omega

theorem Acc.of_eq' {x0 x1 : BitVec 128} {P P' H n : Nat} (A : Acc x0 x1 P H n) (h : P = P') :
    Acc x0 x1 P' H n := h ▸ A

theorem toNat_add_self (q : BitVec 64) (h : 2 * q.toNat < 2 ^ 64) : (q + q).toNat = 2 * q.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega

theorem Acc.double {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) (hH : 2 * H < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 x0) (XBinOp.eval .paddq x1 x1) (2 * P) (2 * H) (2 * n) := by
  have hh := A.sums.high
  have := A.le
  have := A.low
  refine ⟨⟨?_, ?_⟩, by omega, ?_⟩
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide),
      show qword x0 0 + qword x0 0 + (qword x0 1 + qword x0 1) = (qword x0 0 + qword x0 1) +
        (qword x0 0 + qword x0 1) by ac_rfl, A.sums.low, ← BitVec.ofNat_add, Nat.two_mul]
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide), toNat_add_self _ (by omega),
      toNat_add_self _ (by omega)]
    omega
  · rw [Nat.mul_assoc 2 n]; omega

theorem Acc.single {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) {u v : BitVec 32}
    (hH : H + 2 ^ 32 < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 (singleP u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (singleP u v) 32))
      (P + u.toNat * v.toNat) (H + u.toNat * v.toNat / 2 ^ 32) (n + 1) := by
  have hs := A.sums.add (singleP_0 u v) (singleP_1 u v) (word_mul_lt _ _) (by decide) hH
  have hd := Nat.div_add_mod (u.toNat * v.toNat) (2 ^ 32)
  have hm := Nat.mod_lt (u.toNat * v.toNat) (show 0 < 2 ^ 32 by decide)
  have := A.le
  have := A.low
  refine ⟨by simpa using hs, by omega, ?_⟩
  rw [Nat.succ_mul]; omega

/-! ## The SSE instructions of the input -/

/-- `movd xmm2, eax; pmuludq xmm2, xmm2`, then the product into the sums. -/
theorem sq_run (s : State) (hm : 0 < s.mcdt) :
    ∃ t, runBlock isa (([.xop (.movd .xmm2 .eax), .pmuludq .xmm2 .xmm2] : List Instr) ++ acc .xmm2) s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (singleP (s.gpr .eax) (s.gpr .eax)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1)
        (XShiftOp.eval .psrlq (singleP (s.gpr .eax) (s.gpr .eax)) 32) := by
  simp only [acc, List.cons_append, List.nil_append, runBlock_cons, exec, runStep_some,
    XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left', mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq,
    runBlock_nil, gpr_setXmm]
  exact ⟨trivial, rfl, rfl, rfl, trivial, rfl, rfl⟩

/-- `paddq xmm0, xmm0; paddq xmm1, xmm1`. -/
theorem double_run (s : State) :
    runBlock isa [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)] s =
      some ((s.setXmm .xmm0 (XBinOp.eval .paddq (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .paddq (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

/-! ## The products of a column -/

/-- What every stage of a column has: the working space, the parameters
(`4 N` among them), `ecx = 4 k`, `edx = 4 (k + 1 - N)` and `pmuludq` allowed. -/
structure ColEnv (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N k : Nat) : Prop where
  ws : Ws s W L
  prm : Params s W L V 12
  n4 : (V pN4).toNat = 4 * N
  hk : k < 2 * N
  hN : N < 2 ^ 29
  ecx : s.gpr .ecx = BitVec.ofNat 32 (4 * k)
  edx : s.gpr .edx = BitVec.ofNat 32 (4 * (k + 1 - N))
  mcdt : 0 < s.mcdt

theorem ColEnv.of_keeps {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Keeps rs s t) (hm : t.mem = s.mem) (hc : t.mcdt = s.mcdt)
    (hcx : .ecx ∉ rs := by decide) (hdx : .edx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k :=
  ⟨C.ws.of_keeps K, C.prm.keep (by rw [hm]; exact Outs.refl _ _ _) (K.1 _ hsp) K.2.1 K.2.2, C.n4, C.hk, C.hN,
    by rw [K.1 _ hcx]; exact C.ecx, by rw [K.1 _ hdx]; exact C.edx, by rw [hc]; exact C.mcdt⟩

theorem ColEnv.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Sk rs s t)
    (hcx : .ecx ∉ rs := by decide) (hdx : .edx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k := C.of_keeps K.keep K.mem K.mcdt hcx hdx hsp

/-- `dot`, on the sums. -/
theorem dotAcc_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k x y e P H n : Nat}
    (C : ColEnv t W L V N k) (hx : PtrAt t W .esi x) (hy : PtrAt t W .edi y)
    (hbx : t.gpr .ebx = BitVec.ofNat 32 (4 * e)) (hie : k + 1 - N ≤ e) (ek : e ≤ k + 1)
    (xr : x + 4 * e ≤ L) (yr : y + 4 * (k - (k + 1 - N)) + 4 ≤ L) (hH : H + (e - (k + 1 - N) + 1) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n) :
    WP isa dot t fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + lowSum t.mem W x y k (k + 1 - N) (e - (k + 1 - N)))
        (H + highSum t.mem W x y k (k + 1 - N) (e - (k + 1 - N))) (n + (e - (k + 1 - N))) ∧
      Keeps [.eax, .esi, .edi, .ebp] t u ∧ u.mem = t.mem ∧ u.mcdt = t.mcdt := by
  have hk := C.hk
  have hN := C.hN
  exact WP.mono (dot_ok ⟨xr, yr, ek, hH, by omega, C.mcdt⟩ C.ws hie hx hy C.ecx C.edx hbx A.sums)
    fun u D => ⟨A.dot D.sums, D.keep, D.mem, D.mcdt⟩

/-- A pointer from a parameter. -/
theorem ptr_of_param {u : State} {W : Addr} {r : Reg} {v : BitVec 32} {x : Nat} (h : u.gpr r = v)
    (hv : v.toNat = (W.toNat + x) % 2 ^ 32) : PtrAt u W r x := by rw [PtrAt, h, hv]

/-- The products of `A` and `B`, not a square. -/
theorem product_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k a b : Nat}
    (C : ColEnv s W L V N k) (hA : (V pA).toNat = (W.toNat + a) % 2 ^ 32)
    (hB : (V pB).toNat = (W.toNat + b) % 2 ^ 32) (ha : a + 4 * N ≤ L) (hb : b + 4 * N ≤ L)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (.seq endProduct (.seq (.block (ld pA .esi ++ ld pB .edi)) dot)) s fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)
        (highSum s.mem W a b k (k + 1 - N) (min (k + 1) N - (k + 1 - N))) (min (k + 1) N - (k + 1 - N)) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt := by
  have hk := C.hk
  have hN := C.hN
  refine WP.seq (WP.mono (endProduct_ok C.prm C.n4 C.ecx (by omega)) fun t1 ⟨b1, K1⟩ => ?_)
  have K1' := K1.mono [.eax, .ebx, .esi, .edi]
  simp only [ld, List.cons_append, List.nil_append]
  refine WP.seq (wp_movX (C.prm.readSk K1 (i := pA) (by decide)) fun t2 u2 m2 x2 => ?_)
  have K2 := K1'.trans (Sk.of_upd [.esi] u2 m2 x2)
  refine wp_movX (C.prm.readSk K2 (i := pB) (by decide)) fun t3 u3 m3 x3 => WP.block_nil ?_
  have K3 := K2.trans (Sk.of_upd [.edi] u3 m3 x3)
  have C3 := C.of_sk K3
  refine WP.mono (dotAcc_ok C3 (x := a) (y := b) (e := min (k + 1) N) (P := 0) (H := 0) (n := 0) (ptr_of_param (by rw [u3.other _ (by decide), u2.gpr]) hA)
    (ptr_of_param u3.gpr hB) (by rw [u3.other _ (by decide), u2.other _ (by decide), b1]) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [K3.xmm]; exact A)) fun u ⟨A', K', mu, cu⟩ => ?_
  rw [K3.mem, Nat.zero_add, Nat.zero_add, Nat.zero_add, lowSum_product] at A'
  exact ⟨A', (K3.keep.mono (by decide)).trans (K'.mono (by decide)), by rw [mu, K3.mem], by rw [cu, K3.mcdt]⟩

theorem wp_shrX {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, Upd s t d (s.gpr d >>> n) → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true])
    (k _ (Upd.setFlags _ _ (some ((s.gpr d).getLsbD (n - 1))) (if n = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> n == 0)) (some (s.gpr d >>> n).msb) _) rfl rfl)

/-- `endHalf`'s `ebx`: `4 ⌊(k + 1) / 2⌋`. -/
theorem half_val {k : Nat} (hk : 4 * (k + 1) < 2 ^ 32) :
    let v := (BitVec.ofNat 32 (4 * k) + 4) >>> 3
    v + v + (v + v) = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
  intro v
  have hv : v.toNat = (k + 1) / 2 := by
    simp only [v, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]
    rw [Nat.mod_eq_of_lt (a := 4 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  apply ofNat_of_toNat
  simp only [BitVec.toNat_add, hv]
  omega

/-- A square's products: those above the diagonal, doubled, and the diagonal's. -/
theorem square_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k a : Nat}
    (C : ColEnv s W L V N k) (hA : (V pA).toNat = (W.toNat + a) % 2 ^ 32) (ha : a + 4 * N ≤ L)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (seqs [.block (endHalf ++ ld pA .esi ++ ld pA .edi), dot,
      .block [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)], diag]) s fun u =>
      ∃ H n, Acc (u.xmm .xmm0) (u.xmm .xmm1) (Column.coeff (digits s.mem W a) (digits s.mem W a) N k) H n ∧
        n ≤ N + 1 ∧ Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt := by
  have hk := C.hk
  have hN := C.hN
  have hn := C.ws.nowrap
  simp only [seqs, endHalf, ld, List.cons_append, List.nil_append]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 =>
    wp_shrX (by decide) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 => wp_addX rfl fun t5 u5 _ m5 x5 => ?_)
  have K5 : Sk [.ebx, .esi, .edi] s t5 := (((((Sk.of_upd [.ebx, .esi, .edi] u1 m1 x1).trans
    (Sk.of_upd [.ebx] u2 m2 x2)).trans (Sk.of_upd [.ebx] u3 m3 x3)).trans (Sk.of_upd [.ebx] u4 m4 x4)).trans
    (Sk.of_upd [.ebx] u5 m5 x5))
  have b5 : t5.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr, C.ecx]; exact half_val (by omega_arith)
  refine wp_movX (C.prm.readSk K5 (i := pA) (by decide)) fun t6 u6 m6 x6 => ?_
  have K6 := K5.trans (Sk.of_upd [.esi] u6 m6 x6)
  refine wp_movX (C.prm.readSk K6 (i := pA) (by decide)) fun t7 u7 m7 x7 => WP.block_nil ?_
  have K7 := K6.trans (Sk.of_upd [.edi] u7 m7 x7)
  have C7 := C.of_sk K7
  have b7 : t7.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [u7.other _ (by decide), u6.other _ (by decide), b5]
  refine WP.seq (WP.mono (dotAcc_ok C7 (x := a) (y := a) (e := (k + 1) / 2) (P := 0) (H := 0) (n := 0)
    (ptr_of_param (by rw [u7.other _ (by decide), u6.gpr]) hA) (ptr_of_param u7.gpr hA) b7 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by rw [K7.xmm]; exact A)) fun u ⟨A', K', mu, cu⟩ => ?_)
  rw [K7.mem, Nat.zero_add, Nat.zero_add, Nat.zero_add, lowSum_cross _ _ _ hk] at A'
  have hl := highSum_le s.mem W a a k (k + 1 - N) ((k + 1) / 2 - (k + 1 - N))
  refine WP.seq (WP.of_runBlock ⟨_, double_run u, ?_⟩)
  have Cu := C7.of_keeps K' mu cu
  have Ad := A'.double (by omega_arith)
  have bu : u.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by rw [K'.1 _ (by decide), b7]
  let v := (u.setXmm .xmm0 (XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0))).setXmm .xmm1
    (XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1))
  have Ku : Keeps [.eax, .ebx, .esi, .edi, .ebp] s u :=
    (K7.keep.mono (by decide)).trans (K'.mono (by decide))
  have mus : u.mem = s.mem := by rw [mu, K7.mem]
  have cus : u.mcdt = s.mcdt := by rw [cu, K7.mcdt]
  have Cv : ColEnv v W L V N k := Cu.of_keeps (rs := []) ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl
  have x0v : v.xmm .xmm0 = XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0) := rfl
  have x1v : v.xmm .xmm1 = XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1) := rfl
  rw [← x0v, ← x1v] at Ad
  have vm : v.mem = u.mem := rfl
  have vc : v.mcdt = u.mcdt := rfl
  have hcross : 2 * Column.crossCoeff (digits s.mem W a) N k + Column.diagCoeff (digits s.mem W a) N k =
      Column.coeff (digits s.mem W a) (digits s.mem W a) N k := (Column.coeff_square _ _ _).symm
  rw [Column.diagCoeff_value] at hcross
  unfold diag
  refine WP.seq (wp_movX rfl fun w1 y1 n1 z1 => wp_addX rfl fun w2 y2 _ n2 z2 =>
    wp_cmpX rfl fun w3 f3 _ zf3 n3 z3 => WP.block_nil ?_)
  have e2 : w2.gpr .eax = BitVec.ofNat 32 (8 * ((k + 1) / 2)) := by
    rw [y2.gpr, y1.gpr, show v.gpr .ebx = u.gpr .ebx from rfl, bu, ← BitVec.ofNat_add]; congr 1; omega_arith
  have c2 : w2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by
    rw [y2.other _ (by decide), y1.other _ (by decide)]; exact Cv.ecx
  have K3 : Sk [.eax, .esi] v w3 := ((Sk.of_upd [.eax, .esi] y1 n1 z1).trans (Sk.of_upd [.eax] y2 n2 z2)).trans
    (Sk.of_fupd f3 n3 z3 [.eax])
  have Kvs : Keeps [.eax, .ebx, .esi, .edi, .ebp] s v := Ku.trans ⟨fun _ _ => rfl, rfl, rfl⟩
  by_cases hev : k % 2 = 0
  · refine WP.ite true (by
        show w3.zf = some true
        rw [zf3, e2, c2, sub_beq (by omega_arith) (by omega_arith), decide_eq_true (by omega_arith)])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.cons_append, List.cons_append, List.cons_append]
    have C3 := Cv.of_sk K3
    refine wp_movX (C3.prm.read pA (by decide)) fun w4 y4 n4 z4 => wp_addX rfl fun w5 y5 _ n5 z5 => ?_
    have K5 : Sk [.eax, .esi] v w5 := (K3.trans (Sk.of_upd [.esi] y4 n4 z4)).trans (Sk.of_upd [.esi] y5 n5 z5)
    have p5 : PtrAt w5 (W := W) .esi (a + 4 * (k / 2)) := by
      have := (V pA).isLt
      rw [PtrAt, y5.gpr, y4.gpr, y4.other _ (by decide), f3.gpr, y2.other _ (by decide), y1.other _ (by decide),
        show v.gpr .ebx = u.gpr .ebx from rfl, bu, BitVec.toNat_add, hA, toNat_ofNat_lt (by omega_arith)]
      omega_arith
    have hw5 := C.ws.of_keeps (Kvs.trans (K5.keep.mono (by decide)))
    refine wp_movX (readSrc_ptr hw5 p5 (d := 0) (by omega_arith)) fun w6 y6 n6 z6 => ?_
    have K6 : Sk [.eax, .esi] v w6 := K5.trans (Sk.of_upd [.eax] y6 n6 z6)
    obtain ⟨w7, run, g7, m7, rd7, wr7, mc7, a0, a1⟩ := sq_run w6 (by rw [K6.mcdt]; exact Cv.mcdt)
    have Af := Ad.single (u := w6.gpr .eax) (v := w6.gpr .eax) (by omega_arith)
    rw [← K6.xmm, ← a0, ← a1] at Af
    refine WP.of_runBlock ⟨w7, run, _, _, Af.of_eq' ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hcross, ite_eq_left ⟨hev, by omega_arith⟩, y6.gpr, K5.mem, vm, mus]
      simp only [digits, w32, Nat.add_zero]
    · omega_arith
    · exact (Kvs.trans (K6.keep.mono (by decide))).trans ⟨fun r _ => by rw [g7], rd7, wr7⟩
    · rw [m7, K6.mem, vm, mus]
    · rw [mc7, K6.mcdt, vc, cus]
  · refine WP.ite false (by
        show w3.zf = some false
        rw [zf3, e2, c2, sub_beq (by omega_arith) (by omega_arith), decide_eq_false (by omega_arith)])
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ?_)
    have Ao := Ad
    rw [← K3.xmm] at Ao
    refine ⟨_, _, Ao.of_eq' ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hcross, ite_eq_right (by omega_arith), Nat.add_zero]
    · omega_arith
    · exact Kvs.trans (K3.keep.mono (by decide))
    · rw [K3.mem, vm, mus]
    · rw [K3.mcdt, vc, cus]

/-- A parameter `W + x` as a number. -/
theorem param_ofNat {v : BitVec 32} {W : Addr} {x L : Nat} (hv : v.toNat = (W.toNat + x) % 2 ^ 32)
    (hx : x < L) (hn : W.toNat + L ≤ 2 ^ 32) : v = BitVec.ofNat 32 (W.toNat + x) :=
  ofNat_of_toNat (by rw [hv, Nat.mod_eq_of_lt (by omega)])

/-- The products of `A` and `B`: a square's if `A` is `B`. -/
theorem input_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k a b : Nat}
    (C : ColEnv s W L V N k) (hA : (V pA).toNat = (W.toNat + a) % 2 ^ 32)
    (hB : (V pB).toNat = (W.toNat + b) % 2 ^ 32) (ha : a + 4 * N ≤ L) (hb : b + 4 * N ≤ L)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa input s fun u =>
      ∃ H n, Acc (u.xmm .xmm0) (u.xmm .xmm1) (Column.coeff (digits s.mem W a) (digits s.mem W b) N k) H n ∧
        n ≤ N + 1 ∧ Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt := by
  have hk := C.hk
  have hn := C.ws.nowrap
  unfold input
  refine WP.seq (wp_movX (C.prm.read pA (by decide)) fun t1 u1 m1 x1 =>
    wp_movX (C.prm.readSk (Sk.of_upd [.eax] u1 m1 x1) (i := pB) (by decide)) fun t1' u1' m1' x1' =>
    wp_cmpX rfl fun t2 f2 _ z2 m2 x2 => WP.block_nil ?_)
  have K2 : Sk [.eax, .ebx] s t2 := ((Sk.of_upd [.eax, .ebx] u1 m1 x1).trans (Sk.of_upd [.eax, .ebx] u1' m1' x1')).trans
    (Sk.of_fupd f2 m2 x2 [.eax, .ebx])
  have C2 := C.of_sk K2
  have A2 : Acc (t2.xmm .xmm0) (t2.xmm .xmm1) 0 0 0 := by rw [K2.xmm]; exact A
  have z : t2.zf = some (decide (a = b)) := by
    rw [z2, u1'.gpr, u1'.other _ (by decide), u1.gpr, param_ofNat hA (by omega) hn, param_ofNat hB (by omega) hn,
      sub_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  have post : ∀ u, Keeps [.eax, .ebx, .esi, .edi, .ebp] t2 u → u.mem = t2.mem → u.mcdt = t2.mcdt →
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt := fun u K m c =>
    ⟨(K2.keep.mono (by decide)).trans K, by rw [m, K2.mem], by rw [c, K2.mcdt]⟩
  by_cases hab : a = b
  · subst hab
    refine WP.ite true (by show t2.zf = _; rw [z, decide_eq_true rfl]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (square_ok C2 hA ha A2) fun u ⟨H, n, Au, hnu, K, m, c⟩ => ?_
    rw [K2.mem] at Au
    exact ⟨H, n, Au, hnu, post u K m c⟩
  · refine WP.ite false (by show t2.zf = _; rw [z, decide_eq_false hab]) (fun h => absurd h (by decide))
      (fun _ => ?_)
    refine WP.mono (product_ok C2 hA hB ha hb A2) fun u ⟨Au, K, m, c⟩ => ?_
    rw [K2.mem] at Au
    exact ⟨_, _, Au, by omega, post u K m c⟩

/-- The products of the quotient digits written so far (at `S + 24`) and `M`. -/
theorem reduce_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo P H n : Nat}
    (C : ColEnv s W L V N k) (hS : (V pS).toNat = (W.toNat + S) % 2 ^ 32)
    (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32) (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 * N ≤ L)
    (hH : H + (N + 1) * 2 ^ 32 < 2 ^ 64) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) P H n) :
    WP isa reduce s fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1)
        (P + Column.coeff (Column.prefixDigits (digits s.mem W (S + 24)) k) (digits s.mem W mo) N k)
        (H + highSum s.mem W (S + 24) mo k (k + 1 - N) (min k N - (k + 1 - N))) (n + (min k N - (k + 1 - N))) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt := by
  have hk := C.hk
  have hN := C.hN
  unfold reduce
  refine WP.seq (WP.mono (endReduce_ok C.prm C.n4 C.ecx (by omega)) fun t1 ⟨b1, K1⟩ => ?_)
  have K1' := K1.mono [.eax, .ebx, .esi, .edi]
  simp only [ldQ, ld, List.cons_append, List.nil_append]
  refine WP.seq (wp_movX (C.prm.readSk K1 (i := pS) (by decide)) fun t2 u2 m2 x2 =>
    wp_addX rfl fun t3 u3 _ m3 x3 => ?_)
  have K3 := (K1'.trans (Sk.of_upd [.esi] u2 m2 x2)).trans (Sk.of_upd [.esi] u3 m3 x3)
  refine wp_movX (C.prm.readSk K3 (i := pM) (by decide)) fun t4 u4 m4 x4 => WP.block_nil ?_
  have K4 := K3.trans (Sk.of_upd [.edi] u4 m4 x4)
  have C4 := C.of_sk K4
  have p4 : PtrAt t4 W .esi (S + 24) := by
    have := (V pS).isLt
    rw [PtrAt, u4.other _ (by decide), u3.gpr, u2.gpr, BitVec.toNat_add, hS]
    simp only [offW, BitVec.toNat_ofNat]
    omega
  refine WP.mono (dotAcc_ok C4 (x := S + 24) (y := mo) (e := min k N) (P := P) (H := H) (n := n) p4 (ptr_of_param u4.gpr hM)
    (by rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), b1]) (by omega) (by omega)
    (by omega) (by omega)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) hH)
    (by rw [K4.xmm]; exact A)) fun u ⟨A', K', mu, cu⟩ => ?_
  rw [K4.mem, lowSum_reduce] at A'
  exact ⟨A', (K4.keep.mono (by decide)).trans (K'.mono (by decide)), by rw [mu, K4.mem], by rw [cu, K4.mcdt]⟩

end VG.Proof.Mont.X86.Sse2
