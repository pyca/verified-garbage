module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Pair
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # The products of a column: `dot`

`dot` adds `Σ X_i Y_(k-i)` over `i0 ≤ i < e` to the sums (`Sums`), for numbers
`X` and `Y` at offsets `x` and `y` of the working space: four products at a
time (`quadBody`), then two (`pair`), then one (`single`), counted down by
`ebp`, the bytes of `X` left. `edi` is tracked as `edi + 12`, the address of
`Y_(k-i)`, since `edi` may lie below `Y`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.X86.Wp

/-! ## Sums of products -/

/-- `Σ f (a + j)` for `j < n`. -/
def rsum (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rsum f a n + f (a + n)

/-- The product `X_i Y_(k-i)` of the words at offsets `x + 4 i` and `y + 4 (k - i)`. -/
def prod (m : Mem) (W : Addr) (x y k i : Nat) : Nat := w32 m W (x + 4 * i) * w32 m W (y + 4 * (k - i))

/-- The products' sum and their high words' sum, over `i0 ≤ i < i0 + n`. -/
def lowSum (m : Mem) (W : Addr) (x y k i0 n : Nat) : Nat := rsum (prod m W x y k) i0 n
def highSum (m : Mem) (W : Addr) (x y k i0 n : Nat) : Nat := rsum (fun i => prod m W x y k i / 2 ^ 32) i0 n

theorem prod_lt (m : Mem) (W : Addr) (x y k i : Nat) : prod m W x y k i < 2 ^ 64 := by
  have := word_mul_lt (m.readW (off W (x + 4 * i)) 32) (m.readW (off W (y + 4 * (k - i))) 32)
  simpa [prod, w32] using this

theorem highSum_le (m : Mem) (W : Addr) (x y k i0 n : Nat) : highSum m W x y k i0 n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => simp [highSum, rsum]
  | succ n ih =>
    have := prod_lt m W x y k (i0 + n)
    have q : prod m W x y k (i0 + n) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
      have := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 32)).2 (show prod m W x y k (i0 + n) < 2 ^ 32 * 2 ^ 32 by
        simpa using this)
      omega
    simp only [highSum, rsum] at ih ⊢
    rw [Nat.succ_mul]; omega

/-! ## Addresses -/

/-- `[r + d]`, for `r + c = W + y`. -/
theorem ea_top {s : State} {W : Addr} {L : Nat} (hw : Ws s W L) {r : Reg} {c y d : Nat}
    (hp : (s.gpr r + BitVec.ofNat 32 c).toNat = (W.toNat + y) % 2 ^ 32) (hd : d ≤ c) (hy : c - d ≤ y)
    (hl : y < L) (hc : c < 2 ^ 32) : s.ea (at_ r d) = off W (y - (c - d)) := by
  have nw := hw.nowrap
  have hW : W.toNat < 2 ^ 64 := W.isLt
  have hR := (s.gpr r).isLt
  rw [at_, ea_mk]
  apply BitVec.eq_of_toNat_eq
  simp only [addr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at hp ⊢
  rw [Nat.mod_eq_of_lt (a := c) (by omega)] at hp
  rw [Nat.mod_eq_of_lt (a := W.toNat + y) (by omega)] at hp
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := y - (c - d)) (by omega),
    Nat.mod_eq_of_lt (a := W.toNat + (y - (c - d))) (by omega)]
  rw [Nat.mod_eq_of_lt (a := ((s.gpr r).toNat + d) % 2 ^ 32) (by omega)]
  omega

/-- The two words of 8 bytes of the working space. -/
theorem read8_lo (m : Mem) (W : Addr) (a : Nat) : ((m.readW (off W a) 64).extractLsb' 0 32).toNat = w32 m W a := by
  rw [readW64_lo]

theorem read8_hi (m : Mem) (W : Addr) (a : Nat) :
    ((m.readW (off W a) 64).extractLsb' 32 32).toNat = w32 m W (a + 4) := by
  rw [readW64_hi, w32]
  have e : off W a + 4 = off W (a + 4) := by
    rw [off, off, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact congrArg (fun p => (m.readW p 32).toNat) e

/-! ## The loop's invariant -/

/-- After the products `i0 ≤ j < i` (from the state `s0` before them): the
pointers, the count `4 (e - i)`, the sums, and what stays. -/
structure DotI (s0 : State) (W : Addr) (L x y k i0 e S H i : Nat) (t : State) : Prop where
  lo : i0 ≤ i
  hi : i ≤ e
  ws : Ws t W L
  esi : PtrAt t W .esi (x + 4 * i)
  top : i < e → (t.gpr .edi + 12).toNat = (W.toNat + (y + 4 * (k - i))) % 2 ^ 32
  cnt : t.gpr .ebp = BitVec.ofNat 32 (4 * (e - i))
  sums : Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + lowSum s0.mem W x y k i0 (i - i0))
    (H + highSum s0.mem W x y k i0 (i - i0))
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 t
  mem : t.mem = s0.mem
  mcdt : t.mcdt = s0.mcdt
  x4 : t.xmm .xmm4 = s0.xmm .xmm4
  x5 : t.xmm .xmm5 = s0.xmm .xmm5
  x6 : t.xmm .xmm6 = s0.xmm .xmm6
  x7 : t.xmm .xmm7 = s0.xmm .xmm7

/-- What the products need: `X`'s words up to `e` and `Y`'s down from `k - i0`
within the working space, `e ≤ k + 1`, room for the high sums, `pmuludq`
allowed, and counts below `2³²`. -/
structure DotEnv (s0 : State) (L x y k i0 e H : Nat) : Prop where
  xr : x + 4 * e ≤ L
  yr : y + 4 * (k - i0) + 4 ≤ L
  ek : e ≤ k + 1
  hH : H + (e - i0 + 1) * 2 ^ 32 < 2 ^ 64
  hk : 4 * (k + 1) < 2 ^ 32
  mcdt : 0 < s0.mcdt

theorem lowSum_succ (m : Mem) (W : Addr) (x y k i0 n : Nat) :
    lowSum m W x y k i0 (n + 1) = lowSum m W x y k i0 n + prod m W x y k (i0 + n) := rfl

theorem highSum_succ (m : Mem) (W : Addr) (x y k i0 n : Nat) :
    highSum m W x y k i0 (n + 1) = highSum m W x y k i0 n + prod m W x y k (i0 + n) / 2 ^ 32 := rfl

/-- The words a pair at `X_i`, `Y_(k-i-1)` multiplies, as `pair_sums` names them. -/
theorem pair_words0 (m : Mem) (W : Addr) {x y k i : Nat} (hk : i + 1 ≤ k) :
    ((m.readW (off W (x + 4 * i)) 64).extractLsb' 0 32).toNat *
      ((m.readW (off W (y + 4 * (k - i - 1))) 64).extractLsb' 32 32).toNat = prod m W x y k i := by
  rw [read8_lo, read8_hi, prod, show y + 4 * (k - i - 1) + 4 = y + 4 * (k - i) by omega]

theorem pair_words1 (m : Mem) (W : Addr) (x y k i : Nat) :
    ((m.readW (off W (x + 4 * i)) 64).extractLsb' 32 32).toNat *
      ((m.readW (off W (y + 4 * (k - i - 1))) 64).extractLsb' 0 32).toNat = prod m W x y k (i + 1) := by
  rw [read8_lo, read8_hi, prod, show x + 4 * i + 4 = x + 4 * (i + 1) by omega,
    show k - i - 1 = k - (i + 1) by omega]

theorem Sums.of_eq {x0 x1 : BitVec 128} {S H S' H' : Nat} (h : Sums x0 x1 S H) (hs : S = S') (hh : H = H') :
    Sums x0 x1 S' H' := hs ▸ hh ▸ h

theorem lowSum_step (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    lowSum m W x y k i0 (i + 1 - i0) = lowSum m W x y k i0 (i - i0) + prod m W x y k i := by
  rw [show i + 1 - i0 = (i - i0) + 1 by omega, lowSum_succ, show i0 + (i - i0) = i by omega]

theorem highSum_step (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    highSum m W x y k i0 (i + 1 - i0) = highSum m W x y k i0 (i - i0) + prod m W x y k i / 2 ^ 32 := by
  rw [show i + 1 - i0 = (i - i0) + 1 by omega, highSum_succ, show i0 + (i - i0) = i by omega]

theorem ea_of_gpr {s t : State} (h : t.gpr = s.gpr) (m : MemOp) : t.ea m = s.ea m := by
  simp only [State.ea, h]

/-! ## Scalar instructions, keeping `mcdt` and the XMM registers -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_addX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) → t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_subX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_cmpX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → t.zf = some (s.gpr d - v == 0) →
      t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl)

theorem wp_movX {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d v → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  cons (s' := s.setReg d v) (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl rfl)

end

/-- A pair's run as a weakest precondition. -/
theorem wp_pair {s : State} {dx dy : Nat} {rest : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h1 : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi dx)) 8) (h2 : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi dy)) 8)
    (k : ∀ t, SseOnly s t →
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0)
        (pairP (s.mem.readW (s.ea (at_ .esi dx)) 64) (s.mem.readW (s.ea (at_ .edi dy)) 64)) →
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1) (XShiftOp.eval .psrlq
        (pairP (s.mem.readW (s.ea (at_ .esi dx)) 64) (s.mem.readW (s.ea (at_ .edi dy)) 64)) 32) →
      WP isa (.block rest) t Q) :
    WP isa (.block (pair dx dy ++ rest)) s Q := by
  obtain ⟨t, e, o, a, b⟩ := pair_run s dx dy hm h1 h2
  exact WP.block_append (WP.of_runBlock ⟨t, e, k t o a b⟩)

/-- The scalar tail of `quadBody`: the pointers and the count moved, CF
from the count's comparison with 16. -/
theorem wp_quadTail {s : State} {Q : State → Prop}
    (k : ∀ t, t.gpr .esi = s.gpr .esi + 16 → t.gpr .edi = s.gpr .edi - 16 → t.gpr .ebp = s.gpr .ebp - 16 →
      (∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t.gpr r = s.gpr r) →
      t.cf = some (decide ((s.gpr .ebp - 16).toNat < 16)) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      t.mcdt = s.mcdt → t.xmm = s.xmm → Q t) :
    WP isa (.block [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 16), .alu .sub .ebp (.imm 16),
      .alu .cmp .ebp (.imm 16)]) s Q := by
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine k _ ?_ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ rfl rfl rfl rfl rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ↓reduceIte]
  · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte]; rfl

theorem prod_div_lt (m : Mem) (W : Addr) (x y k i : Nat) : prod m W x y k i / 2 ^ 32 < 2 ^ 32 :=
  (Nat.div_lt_iff_lt_mul (by decide)).2 (by have := prod_lt m W x y k i; omega)

theorem lowSum_four (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    lowSum m W x y k i0 (i + 4 - i0) = lowSum m W x y k i0 (i - i0) + prod m W x y k i +
      prod m W x y k (i + 1) + prod m W x y k (i + 2) + prod m W x y k (i + 3) := by
  rw [show i + 4 = i + 3 + 1 from rfl, lowSum_step _ _ (by omega), show i + 3 = i + 2 + 1 from rfl,
    lowSum_step _ _ (by omega), show i + 2 = i + 1 + 1 from rfl, lowSum_step _ _ (by omega),
    lowSum_step _ _ h]

theorem highSum_four (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    highSum m W x y k i0 (i + 4 - i0) = highSum m W x y k i0 (i - i0) + prod m W x y k i / 2 ^ 32 +
      prod m W x y k (i + 1) / 2 ^ 32 + prod m W x y k (i + 2) / 2 ^ 32 + prod m W x y k (i + 3) / 2 ^ 32 := by
  rw [show i + 4 = i + 3 + 1 from rfl, highSum_step _ _ (by omega), show i + 3 = i + 2 + 1 from rfl,
    highSum_step _ _ (by omega), show i + 2 = i + 1 + 1 from rfl, highSum_step _ _ (by omega),
    highSum_step _ _ h]

/-- Four products: the loop's body. -/
theorem quad_ok {s0 t : State} {W : Addr} {L x y k i0 e S H i : Nat} (E : DotEnv s0 L x y k i0 e H)
    (I : DotI s0 W L x y k i0 e S H i t) (hi : i + 4 ≤ e) :
    WP isa (.block quadBody) t fun u =>
      DotI s0 W L x y k i0 e S H (i + 4) u ∧ u.cf = some (decide (4 * (e - (i + 4)) < 16)) := by
  have hn := I.ws.nowrap
  have xr := E.xr
  have yr := E.yr
  have ek := E.ek
  have lo := I.lo
  have hk := E.hk
  have top := I.top (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 : t.ea (at_ .esi 0) = off W (x + 4 * i) := by rw [ea_ptr I.ws I.esi (by omega), Nat.add_zero]
  have ex8 : t.ea (at_ .esi 8) = off W (x + 4 * (i + 2)) := by
    rw [ea_ptr I.ws I.esi (by omega), show x + 4 * i + 8 = x + 4 * (i + 2) by omega]
  have ey8 : t.ea (at_ .edi 8) = off W (y + 4 * (k - i - 1)) := by
    rw [ea_top I.ws top (c := 12) (by decide) (by omega) (by omega) (by decide),
      show y + 4 * (k - i) - (12 - 8) = y + 4 * (k - i - 1) by omega]
  have ey0 : t.ea (at_ .edi 0) = off W (y + 4 * (k - (i + 2) - 1)) := by
    rw [ea_top I.ws top (c := 12) (by decide) (by omega) (by omega) (by decide),
      show y + 4 * (k - i) - (12 - 0) = y + 4 * (k - (i + 2) - 1) by omega]
  rw [quadBody, List.append_assoc]
  refine wp_pair hm (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey8]; exact ws_read I.ws (by omega))
    fun t1 o1 a1 b1 => ?_
  have hm1 : 0 < t1.mcdt := o1.mcdt ▸ hm
  refine wp_pair hm1 (by rw [o1.rd, o1.wr, ea_of_gpr o1.gpr, ex8]; exact ws_read I.ws (by omega))
    (by rw [o1.rd, o1.wr, ea_of_gpr o1.gpr, ey0]; exact ws_read I.ws (by omega)) fun t2 o2 a2 b2 => ?_
  refine wp_quadTail fun u esi edi ebp oth cf mem rd wr mcdt xmm => ?_
  rw [ex0, ey8, I.mem] at a1 b1
  rw [ea_of_gpr o1.gpr, ea_of_gpr o1.gpr, ex8, ey0, o1.mem, I.mem] at a2 b2
  have hl := highSum_le s0.mem W x y k i0 (i - i0)
  have hH := E.hH
  have q0 := prod_div_lt s0.mem W x y k i
  have q1 := prod_div_lt s0.mem W x y k (i + 1)
  have q2 := prod_div_lt s0.mem W x y k (i + 2)
  have q3 := prod_div_lt s0.mem W x y k (i + 3)
  have s1 := pair_sums I.sums (by omega) a1 b1
  dsimp only at s1
  rw [pair_words0 s0.mem W (x := x) (y := y) (i := i) (by omega), pair_words1] at s1
  have s2 := pair_sums s1 (by omega) a2 b2
  dsimp only at s2
  rw [pair_words0 s0.mem W (x := x) (y := y) (i := i + 2) (by omega), pair_words1] at s2
  have g : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → u.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [oth r h1 h2 h3, o2.gpr, o1.gpr]
  have ebp' : u.gpr .ebp = BitVec.ofNat 32 (4 * (e - (i + 4))) := by
    rw [ebp, o2.gpr, o1.gpr, I.cnt, show 4 * (e - (i + 4)) = 4 * (e - i) - 16 by omega]
    exact sub_ofNat (b := 16) (by omega)
  refine ⟨⟨by omega, hi, I.ws.of_wr (by rw [wr, o2.wr, o1.wr]), ?_, fun h => ?_, ebp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, esi, o2.gpr, o1.gpr, ptr_add I.esi, show (16 : BitVec 32).toNat = 16 from rfl]
    omega
  · rw [edi, o2.gpr, o1.gpr]
    have := (t.gpr .edi).isLt
    rw [BitVec.toNat_add] at top
    simp only [BitVec.toNat_add, BitVec.toNat_sub, show (16 : BitVec 32).toNat = 16 from rfl,
      show (12 : BitVec 32).toNat = 12 from rfl] at top ⊢
    omega
  · rw [xmm]
    refine s2.of_eq ?_ ?_
    · rw [lowSum_four _ _ lo, show i + 2 + 1 = i + 3 from rfl]; omega
    · rw [highSum_four _ _ lo, show i + 2 + 1 = i + 3 from rfl]; omega
  · refine ⟨fun r hr => ?_, by rw [rd, o2.rd, o1.rd, I.keep.2.1], by rw [wr, o2.wr, o1.wr, I.keep.2.2]⟩
    rw [g r (by intro h; simp [h] at hr) (by intro h; simp [h] at hr) (by intro h; simp [h] at hr)]
    exact I.keep.1 r hr
  · rw [mem, o2.mem, o1.mem, I.mem]
  · rw [mcdt, o2.mcdt, o1.mcdt, I.mcdt]
  · rw [xmm, o2.x4, o1.x4, I.x4]
  · rw [xmm, o2.x5, o1.x5, I.x5]
  · rw [xmm, o2.x6, o1.x6, I.x6]
  · rw [xmm, o2.x7, o1.x7, I.x7]
  · rw [cf, ← ebp, ebp', toNat_ofNat_lt (by omega)]

theorem lowSum_two (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    lowSum m W x y k i0 (i + 2 - i0) =
      lowSum m W x y k i0 (i - i0) + prod m W x y k i + prod m W x y k (i + 1) := by
  rw [show i + 2 = i + 1 + 1 from rfl, lowSum_step _ _ (by omega), lowSum_step _ _ h]

theorem highSum_two (m : Mem) (W : Addr) {x y k i0 i : Nat} (h : i0 ≤ i) :
    highSum m W x y k i0 (i + 2 - i0) =
      highSum m W x y k i0 (i - i0) + prod m W x y k i / 2 ^ 32 + prod m W x y k (i + 1) / 2 ^ 32 := by
  rw [show i + 2 = i + 1 + 1 from rfl, highSum_step _ _ (by omega), highSum_step _ _ h]

/-- Two products, after the loop. -/
theorem twin_ok {s0 t : State} {W : Addr} {L x y k i0 e S H i : Nat} (E : DotEnv s0 L x y k i0 e H)
    (I : DotI s0 W L x y k i0 e S H i t) (hi : i + 2 ≤ e) :
    WP isa (.block (pair 0 8 ++ ([.alu .add .esi (.imm 8), .alu .sub .edi (.imm 8), .alu .sub .ebp (.imm 8)] : List Instr))) t
      (DotI s0 W L x y k i0 e S H (i + 2)) := by
  have hn := I.ws.nowrap
  have xr := E.xr
  have yr := E.yr
  have ek := E.ek
  have lo := I.lo
  have hk := E.hk
  have top := I.top (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 : t.ea (at_ .esi 0) = off W (x + 4 * i) := by rw [ea_ptr I.ws I.esi (by omega), Nat.add_zero]
  have ey8 : t.ea (at_ .edi 8) = off W (y + 4 * (k - i - 1)) := by
    rw [ea_top I.ws top (c := 12) (by decide) (by omega) (by omega) (by decide),
      show y + 4 * (k - i) - (12 - 8) = y + 4 * (k - i - 1) by omega]
  refine wp_pair hm (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey8]; exact ws_read I.ws (by omega))
    fun t1 o1 a1 b1 => ?_
  refine wp_addX rfl fun t2 u2 _ m2 x2 => wp_subX rfl fun t3 u3 _ m3 x3 =>
    wp_subX rfl fun u u4 _ m4 x4 => WP.block_nil ?_
  rw [ex0, ey8, I.mem] at a1 b1
  have hl := highSum_le s0.mem W x y k i0 (i - i0)
  have hH := E.hH
  have q0 := prod_div_lt s0.mem W x y k i
  have q1 := prod_div_lt s0.mem W x y k (i + 1)
  have s1 := pair_sums I.sums (by omega) a1 b1
  dsimp only at s1
  rw [pair_words0 s0.mem W (x := x) (y := y) (i := i) (by omega), pair_words1] at s1
  have g : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → u.gpr r = t.gpr r := fun r h1 h2 h3 => by
    rw [u4.other r h3, u3.other r h2, u2.other r h1, o1.gpr]
  have xm : u.xmm = t1.xmm := by rw [x4, x3, x2]
  refine ⟨by omega, hi, I.ws.of_wr (by rw [u4.wr, u3.wr, u2.wr, o1.wr]), ?_, fun h => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, u4.other _ (by decide), u3.other _ (by decide), u2.gpr, o1.gpr, ptr_add I.esi,
      show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  · rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), o1.gpr]
    have := (t.gpr .edi).isLt
    rw [BitVec.toNat_add] at top
    simp only [BitVec.toNat_add, BitVec.toNat_sub, show (8 : BitVec 32).toNat = 8 from rfl,
      show (12 : BitVec 32).toNat = 12 from rfl] at top ⊢
    omega
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), o1.gpr, I.cnt,
      show 4 * (e - (i + 2)) = 4 * (e - i) - 8 by omega]
    exact sub_ofNat (b := 8) (by omega)
  · rw [xm]
    refine s1.of_eq ?_ ?_
    · rw [lowSum_two _ _ lo]; omega
    · rw [highSum_two _ _ lo]; omega
  · refine ⟨fun r hr => ?_, by rw [u4.rd, u3.rd, u2.rd, o1.rd, I.keep.2.1],
      by rw [u4.wr, u3.wr, u2.wr, o1.wr, I.keep.2.2]⟩
    rw [g r (by intro h; simp [h] at hr) (by intro h; simp [h] at hr) (by intro h; simp [h] at hr)]
    exact I.keep.1 r hr
  · rw [u4.mem, u3.mem, u2.mem, o1.mem, I.mem]
  · rw [m4, m3, m2, o1.mcdt, I.mcdt]
  · rw [xm, o1.x4, I.x4]
  · rw [xm, o1.x5, I.x5]
  · rw [xm, o1.x6, I.x6]
  · rw [xm, o1.x7, I.x7]

/-- The invariant through an instruction that changes only flags. -/
theorem DotI.of_same {s0 t t' : State} {W : Addr} {L x y k i0 e S H i : Nat} (I : DotI s0 W L x y k i0 e S H i t)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hr : t'.rd = t.rd) (hw : t'.wr = t.wr) (hc : t'.mcdt = t.mcdt)
    (hx : t'.xmm = t.xmm) : DotI s0 W L x y k i0 e S H i t' := by
  refine ⟨I.lo, I.hi, I.ws.of_wr hw, ?_, fun h => ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, hg]; exact I.esi
  · rw [hg]; exact I.top h
  · rw [hg]; exact I.cnt
  · rw [hx]; exact I.sums
  · rw [hg]; exact I.keep.1 r hr
  · rw [hr]; exact I.keep.2.1
  · rw [hw]; exact I.keep.2.2
  · rw [hm]; exact I.mem
  · rw [hc]; exact I.mcdt
  · rw [hx]; exact I.x4
  · rw [hx]; exact I.x5
  · rw [hx]; exact I.x6
  · rw [hx]; exact I.x7

/-- Four products at a time while at least four remain. -/
theorem quads_ok {s0 t : State} {W : Addr} {L x y k i0 e S H i : Nat} (E : DotEnv s0 L x y k i0 e H)
    (I : DotI s0 W L x y k i0 e S H i t) (hc : t.cf = some (decide (4 * (e - i) < 16))) :
    WP isa (.ite .ae (.loop (.block quadBody) .ae) (.block [])) t
      fun u => ∃ j, DotI s0 W L x y k i0 e S H j u ∧ e < j + 4 := by
  have hi := I.hi
  by_cases h4 : e < i + 4
  · refine WP.ite false (by show t.cf.map _ = _; rw [hc, decide_eq_true (by omega)]; rfl)
      (fun h => absurd h (by decide)) fun _ => WP.block_nil ⟨i, I, h4⟩
  refine WP.ite true (by show t.cf.map _ = _; rw [hc, decide_eq_false (by omega)]; rfl) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine WP.loop (M := isa) (fun m u => ∃ j, m = e - j ∧ j + 4 ≤ e ∧ DotI s0 W L x y k i0 e S H j u) ?_ (e - i) t
    ⟨i, rfl, by omega, I⟩
  rintro m u ⟨j, rfl, hj, J⟩
  refine WP.mono (quad_ok E J hj) fun v ⟨J', cv⟩ => ?_
  have hv : isa.eval .ae v = some (!decide (4 * (e - (j + 4)) < 16)) := by
    show v.cf.map _ = _; rw [cv]; rfl
  by_cases h : e < j + 4 + 4
  · exact .inl ⟨by rw [hv, decide_eq_true (by omega)]; rfl, j + 4, J', h⟩
  · exact .inr ⟨by rw [hv, decide_eq_false (by omega)]; rfl, e - (j + 4), by omega, j + 4, rfl, by omega, J'⟩

/-- Two products if at least two remain. -/
theorem twins_ok {s0 t : State} {W : Addr} {L x y k i0 e S H : Nat} (E : DotEnv s0 L x y k i0 e H)
    (h : ∃ j, DotI s0 W L x y k i0 e S H j t ∧ e < j + 4) :
    WP isa (.seq (.block [.alu .cmp .ebp (.imm 8)])
      (.ite .ae (.block (pair 0 8 ++ ([.alu .add .esi (.imm 8), .alu .sub .edi (.imm 8), .alu .sub .ebp (.imm 8)] : List Instr)))
        (.block []))) t
      fun u => ∃ j, DotI s0 W L x y k i0 e S H j u ∧ e < j + 2 := by
  obtain ⟨j, I, hj⟩ := h
  have hi := I.hi
  have hk := E.hk
  have ek := E.ek
  refine WP.seq (wp_cmpX rfl fun t1 f1 c1 _ m1 x1 => WP.block_nil ?_)
  have I1 := I.of_same f1.gpr f1.mem f1.rd f1.wr m1 x1
  have hc : isa.eval .ae t1 = some (!decide (4 * (e - j) < 8)) := by
    show t1.cf.map _ = _
    rw [c1, I.cnt, toNat_ofNat_lt (by omega)]; rfl
  by_cases h2 : e < j + 2
  · exact WP.ite false (by rw [hc, decide_eq_true (by omega)]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ⟨j, I1, h2⟩
  · exact WP.ite true (by rw [hc, decide_eq_false (by omega)]; rfl)
      (fun _ => WP.mono (twin_ok E I1 (by omega)) fun u J => ⟨j + 2, J, by omega⟩) (fun h => absurd h (by decide))

/-- What `dot` leaves: the sums of the products `i0 ≤ i < e`, and what stays. -/
structure DotPost (s0 : State) (W : Addr) (x y k i0 e S H : Nat) (u : State) : Prop where
  sums : Sums (u.xmm .xmm0) (u.xmm .xmm1) (S + lowSum s0.mem W x y k i0 (e - i0))
    (H + highSum s0.mem W x y k i0 (e - i0))
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 u
  mem : u.mem = s0.mem
  mcdt : u.mcdt = s0.mcdt
  x4 : u.xmm .xmm4 = s0.xmm .xmm4
  x5 : u.xmm .xmm5 = s0.xmm .xmm5
  x6 : u.xmm .xmm6 = s0.xmm .xmm6
  x7 : u.xmm .xmm7 = s0.xmm .xmm7

/-- The last product if one remains. -/
theorem last_ok {s0 t : State} {W : Addr} {L x y k i0 e S H : Nat} (E : DotEnv s0 L x y k i0 e H)
    (h : ∃ j, DotI s0 W L x y k i0 e S H j t ∧ e < j + 2) :
    WP isa (.seq (.block [.alu .add .edi (.imm 8), .alu .cmp .ebp (.imm 4)]) (.ite .ae (.block single) (.block []))) t
      (DotPost s0 W x y k i0 e S H) := by
  obtain ⟨j, I, hj⟩ := h
  have hi := I.hi
  have hk := E.hk
  have ek := E.ek
  have xr := E.xr
  have yr := E.yr
  have lo := I.lo
  have hn := I.ws.nowrap
  refine WP.seq (wp_addX rfl fun t1 u1 _ m1 x1 => wp_cmpX rfl fun t2 f2 c2 _ m2 x2 => WP.block_nil ?_)
  have hc : isa.eval .ae t2 = some (!decide (4 * (e - j) < 4)) := by
    show t2.cf.map _ = _
    rw [c2, u1.other _ (by decide), I.cnt, toNat_ofNat_lt (by omega)]; rfl
  have g : ∀ r, r ≠ .edi → t2.gpr r = t.gpr r := fun r h => by rw [f2.gpr, u1.other r h]
  have K2 : Keeps [.eax, .esi, .edi, .ebp] s0 t2 := ⟨fun r hr => by
      rw [g r (by intro h; simp [h] at hr)]; exact I.keep.1 r hr,
    by rw [f2.rd, u1.rd, I.keep.2.1], by rw [f2.wr, u1.wr, I.keep.2.2]⟩
  have xm : t2.xmm = t.xmm := by rw [x2, x1]
  by_cases he : e = j
  · subst he
    refine WP.ite false (by rw [hc, decide_eq_true (by omega)]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ⟨?_, K2, by rw [f2.mem, u1.mem, I.mem], by rw [m2, m1, I.mcdt],
        by rw [xm, I.x4], by rw [xm, I.x5], by rw [xm, I.x6], by rw [xm, I.x7]⟩
    rw [xm]; exact I.sums
  refine WP.ite true (by rw [hc, decide_eq_false (by omega)]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
  have top := I.top (by omega)
  have hm : 0 < t2.mcdt := by rw [m2, m1, I.mcdt]; exact E.mcdt
  have hw2 : Ws t2 W L := I.ws.of_wr (by rw [f2.wr, u1.wr])
  have ex : t2.ea (at_ .esi 0) = off W (x + 4 * j) := by
    have p : PtrAt t2 W .esi (x + 4 * j) := by rw [PtrAt, g _ (by decide)]; exact I.esi
    rw [ea_ptr hw2 p (by omega), Nat.add_zero]
  have ey : t2.ea (at_ .edi 4) = off W (y + 4 * (k - j)) := by
    have p : (t2.gpr .edi + BitVec.ofNat 32 4).toNat = (W.toNat + (y + 4 * (k - j))) % 2 ^ 32 := by
      rw [f2.gpr, u1.gpr, BitVec.add_assoc]; exact top
    rw [ea_top hw2 p (by decide) (by omega) (by omega) (by decide), Nat.sub_self, Nat.sub_zero]
  obtain ⟨u, run, mu, rdu, wru, mcu, gu, u4, u5, u6, u7, a, b⟩ :=
    single_run t2 hm (by rw [ex]; exact ws_read hw2 (by omega)) (by rw [ey]; exact ws_read hw2 (by omega))
  refine WP.of_runBlock ⟨u, run, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ex, ey, f2.mem, u1.mem, I.mem] at a b
    have hl := highSum_le s0.mem W x y k i0 (j - i0)
    have hH := E.hH
    have q := prod_div_lt s0.mem W x y k j
    have s1 := single_sums (by rw [xm]; exact I.sums) (by omega) a b
    refine s1.of_eq ?_ ?_
    · rw [show e = j + 1 by omega, lowSum_step _ _ lo, ← Nat.add_assoc]; rfl
    · rw [show e = j + 1 by omega, highSum_step _ _ lo, ← Nat.add_assoc]; rfl
  · rw [gu r (by intro h; simp [h] at hr)]; exact K2.1 r hr
  · rw [rdu]; exact K2.2.1
  · rw [wru]; exact K2.2.2
  · rw [mu, f2.mem, u1.mem, I.mem]
  · rw [mcu, m2, m1, I.mcdt]
  · rw [u4, xm, I.x4]
  · rw [u5, xm, I.x5]
  · rw [u6, xm, I.x6]
  · rw [u7, xm, I.x7]

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q := by
  rw [WP.seq_iff, WP.seq_iff] at h
  rw [WP.seq_iff]
  exact WP.mono h fun _ h => WP.seq_iff.mpr h

/-- `dot`: the products `X_i Y_(k-i)`, `i0 ≤ i < e`, added to the sums, for
`esi = W + x`, `edi = W + y`, `ecx = 4 k`, `edx = 4 i0` and `ebx = 4 e`. -/
theorem dot_ok {s0 : State} {W : Addr} {L x y k i0 e S H : Nat} (E : DotEnv s0 L x y k i0 e H) (hw : Ws s0 W L)
    (hie : i0 ≤ e) (hx : PtrAt s0 W .esi x) (hy : PtrAt s0 W .edi y) (hcx : s0.gpr .ecx = BitVec.ofNat 32 (4 * k))
    (hdx : s0.gpr .edx = BitVec.ofNat 32 (4 * i0)) (hbx : s0.gpr .ebx = BitVec.ofNat 32 (4 * e))
    (hs : Sums (s0.xmm .xmm0) (s0.xmm .xmm1) S H) :
    WP isa dot s0 (DotPost s0 W x y k i0 e S H) := by
  have hk := E.hk
  have ek := E.ek
  have hn := hw.nowrap
  simp only [dot, seqs]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_subX rfl fun t2 u2 c2 m2 x2 => WP.block_nil ?_)
  have edx1 : t1.gpr .edx = BitVec.ofNat 32 (4 * i0) := by rw [u1.other _ (by decide), hdx]
  have ebp2 : t2.gpr .ebp = BitVec.ofNat 32 (4 * (e - i0)) := by
    rw [u2.gpr, u1.gpr, edx1, hbx, show 4 * (e - i0) = 4 * e - 4 * i0 by omega]
    exact sub_ofNat (by omega)
  refine WP.seq (WP.ite false (by
      show t2.cf = _
      rw [c2, edx1, u1.gpr, hbx, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), decide_eq_false (by omega)])
    (fun h => absurd h (by decide)) fun _ => WP.block_nil ?_)
  refine WP.seq (wp_addX rfl fun t3 u3 _ m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 => wp_subX rfl fun t5 u5 _ m5 x5 =>
    wp_subX rfl fun t6 u6 _ m6 x6 => wp_cmpX rfl fun t7 f7 c7 _ m7 x7 => WP.block_nil ?_)
  have g : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t7.gpr r = s0.gpr r := fun r h1 h2 h3 => by
    rw [f7.gpr, u6.other r h2, u5.other r h2, u4.other r h2, u3.other r h1, u2.other r h3, u1.other r h3]
  have edx2 : t2.gpr .edx = s0.gpr .edx := by rw [u2.other .edx (by decide), u1.other .edx (by decide)]
  have esi2 : t2.gpr .esi = s0.gpr .esi := by rw [u2.other .esi (by decide), u1.other .esi (by decide)]
  have edi2 : t2.gpr .edi = s0.gpr .edi := by rw [u2.other .edi (by decide), u1.other .edi (by decide)]
  have ecx2 : t2.gpr .ecx = s0.gpr .ecx := by rw [u2.other .ecx (by decide), u1.other .ecx (by decide)]
  have esi7 : t7.gpr .esi = s0.gpr .esi + BitVec.ofNat 32 (4 * i0) := by
    rw [f7.gpr, u6.other .esi (by decide), u5.other .esi (by decide), u4.other .esi (by decide), u3.gpr, edx2,
      esi2, hdx]
  have edi7 : t7.gpr .edi = s0.gpr .edi + BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 (4 * i0) - 12 := by
    rw [f7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.other .edi (by decide), u3.other .ecx (by decide),
      u4.other .edx (by decide), u3.other .edx (by decide), edx2, edi2, ecx2, hcx, hdx]
  have ebp7 : t7.gpr .ebp = BitVec.ofNat 32 (4 * (e - i0)) := by
    rw [f7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), ebp2]
  have xm : t7.xmm = s0.xmm := by rw [x7, x6, x5, x4, x3, x2, x1]
  have I7 : DotI s0 W L x y k i0 e S H i0 t7 := by
    refine ⟨Nat.le_refl _, hie, hw.of_wr (by rw [f7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]), ?_, fun h => ?_,
      ebp7, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, esi7, ptr_add hx, toNat_ofNat_lt (by omega)]
    · have := (s0.gpr .edi).isLt
      rw [edi7]
      simp only [BitVec.toNat_add, BitVec.toNat_sub, toNat_ofNat_lt (show 4 * k < 2 ^ 32 by omega),
        toNat_ofNat_lt (show 4 * i0 < 2 ^ 32 by omega), show (12 : BitVec 32).toNat = 12 from rfl, hy]
      omega
    · rw [xm, Nat.sub_self]; exact hs
    · rw [g r (by intro h; simp [h] at hr) (by intro h; simp [h] at hr) (by intro h; simp [h] at hr)]
    · rw [f7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [f7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [f7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    · rw [m7, m6, m5, m4, m3, m2, m1]
    · rw [xm]
    · rw [xm]
    · rw [xm]
    · rw [xm]
  have hc7 : t7.cf = some (decide (4 * (e - i0) < 16)) := by
    rw [c7, u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), ebp2,
      toNat_ofNat_lt (by omega)]; rfl
  exact WP.seq (WP.mono (quads_ok E I7 hc7) fun u h =>
    wp_seq_assoc (WP.seq (WP.mono (twins_ok E h) fun _ h' => last_ok E h')))

end VG.Proof.Mont.X86.Sse2
