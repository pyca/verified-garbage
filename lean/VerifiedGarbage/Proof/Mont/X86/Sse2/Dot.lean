module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Pair
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # The products of a column: `dot`

`dot` adds `Σ X_j Y_j` over `j < n` to the sums (`Sums`), for numbers `X`
and `Y` at offsets `x` and `y` of the working space (`dsum`): four products
at a time while a fifth word follows (`quadBody`), then four (`quadLast`),
two (`pair`) and one (`single`), counted down by `ebp`, the bytes left.
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

/-- The product of the words `j` of the numbers at offsets `x` and `y`. -/
def dprod (m : Mem) (W : Addr) (x y j : Nat) : Nat := w32 m W (x + 4 * j) * w32 m W (y + 4 * j)

/-- The products' sum and their high words' sum, over `j < n`. -/
def dsum (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (dprod m W x y) 0 n
def dhigh (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (fun j => dprod m W x y j / 2 ^ 32) 0 n

theorem dprod_lt (m : Mem) (W : Addr) (x y j : Nat) : dprod m W x y j < 2 ^ 64 := by
  have := word_mul_lt (m.readW (off W (x + 4 * j)) 32) (m.readW (off W (y + 4 * j)) 32)
  simpa [dprod, w32] using this

theorem dprod_div_lt (m : Mem) (W : Addr) (x y j : Nat) : dprod m W x y j / 2 ^ 32 < 2 ^ 32 :=
  (Nat.div_lt_iff_lt_mul (by decide)).2 (by have := dprod_lt m W x y j; omega)

theorem dhigh_le (m : Mem) (W : Addr) (x y n : Nat) : dhigh m W x y n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => simp [dhigh, rsum]
  | succ n ih =>
    have := dprod_div_lt m W x y n
    simp only [dhigh, rsum, Nat.zero_add] at ih ⊢
    rw [Nat.succ_mul]; omega

theorem dsum_succ (m : Mem) (W : Addr) (x y n : Nat) :
    dsum m W x y (n + 1) = dsum m W x y n + dprod m W x y n := by
  simp only [dsum, rsum, Nat.zero_add]

theorem dhigh_succ (m : Mem) (W : Addr) (x y n : Nat) :
    dhigh m W x y (n + 1) = dhigh m W x y n + dprod m W x y n / 2 ^ 32 := by
  simp only [dhigh, rsum, Nat.zero_add]

/-- The address `d` bytes past `off W a`. -/
theorem off_plus (W : Addr) (a d : Nat) : off W a + BitVec.ofNat 64 d = off W (a + d) := by
  rw [off, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem off_4 (W : Addr) (a : Nat) : off W a + 4 = off W (a + 4) := off_plus W a 4
theorem off_8 (W : Addr) (a : Nat) : off W a + 8 = off W (a + 8) := off_plus W a 8
theorem off_12 (W : Addr) (a : Nat) : off W a + 12 = off W (a + 12) := off_plus W a 12

theorem pw_d0 (m : Mem) (W : Addr) (x y j : Nat) :
    pw m (off W (x + 4 * j)) (off W (y + 4 * j)) = dprod m W x y j := rfl

theorem pw_d (m : Mem) (W : Addr) (x y j d k : Nat) (hk : 4 * k = 4 * j + d) :
    pw m (off W (x + 4 * j + d)) (off W (y + 4 * j + d)) = dprod m W x y k := by
  simp only [pw, dprod, w32]
  rw [show x + 4 * j + d = x + 4 * k by omega, show y + 4 * j + d = y + 4 * k by omega]

theorem pw_dd (m : Mem) (W : Addr) (x y j d e k : Nat) (hk : 4 * k = 4 * j + d + e) :
    pw m (off W (x + 4 * j + d + e)) (off W (y + 4 * j + d + e)) = dprod m W x y k := by
  simp only [pw, dprod, w32]
  rw [show x + 4 * j + d + e = x + 4 * k by omega, show y + 4 * j + d + e = y + 4 * k by omega]

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

/-! ## The loop's invariant -/

/-- After the products `j' < j` (from the state `s0` before them): the
pointers, the count `4 (n - j)`, the sums, and what stays. -/
structure DotI (s0 : State) (W : Addr) (L x y n S H j : Nat) (t : State) : Prop where
  hi : j ≤ n
  ws : Ws t W L
  esi : PtrAt t W .esi (x + 4 * j)
  edi : PtrAt t W .edi (y + 4 * j)
  cnt : t.gpr .ebp = BitVec.ofNat 32 (4 * (n - j))
  sums : Sums (t.xmm .xmm0) (t.xmm .xmm1) (S + dsum s0.mem W x y j) (H + dhigh s0.mem W x y j)
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 t
  mem : t.mem = s0.mem
  mcdt : t.mcdt = s0.mcdt
  x6 : t.xmm .xmm6 = s0.xmm .xmm6
  x7 : t.xmm .xmm7 = s0.xmm .xmm7

/-- What the products need: both numbers' `n` words within the working space
(if there are any),
room for the high sums, `pmuludq` allowed, and counts below `2³²`. -/
structure DotEnv (s0 : State) (L x y n H : Nat) : Prop where
  xr : n = 0 ∨ x + 4 * n ≤ L
  yr : n = 0 ∨ y + 4 * n ≤ L
  hH : H + (n + 4) * 2 ^ 32 < 2 ^ 64
  hn : 4 * n < 2 ^ 32
  mcdt : 0 < s0.mcdt

theorem Sums.of_eq {x0 x1 : BitVec 128} {S H S' H' : Nat} (h : Sums x0 x1 S H) (hs : S = S') (hh : H = H') :
    Sums x0 x1 S' H' := hs ▸ hh ▸ h

theorem ea_of_gpr {s t : State} (h : t.gpr = s.gpr) (m : MemOp) : t.ea m = s.ea m := by
  simp only [State.ea, h]

/-- The pointers' advance and the count's, then a comparison of the count. -/
theorem wp_advCmp {s : State} {d c : BitVec 32} {Q : State → Prop}
    (k : ∀ t, t.gpr .esi = s.gpr .esi + d → t.gpr .edi = s.gpr .edi + d → t.gpr .ebp = s.gpr .ebp - d →
      (∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t.gpr r = s.gpr r) →
      t.cf = some (decide ((s.gpr .ebp - d).toNat < c.toNat)) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      t.mcdt = s.mcdt → t.xmm = s.xmm → Q t) :
    WP isa (.block [.alu .add .esi (.imm d), .alu .add .edi (.imm d), .alu .sub .ebp (.imm d),
      .alu .cmp .ebp (.imm c)]) s Q := by
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine k _ ?_ ?_ ?_ (fun r h1 h2 h3 => ?_) ?_ rfl rfl rfl rfl rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ↓reduceIte]
  · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ↓reduceIte]; rfl

/-- The pointers' advance and the count's. -/
theorem wp_adv {s : State} {d : BitVec 32} {Q : State → Prop}
    (k : ∀ t, t.gpr .esi = s.gpr .esi + d → t.gpr .edi = s.gpr .edi + d → t.gpr .ebp = s.gpr .ebp - d →
      (∀ r, r ≠ .esi → r ≠ .edi → r ≠ .ebp → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.mcdt = s.mcdt → t.xmm = s.xmm → Q t) :
    WP isa (.block [.alu .add .esi (.imm d), .alu .add .edi (.imm d), .alu .sub .ebp (.imm d)]) s Q := by
  refine WP.of_runBlock ?_
  simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine k _ ?_ ?_ ?_ (fun r h1 h2 h3 => ?_) rfl rfl rfl rfl rfl
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [gpr_arithFlags, gpr_setReg, h1, h2, h3, ↓reduceIte]

theorem dsum_add (m : Mem) (W : Addr) (x y j i : Nat) :
    dsum m W x y (j + i) = dsum m W x y j + rsum (dprod m W x y) j i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, dsum_succ, ih]; simp only [rsum]; omega

theorem dhigh_add (m : Mem) (W : Addr) (x y j i : Nat) :
    dhigh m W x y (j + i) = dhigh m W x y j + rsum (fun k => dprod m W x y k / 2 ^ 32) j i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← Nat.add_assoc, dhigh_succ, ih]; simp only [rsum]; omega

/-- The invariant after `i` more products, from the sums they add. -/
theorem DotI.step {s0 t u : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t) (i : Nat)
    (hi : j + i ≤ n) (ws : Ws u W L)
    (esi : (u.gpr .esi).toNat = (t.gpr .esi + BitVec.ofNat 32 (4 * i)).toNat)
    (edi : (u.gpr .edi).toNat = (t.gpr .edi + BitVec.ofNat 32 (4 * i)).toNat)
    (cnt : u.gpr .ebp = t.gpr .ebp - BitVec.ofNat 32 (4 * i)) (h4 : 4 * n < 2 ^ 32)
    (sums : Sums (u.xmm .xmm0) (u.xmm .xmm1) (S + dsum s0.mem W x y j + rsum (dprod s0.mem W x y) j i)
      (H + dhigh s0.mem W x y j + rsum (fun k => dprod s0.mem W x y k / 2 ^ 32) j i))
    (keep : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .edi → r ≠ .ebp → u.gpr r = t.gpr r) (rd : u.rd = t.rd)
    (wr : u.wr = t.wr) (mem : u.mem = t.mem) (mcdt : u.mcdt = t.mcdt) (x6 : u.xmm .xmm6 = t.xmm .xmm6)
    (x7 : u.xmm .xmm7 = t.xmm .xmm7) : DotI s0 W L x y n S H (j + i) u := by
  have hn := I.ws.nowrap
  refine ⟨hi, ws, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, by rw [rd, I.keep.2.1], by rw [wr, I.keep.2.2]⟩,
    by rw [mem, I.mem], by rw [mcdt, I.mcdt], by rw [x6, I.x6], by rw [x7, I.x7]⟩
  · rw [PtrAt, esi, ptr_add I.esi, toNat_ofNat_lt (by omega)]; omega
  · rw [PtrAt, edi, ptr_add I.edi, toNat_ofNat_lt (by omega)]; omega
  · rw [cnt, I.cnt, sub_ofNat (by omega)]; congr 1; omega
  · refine sums.of_eq ?_ ?_
    · rw [dsum_add]; omega
    · rw [dhigh_add]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2]; exact I.keep.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])

theorem rsum_four (f : Nat → Nat) (j : Nat) : rsum f j 4 = f j + f (j + 1) + f (j + 2) + f (j + 3) := by
  simp only [rsum, Nat.add_zero, Nat.zero_add]

theorem rsum_two (f : Nat → Nat) (j : Nat) : rsum f j 2 = f j + f (j + 1) := by
  simp only [rsum, Nat.add_zero, Nat.zero_add]

theorem rsum_one (f : Nat → Nat) (j : Nat) : rsum f j 1 = f j := by
  simp only [rsum, Nat.add_zero, Nat.zero_add]

/-- The addresses of a number's word `j`, `d` bytes on. -/
theorem ea_w {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {r : Reg} {x j : Nat} (hp : PtrAt t W r (x + 4 * j))
    {d : Nat} (hd : x + 4 * j + d < L) : t.ea (at_ r d) = off W (x + 4 * j + d) := ea_ptr hw hp hd

/-- Four products, the loop's body, while a fifth word follows. -/
theorem quad_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 5 ≤ n) :
    WP isa (.block quadBody) t fun u =>
      DotI s0 W L x y n S H (j + 4) u ∧ u.cf = some (decide (4 * (n - (j + 4)) < 20)) := by
  have xr := E.xr.resolve_left (by omega)
  have yr := E.yr.resolve_left (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega)
  have ex4 := ea_w I.ws I.esi (d := 4) (by omega)
  have ey4 := ea_w I.ws I.edi (d := 4) (by omega)
  rw [quadBody]
  obtain ⟨t1, run1, o1, a1, b1⟩ := quadMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey0]; exact ws_read I.ws (by omega))
    (by rw [ex4]; exact ws_read I.ws (by omega)) (by rw [ey4]; exact ws_read I.ws (by omega))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_advCmp fun u esi edi ebp oth cf mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := quad_sums I.sums (by omega) a1 b1
  rw [ex0, ey0, ex4, ey4, Nat.add_zero, Nat.add_zero, off_8, off_8, off_8, off_8, I.mem, pw_d0,
    pw_d _ _ _ _ _ 8 (j + 2) (by omega), pw_d _ _ _ _ _ 4 (j + 1) (by omega),
    pw_dd _ _ _ _ _ 4 8 (j + 3) (by omega)] at s1
  have I' := I.step 4 (by omega) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_four, rsum_four]; refine s1.of_eq ?_ ?_ <;> omega)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])
  refine ⟨I', ?_⟩
  rw [cf, ← ebp, I'.cnt, toNat_ofNat_lt (by have := E.hn; omega)]; rfl

/-- The last four products. -/
theorem quadLast_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 4 ≤ n) :
    WP isa (.block quadLast) t (DotI s0 W L x y n S H (j + 4)) := by
  have xr := E.xr.resolve_left (by omega)
  have yr := E.yr.resolve_left (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega)
  rw [quadLast]
  obtain ⟨t1, run1, o1, a1, b1⟩ := quadLastMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey0]; exact ws_read I.ws (by omega))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_adv fun u esi edi ebp oth mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := quadLast_sums I.sums (by omega) a1 b1
  rw [ex0, ey0, Nat.add_zero, Nat.add_zero, off_8, off_8, off_4, off_4, off_12, off_12, I.mem, pw_d0,
    pw_d _ _ _ _ _ 8 (j + 2) (by omega), pw_d _ _ _ _ _ 4 (j + 1) (by omega),
    pw_d _ _ _ _ _ 12 (j + 3) (by omega)] at s1
  exact I.step 4 (by omega) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_four, rsum_four]; refine s1.of_eq ?_ ?_ <;> omega)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])

/-- Two products. -/
theorem twin_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 2 ≤ n) :
    WP isa (.block pair) t (DotI s0 W L x y n S H (j + 2)) := by
  have xr := E.xr.resolve_left (by omega)
  have yr := E.yr.resolve_left (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega)
  rw [pair]
  obtain ⟨t1, run1, o1, a1, b1⟩ := pairMul_run t hm
    (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey0]; exact ws_read I.ws (by omega))
  refine WP.block_append (WP.of_runBlock ⟨t1, run1, ?_⟩)
  refine wp_adv fun u esi edi ebp oth mem rd wr mcdt xmm => ?_
  have hl := dhigh_le s0.mem W x y j
  have hH := E.hH
  have s1 := pair_sums I.sums (by omega) a1 b1
  rw [ex0, ey0, Nat.add_zero, Nat.add_zero, off_4, off_4, I.mem, pw_d0,
    pw_d _ _ _ _ _ 4 (j + 1) (by omega)] at s1
  exact I.step 2 (by omega) (I.ws.of_wr (by rw [wr, o1.wr])) (by rw [esi, o1.gpr]; rfl) (by rw [edi, o1.gpr]; rfl)
    (by rw [ebp, o1.gpr]; rfl) E.hn (by rw [xmm, rsum_two, rsum_two]; refine s1.of_eq ?_ ?_ <;> omega)
    (fun r h0 h1 h2 h3 => by rw [oth r h1 h2 h3, o1.gpr]) (by rw [rd, o1.rd]) (by rw [wr, o1.wr])
    (by rw [mem, o1.mem]) (by rw [mcdt, o1.mcdt]) (by rw [xmm, o1.x6]) (by rw [xmm, o1.x7])

/-- What `dot` leaves: the sums of the products `j < n`, and what stays. -/
structure DotPost (s0 : State) (W : Addr) (x y n S H : Nat) (u : State) : Prop where
  sums : Sums (u.xmm .xmm0) (u.xmm .xmm1) (S + dsum s0.mem W x y n) (H + dhigh s0.mem W x y n)
  keep : Keeps [.eax, .esi, .edi, .ebp] s0 u
  mem : u.mem = s0.mem
  mcdt : u.mcdt = s0.mcdt
  x6 : u.xmm .xmm6 = s0.xmm .xmm6
  x7 : u.xmm .xmm7 = s0.xmm .xmm7

/-- The last product. -/
theorem one_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hj : j + 1 = n) :
    WP isa (.block single) t (DotPost s0 W x y n S H) := by
  have xr := E.xr.resolve_left (by omega)
  have yr := E.yr.resolve_left (by omega)
  have hm : 0 < t.mcdt := I.mcdt ▸ E.mcdt
  have ex0 := ea_w I.ws I.esi (d := 0) (by omega)
  have ey0 := ea_w I.ws I.edi (d := 0) (by omega)
  obtain ⟨u, run, mu, rdu, wru, mcu, gu, u6, u7, a, b⟩ :=
    single_run t hm (by rw [ex0]; exact ws_read I.ws (by omega)) (by rw [ey0]; exact ws_read I.ws (by omega))
  refine WP.of_runBlock ⟨u, run, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hl := dhigh_le s0.mem W x y j
    have hH := E.hH
    have s1 := single_sums I.sums (by omega) a b
    rw [ex0, ey0, I.mem] at s1
    refine s1.of_eq ?_ ?_
    · rw [← hj, dsum_succ, ← Nat.add_assoc]; simp only [dprod, w32, Nat.add_zero]
    · rw [← hj, dhigh_succ, ← Nat.add_assoc]; simp only [dprod, w32, Nat.add_zero]
  · rw [gu r (by intro h; simp [h] at hr)]; exact I.keep.1 r hr
  · rw [rdu]; exact I.keep.2.1
  · rw [wru]; exact I.keep.2.2
  · rw [mu, I.mem]
  · rw [mcu, I.mcdt]
  · rw [u6, I.x6]
  · rw [u7, I.x7]

theorem DotI.done {s0 t : State} {W : Addr} {L x y n S H : Nat} (I : DotI s0 W L x y n S H n t) :
    DotPost s0 W x y n S H t := ⟨I.sums, I.keep, I.mem, I.mcdt, I.x6, I.x7⟩

/-- The invariant through an instruction that changes only flags. -/
theorem DotI.of_same {s0 t t' : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hr : t'.rd = t.rd) (hw : t'.wr = t.wr) (hc : t'.mcdt = t.mcdt)
    (hx : t'.xmm = t.xmm) : DotI s0 W L x y n S H j t' := by
  refine ⟨I.hi, I.ws.of_wr hw, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, hg]; exact I.esi
  · rw [PtrAt, hg]; exact I.edi
  · rw [hg]; exact I.cnt
  · rw [hx]; exact I.sums
  · rw [hg]; exact I.keep.1 r hr
  · rw [hr]; exact I.keep.2.1
  · rw [hw]; exact I.keep.2.2
  · rw [hm]; exact I.mem
  · rw [hc]; exact I.mcdt
  · rw [hx]; exact I.x6
  · rw [hx]; exact I.x7

/-- `cmp ebp, c` on the invariant: CF is `4 (n - j) < c`. -/
theorem wp_cmpCnt {s0 t : State} {W : Addr} {L x y n S H j : Nat} (I : DotI s0 W L x y n S H j t) (hn : 4 * n < 2 ^ 32)
    {c : Nat} (hc : c < 2 ^ 32) {rest : List Instr} {Q : State → Prop}
    (k : ∀ u, DotI s0 W L x y n S H j u → isa.eval .ae u = some (!decide (4 * (n - j) < c)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (.alu .cmp .ebp (.imm (BitVec.ofNat 32 c)) :: rest)) t Q :=
  wp_cmpX rfl fun u f c1 _ m1 x1 => k u (I.of_same f.gpr f.mem f.rd f.wr m1 x1) (by
    show u.cf.map _ = _
    rw [c1, I.cnt, toNat_ofNat_lt (by omega), toNat_ofNat_lt hc]; rfl)

/-- Four products at a time while at least five words remain. -/
theorem quads_ok {s0 t : State} {W : Addr} {L x y n S H j : Nat} (E : DotEnv s0 L x y n H)
    (I : DotI s0 W L x y n S H j t) (hc : isa.eval .ae t = some (!decide (4 * (n - j) < 20))) :
    WP isa (.ite .ae (.loop (.block quadBody) .ae) (.block [])) t
      fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 5 := by
  have hi := I.hi
  by_cases h5 : n < j + 5
  · exact WP.ite false (by rw [hc, decide_eq_true (by omega)]; rfl)
      (fun h => absurd h (by decide)) fun _ => WP.block_nil ⟨j, I, h5⟩
  refine WP.ite true (by rw [hc, decide_eq_false (by omega)]; rfl) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine WP.loop (M := isa) (fun m u => ∃ j, m = n - j ∧ j + 5 ≤ n ∧ DotI s0 W L x y n S H j u) ?_ (n - j) t
    ⟨j, rfl, by omega, I⟩
  rintro m u ⟨j, rfl, hj, J⟩
  refine WP.mono (quad_ok E J hj) fun v ⟨J', cv⟩ => ?_
  have hv : isa.eval .ae v = some (!decide (4 * (n - (j + 4)) < 20)) := by
    show v.cf.map _ = _; rw [cv]; rfl
  by_cases h : n < j + 4 + 5
  · exact .inl ⟨by rw [hv, decide_eq_true (by omega)]; rfl, j + 4, J', h⟩
  · exact .inr ⟨by rw [hv, decide_eq_false (by omega)]; rfl, n - (j + 4), by omega, j + 4, rfl, by omega, J'⟩

/-- `dot`: the products `X_j Y_j`, `j < n`, added to the sums, for
`esi = W + x`, `edi = W + y` and `ebp = 4 n`. -/
theorem dot_ok {s0 : State} {W : Addr} {L x y n S H : Nat} (E : DotEnv s0 L x y n H) (hw : Ws s0 W L)
    (hx : PtrAt s0 W .esi x) (hy : PtrAt s0 W .edi y) (hbp : s0.gpr .ebp = BitVec.ofNat 32 (4 * n))
    (hs : Sums (s0.xmm .xmm0) (s0.xmm .xmm1) S H) :
    WP isa dot s0 (DotPost s0 W x y n S H) := by
  have hn := E.hn
  have I0 : DotI s0 W L x y n S H 0 s0 := ⟨Nat.zero_le _, hw, by simpa using hx, by simpa using hy,
    by simpa using hbp, by simpa [dsum, dhigh, rsum] using hs, Keeps.refl _ _, rfl, rfl, rfl, rfl⟩
  simp only [dot, seqs]
  refine WP.seq (wp_cmpCnt I0 hn (c := 20) (by decide) fun t1 I1 c1 => WP.block_nil ?_)
  refine WP.seq (WP.mono (quads_ok E I1 c1) fun t2 ⟨j, I2, h2⟩ => ?_)
  refine WP.seq (wp_cmpCnt I2 hn (c := 16) (by decide) fun t3 I3 c3 => WP.block_nil ?_)
  refine WP.seq (WP.mono (Q := fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 4) (WP.iteCold_iff.mpr ?_)
    fun t4 ⟨j, I4, h4⟩ => ?_)
  · by_cases h4 : n < j + 4
    · exact WP.ite false (by rw [c3, decide_eq_true (by omega)]; rfl) (fun h => absurd h (by decide))
        fun _ => WP.block_nil ⟨j, I3, h4⟩
    · exact WP.ite true (by rw [c3, decide_eq_false (by omega)]; rfl)
        (fun _ => WP.mono (quadLast_ok E I3 (by omega)) fun u J => ⟨j + 4, J, by have := I3.hi; omega⟩)
        (fun h => absurd h (by decide))
  refine WP.seq (wp_cmpCnt I4 hn (c := 8) (by decide) fun t5 I5 c5 => WP.block_nil ?_)
  refine WP.seq (WP.mono (Q := fun u => ∃ j, DotI s0 W L x y n S H j u ∧ n < j + 2) ?_ fun t6 ⟨j, I6, h6⟩ => ?_)
  · by_cases h2 : n < j + 2
    · exact WP.ite false (by rw [c5, decide_eq_true (by omega)]; rfl) (fun h => absurd h (by decide))
        fun _ => WP.block_nil ⟨j, I5, h2⟩
    · exact WP.ite true (by rw [c5, decide_eq_false (by omega)]; rfl)
        (fun _ => WP.mono (twin_ok E I5 (by omega)) fun u J => ⟨j + 2, J, by have := I5.hi; omega⟩)
        (fun h => absurd h (by decide))
  refine WP.seq (wp_cmpCnt I6 hn (c := 4) (by decide) fun t7 I7 c7 => WP.block_nil ?_)
  have := I7.hi
  by_cases h1 : n = j
  · subst h1
    exact WP.ite false (by rw [c7, decide_eq_true (by omega)]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil I7.done
  · exact WP.ite true (by rw [c7, decide_eq_false (by omega)]; rfl) (fun _ => one_ok E I7 (by omega))
      (fun h => absurd h (by decide))

end VG.Proof.Mont.X86.Sse2
