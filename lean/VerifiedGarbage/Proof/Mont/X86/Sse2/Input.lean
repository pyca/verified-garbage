module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Products
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.X86.ArgFar

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
/-! # A column's sums

`Acc`: the lanes hold a column's sum `P` modulo `2⁶⁴` and the sum `H` of
its products' high words, with `P - 2³² H` the sum of at most `n` low words.
`dot` adds its products (`Acc.dot`); a square's sum is doubled
(`Acc.double`) and gets the diagonal's product (`Acc.single`).

`input sq hi` adds the column's products of `A` and `B` (`input_ok`), and
`reduce hi` those of the quotient digits and `M` (`reduce_ok`), from `A'`
and the digits stored in reverse (`RevA`, `RevQ`) and, while `k < N`, the two
latest digits in `xmm6` (`Window`).
-/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Sse2/Index.lean`, which only this module imported.
section

/-! # The parameters

The kernel's seven parameters are words on the stack, `d` bytes above `esp`
(`Params`), past the working space, so changes within it keep them; `Sk`
records what a step keeps.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

/-- The parameters `V i` at `[esp + d + 4 i]`, past the working space. -/
structure Params (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (d : Nat) : Prop where
  read : ∀ i < 7, readSrc s (.mem (prm d i)) = some (V i)
  far : ∀ i < 7, ArgFar s W L (prm d i)

/-- Changes within the working space, with `esp` and the permissions as they
were, keep the parameters. -/
theorem Params.keep {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Params t W L V d :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

/-- What scalar code leaves: the registers but `rs`, the memory, the MCDT
depth and the XMM registers. -/
structure Sk (rs : List Reg) (s t : State) : Prop where
  keep : Keeps rs s t
  mem : t.mem = s.mem
  mcdt : t.mcdt = s.mcdt
  xmm : t.xmm = s.xmm

theorem Sk.refl (rs : List Reg) (s : State) : Sk rs s s := ⟨Keeps.refl _ _, rfl, rfl, rfl⟩

theorem Sk.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Sk rs' s₁ s₂) (h₂ : Sk rs s₂ s₃)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s₁ s₃ :=
  ⟨h₁.keep.widen h₂.keep hs, h₂.mem.trans h₁.mem, h₂.mcdt.trans h₁.mcdt, h₂.xmm.trans h₁.xmm⟩

theorem Sk.mono {rs : List Reg} {s t : State} (h : Sk rs s t) (rs' : List Reg)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s t :=
  ⟨h.keep.mono hs, h.mem, h.mcdt, h.xmm⟩

theorem Sk.of_upd (rs : List Reg) {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (hd : d ∈ rs := by decide) : Sk rs s t :=
  ⟨u.keeps.mono fun r hr => by simp only [List.mem_singleton] at hr; exact hr ▸ hd, u.mem, hm, hx⟩

theorem Sk.of_fupd {s t : State} (u : Fupd s t) (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (rs : List Reg) :
    Sk rs s t := ⟨u.keeps rs, u.mem, hm, hx⟩

theorem Params.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep (by rw [K.mem]; exact Outs.refl _ _ _) (K.keep.1 _ hsp) K.keep.2.1 K.keep.2.2

theorem Ws.of_sk {s t : State} {W : Addr} {L : Nat} (h : Ws s W L) {rs : List Reg} (K : Sk rs s t) : Ws t W L :=
  h.of_keeps K.keep

/-- A parameter read in a state `Sk` from one where it is known. -/
theorem Params.readSk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) {i : Nat} (hi : i < 7) (hsp : .esp ∉ rs := by decide) :
    readSrc t (.mem (prm d i)) = some (V i) := (h.of_sk K hsp).read i hi

theorem ofNat_of_toNat {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ v.isLt)]

end VG.Proof.Mont.X86.Sse2
end

end

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
    {x y c : Nat} (D : Sums y0 y1 (P + dsum m W x y c) (H + dhigh m W x y c)) :
    Acc y0 y1 (P + dsum m W x y c) (H + dhigh m W x y c) (n + c) := by
  obtain ⟨e, l⟩ := dsum_split m W x y c
  have := A.le
  have := A.low
  refine ⟨D, by omega_arith, ?_⟩
  rw [Nat.add_mul]; omega_arith

theorem Acc.of_eq' {x0 x1 : BitVec 128} {P P' H n : Nat} (A : Acc x0 x1 P H n) (h : P = P') :
    Acc x0 x1 P' H n := h ▸ A

theorem toNat_add_self (q : BitVec 64) (h : 2 * q.toNat < 2 ^ 64) : (q + q).toNat = 2 * q.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

theorem Acc.double {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) (hH : 2 * H < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 x0) (XBinOp.eval .paddq x1 x1) (2 * P) (2 * H) (2 * n) := by
  have hh := A.sums.high
  have := A.le
  have := A.low
  refine ⟨⟨?_, ?_⟩, by omega_arith, ?_⟩
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide),
      show qword x0 0 + qword x0 0 + (qword x0 1 + qword x0 1) = (qword x0 0 + qword x0 1) +
        (qword x0 0 + qword x0 1) by ac_rfl, A.sums.low, ← BitVec.ofNat_add, Nat.two_mul]
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide), toNat_add_self _ (by omega_arith),
      toNat_add_self _ (by omega_arith)]
    omega_arith
  · rw [Nat.mul_assoc 2 n]; omega_arith

theorem Acc.single {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) {u v : BitVec 32}
    (hH : H + 2 ^ 32 < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 (singleP u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (singleP u v) 32))
      (P + u.toNat * v.toNat) (H + u.toNat * v.toNat / 2 ^ 32) (n + 1) := by
  have hs := A.sums.add (singleP_0 u v) (singleP_1 u v) (word_mul_lt _ _) (by decide) hH
  have hd := Nat.div_add_mod (u.toNat * v.toNat) (2 ^ 32)
  have hm := Nat.mod_lt (u.toNat * v.toNat) (show 0 < 2 ^ 32 by decide)
  have := A.le
  have := A.low
  refine ⟨by simpa using hs, by omega_arith, ?_⟩
  rw [Nat.succ_mul]; omega_arith

/-- Two products by `pmuludq`, of doublewords 0 and 2. -/
theorem Acc.mul {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) (u v : BitVec 128)
    (hH : H + 2 * 2 ^ 32 < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 (pmuludq u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (pmuludq u v) 32))
      (P + ((dword u 0).toNat * (dword v 0).toNat + (dword u 2).toNat * (dword v 2).toNat))
      (H + ((dword u 0).toNat * (dword v 0).toNat / 2 ^ 32 + (dword u 2).toNat * (dword v 2).toNat / 2 ^ 32))
      (n + 2) := by
  have q0 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword u 0).toNat * (dword v 0).toNat) (y := 2 ^ 32)
    (by decide) |>.2 (by have := word_mul_lt (dword u 0) (dword v 0); omega_arith)
  have hs := A.sums.addMul (u := u) (v := v) (by omega_arith)
  have d0 := Nat.div_add_mod ((dword u 0).toNat * (dword v 0).toNat) (2 ^ 32)
  have m0 := Nat.mod_lt ((dword u 0).toNat * (dword v 0).toNat) (show 0 < 2 ^ 32 by decide)
  have d2 := Nat.div_add_mod ((dword u 2).toNat * (dword v 2).toNat) (2 ^ 32)
  have m2 := Nat.mod_lt ((dword u 2).toNat * (dword v 2).toNat) (show 0 < 2 ^ 32 by decide)
  have := A.le
  have := A.low
  refine ⟨hs.of_eq (by omega_arith) (by omega_arith), by omega_arith, ?_⟩
  rw [Nat.add_mul]; omega_arith

/-! ## The SSE instructions of the input -/

theorem movdqa_eval (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-- `movd xmm2, eax; pmuludq xmm2, xmm2`, then the product into the sums. -/
theorem sq_run (s : State) (hm : 0 < s.mcdt) :
    ∃ t, runBlock isa (([.xop (.movd .xmm2 .eax), .pmuludq .xmm2 .xmm2] : List Instr) ++ acc .xmm2) s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (singleP (s.gpr .eax) (s.gpr .eax)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1)
        (XShiftOp.eval .psrlq (singleP (s.gpr .eax) (s.gpr .eax)) 32) := by
  simp only [acc, List.cons_append, List.nil_append, runBlock_cons, exec, runStep_some,
    XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left', mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq,
    runBlock_nil, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, singleP, and_self]

/-- `paddq xmm0, xmm0; paddq xmm1, xmm1`. -/
theorem double_run (s : State) :
    runBlock isa [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)] s =
      some ((s.setXmm .xmm0 (XBinOp.eval .paddq (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .paddq (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

/-- `movdqa xmm2, xmm6; pmuludq xmm2, xmm7`, then the products into the sums. -/
theorem window_run (s : State) (hm : 0 < s.mcdt) :
    ∃ t, runBlock isa (([.xop (.bin .movdqa .xmm2 .xmm6), .pmuludq .xmm2 .xmm7] : List Instr) ++ acc .xmm2) s =
        some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (pmuludq (s.xmm .xmm6) (s.xmm .xmm7)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1)
        (XShiftOp.eval .psrlq (pmuludq (s.xmm .xmm6) (s.xmm .xmm7)) 32) := by
  simp only [acc, List.cons_append, List.nil_append, runBlock_cons, exec, runStep_some,
    XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left', mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq,
    runBlock_nil, gpr_setXmm, movdqa_eval, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

/-! ## The products of a column -/

/-- What every stage of a column has: the working space, the parameters
(`4 N` among them), `ecx = 4 k` and `pmuludq` allowed. -/
structure ColEnv (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N k : Nat) : Prop where
  ws : Ws s W L
  prm : Params s W L V 12
  n4 : (V pN4).toNat = 4 * N
  hk : k < 2 * N
  hN : N < 2 ^ 29
  ecx : s.gpr .ecx = BitVec.ofNat 32 (4 * k)
  mcdt : 0 < s.mcdt

theorem ColEnv.of_keeps {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Keeps rs s t) (hm : t.mem = s.mem) (hc : t.mcdt = s.mcdt)
    (hcx : .ecx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k :=
  ⟨C.ws.of_keeps K, C.prm.keep (by rw [hm]; exact Outs.refl _ _ _) (K.1 _ hsp) K.2.1 K.2.2, C.n4, C.hk, C.hN,
    by rw [K.1 _ hcx]; exact C.ecx, by rw [hc]; exact C.mcdt⟩

theorem ColEnv.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Sk rs s t)
    (hcx : .ecx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k := C.of_keeps K.keep K.mem K.mcdt hcx hsp

/-- `dot`, on the sums. -/
theorem dotAcc_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k x y n P H n0 : Nat}
    (C : ColEnv t W L V N k) (hx : PtrAt t W .esi x) (hy : PtrAt t W .edi y)
    (hbp : t.gpr .ebp = BitVec.ofNat 32 (4 * n)) (xr : n = 0 ∨ x + 4 * n ≤ L) (yr : n = 0 ∨ y + 4 * n ≤ L)
    (hn : n ≤ 2 * N) (hH : H + (n + 4) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n0) :
    WP isa dot t fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + dsum t.mem W x y n) (H + dhigh t.mem W x y n) (n0 + n) ∧
      Keeps [.eax, .esi, .edi, .ebp] t u ∧ u.mem = t.mem ∧ u.mcdt = t.mcdt ∧
      u.xmm .xmm6 = t.xmm .xmm6 ∧ u.xmm .xmm7 = t.xmm .xmm7 := by
  have hN := C.hN
  exact WP.mono (dot_ok ⟨xr, yr, hH, by omega_arith, C.mcdt⟩ C.ws hx hy hbp A.sums)
    fun u D => ⟨A.dot D.sums, D.keep, D.mem, D.mcdt, D.x6, D.x7⟩

/-- A pointer from a parameter. -/
theorem ptr_of_param {u : State} {W : Addr} {r : Reg} {v : BitVec 32} {x : Nat} (h : u.gpr r = v)
    (hv : v.toNat = (W.toNat + x) % 2 ^ 32) : PtrAt u W r x := by rw [PtrAt, h, hv]

/-- A pointer as a value. -/
theorem ptr_iff {u : State} {W : Addr} {r : Reg} {x : Nat} :
    PtrAt u W r x ↔ u.gpr r = BitVec.ofNat 32 (W.toNat + x) := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]
  · intro h; rw [PtrAt, h, BitVec.toNat_ofNat]

theorem pv_ofNat {v : BitVec 32} {W : Addr} {x : Nat} (h : v.toNat = (W.toNat + x) % 2 ^ 32) :
    v = BitVec.ofNat 32 (W.toNat + x) := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]

theorem ofNat_add3 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

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
    rw [Nat.mod_eq_of_lt (a := 4 * k) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  apply ofNat_of_toNat
  simp only [BitVec.toNat_add, hv]
  omega_arith

/-- The parameters' values: pointers into the working space and `4 N`. -/
structure PVals (V : Nat → BitVec 32) (W : Addr) (N S mo inv o a b : Nat) : Prop where
  a : (V pA).toNat = (W.toNat + a) % 2 ^ 32
  b : (V pB).toNat = (W.toNat + b) % 2 ^ 32
  mo : (V pM).toNat = (W.toNat + mo) % 2 ^ 32
  o : (V pO).toNat = (W.toNat + o) % 2 ^ 32
  s : (V pS).toNat = (W.toNat + S) % 2 ^ 32
  inv : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32
  n4 : (V pN4).toNat = 4 * N

/-- `A'`: `A` in reverse at `S + 24 + 4 N`. -/
def RevA (m : Mem) (W : Addr) (N S a : Nat) : Prop :=
  ∀ i < N, w32 m W (S + 24 + 4 * N + 4 * (N - 1 - i)) = digits m W a i

/-- `j` times `add r, eax`. -/
theorem addRep_ok {s : State} {r : Reg} (hr : r ≠ .eax) {X V4 : Nat} (hx : s.gpr r = BitVec.ofNat 32 X)
    (ha : s.gpr .eax = BitVec.ofNat 32 V4) (j : Nat) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = BitVec.ofNat 32 (X + j * V4) → t.gpr .eax = BitVec.ofNat 32 V4 → Sk [r] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (List.replicate j (.alu .add r (.reg .eax)) ++ rest)) s Q := by
  induction j generalizing s X with
  | zero => exact k s (by rw [hx, Nat.zero_mul, Nat.add_zero]) ha (Sk.refl _ _)
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append]
    refine wp_addX rfl fun t u _ m x => ih (X := X + V4) (by rw [u.gpr, hx, ha, ofNat_add3])
      (by rw [u.other _ (Ne.symm hr), ha]) fun t' e a K => k t' (by rw [e]; congr 1; rw [Nat.succ_mul]; omega_arith) a
        ((Sk.of_upd [r] u m x (by simp)).trans K (by simp))

/-- `ldW r d j`: `r = S + 24 + d + j (4 N)` and `eax = 4 N`. -/
theorem ldW_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S : Nat} (P : Params s W L V 12)
    (hS : (V pS).toNat = (W.toNat + S) % 2 ^ 32) (hN : (V pN4).toNat = 4 * N) {r : Reg} (hr : r ≠ .eax)
    (hsp : r ≠ .esp) (d j : Nat) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d) + j * (4 * N)) →
      t.gpr .eax = BitVec.ofNat 32 (4 * N) → Sk [r, .eax] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ldW r d j ++ rest)) s Q := by
  simp only [ldW, List.cons_append, List.append_assoc, offW]
  refine wp_movX (P.read pS (by decide)) fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 => ?_
  have K2 : Sk [r, .eax] s t2 := (Sk.of_upd [r, .eax] u1 m1 x1 (by simp)).trans (Sk.of_upd [r, .eax] u2 m2 x2 (by simp)) (by simp)
  have e2 : t2.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d)) := by
    rw [u2.gpr, u1.gpr, pv_ofNat hS]; show _ + BitVec.ofNat 32 (24 + d) = _; rw [ofNat_add3]; congr 1; omega_arith
  refine wp_movX (P.readSk K2 (i := pN4) (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨Ne.symm hsp, by decide⟩)) fun t3 u3 m3 x3 => ?_
  have K3 : Sk [r, .eax] s t3 := K2.trans (Sk.of_upd [r, .eax] u3 m3 x3 (by simp)) (by simp)
  have a3 : t3.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [u3.gpr]; exact ofNat_of_toNat hN
  have e3 : t3.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d)) := by rw [u3.other _ hr, e2]
  exact addRep_ok hr e3 a3 j fun t e a K => k t e a (K3.trans K (by simp))

/-- `dot` over a number stored in reverse (its word `N - 1 - i` at `xp` is
`f_i` for `i0 ≤ i < e`) and one at `y`: the column's `Σ f_i Y_(k-i)`, `i0 ≤ i < e`. -/
theorem dotRev_ok {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k xp y e i0 P H n0 : Nat}
    {f : Nat → Nat} (C : ColEnv t W L V N k) (K : Sk [.eax, .ebx, .esi, .edi, .ebp] s t)
    (hx : PtrAt t W .esi (xp + 4 * (N - e))) (hy : PtrAt t W .edi (y + 4 * (k + 1 - e)))
    (hbp : t.gpr .ebp = BitVec.ofNat 32 (4 * (e - i0))) (he : e ≤ N) (hek : e ≤ k + 1) (hi : i0 ≤ e)
    (hf : ∀ i, i0 ≤ i → i < e → w32 s.mem W (xp + 4 * (N - 1 - i)) = f i)
    (xr : e = i0 ∨ xp + 4 * N ≤ L) (yr : e = i0 ∨ y + 4 * (k + 1 - i0) ≤ L) (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n0) :
    WP isa dot t fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + csum f (digits s.mem W y) k i0 (e - i0))
        (H + dhigh s.mem W (xp + 4 * (N - e)) (y + 4 * (k + 1 - e)) (e - i0)) (n0 + (e - i0)) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 ∧ u.xmm .xmm7 = s.xmm .xmm7 ∧ u.gpr .ebx = t.gpr .ebx := by
  have hN := C.hN
  refine WP.mono (dotAcc_ok C hx hy hbp (by omega_arith) (by omega_arith) (by omega_arith)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega_arith)) _) hH) A)
    fun u ⟨Au, Ku, mu, cu, u6, u7⟩ => ?_
  rw [K.mem, dsum_rev s.mem W xp y f he hek hi hf] at Au
  exact ⟨Au, (K.keep.mono (by decide)).trans (Ku.mono (by decide)), by rw [mu, K.mem], by rw [cu, K.mcdt],
    by rw [u6, K.xmm], by rw [u7, K.xmm], Ku.1 _ (by decide)⟩

/-- What the products of `A` and `B` leave: their coefficient in the sums,
with at most `N + 1` low words, and what stays. -/
structure InPost (s : State) (N P : Nat) (u : State) : Prop where
  acc : ∃ H n, Acc (u.xmm .xmm0) (u.xmm .xmm1) P H n ∧ n ≤ N + 1 ∧ H ≤ (N + 1) * 2 ^ 32
  keep : Keeps [.eax, .ebx, .esi, .edi, .ebp] s u
  mem : u.mem = s.mem
  mcdt : u.mcdt = s.mcdt
  x6 : u.xmm .xmm6 = s.xmm .xmm6
  x7 : u.xmm .xmm7 = s.xmm .xmm7

theorem dhigh_le' (m : Mem) (W : Addr) (x y n : Nat) : dhigh m W x y n ≤ n * 2 ^ 32 :=
  Nat.le_trans (dhigh_le m W x y n) (Nat.mul_le_mul_left _ (by omega_arith))

/-- The products of `A` and `B` while `k < N`. -/
theorem mulLo_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : k < N) (hb : b + 4 * N ≤ L)
    (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input false false) s
      (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  have hN := C.hN
  have hn := C.ws.nowrap
  simp only [input, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 => ?_)
  have K2 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t2 := (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u2 m2 x2)
  have b2 : t2.gpr .ebp = BitVec.ofNat 32 (4 * (k + 1)) := by
    rw [u2.gpr, u1.gpr, C.ecx]; show _ + BitVec.ofNat 32 4 = _; rw [ofNat_add3]; congr 1
  refine ldW_ok (C.prm.of_sk K2) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 2 fun t3 e3 a3 K3 => ?_
  refine wp_subX rfl fun t4 u4 _ m4 x4 => wp_movX ((C.prm.of_sk (K2.trans K3)).readSk (Sk.of_upd [.esi] u4 m4 x4)
    (i := pB) (by decide)) fun t5 u5 m5 x5 => WP.block_nil ?_
  have K5 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t5 :=
    ((K2.trans K3).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u4 m4 x4)).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u5 m5 x5)
  have C5 := C.of_sk K5
  have esi5 : PtrAt t5 W .esi (S + 24 + 4 * N + 4 * (N - (k + 1))) := by
    rw [ptr_iff, u5.other _ (by decide), u4.gpr, e3, K3.keep.1 _ (by decide), b2, sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  have edi5 : PtrAt t5 W .edi (b + 4 * (k + 1 - (k + 1))) := by
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact ptr_of_param u5.gpr PV.b
  have ebp5 : t5.gpr .ebp = BitVec.ofNat 32 (4 * (k + 1 - 0)) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), K3.keep.1 _ (by decide), b2, Nat.sub_zero]
  refine WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C5 K5 esi5 edi5 ebp5 (by omega_arith)
    (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith)) (by omega_arith)
    (by rw [K5.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7, _⟩ => ⟨?_, Ku, mu, cu, u6, u7⟩
  have e := csum_product (digits s.mem W a) (digits s.mem W b) (N := N) (k := k)
  rw [show k + 1 - N = 0 by omega_arith, show min (k + 1) N = k + 1 by omega_arith] at e
  rw [Nat.zero_add, Nat.zero_add, e] at Au
  exact ⟨_, _, Au, by omega_arith, Nat.le_trans (dhigh_le' _ _ _ _ _) (Nat.mul_le_mul_right _ (by omega_arith))⟩

/-- `lenHigh`: `ebp = 4 (2 N - 1 - k)` and `eax = 4 N`. -/
theorem lenHigh_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat} (C : ColEnv s W L V N k)
    (hkN : N ≤ k) {rest : List Instr} {Q : State → Prop}
    (h : ∀ t, t.gpr .ebp = BitVec.ofNat 32 (4 * (2 * N - 1 - k)) → t.gpr .eax = BitVec.ofNat 32 (4 * N) →
      Sk [.eax, .ebp] s t → WP isa (.block rest) t Q) :
    WP isa (.block (lenHigh ++ rest)) s Q := by
  have hk := C.hk
  have hN := C.hN
  simp only [lenHigh, List.cons_append, List.nil_append]
  refine wp_movX (C.prm.read pN4 (by decide)) fun t1 u1 m1 x1 => wp_movX rfl fun t2 u2 m2 x2 =>
    wp_addX rfl fun t3 u3 _ m3 x3 => wp_subX rfl fun t4 u4 _ m4 x4 => wp_subX rfl fun t5 u5 _ m5 x5 => ?_
  have K5 : Sk [.eax, .ebp] s t5 := ((((Sk.of_upd [.eax, .ebp] u1 m1 x1).trans (Sk.of_upd [.eax, .ebp] u2 m2 x2)).trans
    (Sk.of_upd [.eax, .ebp] u3 m3 x3)).trans (Sk.of_upd [.eax, .ebp] u4 m4 x4)).trans (Sk.of_upd [.eax, .ebp] u5 m5 x5)
  have a1 : t1.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [u1.gpr]; exact ofNat_of_toNat C.n4
  have c1 : t1.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [u1.other _ (by decide)]; exact C.ecx
  refine h t5 ?_ (by simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, a1]) K5
  simp (disch := decide) only [u5.gpr, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other, a1, c1,
    ofNat_add3]
  show BitVec.ofNat 32 (4 * N + 4 * N) - BitVec.ofNat 32 4 - _ = _
  rw [sub_ofNat (by omega_arith), sub_ofNat (by omega_arith)]; congr 1; omega_arith

/-- The products of `A` and `B` from `k = N` on. -/
theorem mulHi_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : N ≤ k) (hb : b + 4 * N ≤ L)
    (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input false true) s
      (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [input, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (lenHigh_ok C hkN fun t1 b1 a1 K1 => ?_)
  have K1' := K1.mono [.eax, .ebx, .esi, .edi, .ebp]
  refine ldW_ok (C.prm.of_sk K1) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 1 fun t2 e2 a2 K2 => ?_
  have K2' := K1'.trans K2
  refine wp_movX ((C.prm.of_sk K2').read pB (by decide)) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 =>
    wp_addX rfl fun t5 u5 _ m5 x5 => wp_subX rfl fun t6 u6 _ m6 x6 => WP.block_nil ?_
  have K6 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t6 := (((K2'.trans (Sk.of_upd [.edi] u3 m3 x3)).trans
    (Sk.of_upd [.edi] u4 m4 x4)).trans (Sk.of_upd [.edi] u5 m5 x5)).trans (Sk.of_upd [.edi] u6 m6 x6)
  have C6 := C.of_sk K6
  have c2 : t2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K2.keep.1 _ (by decide), K1.keep.1 _ (by decide), C.ecx]
  have esi6 : PtrAt t6 W .esi (S + 24 + 4 * N + 4 * (N - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, e2]
    congr 1; omega_arith
  have edi6 : PtrAt t6 W .edi (b + 4 * (k + 1 - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
      u3.other, a2, c2, pv_ofNat PV.b]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  have ebp6 : t6.gpr .ebp = BitVec.ofNat 32 (4 * (N - (k + 1 - N))) := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other]
    rw [K2.keep.1 _ (by decide), b1]; congr 1; omega_arith
  refine WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C6 K6 esi6 edi6 ebp6 (by omega_arith)
    (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith)) (by omega_arith)
    (by rw [K6.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7, _⟩ => ⟨?_, Ku, mu, cu, u6, u7⟩
  have e := csum_product (digits s.mem W a) (digits s.mem W b) (N := N) (k := k)
  rw [show min (k + 1) N = N by omega_arith] at e
  rw [Nat.zero_add, Nat.zero_add, e] at Au
  exact ⟨_, _, Au, by omega_arith, Nat.le_trans (dhigh_le' _ _ _ _ _) (Nat.mul_le_mul_right _ (by omega_arith))⟩

/-- A square's sum doubled, then the diagonal's product: from the products
above the diagonal, with `ebx = 4 ⌊(k + 1) / 2⌋`. -/
theorem sqTail_ok {u : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k a H n : Nat}
    (C : ColEnv u W L V N k) (hA : (V pA).toNat = (W.toNat + a) % 2 ^ 32) (ha : a + 4 * N ≤ L)
    (bu : u.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2))) (hH : 2 * H + 2 ^ 32 < 2 ^ 64)
    (A' : Acc (u.xmm .xmm0) (u.xmm .xmm1) (Column.crossCoeff (digits u.mem W a) N k) H n) :
    WP isa (.seq (.block [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)]) diag) u fun w =>
      ∃ H' n', Acc (w.xmm .xmm0) (w.xmm .xmm1) (Column.coeff (digits u.mem W a) (digits u.mem W a) N k) H' n' ∧
        n' ≤ 2 * n + 1 ∧ H' ≤ 2 * H + 2 ^ 32 ∧ Keeps [.eax, .esi] u w ∧ w.mem = u.mem ∧ w.mcdt = u.mcdt ∧
        w.xmm .xmm6 = u.xmm .xmm6 ∧ w.xmm .xmm7 = u.xmm .xmm7 := by
  have hk := C.hk
  have hN := C.hN
  have hn := C.ws.nowrap
  refine WP.seq (WP.of_runBlock ⟨_, double_run u, ?_⟩)
  have Ad := A'.double (by omega_arith)
  let v := (u.setXmm .xmm0 (XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0))).setXmm .xmm1
    (XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1))
  have Cv : ColEnv v W L V N k := C.of_keeps (rs := []) ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl
  have x0v : v.xmm .xmm0 = XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0) := rfl
  have x1v : v.xmm .xmm1 = XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1) := rfl
  have x6v : v.xmm .xmm6 = u.xmm .xmm6 := rfl
  have x7v : v.xmm .xmm7 = u.xmm .xmm7 := rfl
  rw [← x0v, ← x1v] at Ad
  have vm : v.mem = u.mem := rfl
  have vc : v.mcdt = u.mcdt := rfl
  have hcross : 2 * Column.crossCoeff (digits u.mem W a) N k + Column.diagCoeff (digits u.mem W a) N k =
      Column.coeff (digits u.mem W a) (digits u.mem W a) N k := (Column.coeff_square _ _ _).symm
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
  have Kvs : Keeps [.eax, .esi] u v := ⟨fun _ _ => rfl, rfl, rfl⟩
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
    obtain ⟨w7, run, g7, m7, rd7, wr7, mc7, s6, s7, a0, a1⟩ := sq_run w6 (by rw [K6.mcdt]; exact Cv.mcdt)
    have Af := Ad.single (u := w6.gpr .eax) (v := w6.gpr .eax) (by omega_arith)
    rw [← K6.xmm, ← a0, ← a1] at Af
    have hq : (w6.gpr .eax).toNat * (w6.gpr .eax).toNat / 2 ^ 32 < 2 ^ 32 :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by have := word_mul_lt (w6.gpr .eax) (w6.gpr .eax); omega_arith)
    refine WP.of_runBlock ⟨w7, run, _, _, Af.of_eq' ?_, by omega_arith, by omega_arith, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hcross, ite_eq_left ⟨hev, by omega_arith⟩, y6.gpr, K5.mem, vm]
      simp only [digits, w32, Nat.add_zero]
    · exact (Kvs.trans (K6.keep.mono (by decide))).trans ⟨fun r _ => by rw [g7], rd7, wr7⟩
    · rw [m7, K6.mem, vm]
    · rw [mc7, K6.mcdt, vc]
    · rw [s6, K6.xmm, x6v]
    · rw [s7, K6.xmm, x7v]
  · refine WP.ite false (by
        show w3.zf = some false
        rw [zf3, e2, c2, sub_beq (by omega_arith) (by omega_arith), decide_eq_false (by omega_arith)])
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ?_)
    have Ao := Ad
    rw [← K3.xmm] at Ao
    refine ⟨_, _, Ao.of_eq' ?_, by omega_arith, by omega_arith, Kvs.trans (K3.keep.mono (by decide)), by rw [K3.mem, vm],
      by rw [K3.mcdt, vc], by rw [K3.xmm, x6v], by rw [K3.xmm, x7v]⟩
    rw [← hcross, ite_eq_right (by omega_arith), Nat.add_zero]

/-- A square's count of products above the diagonal: `ebp = 4 (e - (k + 1 - N))`
for `ebx = 4 e`, `e = ⌊(k + 1) / 2⌋`. -/
theorem sqLen_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat} (C : ColEnv t W L V N k)
    (hi : Bool) (hhi : hi = true ↔ N ≤ k) (bx : t.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)))
    {rest : List Instr} {Q : State → Prop}
    (h : ∀ u, u.gpr .ebp = BitVec.ofNat 32 (4 * ((k + 1) / 2 - (k + 1 - N))) → Sk [.eax, .ebp] t u →
      WP isa (.block rest) u Q) :
    WP isa (.block ((if hi then [.mov .eax (.mem (kp pN4)), .mov .ebp (.reg .ebx), .alu .add .ebp (.reg .eax),
      .alu .sub .ebp (.reg .ecx), .alu .sub .ebp (.imm 4)] else [.mov .ebp (.reg .ebx)]) ++ rest)) t Q := by
  have hk := C.hk
  have hN := C.hN
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    refine wp_movX rfl fun u1 v1 m1 x1 => h u1 ?_ (Sk.of_upd [.eax, .ebp] v1 m1 x1)
    rw [v1.gpr, bx]; congr 1; have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    have hkN := hhi.mp rfl
    refine wp_movX (C.prm.read pN4 (by decide)) fun u1 v1 m1 x1 => wp_movX rfl fun u2 v2 m2 x2 =>
      wp_addX rfl fun u3 v3 _ m3 x3 => wp_subX rfl fun u4 v4 _ m4 x4 => wp_subX rfl fun u5 v5 _ m5 x5 => ?_
    refine h u5 ?_ ((((((Sk.of_upd [.eax, .ebp] v1 m1 x1).trans (Sk.of_upd [.eax, .ebp] v2 m2 x2)).trans
      (Sk.of_upd [.eax, .ebp] v3 m3 x3)).trans (Sk.of_upd [.eax, .ebp] v4 m4 x4)).trans (Sk.of_upd [.eax, .ebp] v5 m5 x5)))
    have a1 : u1.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [v1.gpr]; exact ofNat_of_toNat C.n4
    simp (disch := decide) only [v5.gpr, v4.gpr, v3.gpr, v3.other, v2.gpr, v2.other, v1.other, a1, bx,
      C.ecx, ofNat_add3]
    show BitVec.ofNat 32 _ - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 4 = _
    rw [sub_ofNat (by omega_arith), sub_ofNat (by omega_arith)]; congr 1; omega_arith

/-- A square's products: those above the diagonal, doubled, and the diagonal's. -/
theorem sq_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hi : Bool) (hhi : hi = true ↔ N ≤ k)
    (ha : a + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input true hi) s (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W a) N k)) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [input, seqs, endHalf, ld, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 =>
    wp_shrX (by decide) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 => wp_addX rfl fun t5 u5 _ m5 x5 => ?_)
  have K5 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t5 := ((((Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans
    (Sk.of_upd [.ebx] u2 m2 x2)).trans (Sk.of_upd [.ebx] u3 m3 x3)).trans (Sk.of_upd [.ebx] u4 m4 x4)).trans
    (Sk.of_upd [.ebx] u5 m5 x5)
  have C5 := C.of_sk K5
  have b5 : t5.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr, C.ecx]; exact half_val (by omega_arith)
  refine sqLen_ok C5 hi hhi b5 fun t6 bp6 K6 => ?_
  have K6' := K5.trans (K6.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine ldW_ok (C.prm.of_sk K6') PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 2 fun t7 e7 a7 K7 => ?_
  have K7' := K6'.trans (K7.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine wp_subX rfl fun t8 u8 _ m8 x8 => wp_movX ((C.prm.of_sk K7').readSk (Sk.of_upd [.esi] u8 m8 x8)
    (i := pA) (by decide)) fun t9 u9 m9 x9 => wp_addX rfl fun t10 u10 _ m10 x10 =>
    wp_addX rfl fun t11 u11 _ m11 x11 => wp_subX rfl fun t12 u12 _ m12 x12 => WP.block_nil ?_
  have K12 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t12 := ((((K7'.trans (Sk.of_upd [.esi] u8 m8 x8)).trans
    (Sk.of_upd [.edi] u9 m9 x9)).trans (Sk.of_upd [.edi] u10 m10 x10)).trans (Sk.of_upd [.edi] u11 m11 x11)).trans
    (Sk.of_upd [.edi] u12 m12 x12)
  have C12 := C.of_sk K12
  have b7 : t7.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [K7.keep.1 _ (by decide), K6.keep.1 _ (by decide), b5]
  have c7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by
    rw [K7.keep.1 _ (by decide), K6.keep.1 _ (by decide)]; exact C5.ecx
  have b12 : t12.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, b7]
  have esi12 : PtrAt t12 W .esi (S + 24 + 4 * N + 4 * (N - (k + 1) / 2)) := by
    rw [ptr_iff]; simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.gpr, e7, b7]
    rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  have edi12 : PtrAt t12 W .edi (a + 4 * (k + 1 - (k + 1) / 2)) := by
    have := (V pA).isLt
    rw [ptr_iff]; simp (disch := decide) only [u12.gpr, u11.gpr, u11.other, u10.gpr, u10.other, u9.gpr, u9.other,
      u8.other, b7, c7, pv_ofNat PV.a]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  have ebp12 : t12.gpr .ebp = BitVec.ofNat 32 (4 * ((k + 1) / 2 - (k + 1 - N))) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other]
    rw [K7.keep.1 _ (by decide), bp6]
  refine WP.seq (WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C12 K12 esi12 edi12 ebp12
    (by omega_arith) (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith))
    (by omega_arith) (by rw [K12.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7, bxu⟩ => ?_)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, csum_cross _ hk] at Au
  have Cu := C.of_keeps (rs := [.eax, .ebx, .esi, .edi, .ebp]) Ku mu cu
  have bu : u.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by rw [bxu, b12]
  rw [← mu] at Au
  have hl := dhigh_le' u.mem W (S + 24 + 4 * N + 4 * (N - (k + 1) / 2)) (a + 4 * (k + 1 - (k + 1) / 2))
    ((k + 1) / 2 - (k + 1 - N))
  refine WP.mono (sqTail_ok Cu PV.a ha bu (by omega_arith) Au) fun w ⟨H', n', Aw, hn', hH', Kw, mw, cw, w6, w7⟩ => ?_
  rw [mu] at Aw
  exact ⟨⟨H', n', Aw, by omega_arith, by omega_arith⟩, Ku.trans (Kw.mono (by decide)), by rw [mw, mu],
    by rw [cw, cu], by rw [w6, u6], by rw [w7, u7]⟩

/-- The products of `A` and `B`: a square's if `A` is `B`. -/
theorem input_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) (ha : a + 4 * N ≤ L) (hb : b + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L)
    (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input sq hi) s (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  cases sq with
  | true => rw [← hsq rfl]; exact sq_ok C PV hi hhi ha hs RA A
  | false =>
    cases hi with
    | false => exact mulLo_ok C PV (by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith) hb hs RA A
    | true => exact mulHi_ok C PV (hhi.mp rfl) hb hs RA A

/-- What the products of the quotient digits and `M` leave. -/
structure RedPost (s : State) (N P H n : Nat) (u : State) : Prop where
  acc : ∃ H' n', Acc (u.xmm .xmm0) (u.xmm .xmm1) P H' n' ∧ n' ≤ n + (N + 2) ∧ H' ≤ H + (N + 2) * 2 ^ 32
  keep : Keeps [.eax, .ebx, .esi, .edi, .ebp] s u
  mem : u.mem = s.mem
  mcdt : u.mcdt = s.mcdt
  x6 : u.xmm .xmm6 = s.xmm .xmm6
  x7 : u.xmm .xmm7 = s.xmm .xmm7

/-- The quotient digits, in reverse at `S + 24`: `Q_i` for `lo ≤ i < hi`. -/
def RevQ (m : Mem) (W : Addr) (N S : Nat) (q : Nat → Nat) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → w32 m W (S + 24 + 4 * (N - 1 - i)) = q i

/-- The products of the quotient digits and `M` from `k = N` on. -/
theorem reduceHi_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b P H n : Nat}
    {q : Nat → Nat} (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : N ≤ k)
    (hm : mo + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RQ : RevQ s.mem W N S q (k + 1 - N) N)
    (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) P H n) :
    WP isa (reduce true) s
      (RedPost s N (P + Column.coeff (Column.prefixDigits q k) (digits s.mem W mo) N k) H n) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [reduce, ↓reduceIte, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (lenHigh_ok C hkN fun t1 b1 a1 K1 => ?_)
  have K1' := K1.mono [.eax, .ebx, .esi, .edi, .ebp]
  refine ldW_ok (C.prm.of_sk K1) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 0 fun t2 e2 a2 K2 => ?_
  have K2' := K1'.trans K2
  refine wp_movX ((C.prm.of_sk K2').read pM (by decide)) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 =>
    wp_addX rfl fun t5 u5 _ m5 x5 => wp_subX rfl fun t6 u6 _ m6 x6 => WP.block_nil ?_
  have K6 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t6 := (((K2'.trans (Sk.of_upd [.edi] u3 m3 x3)).trans
    (Sk.of_upd [.edi] u4 m4 x4)).trans (Sk.of_upd [.edi] u5 m5 x5)).trans (Sk.of_upd [.edi] u6 m6 x6)
  have C6 := C.of_sk K6
  have c2 : t2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K2.keep.1 _ (by decide), K1.keep.1 _ (by decide), C.ecx]
  have esi6 : PtrAt t6 W .esi (S + 24 + 4 * (N - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, e2]
    congr 1; omega_arith
  have edi6 : PtrAt t6 W .edi (mo + 4 * (k + 1 - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
      u3.other, a2, c2, pv_ofNat PV.mo]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  have ebp6 : t6.gpr .ebp = BitVec.ofNat 32 (4 * (N - (k + 1 - N))) := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other]
    rw [K2.keep.1 _ (by decide), b1]; congr 1; omega_arith
  refine WP.mono (dotRev_ok (xp := S + 24) (y := mo) (f := q) (P := P) (H := H) (n0 := n) C6 K6 esi6 edi6 ebp6 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i h1 h2 => RQ i h1 h2) (.inr (by omega_arith)) (.inr (by omega_arith)) hH
    (by rw [K6.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7, _⟩ => ⟨?_, Ku, mu, cu, u6, u7⟩
  have e := csum_reduce q (digits s.mem W mo) (N := N) (k := k)
  rw [show min k N = N by omega_arith] at e
  rw [e] at Au
  have := dhigh_le' s.mem W (S + 24 + 4 * (N - N)) (mo + 4 * (k + 1 - N)) (N - (k + 1 - N))
  exact ⟨_, _, Au, by omega_arith, by omega_arith⟩

/-- The two latest digits in `xmm6` (doublewords 0 and 2) and `M_1`, `M_2` in
`xmm7`, while `k < N`. -/
structure Window (s : State) (W : Addr) (N mo k : Nat) (q : Nat → Nat) : Prop where
  q1 : (dword (s.xmm .xmm6) 0).toNat = if 1 ≤ k then q (k - 1) else 0
  q2 : (dword (s.xmm .xmm6) 2).toNat = if 2 ≤ k then q (k - 2) else 0
  m1 : (dword (s.xmm .xmm7) 0).toNat = digits s.mem W mo 1
  m2 : (dword (s.xmm .xmm7) 2).toNat = if 3 ≤ N then digits s.mem W mo 2 else 0

theorem csum_window (q g : Nat → Nat) {N k : Nat} (hk : k < N) (q1 q2 m1 m2 : Nat)
    (hq1 : q1 = if 1 ≤ k then q (k - 1) else 0) (hq2 : q2 = if 2 ≤ k then q (k - 2) else 0)
    (hm1 : m1 = g 1) (hm2 : m2 = if 3 ≤ N then g 2 else 0) :
    csum q g k 0 (k - 2) + (q1 * m1 + q2 * m2) = Column.coeff (Column.prefixDigits q k) g N k := by
  rw [← csum_reduce0 q g hk]
  subst hq1 hq2 hm1 hm2
  by_cases h2 : 2 ≤ k
  · rw [csum_two q g h2, ite_eq_left (by omega_arith), ite_eq_left h2, ite_eq_left (by omega_arith)]; omega_arith
  · rw [ite_eq_right h2, Nat.zero_mul, Nat.add_zero]
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · simp [csum]
    · simp [csum]

/-- The products of the quotient digits and `M` while `k < N`: those of the
digits stored before the two latest, then those in `xmm6`. -/
theorem reduceLo_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b P H n : Nat}
    {q : Nat → Nat} (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : k < N)
    (hm : mo + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RQ : RevQ s.mem W N S q 0 (k - 2))
    (Wd : Window s W N mo k q) (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) P H n) :
    WP isa (reduce false) s
      (RedPost s N (P + Column.coeff (Column.prefixDigits q k) (digits s.mem W mo) N k) H n) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [reduce, Bool.false_eq_true, ↓reduceIte, seqs, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_subX rfl fun t2 u2 c2 m2 x2 => WP.block_nil ?_)
  have K2 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t2 := (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans
    (Sk.of_upd [.ebp] u2 m2 x2)
  have e1 : t1.gpr .ebp = BitVec.ofNat 32 (4 * k) := by rw [u1.gpr, C.ecx]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .ebp = BitVec.ofNat 32 (4 * (k - 2)) ∧
    Sk [.eax, .ebx, .esi, .edi, .ebp] s t) ?_ fun t3 ⟨b3, K3⟩ => ?_)
  · by_cases h2 : k < 2
    · refine WP.ite false (by
          show t2.cf.map (!·) = _; rw [c2, e1, toNat_ofNat_lt (by omega_arith), decide_eq_true (by show 4 * k < 8; omega_arith)]
          rfl)
        (fun h => absurd h (by decide))
        (fun _ => wp_movX rfl fun t4 u4 m4 x4 => WP.block_nil ⟨?_, K2.trans (Sk.of_upd [.ebp] u4 m4 x4)⟩)
      rw [u4.gpr, show k - 2 = 0 by omega_arith]; rfl
    · refine WP.ite true (by
          show t2.cf.map (!·) = _; rw [c2, e1, toNat_ofNat_lt (by omega_arith), decide_eq_false (by show ¬ 4 * k < 8; omega_arith)]
          rfl)
        (fun _ => WP.block_nil ⟨?_, K2⟩) (fun h => absurd h (by decide))
      rw [u2.gpr, e1]; show _ - BitVec.ofNat 32 8 = _; rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  refine WP.seq (ldW_ok (C.prm.of_sk K3) PV.s PV.n4 (r := .esi) (by decide) (by decide) 8 1 fun t4 e4 a4 K4 => ?_)
  have K4' := K3.trans (K4.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine wp_subX rfl fun t5 u5 _ m5 x5 => wp_movX ((C.prm.of_sk K4').readSk (Sk.of_upd [.esi] u5 m5 x5)
    (i := pM) (by decide)) fun t6 u6 m6 x6 => wp_addX rfl fun t7 u7 _ m7 x7 => WP.block_nil ?_
  have K7 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t7 := ((K4'.trans (Sk.of_upd [.esi] u5 m5 x5)).trans
    (Sk.of_upd [.edi] u6 m6 x6)).trans (Sk.of_upd [.edi] u7 m7 x7)
  have C7 := C.of_sk K7
  have c4 : t4.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K4.keep.1 _ (by decide), K3.keep.1 _ (by decide), C.ecx]
  have esi7 : PtrAt t7 W .esi (S + 32 + 4 * N - 4 * k) := by
    rw [ptr_iff]; simp (disch := decide) only [u7.other, u6.other, u5.gpr, e4, c4]
    rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  have edi7 : PtrAt t7 W .edi (mo + 12) := by
    rw [ptr_iff, u7.gpr, u6.gpr, pv_ofNat PV.mo]; show _ + BitVec.ofNat 32 12 = _; rw [ofNat_add3]; congr 1
  have ebp7 : t7.gpr .ebp = BitVec.ofNat 32 (4 * (k - 2)) := by
    simp (disch := decide) only [u7.other, u6.other, u5.other]; rw [K4.keep.1 _ (by decide), b3]
  -- The digits before the two latest.
  have hdot : WP isa dot t7 fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + csum q (digits s.mem W mo) k 0 (k - 2))
        (H + dhigh s.mem W (S + 32 + 4 * N - 4 * k) (mo + 12) (k - 2)) (n + (k - 2)) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 ∧ u.xmm .xmm7 = s.xmm .xmm7 := by
    by_cases h2 : 2 ≤ k
    · have e7 : S + 32 + 4 * N - 4 * k = S + 24 + 4 * (N - (k - 2)) := by omega_arith
      have f7 : mo + 4 * (k + 1 - (k - 2)) = mo + 12 := by omega_arith
      have esi7' : PtrAt t7 W .esi (S + 24 + 4 * (N - (k - 2))) := by rw [← e7]; exact esi7
      have edi7' : PtrAt t7 W .edi (mo + 4 * (k + 1 - (k - 2))) := by rw [f7]; exact edi7
      refine WP.mono (dotRev_ok (xp := S + 24) (y := mo) (f := q) (i0 := 0) (P := P) (H := H) (n0 := n) C7 K7
        esi7' edi7' (by rw [ebp7, Nat.sub_zero]) (by omega_arith) (by omega_arith) (by omega_arith)
        (fun i _ h => RQ i (Nat.zero_le _) h) (.inr (by omega_arith)) (.inr (by omega_arith)) hH
        (by rw [K7.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7, _⟩ => ⟨?_, Ku, mu, cu, u6, u7⟩
      rw [Nat.sub_zero, ← e7, f7] at Au; exact Au
    · refine WP.mono (dotAcc_ok (n := 0) (P := P) (H := H) (n0 := n) C7 esi7 edi7
        (by rw [ebp7, show k - 2 = 0 by omega_arith]) (.inl rfl) (.inl rfl)
        (Nat.zero_le _) (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _
          (Nat.add_le_add_right (Nat.zero_le N) 4)) _) hH) (by rw [K7.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, u7⟩ => ?_
      rw [show k - 2 = 0 by omega_arith]
      refine ⟨by simpa only [dsum, dhigh, csum, rsum, NatSum.zero, Nat.add_zero] using Au, (K7.keep.mono (by decide)).trans (Ku.mono (by decide)), by rw [mu, K7.mem], by rw [cu, K7.mcdt],
        by rw [u6, K7.xmm], by rw [u7, K7.xmm]⟩
  refine WP.seq (WP.mono hdot fun u ⟨Au, Ku, mu, cu, u6, u7⟩ => ?_)
  obtain ⟨w, run, g, mw, rdw, wrw, mcw, w6, w7, a0, a1⟩ := window_run u (by rw [cu]; exact C.mcdt)
  have hl := dhigh_le' s.mem W (S + 32 + 4 * N - 4 * k) (mo + 12) (k - 2)
  have Aw := Au.mul (u.xmm .xmm6) (u.xmm .xmm7) (by omega_arith)
  rw [← a0, ← a1, u6, u7, Nat.add_assoc,
    csum_window q (digits s.mem W mo) hkN _ _ _ _ Wd.q1 Wd.q2 (by rw [Wd.m1]) (by rw [Wd.m2])] at Aw
  refine WP.of_runBlock ⟨w, run, ⟨_, _, Aw, by omega_arith, ?_⟩, ⟨fun r hr => by rw [g]; exact Ku.1 r hr,
    by rw [rdw]; exact Ku.2.1, by rw [wrw]; exact Ku.2.2⟩, by rw [mw, mu], by rw [mcw, cu], by rw [w6, u6],
    by rw [w7, u7]⟩
  have := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.xmm .xmm6) 0).toNat * (dword (s.xmm .xmm7) 0).toNat)
    (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.xmm .xmm6) 0) (dword (s.xmm .xmm7) 0); omega_arith)
  have := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.xmm .xmm6) 2).toNat * (dword (s.xmm .xmm7) 2).toNat)
    (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.xmm .xmm6) 2) (dword (s.xmm .xmm7) 2); omega_arith)
  omega_arith

end VG.Proof.Mont.X86.Sse2
