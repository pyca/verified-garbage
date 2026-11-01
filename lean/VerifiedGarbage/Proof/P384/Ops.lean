module

public import VerifiedGarbage.Impl.P384.Ops
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
public import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Rows
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-!
# P-384's field operations inline on AArch64

`mul_ok` and `sqr_ok`: `Ops.mul` and `Ops.sqr` (`Impl/P384/Ops.lean`) compute
Montgomery's product and square modulo `p`, as `vg_p384_mul_mod_p` and
`vg_p384_sqr_mod_p` do (`Proof/Weierstrass/AArch64/MontFn384.lean`), but on
the working space at `x0`, changing only the registers `clobX` (`clob 6` and
`x21`–`x25`) and the result's slot (`OpKeepX`). `fop_ok` and `fprog_ok` are `Fprog.lean`'s for a
straight line of `Ops.op`.
-/

@[expose] public section

-- Powers of two up to `2^768` are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.P384.Ops

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.P384.Ops VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

theorem M_n : M.n = 6 := rfl

/-- The registers the inline operations change: `clob 6`, and the callee-saved
`x21`–`x25` that the products use. -/
def clobX : List Reg := clob 6 ++ [.x21, .x22, .x23, .x24, .x25]

theorem clob_clobX : ∀ r ∈ clob 6, r ∈ clobX := fun _ h => List.mem_append_left _ h

theorem x0_not_clobX : Reg.x0 ∉ clobX := by decide

/-- `OpKeep`, with the frame `clobX`. -/
structure OpKeepX (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clobX → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (ofs base x < o ∨ o + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem OpKeep.toX {base : Addr} {o : Nat} {s s' : State} (h : OpKeep M base o s s') :
    OpKeepX base o s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (clob_clobX r h'), h.rd, h.wr, h.sp, h.mem⟩

/-- A number in memory apart from what an operation writes. -/
theorem opKeepX_wordsVal {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeepX base o s s') : ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 8 * M.n ≤ y) →
      (y + 8 * k ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y) → y + 8 * k ≤ 2 ^ 64 →
      wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    simp only [wordsVal]
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
        (by rw [ofs_off base (by omega_arith)]; omega_arith)
    rw [opKeepX_wordsVal h (k := k) (y := y + 8) (by omega_arith) (by omega_arith) (by omega_arith), hw]

/-- `Inv.update`, for `OpKeepX`. -/
theorem Inv.updateX {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : OpKeepX base o s s') (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hlo := hL.le o ho
  have hmo := hL.mo o ho
  have hto := hL.tmp o ho
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => by
      have := hL.apart x o hx ho hxo
      have := hL.tmp x hx
      have := hL.le x hx
      exact opKeepX_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨⟨(hk.gpr _ x0_not_clobX).trans hI.scr.x0, hk.wr ▸ hI.scr.wr, hn, hI.scr.enc⟩,
    ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red, hM.call⟩, ?_, ?_, ?_⟩
  · have := hM.mo
    have := hM.sep
    rw [opKeepX_wordsVal hk (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hM.val
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · rw [heq x (hI.sl x (List.mem_of_ne_of_mem hxo hx)) hxo]
      exact hI.lt x (List.mem_of_ne_of_mem hxo hx)
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- `ProgKeep`, with the frame `clobX`. -/
structure ProgKeepX (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clobX → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem ProgKeepX.refl (base : Addr) (W : List Nat) (s : State) : ProgKeepX base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem ProgKeepX.mono {base : Addr} {W W' : List Nat} {s s' : State}
    (h : ProgKeepX base W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeepX base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem ProgKeepX.unch {base : Addr} {W : List Nat} {s s' : State} (h : ProgKeepX base W s s') :
    Unch base (W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n)]) s.mem s'.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

/-- P-384's prime, as the reductions write it. -/
theorem p_eq : P384Mul.p = p384 := by decide

/-- The low word of `p`, from its slot, and `2^64` less it: the reductions' constants. -/
theorem redLoad_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .x7 = 0)
    (hmo : M.mo + 48 ≤ size) (hmo8 : M.mo % 8 = 0) (hm : wordsVal s.mem base M.mo 6 = p384) :
    WP isa (.block redLoad) s fun t =>
      t.gpr .x16 = P384Mul.c0 ∧ t.gpr .x17 = P384Mul.c1 ∧ Keeps [.x16, .x17] s t := by
  have hw : word s.mem base M.mo = P384Mul.c1 := by
    apply BitVec.eq_of_toNat_eq
    have h := hm
    simp only [wordsVal] at h
    rw [show P384Mul.c1.toNat = p384 % 2 ^ 64 by decide]
    omega_arith
  rw [redLoad, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ldR_ok hs.ptr (d := M.mo) (by omega_arith) hmo8 .x17) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', z₁, l₁, hw, reduceCtorEq, ite_false, ite_true]
  refine ⟨by decide, by decide, ⟨fun r hr => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, ite_false]
  exact k₁.gpr r (by simp [hr.2])

/-- What the finish needs of its registers. -/
theorem finish_regs :
    Reg.x7 ∉ ([.x16, .x17] : List Reg) ∧ Reg.x7 ∉ ([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs ∧
    (∀ r ∈ P384Mul.lowRegs, r ∉ ([.x16, .x17] : List Reg)) ∧
    (∀ r ∈ P384Mul.highRegs, r ∉ ([.x16, .x17] : List Reg)) ∧
    (∀ r ∈ P384Mul.highRegs, r ∉ ([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs) ∧
    Reg.x7 ∉ Reg.x21 :: P384Mul.lowRegs ∧ Reg.x0 ∉ Reg.x2 :: .x17 :: (P384Mul.lowRegs ++ dRegs 6) ∧
    P384Mul.accRegs = P384Mul.lowRegs ++ P384Mul.highRegs ∧ P384Mul.lowRegs.length = 6 ∧
    Fresh (.x21 :: P384Mul.lowRegs) ∧ P384Mul.lowRegs.Nodup ∧ Reg.x0 ∉ [Reg.x16, .x17] ∧
    Reg.x0 ∉ ([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs ∧ Reg.x0 ∉ Reg.x21 :: P384Mul.lowRegs ∧
    (∀ r ∈ ([.x16, .x17] : List Reg) ++ (([.x1, .x2, .x3] : List Reg) ++ P384Mul.lowRegs) ++
      (Reg.x21 :: P384Mul.lowRegs) ++ (Reg.x2 :: .x17 :: (P384Mul.lowRegs ++ dRegs 6)), r ∈ clobX) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- After the product or square, `[acc] = X < 2^384 p`: `[o] = X 2^-384 mod p`. -/
theorem finish_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) {o : Nat} (ho : o + 48 ≤ size) (ho8 : o % 8 = 0)
    (hz : s.gpr .x7 = 0) (hX : regsVal s P384Mul.accRegs < 2 ^ 384 * p384) :
    WP isa (.block (finish o)) s fun s' =>
      (∀ r, r ∉ clobX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside base o 48 s.mem s'.mem ∧ wordsVal s'.mem base o 6 < p384 ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % p384 = regsVal s P384Mul.accRegs % p384 := by
  obtain ⟨n7c, n7r, loC, hiC, hiR, n7l, -, accE, llen, fr, lnd, x0c, x0r, x0l, wC⟩ := finish_regs
  have hmo : M.mo + 48 ≤ size := hM.mo
  have hmo8 : M.mo % 8 = 0 := by decide
  have hm : wordsVal s.mem base M.mo 6 = p384 := hM.val
  have e₃' : regsVal s P384Mul.accRegs =
      regsVal s P384Mul.lowRegs + 2 ^ (64 * 6) * regsVal s P384Mul.highRegs := by
    rw [show regsVal s P384Mul.accRegs = regsVal s (P384Mul.lowRegs ++ P384Mul.highRegs) by rw [← accE],
      regsVal_append, llen]
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ clobX) →
      ∀ r, r ∉ clobX → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  -- The reductions' constants.
  rw [finish, WP.block_append_iff]
  refine WP.mono (redLoad_ok hs hz hmo hmo8 hm) fun s₁ ⟨h16, h17, k₁⟩ => ?_
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ n7c, hz]
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁ x0c
  have hl₁ : regsVal s₁ P384Mul.lowRegs = regsVal s P384Mul.lowRegs :=
    regsVal_congr fun r hr => k₁.gpr r (loC r hr)
  have hh₁ : regsVal s₁ P384Mul.highRegs = regsVal s P384Mul.highRegs :=
    regsVal_congr fun r hr => k₁.gpr r (hiC r hr)
  -- The reductions.
  rw [WP.block_append_iff]
  refine WP.mono (P384Mul.redsN_ok 6 (by decide) s₁ z₁ h16 h17) fun s₂ ⟨⟨W, hW, e₂⟩, k₂⟩ => ?_
  rw [P384Mul.rot_six, hl₁, p_eq] at e₂
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ n7r, z₁]
  have hH₂ : regsVal s₂ P384Mul.highRegs = regsVal s P384Mul.highRegs := by
    rw [← hh₁]; exact regsVal_congr fun r hr => k₂.gpr r (hiR r hr)
  -- The high half added.
  rw [WP.block_append_iff]
  refine WP.mono (P384Mul.addHigh_ok s₂ z₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ n7l, z₂]
  rw [hH₂] at e₃
  have hsum : 2 ^ 384 * (regsVal s₃ P384Mul.lowRegs + 2 ^ 384 * (s₃.gpr .x21).toNat) =
      regsVal s P384Mul.accRegs + W * p384 := by
    rw [e₃, Nat.mul_add, e₂, e₃']; omega_arith
  have hlt : regsVal s P384Mul.accRegs + W * p384 < 2 ^ 384 * (2 * p384) := by
    have h2 : W * p384 < 2 ^ 384 * p384 := Nat.mul_lt_mul_of_pos_right (by simpa using hW) (by decide)
    omega_arith
  rw [← hsum] at hlt
  have hV := Nat.lt_of_mul_lt_mul_left hlt
  -- The sum reduced.
  have hs₃ : Scr s₃ base size := (hs₁.of_keeps k₂ x0r).of_keeps k₃ x0l
  have hm₃ : wordsVal s₃.mem base M.mo M.n = p384 := by rw [k₃.mem, k₂.mem, k₁.mem]; exact hm
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok hs₃ (M := M) (ts := P384Mul.lowRegs) (top := .x21) llen (by decide) (by decide) fr
    hmo hmo8 z₃ hm₃ hV) fun s₄ ⟨e₄, k₄⟩ => ?_
  -- The store.
  have hs₄ : Scr s₄ base size := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (stores_ok P384Mul.lowRegs hs₄ (o := o) (by rw [llen]; exact ho) ho8 lnd)
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [llen] at e₅ O₅
  have kr : ∀ r, r ∉ clobX → s₄.gpr r = s.gpr r := fun r hr => by
    rw [kw k₄ (by decide) r hr, kw k₃ (by decide) r hr, kw k₂ (by decide) r hr, kw k₁ (by decide) r hr]
  have hmem₄ : s₄.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  have hR : wordsVal s₅.mem base o 6 =
      (regsVal s₃ P384Mul.lowRegs + 2 ^ 384 * (s₃.gpr .x21).toNat) % p384 := by
    rw [e₅, e₄, M_n]
  refine ⟨fun r hr => by rw [k₅.gpr r (by simp), kr r hr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₅.rd, k₄.rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₅.wr, k₄.wr, k₃.wr, k₂.wr, k₁.wr]
  · rw [k₅.sp, k₄.sp, k₃.sp, k₂.sp, k₁.sp]
  · intro x hx; rw [O₅ x hx, hmem₄]
  · rw [hR]; exact Nat.mod_lt _ (by decide)
  · rw [hR, Nat.mod_mul_mod, show (64 * 6 : Nat) = 384 from rfl, Nat.mul_comm, hsum,
      Nat.add_mul_mod_self_right]

theorem baseOk_x0 : P384Mul.BaseOk .x0 := by decide

theorem rmOk_x0 : P384Sqr.RmOk .x0 := by decide

/-- `[o] = [a] [b] 2^-384 mod p`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) {o a b : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size)
    (hb : b + 48 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (Impl.P384.Ops.mul o a b)) s fun s' => OpKeepX base o s s' ∧
      wordsVal s'.mem base o 6 < p384 ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % p384 := by
  have wB : ∀ r ∈ P384Mul.bRegs384, r ∈ clobX := by decide
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ clobX) →
      ∀ r, r ∉ clobX → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  rw [Impl.P384.Ops.mul, WP.block_append_iff, loads_eq]
  refine WP.mono (loadsEach_ok P384Mul.bRegs384 hs.ptr (a := b) hb hb8 (by decide) (by decide))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hB₁ : regsVal s₁ P384Mul.bRegs384 = wordsVal s.mem base b 6 := VG.Proof.Weierstrass.AArch64.Mont.regsVal_of_loads _ b e₁
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁ (by decide)
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₁) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base size := hs₁.of_keeps k₂ (by decide)
  have hB₂ : regsVal s₂ P384Mul.bRegs384 = wordsVal s.mem base b 6 := by
    rw [← hB₁]; exact regsVal_congr fun r hr => k₂.gpr r (by revert r; decide)
  rw [WP.block_append_iff]
  refine WP.mono (P384Mul.prodAt_ok baseOk_x0 hs₂.ptr ha ha8 z₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), z₂]
  rw [hB₂, k₂.mem, k₁.mem] at e₃
  have hs₃ : Scr s₃ base size := hs₂.of_keeps k₃ (by decide)
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hM₃ : ModOkA M size p384 s₃.mem base := hm₃ ▸ hM
  have hX : regsVal s₃ P384Mul.accRegs < 2 ^ 384 * p384 := by
    rw [e₃]
    exact Nat.mul_lt_mul_of_lt_of_le (by simpa using wordsVal_lt s.mem base a 6) (Nat.le_of_lt hB) (by decide)
  refine WP.mono (finish_ok hs₃ hM₃ ho ho8 z₃ hX) fun s' ⟨G, rd, wr, sp, O, V, C⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [rd, k₃.rd, k₂.rd, k₁.rd], by rw [wr, k₃.wr, k₂.wr, k₁.wr],
    by rw [sp, k₃.sp, k₂.sp, k₁.sp], fun x hx _ => by rw [O x hx, hm₃]⟩, V, by rw [C, e₃]⟩
  rw [G r hr, kw k₃ (by decide) r hr, kw k₂ (by decide) r hr, kw k₁ wB r hr]

/-- `[o] = [a]^2 2^-384 mod p`. -/
theorem sqr_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) {o a : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hA : wordsVal s.mem base a 6 < p384) :
    WP isa (.block (Impl.P384.Ops.sqr o a)) s fun s' => OpKeepX base o s s' ∧
      wordsVal s'.mem base o 6 < p384 ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % p384 := by
  have wB : ∀ r ∈ P384Sqr.aRegs, r ∈ clobX := by decide
  have kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ clobX) →
      ∀ r, r ∉ clobX → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  rw [Impl.P384.Ops.sqr, WP.block_append_iff, loads_eq]
  refine WP.mono (loadsEach_ok P384Sqr.aRegs hs.ptr (a := a) ha ha8 (by decide) (by decide))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hA₁ : regsVal s₁ P384Sqr.aRegs = wordsVal s.mem base a 6 := VG.Proof.Weierstrass.AArch64.Mont.regsVal_of_loads _ a e₁
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁ (by decide)
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₁) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base size := hs₁.of_keeps k₂ (by decide)
  have hA₂ : regsVal s₂ P384Sqr.aRegs = wordsVal s.mem base a 6 := by
    rw [← hA₁]; exact regsVal_congr fun r hr => k₂.gpr r (by revert r; decide)
  rw [WP.block_append_iff]
  refine WP.mono (P384Sqr.sqAt_ok rmOk_x0 hs₂.ptr z₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), z₂]
  rw [hA₂] at e₃
  have hs₃ : Scr s₃ base size := hs₂.of_keeps k₃ (by decide)
  have hm₃ : s₃.mem = s.mem := by rw [k₃.mem, k₂.mem, k₁.mem]
  have hM₃ : ModOkA M size p384 s₃.mem base := hm₃ ▸ hM
  have hX : regsVal s₃ P384Mul.accRegs < 2 ^ 384 * p384 := by
    rw [e₃]
    exact Nat.mul_lt_mul_of_lt_of_le (by simpa using wordsVal_lt s.mem base a 6) (Nat.le_of_lt hA) (by decide)
  refine WP.mono (finish_ok hs₃ hM₃ ho ho8 z₃ hX) fun s' ⟨G, rd, wr, sp, O, V, C⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [rd, k₃.rd, k₂.rd, k₁.rd], by rw [wr, k₃.wr, k₂.wr, k₁.wr],
    by rw [sp, k₃.sp, k₂.sp, k₁.sp], fun x hx _ => by rw [O x hx, hm₃]⟩, V, by rw [C, e₃]⟩
  rw [G r hr, kw k₃ (by decide) r hr, kw k₂ (by decide) r hr, kw k₁ wB r hr]

/-- `Fprog.lean`'s `mulOp_ok`, for `Ops.op`. -/
theorem mulOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb8 : b % 8 = 0) (hB : wordsVal s.mem base b M.n < p384) :
    WP isa (.block (Impl.P384.Ops.op (.mul o a b))) s fun t =>
      OpKeepX base o s t ∧ wordsVal t.mem base o M.n < p384 ∧
      wordsVal t.mem base o M.n * 2 ^ (64 * M.n) % p384 =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % p384 := by
  rw [M_n] at ho ha hb hB ⊢
  by_cases hab : a = b
  · subst b
    simp only [Impl.P384.Ops.op, beq_self_eq_true, ↓reduceIte]
    exact sqr_ok hs hM ho ha ho8 ha8 hB
  · simp only [Impl.P384.Ops.op, beq_iff_eq, hab, ↓reduceIte]
    exact mul_ok hs hM ho ha hb ho8 ha8 hb8 hB

theorem op_eq_opCode {f : FOp} (hf : ∀ o a b, f ≠ .mul o a b) : Impl.P384.Ops.op f = VG.Impl.Weierstrass.AArch64.opCode M f := by
  cases f with
  | mul o a b => exact absurd rfl (hf o a b)
  | add => rfl
  | sub => rfl

/-- `Fprog.lean`'s `fop_ok`, for `Ops.op`. -/
theorem fop_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {base : Addr} {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (Impl.P384.Ops.op op)) s fun s' =>
      OpKeepX base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  subst hmp
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulOp_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hI.lt b hR.2))
      fun s' ⟨hk, hlt, heq⟩ => ⟨hk, Inv.updateX hL hI hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    rw [op_eq_opCode (by intros; exact FOp.noConfusion)]
    exact WP.mono (Weierstrass.AArch64.fop_ok hL hAl hm hI hS hR) fun _ ⟨k, I⟩ => ⟨OpKeep.toX k, I⟩
  | sub o a b =>
    rw [op_eq_opCode (by intros; exact FOp.noConfusion)]
    exact WP.mono (Weierstrass.AArch64.fop_ok hL hAl hm hI hS hR) fun _ ⟨k, I⟩ => ⟨OpKeep.toX k, I⟩

/-- `Fprog.lean`'s `fprog_ok`, for a straight line of `Ops.op`. -/
theorem fprog_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {base : Addr} :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (ops.flatMap Impl.P384.Ops.op)) s fun s' => ProgKeepX base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeepX.refl _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hmp hL hAl hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hmp hL hAl hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

end VG.Proof.P384.Ops
