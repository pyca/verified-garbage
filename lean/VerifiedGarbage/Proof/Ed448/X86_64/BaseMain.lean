module

import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
public import VerifiedGarbage.Proof.Ed448.Comb
public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
public import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed448.X86_64.BaseBits
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
public import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.X448.X86_64.InvCall
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.X448.X86_64.Inv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit

/-! ### `Ed448.X86_64.CombLoop`, which only this module used -/

section

/-! ### `Ed448.X86_64.CombSelect`, which only this module used -/

section

/-! Constant-time selection of the compact four-column comb's affine point. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Comb

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep off ofs Outside clob mask contains_sc cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

private def pack (a b c d : Nat) : BitVec 64 :=
  let x := (BitVec.ofNat 8 d).setWidth 64
  let y := x + x + (BitVec.ofNat 8 c).setWidth 64
  let z := y + y + (BitVec.ofNat 8 b).setWidth 64
  z + z + (BitVec.ofNat 8 a).setWidth 64

private theorem mask_calc : ∀ a < 2, ∀ b < 2, ∀ c < 2, ∀ d < 2, ∀ i < 16,
    (0 : BitVec 64) - 0 - (BitVec.ofBool (decide
      ((pack a b c d ^^^ (BitVec.ofNat 32 i).signExtend 64).toNat <
        ((1 : BitVec 32).signExtend 64).toNat))).setWidth 64 =
      mask (decide (a + b * 2 + c * 4 + d * 8 = i)) := by decide +kernel

private theorem ea_set {s : State} (r : Reg) (v : BitVec 64) (o : Nat)
    (hr : r ≠ .rdi) (hb : r ≠ .rbx) :
    (s.setReg r v).ea { base := .rdi, index := some .rbx, disp := (o : Int) } =
      s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } := by
  simp only [State.ea, RegUpd.gpr_setReg, Ne.symm hr, Ne.symm hb, ite_false]

private theorem ea_flags {s : State} (v : BitVec 64) (c o' : Bool) (o : Nat) :
    (arithFlags s v c o').ea { base := .rdi, index := some .rbx, disp := (o : Int) } =
      s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } := rfl

/-- The mask compares the four bits with a public table index; no secret affects an address. -/
theorem mask_ok {s : State} {base : Addr} (hs : Scr s base) {t i : Nat}
    (ht : t < 114) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t)
    {a b c d : Nat} (ha : a < 2) (hb' : b < 2) (hc : c < 2) (hd : d < 2)
    (ba : s.mem (off base (BITS + t)) = BitVec.ofNat 8 a)
    (bb : s.mem (off base (BITS + 114 + t)) = BitVec.ofNat 8 b)
    (bc : s.mem (off base (BITS + 228 + t)) = BitVec.ofNat 8 c)
    (bd : s.mem (off base (BITS + 342 + t)) = BitVec.ofNat 8 d) :
    WP isa (.block (combMask i)) s fun u =>
      u.gpr .rcx = mask (decide (a + b * 2 + c * 4 + d * 8 = i)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx] → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  obtain ia : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [ht])⟩
  obtain ib : InRegions (s.rd ++ s.wr) (off base (BITS + 114 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [ht])⟩
  obtain ic : InRegions (s.rd ++ s.wr) (off base (BITS + 228 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [ht])⟩
  obtain id : InRegions (s.rd ++ s.wr) (off base (BITS + 342 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega_using [ht])⟩
  apply WP.of_runBlock
  simp only [combMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, State.load8, State.setReg32, ea_set .rax _ _ (by decide) (by decide), ea_set .rdx _ _ (by decide) (by decide), ea_flags, ea_bitsAt hs.rdi hb, ia, ib, ic, id, ba, bb, bc, bd,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_calc a ha b hb' c hc d hd i hi, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- The expanded scalar bits, beyond the slots every point operation modifies. -/
def Bits (base : Addr) (k : Nat) (s : State) : Prop :=
  ∀ t < 456, s.mem (off base (BITS + t)) = BitVec.ofNat 8 (k / 2 ^ t % 2)

theorem Bits.keep {base : Addr} {k : Nat} {s u : State} (h : Bits base k s) (f : Keep base s u) :
    Bits base k u := by
  intro t ht
  obtain hout : ofs base (off base (BITS + t)) < 64 ∨
      64 + 1584 ≤ ofs base (off base (BITS + t)) := by
    rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega_using [ht])]
    right; simp only [BITS]; omega_using []
  rw [f.mem _ hout]
  exact h t ht

theorem mask_bits_ok {s : State} {base : Addr} (hs : Scr s base) {k t i : Nat}
    (ht : t < 114) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base k s) :
    WP isa (.block (combMask i)) s fun u =>
      u.gpr .rcx = mask (decide (Proof.Ed448.Comb.digit k t = i)) ∧ Keep base s u ∧ u.mem = s.mem := by
  obtain bb := bs (t + 114) (by omega_using [ht])
  obtain bc := bs (t + 228) (by omega_using [ht])
  obtain bd := bs (t + 342) (by omega_using [ht])
  rw [show BITS + (t + 114) = BITS + 114 + t by omega_using []] at bb
  rw [show BITS + (t + 228) = BITS + 228 + t by omega_using []] at bc
  rw [show BITS + (t + 342) = BITS + 342 + t by omega_using []] at bd
  refine WP.mono (mask_ok hs ht hi hb (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (bs t (by omega_using [ht])) bb bc bd)
    fun u ⟨cu, gu, mu, ru, wu⟩ => ⟨cu, ⟨fun r hr => gu r ?_, ru, wu, ?_⟩, mu⟩
  · intro h
    obtain hm : ∀ r ∈ [Reg.rax, .rdx, .rcx], r ∈ clob := by decide
    exact hr (hm r h)
  · rw [mu]; exact Outside.refl _ _ _ _

private theorem entry_words : ∀ i < 16,
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.Comb.entry i).1.val)) =
      (Impl.Ed448.Comb.entry i).1 ∧
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.Comb.entry i).2.val)) =
      (Impl.Ed448.Comb.entry i).2 := by decide +kernel

/-- Selection changes only the selected coordinates and two temporary coordinates. -/
def SelKeeps (e e' : Env) : Prop :=
  ∀ j, j ≠ 3 → j ≠ 4 → j ≠ 8 → j ≠ 9 → e' j = e j

theorem entry_ok {s : State} {base : Addr} (hs : Scr s base) {k t i : Nat}
    (ht : t < 114) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base k s) :
    WP isa (.block (combEntry i)) s fun u =>
      Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) =
        (if Proof.Ed448.Comb.digit k t = i then Impl.Ed448.Comb.entry i
          else (E s.mem base 8, E s.mem base 9)) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  rw [combEntry, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (constE_ok hs 3 _ (entry_words i hi).1) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constE_ok (k1.scr hs) 4 _ (entry_words i hi).2) fun s2 ⟨k2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mask_bits_ok (k2.scr (k1.scr hs)) ht hi
    (by rw [k2.gpr _ (by decide), k1.gpr _ (by decide), hb]) ((bs.keep k1).keep k2))
    fun s3 ⟨c3, k3, m3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k3.scr (k2.scr (k1.scr hs))) 8 3 (by decide) c3)
    fun s4 ⟨k4, c4, e4⟩ => ?_
  refine WP.mono (cswapE (k4.scr (k3.scr (k2.scr (k1.scr hs)))) 9 4 (by decide) (c4.trans c3))
    fun u ⟨ku, _, eu⟩ => ?_
  refine ⟨(((k1.trans k2).trans k3).trans k4).trans ku, ?_, ?_⟩
  · rw [eu, e4, m3, e2, e1]
    by_cases he : Proof.Ed448.Comb.digit k t = i <;>
      simp [opSwap, he]
  · intro j h3 h4 h8 h9
    rw [eu, e4, m3, e2, e1]
    simp only [opSwap, Function.update_of_ne h3, Function.update_of_ne h4,
      Function.update_of_ne h8, Function.update_of_ne h9]

private def picked (xs : List Nat) (d : Nat) (q : Spec.X448.Fe × Spec.X448.Fe) :=
  xs.foldl (fun q i => if d = i then Impl.Ed448.Comb.entry i else q) q

private theorem picked_eq (xs : List Nat) (d : Nat) (q : Spec.X448.Fe × Spec.X448.Fe) :
    picked xs d q = if d ∈ xs then Impl.Ed448.Comb.entry d else q := by
  induction xs generalizing q with
  | nil => simp [picked]
  | cons i xs ih =>
    change picked xs d (if d = i then Impl.Ed448.Comb.entry i else q) = _
    rw [ih]
    by_cases hi : d = i
    · subst i; simp
    · by_cases hx : d ∈ xs <;> simp [hi, hx]

private theorem entries_ok (xs : List Nat) (hx : ∀ i ∈ xs, i < 16)
    {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t < 114) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base k s) :
    WP isa (.block (xs.flatMap combEntry)) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) =
        picked xs (Proof.Ed448.Comb.digit k t) (E s.mem base 8, E s.mem base 9) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ _ _ _ => rfl⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (entry_ok hs ht (hx i List.mem_cons_self) hb bs) fun v ⟨kv, ev, fv⟩ => ?_
    refine WP.mono (ih (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (kv.scr hs)
      (by rw [kv.gpr _ (by decide), hb]) (bs.keep kv)) fun u ⟨ku, eu, fu⟩ => ?_
    refine ⟨kv.trans ku, ?_, fun j h3 h4 h8 h9 => (fu j h3 h4 h8 h9).trans (fv j h3 h4 h8 h9)⟩
    rw [eu, ev]; simp only [picked, List.foldl_cons]

/-- The selected affine point, while preserving the accumulator and curve constant. -/
theorem select_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t < 114) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base k s) :
    WP isa (.block combSelect) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = Impl.Ed448.Comb.entry (Proof.Ed448.Comb.digit k t) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  refine WP.mono (entries_ok (List.range 16) (fun i hi => List.mem_range.mp hi) hs ht hb bs)
    fun u ⟨ku, eu, fu⟩ => ⟨ku, ?_, fu⟩
  rw [eu, picked_eq]
  simp only [List.mem_range, Proof.Ed448.Comb.digit_lt k t, ite_true]

end VG.Proof.Ed448.X86_64.Comb

end

end


/-! The 114 iterations of the four-column Ed448 fixed-base comb. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Comb

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep clob Outside)
open VG.Proof.Ed448.Comb (accScalar digit)

/-- Move the sum into the accumulator, preserving the curve constant and testing the counter. -/
theorem accept_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat}
    (ht : t < 114) (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    WP isa (.block combAccept) s fun u => Keep base s u ∧
      pt (E u.mem base) 0 1 2 = pt (E s.mem base) 3 4 5 ∧
      E u.mem base 11 = E s.mem base 11 ∧ u.zf = some (decide (t = 0)) := by
  rw [combAccept, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 0 3) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k1.scr hs) 1 4) fun s2 ⟨k2, e2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k2.scr (k1.scr hs)) 2 5) fun s3 ⟨k3, e3⟩ => ?_
  refine WP.mono (testRbx_ok s3 t (by omega_using [ht])
    (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), hb]))
    fun u ⟨zu, gu, mu, ru, wu⟩ => ?_
  refine ⟨⟨fun r hr => (gu r).trans (((k1.trans k2).trans k3).gpr r hr),
    ru.trans (k3.rd.trans (k2.rd.trans k1.rd)), wu.trans (k3.wr.trans (k2.wr.trans k1.wr)), ?_⟩,
    ?_, ?_, zu⟩
  · rw [mu]; exact (k1.mem.trans k2.mem).trans k3.mem
  · rw [mu, e3, e2, e1]; simp (disch := decide) only [pt, Function.update_self, Function.update_of_ne]
  · rw [mu, e3, e2, e1]; simp (disch := decide) only [Function.update_of_ne]

private theorem step_rep {p : Spec.Ed448.Point} {k t : Nat} (ht : t < 114)
    (hp : Rep p (accScalar k (t + 1) • baseAff)) :
    Rep (Spec.Ed448.pointAdd (Proof.Ed448.double p)
      (Proof.X448.basePt (Impl.Ed448.Comb.entry (digit k t)))) (accScalar k t • baseAff) := by
  obtain h := pointAdd_rep (double_rep hp) (Proof.Ed448.Comb.entry_rep _ (Proof.Ed448.Comb.digit_lt k t))
  rw [← two_nsmul, smul_smul, ← add_nsmul, ← Proof.Ed448.Comb.accScalar_step k t ht] at h
  exact h

variable {P : Point64.Ops} (hP : Point64.PointOk P)

include hP in
theorem step_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat} (ht : t < 114)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) (bs : Bits base k s)
    (hd : E s.mem base 11 = Spec.Ed448.d)
    (hp : Rep (pt (E s.mem base) 0 1 2) (accScalar k (t + 1) • baseAff)) :
    WP isa (combStep P) s fun u =>
      u.gpr .rbx = BitVec.ofNat 64 t ∧ u.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧
      Outside base 64 1584 s.mem u.mem ∧ E u.mem base 11 = Spec.Ed448.d ∧
      Rep (pt (E u.mem base) 0 1 2) (accScalar k t • baseAff) := by
  rw [combStep]
  refine WP.seq (WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_)
  obtain hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (hP.dbl hs1) fun s2 ⟨k2, e2⟩ => ?_)
  obtain bs2 : Bits base k s2 := (show Bits base k s1 from by intro i hi; rw [m1]; exact bs i hi).keep k2
  obtain b2 : s2.gpr .rbx = BitVec.ofNat 64 t := by rw [k2.gpr _ (by decide), b1]
  refine WP.seq (WP.mono (select_ok (k2.scr hs1) ht b2 bs2) fun s3 ⟨k3, q3, f3⟩ => ?_)
  obtain d3 : E s3.mem base 11 = Spec.Ed448.d := by
    rw [f3 11 (by decide) (by decide) (by decide) (by decide), e2,
      doubleOps_keep _ _ (Or.inl (by decide)), m1, hd]
  obtain p3 : pt (E s3.mem base) 0 1 2 = Proof.Ed448.double (pt (E s.mem base) 0 1 2) := by
    rw [pt_congr (f3 0 (by decide) (by decide) (by decide) (by decide))
      (f3 1 (by decide) (by decide) (by decide) (by decide))
      (f3 2 (by decide) (by decide) (by decide) (by decide)), e2, doubleOps_eval, m1]
  refine WP.seq (WP.mono (hP.add (k3.scr (k2.scr hs1)) d3) fun s4 ⟨k4, e4⟩ => ?_)
  obtain b4 : s4.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), b2]
  refine WP.mono (accept_ok (k4.scr (k3.scr (k2.scr hs1))) ht b4) fun u ⟨ku, pu, du, zu⟩ => ?_
  obtain ku1 := ((k2.trans k3).trans k4).trans ku
  refine ⟨(ku.gpr _ (by decide)).trans b4, zu, fun r hr => ?_, ku1.rd.trans rd1,
    ku1.wr.trans wr1, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    exact (ku1.gpr r hr.2).trans (g1 r hr.1)
  · rw [← m1]; exact ku1.mem
  · rw [du, e4, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), d3]
  · rw [pu, e4, Point64.addAffineOps_eval, d3, addWith_d, p3]
    obtain hx := congrArg Prod.fst q3
    obtain hy := congrArg Prod.snd q3
    dsimp only at hx hy
    rw [hx, hy]
    exact step_rep ht hp

/-- The accumulator represents the already-processed high bits of all four columns. -/
structure Inv (base : Addr) (k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  d : E s.mem base 11 = Spec.Ed448.d
  rep : Rep (pt (E s.mem base) 0 1 2) (accScalar k n • baseAff)

include hP in
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} (bs : Bits base k s₀) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 114 → Inv base k s₀ n s →
      WP isa (.loop (combStep P) .ne) s fun u => Inv base k s₀ 0 u := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun u => Inv base k s₀ 0 u)
    (fun m s => 1 ≤ m ∧ m ≤ 114 ∧ Inv base k s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega_using [hm1]⟩
  obtain bss : Bits base k s := by
    intro j hj
    rw [hi.mem _ (Or.inr (by
      rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [Impl.X448.X86_64.BITS]; omega_using [hj])]
      simp only [Impl.X448.X86_64.BITS]; omega_using []))]
    exact bs j hj
  refine WP.mono (step_ok hP hi.scr (by omega_using [hm2]) hi.rbx bss hi.d hi.rep)
    fun u ⟨bu, zu, gu, ru, wu, ou, du, pu⟩ => ?_
  obtain inv : Inv base k s₀ t u :=
    ⟨⟨(gu _ (by decide)).trans hi.scr.rdi, wu ▸ hi.scr.wr, hi.scr.nowrap⟩, bu,
      fun r hr => (gu r hr).trans (hi.gpr r hr), ru.trans hi.rd, wu.trans hi.wr,
      hi.mem.trans ou, du, pu⟩
  simp only [eval, zu, Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [h] : ¬t = 0), Bool.not_false],
      t, by omega_using [], h, by omega_using [hm2], inv⟩

end VG.Proof.Ed448.X86_64.Comb

end

end


/-!
# Ed448 base-point multiplication on x86-64: the whole function

The correctness of `vg_ed448_scalar_base` against the contract the proof is
written against (`scalarBaseLocal`, `BaseLocal.lean`): the scalar's bits, the
comb loop (`R` represents `[k]B` in the Edwards group; the output's address kept in `rsi` across it and stored at
`OUT` again after it), the inversion of `Z` and the encoding, every write in the
working space but the result's, so the scalar is read unchanged, the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E FieldOk word off Outside ofs Saved clob writeW_outside
  word_writeW_self invert_ok setRbx_ok E_outside contains_sc ofs_off' InvPost invert_post invertCall_post)
open VG.Impl.X448.X86_64 (BITS slot)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The output's address into `r15`, the working space into `rdi`. -/
theorem movOut_ok (s : State) :
    WP isa (.block ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rdx)] : List Instr)) s fun t =>
      t.mem = s.mem ∧ t.gpr .r15 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ∉ [Reg.rdi, .r15] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp [RegUpd.gpr_setReg]
  · simp [RegUpd.gpr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem stashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block stashOut) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .r15) ∧ t.gpr .rsi = s.gpr .r15 ∧
        (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [stashOut, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hb, readSrc,
    State.store64, w, ite_true, Option.some.injEq, exists_eq_left', Option.map_some,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self]
  refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial⟩
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem restashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block restashOut) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .rsi) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  obtain w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [restashOut, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hb,
    State.store64, w, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld) {P : Point64.Ops} (hP : Point64.PointOk P)

include hf hP in
/-- With any point operations `P` that run the field programs (`PointOk`), and any inversion
`inv` that keeps and computes what `invert` does (`InvPost`). -/
theorem scalarBase_correct_of (_hL : BaseLadderOk) {inv : Prog isa}
    (hinv : ∀ {s : State} {base : Addr}, Scr s base → WP isa inv s (InvPost base s))
    {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith fld P inv) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rdx = b := ⟨_, rfl⟩
  rw [hbase] at hd hrs hos hn
  obtain hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  obtain hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  -- The entry: the callee-saved registers, the output's address, the constants.
  apply WP.seq
  rw [entry, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rdx hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movOut_ok s₁) fun s₂ ⟨m₂, r15₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  rw [g₁, hbase] at di₂
  rw [g₁] at r15₂
  obtain hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega_using [hn]⟩
  refine WP.mono (consts_ok hs₂) fun s₃ ⟨p₃, _q₃, d₃, o₃, g₃, rd₃, wr₃, _⟩ => ?_
  obtain hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  obtain rsi₃ : s₃.gpr .rsi = s.gpr .rsi := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁]
  obtain rw₃ : s₃.rd = s.rd ∧ s₃.wr = s.wr := ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  obtain hfar : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hd hi (by decide)
  obtain O₃ : Outside base 0 8192 s.mem s₃.mem := by
    rw [m₂] at o₃
    exact (o₁.mono (by decide) (by decide)).trans (o₃.mono (by decide) (by decide))
  obtain hmem₃ : ∀ i < 57, s₃.mem (s.gpr .rsi + BitVec.ofNat 64 i) =
      s.mem (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => O₃ _ (Or.inr (hfar i hi))
  -- The scalar's bits.
  apply WP.seq
  refine WP.mono (bits_ok hs₃ rsi₃ (fun q hq => ⟨⟨s.gpr .rsi, 57⟩, by rw [rw₃.1, hr]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 57) (by omega_using [hq]) (by omega_using [hq])⟩) hfar)
    fun s₄' ⟨g₄', rd₄', wr₄', o₄', b₄⟩ => ?_
  obtain hs₄' : Scr s₄' base := ⟨(g₄' _ (by decide)).trans hs₃.rdi, wr₄' ▸ hs₃.wr, hs₃.nowrap⟩
  -- The output's address at `OUT`.
  apply WP.seq
  refine WP.mono (stashOut_ok hs₄'.rdi hs₄'.wr) fun s₄ ⟨m₄, si₄, g₄'', rd₄'', wr₄''⟩ => ?_
  obtain g₄ : ∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → s₄.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄'' r hr.2.2.2, g₄' r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  obtain rd₄ : s₄.rd = s₃.rd := by rw [rd₄'', rd₄']
  obtain wr₄ : s₄.wr = s₃.wr := by rw [wr₄'', wr₄']
  obtain oo : Outside base OUT 8 s₄'.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by decide)
  obtain o₄ : Outside base OUT (BITS + 456 - OUT) s₃.mem s₄.mem :=
    (o₄'.mono (by decide) (by decide)).trans (oo.mono (by decide) (by decide))
  obtain hs₄ : Scr s₄ base := ⟨by rw [g₄'' _ (by decide)]; exact hs₄'.rdi, wr₄'' ▸ hs₄'.wr, hs₄'.nowrap⟩
  obtain si₄' : s₄.gpr .rsi = s.gpr .rdi := by rw [si₄, g₄' _ (by decide), g₃ _ (by decide), r15₂]
  obtain b₄' : ∀ t < 456, s₄.mem (off base (BITS + t)) =
      BitVec.ofNat 8 (((s₃.mem (s.gpr .rsi + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1) :=
    fun t ht => by
      rw [oo _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega_using [ht])]; simp only [BITS, OUT]; omega_using []))]
      exact b₄ t ht
  obtain hout₄ : word s₄.mem base OUT = s.gpr .rdi := by
    obtain r15₄ : s₄'.gpr .r15 = s.gpr .rdi := by rw [g₄' _ (by decide), g₃ _ (by decide), r15₂]
    rw [m₄, word_writeW_self, r15₄]
  obtain e₄ : ∀ i : Index, E s₄.mem base i = E s₃.mem base i := fun i => by
    obtain h1 := Proof.X448.X86_64.slot_lt i
    obtain h2 := Proof.X448.X86_64.slot_ge i
    simp only [Impl.X448.X86_64.ACC] at h1
    exact (E_outside oo i (Or.inr (by simp only [OUT]; omega_using [h2]))).trans
      (E_outside o₄' i (Or.inl (by simp only [BITS]; omega_using [h1])))
  -- The loop.
  apply WP.seq
  rw [combLoop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 114))]) s₄ _ from
    setRbx_ok s₄ 114 (by decide)) fun s₅ ⟨rbx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  obtain hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  let K := decodeLE (bytesAt s.mem (s.gpr .rsi) 57)
  obtain hbits : ∀ t < 456, s₅.mem (off base (BITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    intro t ht
    rw [m₅, b₄' t ht, hmem₃ _ (by omega_using [ht]), scalar_bit s.mem _ ht]
  obtain e₅ : ∀ i : Index, E s₅.mem base i = E s₃.mem base i := fun i => by rw [m₅, e₄]
  obtain cbits : Comb.Bits base K s₅ := by
    intro t ht
    simpa only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] using hbits t ht
  obtain I₅ : Comb.Inv base K s₅ 114 s₅ := by
    refine ⟨hs₅, rbx₅, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, ?_⟩
    · rw [e₅]; exact d₃
    · rw [Proof.Ed448.Comb.accScalar_start, zero_smul]
      obtain he : pt (E s₅.mem base) 0 1 2 = Spec.Ed448.identity := by
        simp only [pt, e₅]; exact p₃
      rw [he]; exact identity_rep
  refine WP.mono (Comb.loop_ok hP cbits 114 s₅ (by decide) (by decide) I₅) fun s₆' I₆ => ?_
  -- The output's address at `OUT` again.
  apply WP.seq
  refine WP.mono (restashOut_ok I₆.scr.rdi I₆.scr.wr) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_
  obtain hs₆ : Scr s₆ base := ⟨by rw [g₆]; exact I₆.scr.rdi, wr₆ ▸ I₆.scr.wr, hn⟩
  obtain si₆ : s₆'.gpr .rsi = s.gpr .rdi := by rw [I₆.gpr _ (by decide), g₅ _ (by decide), si₄']
  obtain o₆ : Outside base OUT 8 s₆'.mem s₆.mem := by
    rw [m₆]; exact writeW_outside _ _ _ (by decide)
  obtain e₆ : E s₆.mem base = E s₆'.mem base := funext fun i => by
    obtain h2 := Proof.X448.X86_64.slot_ge i
    exact E_outside o₆ i (Or.inr (by simp only [OUT]; omega_using [h2]))
  -- The inversion of `Z`.
  apply WP.seq
  refine WP.mono (hinv hs₆) fun s₇ ⟨g₇, rd₇, wr₇, o₇, e₇⟩ => ?_
  obtain hs₇ : Scr s₇ base := ⟨(g₇ _ (by decide) (by decide)).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  -- The encoding.
  obtain hout₇ : word s₇.mem base OUT = s.gpr .rdi := by
    rw [o₇.word (by decide) (by decide), m₆, word_writeW_self, si₆]
  obtain sv₇ : Saved base s.gpr s₇.mem := by
    obtain sv₂ : Saved base s.gpr s₂.mem := by rw [m₂]; exact sv₁
    obtain sv₄ := (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
    obtain sv₅ : Saved base s.gpr s₅.mem := by rw [m₅]; exact sv₄
    exact ((sv₅.outside I₆.mem (by decide)).outside o₆ (by decide)).outside o₇ (by decide)
  refine WP.mono (encode_ok hf hs₇ hout₇ (by rw [wr₇, wr₆, I₆.wr, wr₅, wr₄, rw₃.2]; exact hwo) hos sv₇)
    fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  obtain O₇ : Outside base 0 8192 s.mem s₇.mem := by
    obtain O₅ : Outside base 0 8192 s.mem s₅.mem := by
      rw [m₅]; exact O₃.trans (o₄.mono (by decide) (by decide))
    exact ((O₅.trans (I₆.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (o₇.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₇ _ (by decide) (by decide), g₆, I₆.gpr _ (by decide), g₅ _ (by decide),
        g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((VG.Proof.Ed448.X86_64.Outside.frame O₇).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    have r₆ := I₆.rep
    obtain hK : K < 2 ^ 456 := decodeLE_below (by rw [bytesAt_eq]; simp [Spec.X25519.bytesAt])
    rw [Proof.Ed448.Comb.accScalar_total K hK] at r₆
    rw [bt, e₇, E_outside o₇ 0 (by decide), E_outside o₇ 1 (by decide), e₆]
    rw [← encodePoint_code]
    change Spec.Ed448.encodePoint (pt (E s₆'.mem base) 0 1 2) = _
    rw [encodePoint_rep r₆]
    exact (encodePoint_rep (pointMul_rep K basePoint_rep)).symm

theorem scalarBaseFor_inline (v : Impl.Ed448.X86_64.FieldVariant) :
    (scalarBaseFor v).inline = scalarBaseWith v.field v.bodies
      (Impl.X448.X86_64.invertCallWith v.field v.powName [OUT]).inline := by cases v <;> rfl

theorem scalarBaseFor_correct_inline (v : Impl.Ed448.X86_64.FieldVariant)
    (hL : BaseLadderOk) {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa (scalarBaseFor v).inline s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  rw [scalarBaseFor_inline]
  exact scalarBase_correct_of (FieldVariant.field_ok v) (FieldVariant.bodies_ok v) hL
    (fun hs => Proof.X448.X86_64.invertCallWith_post (FieldVariant.field_ok v) v.powName (keep := [OUT]) (by simp [OUT]) hs) hp

end VG.Proof.Ed448.X86_64
