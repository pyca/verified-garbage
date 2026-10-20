module

import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
public import VerifiedGarbage.Proof.Ed448.Comb
public import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X448.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

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
  have ia : InRegions (s.rd ++ s.wr) (off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have ib : InRegions (s.rd ++ s.wr) (off base (BITS + 114 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have ic : InRegions (s.rd ++ s.wr) (off base (BITS + 228 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
  have id : InRegions (s.rd ++ s.wr) (off base (BITS + 342 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [BITS]; omega)⟩
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
  have hout : ofs base (off base (BITS + t)) < 64 ∨
      64 + 1584 ≤ ofs base (off base (BITS + t)) := by
    rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)]
    right; simp only [BITS]; omega
  rw [f.mem _ hout]
  exact h t ht

theorem mask_bits_ok {s : State} {base : Addr} (hs : Scr s base) {k t i : Nat}
    (ht : t < 114) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base k s) :
    WP isa (.block (combMask i)) s fun u =>
      u.gpr .rcx = mask (decide (Proof.Ed448.Comb.digit k t = i)) ∧ Keep base s u ∧ u.mem = s.mem := by
  have bb := bs (t + 114) (by omega)
  have bc := bs (t + 228) (by omega)
  have bd := bs (t + 342) (by omega)
  rw [show BITS + (t + 114) = BITS + 114 + t by omega] at bb
  rw [show BITS + (t + 228) = BITS + 228 + t by omega] at bc
  rw [show BITS + (t + 342) = BITS + 342 + t by omega] at bd
  refine WP.mono (mask_ok hs ht hi hb (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (bs t (by omega)) bb bc bd)
    fun u ⟨cu, gu, mu, ru, wu⟩ => ⟨cu, ⟨fun r hr => gu r ?_, ru, wu, ?_⟩, mu⟩
  · intro h
    have hm : ∀ r ∈ [Reg.rax, .rdx, .rcx], r ∈ clob := by decide
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
