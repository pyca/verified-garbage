module

public import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
public import VerifiedGarbage.Proof.Ed448.Window
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Constant-time selection of the compact four-column comb's affine point. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
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
theorem mask_ok {s : State} {base : Addr} (hs : Scr s base) {o t i : Nat} (ho : o + 456 ≤ 8192)
    (ht : t + 4 ≤ 456) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t)
    {a b c d : Nat} (ha : a < 2) (hb' : b < 2) (hc : c < 2) (hd : d < 2)
    (ba : s.mem (off base (o + t)) = BitVec.ofNat 8 a)
    (bb : s.mem (off base (o + 1 + t)) = BitVec.ofNat 8 b)
    (bc : s.mem (off base (o + 2 + t)) = BitVec.ofNat 8 c)
    (bd : s.mem (off base (o + 3 + t)) = BitVec.ofNat 8 d) :
    WP isa (.block (digitMask o i)) s fun u =>
      u.gpr .rcx = mask (decide (a + b * 2 + c * 4 + d * 8 = i)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rcx] → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (off base (o + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  have ib : InRegions (s.rd ++ s.wr) (off base (o + 1 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  have ic : InRegions (s.rd ++ s.wr) (off base (o + 2 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  have id : InRegions (s.rd ++ s.wr) (off base (o + 3 + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [digitMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, State.load8, State.setReg32, ea_set .rax _ _ (by decide) (by decide), ea_set .rdx _ _ (by decide) (by decide), ea_flags, ea_bitsAt hs.rdi hb, ia, ib, ic, id, ba, bb, bc, bd,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_calc a ha b hb' c hc d hd i hi, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2, ite_false]

/-- The expanded scalar bits, beyond the slots every point operation modifies. -/
def Bits (base : Addr) (o k : Nat) (s : State) : Prop :=
  ∀ t < 456, s.mem (off base (o + t)) = BitVec.ofNat 8 (k / 2 ^ t % 2)

theorem Bits.keep {base : Addr} {o k : Nat} (ho : 2048 ≤ o) (hb : o + 456 ≤ 8192) {s u : State} (h : Bits base o k s) (f : Keep base s u) :
    Bits base o k u := by
  intro t ht
  have hout : ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ ofs base (off base (o + t)) := by
    rw [VG.Proof.X448.X86_64.ofs_off' base (by omega)]
    right; omega
  rw [f.mem _ hout]
  exact h t ht

theorem mask_bits_ok {s : State} {base : Addr} (hs : Scr s base) {o k t i : Nat} (ho : o + 456 ≤ 8192)
    (ht : t + 4 ≤ 456) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (digitMask o i)) s fun u =>
      u.gpr .rcx = mask (decide (Proof.Ed448.Window.digit k t = i)) ∧ Keep base s u ∧ u.mem = s.mem := by
  have bb := bs (t + 1) (by omega)
  have bc := bs (t + 2) (by omega)
  have bd := bs (t + 3) (by omega)
  rw [show o + (t + 1) = o + 1 + t by omega] at bb
  rw [show o + (t + 2) = o + 2 + t by omega] at bc
  rw [show o + (t + 3) = o + 3 + t by omega] at bd
  refine WP.mono (mask_ok hs ho ht hi hb (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (bs t (by omega)) bb bc bd)
    fun u ⟨cu, gu, mu, ru, wu⟩ => ⟨cu, ⟨fun r hr => gu r ?_, ru, wu, ?_⟩, mu⟩
  · intro h
    have hm : ∀ r ∈ [Reg.rax, .rdx, .rcx], r ∈ clob := by decide
    exact hr (hm r h)
  · rw [mu]; exact Outside.refl _ _ _ _

end VG.Proof.Ed448.X86_64.Window
