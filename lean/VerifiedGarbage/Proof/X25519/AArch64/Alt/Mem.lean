module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # `ldp` and `stp` of the workspace

The loads and stores of the field operations of `Impl/X25519/AArch64/AltOps`:
two words of the workspace at `x0` with one `ldp` or `stp`. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64

theorem exec_ldp_x {s : State} {t1 t2 n : Reg} {off : Nat} (ht : t1 ≠ t2)
    (ho : off % 8 = 0 ∧ off ≤ 504)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off + 8) 8) :
    exec (.ldp t1 t2 n off) s = some ((s.write .x t1 (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)).write
      .x t2 (s.mem.readW (s.gpr n + BitVec.ofNat 64 off + 8) 64)) := by
  simp only [exec, ne_eq, ht, not_false_eq_true, ho, and_self, ite_true, State.load, h1, h2,
    Option.bind_some, Option.map_some, Mem.readW, BitVec.setWidth_eq]

theorem exec_stp_x {s : State} {t1 t2 n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off ≤ 504)
    (h1 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8)
    (h2 : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off + 8) 8) :
    exec (.stp t1 t2 n off) s = some { s with
      mem := ((s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t1)).writeW
        (s.gpr n + BitVec.ofNat 64 off + 8) (s.gpr t2)) } := by
  simp only [exec, ho, and_self, ite_true, State.store, h1, Option.bind_some, read_x,
    BitVec.setWidth_eq]
  simp only [h2]
  rfl

theorem eight : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl

/-- `ldp t1, t2, [x0, #d]`: the words at `d` and `d + 8` of the workspace. -/
theorem ldp_sc {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) (hw : d + 16 ≤ workSize large) {t1 t2 : Reg} (ht : t1 ≠ t2) :
    exec (.ldp t1 t2 .x0 d) s = some ((s.write .x t1 (word s.mem base d)).write .x t2
      (word s.mem base (d + 8))) := by
  have _hcap := workSize_le large
  rw [exec_ldp_x ht ⟨ha, hd⟩]
  · rw [hs.x0, word, word, off, off, eight, Offset.add_add]
  · rw [hs.x0]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega)⟩
  · rw [hs.x0, eight, Offset.add_add]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega)⟩

/-- `s` with the memory `m`: a definition, so that a store's state stays
folded, as `RegUpd` keeps register writes folded. -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem gpr_withMem (s : State) (m : Mem) : (withMem s m).gpr = s.gpr := rfl
theorem mem_withMem (s : State) (m : Mem) : (withMem s m).mem = m := rfl
theorem rd_withMem (s : State) (m : Mem) : (withMem s m).rd = s.rd := rfl
theorem wr_withMem (s : State) (m : Mem) : (withMem s m).wr = s.wr := rfl
theorem sp_withMem (s : State) (m : Mem) : (withMem s m).sp = s.sp := rfl
theorem zf_withMem (s : State) (m : Mem) : (withMem s m).zf = s.zf := rfl
theorem c_withMem (s : State) (m : Mem) : (withMem s m).c = s.c := rfl

theorem _root_.VG.Proof.Ed25519.AArch64.Scr.withMem {s : State} {base : Addr} (hs : Scr s base large) (m : Mem) :
    Scr (Alt.withMem s m) base large := ⟨hs.x0, hs.wr, hs.nowrap⟩

theorem _root_.VG.Proof.Ed25519.AArch64.Scr.awc {s : State} {base : Addr} (hs : Scr s base large)
    {r : Reg} (hr : r ≠ .x0) (a b : BitVec 64) (c : Bool) :
    Scr (s.addWithCarry .x r a b c) base large :=
  ⟨(RegUpd.gpr_addWithCarry s .x r a b c .x0).trans (by simp only [Ne.symm hr, ite_false]; exact hs.x0),
    hs.wr, hs.nowrap⟩

/-- Two words stored at `base + d`, as one `stp` stores them. -/
def st2 (m : Mem) (base : Addr) (d : Nat) (v w : BitVec 64) : Mem :=
  (m.writeW (off base d) v).writeW (off base (d + 8)) w

/-- `stp t1, t2, [x0, #d]`: the words at `d` and `d + 8` of the workspace. -/
theorem stp_sc {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) (hw : d + 16 ≤ workSize large) (t1 t2 : Reg) :
    exec (.stp t1 t2 .x0 d) s = some (withMem s (st2 s.mem base d (s.gpr t1) (s.gpr t2))) := by
  have _hcap := workSize_le large
  rw [exec_stp_x ⟨ha, hd⟩]
  · rw [hs.x0, st2, off, off, eight, Offset.add_add]; rfl
  · rw [hs.x0]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega)⟩
  · rw [hs.x0, eight, Offset.add_add]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega)⟩

/-- A word that two stored words do not overlap. -/
theorem word_st2 (m : Mem) (base : Addr) {d e : Nat} (v w : BitVec 64)
    (h : e + 8 ≤ d ∨ d + 16 ≤ e) (hd : d + 16 ≤ 8192) (he : e + 8 ≤ 8192) :
    word (st2 m base d v w) base e = word m base e := by
  rw [st2, word_writeW_sep _ _ _ (by omega) (by omega) (by omega),
    word_writeW_sep _ _ _ (by omega) (by omega) (by omega)]

/-- Two `stp`s of consecutive pairs of words: a field element's four words. -/
theorem st2_st2 (m : Mem) (base : Addr) (o : Nat) (w0 w1 w2 w3 : BitVec 64) :
    st2 (st2 m base o w0 w1) base (o + 16) w2 w3 = st4 m base o w0 w1 w2 w3 := by
  simp only [st2, st4, show o + 16 + 8 = o + 24 by omega]

/-- Two `stp`s storing four registers as the field element at `o`. -/
theorem store4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ha : o % 8 = 0) (hd : o ≤ 480) (hw : o + 32 ≤ workSize large) (r0 r1 r2 r3 : Reg) :
    WP isa (.block [.stp r0 r1 .x0 o, .stp r2 r3 .x0 (o + 16)]) s fun t =>
      t = withMem s (st4 s.mem base o (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, stp_sc hs ha (by omega) (by omega),
    stp_sc (hs.withMem _) (by omega : (o + 16) % 8 = 0) (by omega) (by omega),
    Option.some.injEq, exists_eq_left', gpr_withMem, mem_withMem, st2_st2]
  rfl

/-- The carry out of `adds r, x, x`: the top bit of `x`. -/
theorem fold_c (x : BitVec 64) :
    (decide (2 ^ 64 ≤ x.toNat + x.toNat + false.toNat)).toNat = x.toNat / 2 ^ 63 := by
  have := x.isLt
  rw [Bool.toNat_false, Nat.add_zero]
  by_cases h : 2 ^ 64 ≤ x.toNat + x.toNat
  · rw [decide_eq_true h, Bool.toNat_true]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

/-- `lsr` by one of `x + x`: `x` without its top bit. -/
theorem fold_lo (x : BitVec 64) :
    ((x + x + BitVec.ofNat 64 false.toNat) >>> 1).toNat = x.toNat % 2 ^ 63 := by
  have := x.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false,
    Nat.shiftRight_eq_div_pow]
  omega

/-- A field element the operations of `AltOps` may read or write: aligned, in
the workspace, and in reach of `ldp` and `stp` from `x0`. -/
def AltRange (o : Nat) (large : Bool := true) : Prop :=
  o % 8 = 0 ∧ o ≤ 480 ∧ o + 32 ≤ workSize large

/-- Two field elements are the same or do not overlap. -/
def SameOrApart (o a : Nat) : Prop := o = a ∨ o + 32 ≤ a ∨ a + 32 ≤ o

/-- The registers the operations of `AltOps` may change: x2–x16, not x17
(zero) or x1 (`cmadd_4`'s multiplier). -/
def altClob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16]

/-- What an operation of `AltOps` writing the field element at `o` keeps: the
registers but `altClob`, the regions, the stack pointer, and the memory
outside the field element. -/
structure AltOp (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ altClob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem AltOp.scr {base : Addr} {o : Nat} {s t : State} (h : AltOp base o s t)
    (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem AltOp.fe {base : Addr} {o : Nat} {s t : State} (h : AltOp base o s t) {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : AltRange d large) : fe t.mem base d = fe s.mem base d :=
  h.mem.fe hd (by have := hd'.2.2; have := workSize_le large; omega)

end VG.Proof.X25519.AArch64.Alt
