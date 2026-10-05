import VerifiedGarbage.Impl.Ed25519.AArch64.Word
import VerifiedGarbage.Proof.Ed25519.Canonical64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Spec.Ed25519
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Impl.Ed25519.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Step`. -/
section

/-! Short symbolic executions for four-word A64 arithmetic. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure Keeps (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keeps.trans {rs : List Reg} {s t u : State} (h : VG.Proof.Ed25519.AArch64.Keeps rs s t) (k : VG.Proof.Ed25519.AArch64.Keeps rs t u) :
    VG.Proof.Ed25519.AArch64.Keeps rs s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.mem.trans h.mem,
    k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp⟩

theorem Keeps.mono {rs rs' : List Reg} {s t : State} (h : VG.Proof.Ed25519.AArch64.Keeps rs s t)
    (inc : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Ed25519.AArch64.Keeps rs' s t :=
  ⟨fun r hr => h.gpr r (fun hmem => hr (inc r hmem)), h.mem, h.rd, h.wr, h.sp⟩

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

theorem mulStep_ok (s : State) {t c ai b : Reg} (hz : s.gpr .x10 = 0)
    (ht8 : t ≠ .x8) (ht2 : t ≠ .x2) (ht10 : t ≠ .x10)
    (hc8 : c ≠ .x8) (hc2 : c ≠ .x2)
    (ha8 : ai ≠ .x8) (hb8 : b ≠ .x8) (htc : t ≠ c) :
    WP isa (.block (mulStep t c ai b)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * (s.gpr b).toNat ∧
      VG.Proof.Ed25519.AArch64.Keeps [t, c, .x8, .x2] s s' := by
  apply WP.of_runBlock
  simp only [mulStep, mov, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    ht8, ht2, hc8, hc2, ha8, hb8, Ne.symm ht2, Ne.symm ht10, htc, Ne.symm htc,
    hz, Bool.toNat_false, Nat.add_zero, BitVec.add_zero, show (0 : Nat) < 4096 by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simpa only [Word64.addCarry, Word64.carryOut, Bool.toNat_false,
      Nat.add_zero, BitVec.add_zero] using
      Word64.multiply_accumulate (s.gpr ai) (s.gpr b) (s.gpr c) (s.gpr t)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ VG.Proof.Ed25519.AArch64.Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Mem`. -/
section

/-!
# Ed25519 on AArch64: field elements in the working space

The working space is 8 KiB at `base`, which `x0` holds (`Scr`); a field
element is the four words at an offset of it (`fe`), read as an element of
`GF(p)` by `F`.
-/

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}


open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The working space: `x0` holds its base `base`, it is writable and it
does not wrap around. -/
abbrev workSize (large : Bool) : Nat := if large then 8192 else 4096

theorem workSize_le (large : Bool) : VG.Proof.Ed25519.AArch64.workSize large ≤ 8192 := by cases large <;> decide

theorem workSize_ge (large : Bool) : 4096 ≤ VG.Proof.Ed25519.AArch64.workSize large := by cases large <;> decide

structure Scr (s : State) (base : Addr) (large : Bool := true) : Prop where
  x0 : s.gpr .x0 = base
  wr : (⟨base, VG.Proof.Ed25519.AArch64.workSize large⟩ : Region) ∈ s.wr
  nowrap : base.toNat + VG.Proof.Ed25519.AArch64.workSize large ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (VG.Proof.Ed25519.AArch64.off base d) 64

/-- The field element at `base + o`: four little-endian words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat :=
  val4 (VG.Proof.Ed25519.AArch64.word m base o) (VG.Proof.Ed25519.AArch64.word m base (o + 8)) (VG.Proof.Ed25519.AArch64.word m base (o + 16)) (VG.Proof.Ed25519.AArch64.word m base (o + 24))

theorem contains_scWith {base : Addr} {d n : Nat} (h : d + n ≤ VG.Proof.Ed25519.AArch64.workSize large) :
    (⟨base, VG.Proof.Ed25519.AArch64.workSize large⟩ : Region).Contains (VG.Proof.Ed25519.AArch64.off base d) n :=
  Offset.contains_base base h (by have := VG.Proof.Ed25519.AArch64.workSize_le large; omega)

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (VG.Proof.Ed25519.AArch64.off base d) n := VG.Proof.Ed25519.AArch64.contains_scWith (large := true) h

theorem load_sc {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ VG.Proof.Ed25519.AArch64.workSize large) (r : Reg) :
    exec (ld r d) s = some (s.write .x r (VG.Proof.Ed25519.AArch64.word s.mem base d)) := by
  have _hcap := VG.Proof.Ed25519.AArch64.workSize_le large
  have _hmin := VG.Proof.Ed25519.AArch64.workSize_ge large
  rw [ld, exec_ldr_x ⟨ha, by omega⟩]
  · rw [hs.x0]
  · rw [hs.x0]
    exact ⟨_, List.mem_append_right _ hs.wr, VG.Proof.Ed25519.AArch64.contains_scWith (large := large) hd⟩

theorem store_sc {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ VG.Proof.Ed25519.AArch64.workSize large) (r : Reg) :
    exec (st r d) s = some { s with mem := s.mem.writeW (VG.Proof.Ed25519.AArch64.off base d) (s.gpr r) } := by
  have _hcap := VG.Proof.Ed25519.AArch64.workSize_le large
  have _hmin := VG.Proof.Ed25519.AArch64.workSize_ge large
  rw [st, exec_str_x ⟨ha, by omega⟩]
  · rw [hs.x0]
  · rw [hs.x0]
    exact ⟨_, hs.wr, VG.Proof.Ed25519.AArch64.contains_scWith (large := large) hd⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large)
    (h : VG.Proof.Ed25519.AArch64.Keeps rs s s') (hr : .x0 ∉ rs) : VG.Proof.Ed25519.AArch64.Scr s' base large :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Scr.write {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large)
    {r : Reg} (hr : r ≠ .x0) (v : BitVec 64) : VG.Proof.Ed25519.AArch64.Scr (s.write .x r v) base large :=
  ⟨(RegUpd.gpr_write_of_ne s .x v (Ne.symm hr)).trans hs.x0, hs.wr, hs.nowrap⟩

theorem Scr.setMem {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) (m : Mem) :
    VG.Proof.Ed25519.AArch64.Scr { s with
                 mem := m } base large := ⟨hs.x0, hs.wr, hs.nowrap⟩

/-! ## Stores and frames -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.ofs base (VG.Proof.Ed25519.AArch64.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.Ed25519.AArch64.ofs, VG.Proof.Ed25519.AArch64.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.Ed25519.AArch64.ofs base (VG.Proof.Ed25519.AArch64.off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.Ed25519.AArch64.ofs base x < o ∨ o + n ≤ VG.Proof.Ed25519.AArch64.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.Ed25519.AArch64.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Ed25519.AArch64.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.Ed25519.AArch64.Outside base o n m₂ m₃) : VG.Proof.Ed25519.AArch64.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.Ed25519.AArch64.Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : VG.Proof.Ed25519.AArch64.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Ed25519.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : VG.Proof.Ed25519.AArch64.word m' base d = VG.Proof.Ed25519.AArch64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.Ed25519.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Ed25519.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 32 ≤ o ∨ o + n ≤ d) (hd' : d + 32 < 2 ^ 64) : VG.Proof.Ed25519.AArch64.fe m' base d = VG.Proof.Ed25519.AArch64.fe m base d := by
  simp only [AArch64.fe]
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega), h.word (by omega) (by omega),
    h.word (by omega) (by omega)]

/-- Four words stored at `base + o`. -/
def st4 (m : Mem) (base : Addr) (o : Nat) (w0 w1 w2 w3 : BitVec 64) : Mem :=
  (((m.writeW (VG.Proof.Ed25519.AArch64.off base o) w0).writeW (VG.Proof.Ed25519.AArch64.off base (o + 8)) w1).writeW (VG.Proof.Ed25519.AArch64.off base (o + 16)) w2).writeW
    (VG.Proof.Ed25519.AArch64.off base (o + 24)) w3

theorem sep_off (base : Addr) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : Mem.Sep (VG.Proof.Ed25519.AArch64.off base d) (64 / 8) (VG.Proof.Ed25519.AArch64.off base e) (64 / 8) :=
  Offset.sep base h hd he

theorem fe_st4 (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    VG.Proof.Ed25519.AArch64.fe (VG.Proof.Ed25519.AArch64.st4 m base o w0 w1 w2 w3) base o = val4 w0 w1 w2 w3 := by
  simp only [AArch64.fe, AArch64.word, VG.Proof.Ed25519.AArch64.st4]
  rw [Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64, Mem.readW_writeW_self64]

theorem write_outside (m : Mem) (base : Addr) {d o : Nat} (v : BitVec 64) (h1 : o ≤ d)
    (h2 : d + 8 ≤ o + 32) (h3 : o + 32 < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.Ed25519.AArch64.ofs base x < o ∨ o + 32 ≤ VG.Proof.Ed25519.AArch64.ofs base x) : (m.writeW (VG.Proof.Ed25519.AArch64.off base d) v) x = m x := by
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.Ed25519.AArch64.ofs] at hx
  omega

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 < 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.Outside base d 8 m (m.writeW (VG.Proof.Ed25519.AArch64.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.Ed25519.AArch64.ofs] at hx
  omega

theorem st4_outside (m : Mem) (base : Addr) {o : Nat} (ho : o + 32 < 2 ^ 64) (w0 w1 w2 w3 : BitVec 64) :
    VG.Proof.Ed25519.AArch64.Outside base o 32 m (VG.Proof.Ed25519.AArch64.st4 m base o w0 w1 w2 w3) := by
  intro x hx
  simp only [VG.Proof.Ed25519.AArch64.st4]
  rw [VG.Proof.Ed25519.AArch64.write_outside _ _ _ (by omega) (by omega) ho hx, VG.Proof.Ed25519.AArch64.write_outside _ _ _ (by omega) (by omega) ho hx,
    VG.Proof.Ed25519.AArch64.write_outside _ _ _ (by omega) (by omega) ho hx, VG.Proof.Ed25519.AArch64.write_outside _ _ _ (by omega) (by omega) ho hx]

/-- An aligned field element inside the workspace. -/
def FieldRange (o : Nat) (large : Bool := true) : Prop := o % 8 = 0 ∧ o + 32 ≤ VG.Proof.Ed25519.AArch64.workSize large

theorem stores_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {o : Nat} (ho : VG.Proof.Ed25519.AArch64.FieldRange o large)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun s' =>
      s' = { s with mem := VG.Proof.Ed25519.AArch64.st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) } := by
  have _hcap := VG.Proof.Ed25519.AArch64.workSize_le large
  have _hmin := VG.Proof.Ed25519.AArch64.workSize_ge large
  obtain ⟨ha, hb⟩ := ho
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Ed25519.AArch64.store_sc hs ha (by omega),
    VG.Proof.Ed25519.AArch64.store_sc (hs.setMem _) (show (o + 8) % 8 = 0 by omega) (by omega),
    VG.Proof.Ed25519.AArch64.store_sc (hs.setMem _) (show (o + 16) % 8 = 0 by omega) (by omega),
    VG.Proof.Ed25519.AArch64.store_sc (hs.setMem _) (show (o + 24) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  rfl

theorem store4_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {o : Nat} (ho : VG.Proof.Ed25519.AArch64.FieldRange o large) :
    WP isa (.block (store4 o)) s fun s' =>
      s' = { s with mem := VG.Proof.Ed25519.AArch64.st4 s.mem base o (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := VG.Proof.Ed25519.AArch64.stores_ok hs ho _ _ _ _

theorem ld_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ VG.Proof.Ed25519.AArch64.workSize large) (r : Reg) :
    WP isa (.block [ld r d]) s fun s' =>
      s'.gpr r = VG.Proof.Ed25519.AArch64.word s.mem base d ∧ VG.Proof.Ed25519.AArch64.Keeps [r] s s' := by
  have _hcap := VG.Proof.Ed25519.AArch64.workSize_le large
  have _hmin := VG.Proof.Ed25519.AArch64.workSize_ge large
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, VG.Proof.Ed25519.AArch64.load_sc hs ha hd,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (RegUpd.gpr_write_self s .x r _).trans (BitVec.setWidth_eq _)
  · intro r' hr
    exact RegUpd.gpr_write_of_ne s .x _ (by simpa only [List.mem_singleton] using hr)

theorem loads_ok {s : State} {base : Addr} (hs : VG.Proof.Ed25519.AArch64.Scr s base large) {o : Nat} (ho : VG.Proof.Ed25519.AArch64.FieldRange o large)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (loads o a b c d)) s fun t =>
      t.gpr a = VG.Proof.Ed25519.AArch64.word s.mem base o ∧ t.gpr b = VG.Proof.Ed25519.AArch64.word s.mem base (o + 8) ∧
      t.gpr c = VG.Proof.Ed25519.AArch64.word s.mem base (o + 16) ∧ t.gpr d = VG.Proof.Ed25519.AArch64.word s.mem base (o + 24) ∧
      VG.Proof.Ed25519.AArch64.Keeps [a, b, c, d] s t := by
  have _hcap := VG.Proof.Ed25519.AArch64.workSize_le large
  have _hmin := VG.Proof.Ed25519.AArch64.workSize_ge large
  obtain ⟨halign, hbound⟩ := ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, ha0⟩, ⟨hbc, hbd, hb0⟩, ⟨hcd, hc0⟩, ⟨hd0, _⟩⟩ := hd
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.Ed25519.AArch64.load_sc hs halign (by omega),
    VG.Proof.Ed25519.AArch64.load_sc (hs.write ha0 _) (show (o + 8) % 8 = 0 by omega) (by omega),
    VG.Proof.Ed25519.AArch64.load_sc ((hs.write ha0 _).write hb0 _) (show (o + 16) % 8 = 0 by omega) (by omega),
    VG.Proof.Ed25519.AArch64.load_sc (((hs.write ha0 _).write hb0 _).write hc0 _) (show (o + 24) % 8 = 0 by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, had, hac, hab, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hbd, hbc, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write, hcd, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem read_byte (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem Outside.writeW {base : Addr} {o n d : Nat} {m m' : Mem} (h : VG.Proof.Ed25519.AArch64.Outside base o n m m')
    (h₁ : o ≤ d) (h₂ : d + 8 ≤ o + n) (h₃ : o + n < 2 ^ 64) (v : BitVec 64) :
    VG.Proof.Ed25519.AArch64.Outside base o n m (m'.writeW (VG.Proof.Ed25519.AArch64.off base d) v) :=
  h.trans ((VG.Proof.Ed25519.AArch64.writeW_outside m' base v (by omega)).mono h₁ h₂)

theorem word_writeW_sep (m : Mem) (base : Addr) {d e : Nat} (v : BitVec 64)
    (h : e + 8 ≤ d ∨ d + 8 ≤ e) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    VG.Proof.Ed25519.AArch64.word (m.writeW (VG.Proof.Ed25519.AArch64.off base d) v) base e = VG.Proof.Ed25519.AArch64.word m base e :=
  Mem.readW_writeW_sep (VG.Proof.Ed25519.AArch64.sep_off base h he hd) (by decide)

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    VG.Proof.Ed25519.AArch64.word (m.writeW (VG.Proof.Ed25519.AArch64.off base d) v) base d = v := Mem.readW_writeW_self64 m _ v

theorem write64_eq_writeW (m : Mem) (a : Addr) (v : BitVec 64) :
    m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Codec`. -/
section

/-! The four-word output representation and its memory frame. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 Word64 VG.Proof.X25519

theorem bytesAt_st4 (m : Mem) (q : Addr) (w0 w1 w2 w3 : BitVec 64) :
    Spec.X25519.bytesAt (VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3) q 32 = leBytes 32 (val4 w0 w1 w2 w3) := by
  have e : ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (VG.Proof.Ed25519.AArch64.off q 0) 64).toNat +
      2 ^ 64 * ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).toNat +
      2 ^ 128 * ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).toNat +
      2 ^ 192 * ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).toNat = val4 w0 w1 w2 w3 :=
    VG.Proof.Ed25519.AArch64.fe_st4 m q (by decide) w0 w1 w2 w3
  rw [show VG.Proof.Ed25519.AArch64.off q 0 = q from BitVec.add_zero q] at e
  have := ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW q 64).isLt
  have := ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 8) 64).isLt
  have := ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 16) 64).isLt
  have := ((VG.Proof.Ed25519.AArch64.st4 m q 0 w0 w1 w2 w3).readW (q + 24) 64).isLt
  exact bytesAt_leBytes_words64 _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem scalarSave_frame {base : Addr} {m m' : Mem} (h : VG.Proof.Ed25519.AArch64.Outside base 0 48 m m') :
    Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  simp only [VG.Proof.Ed25519.AArch64.ofs]
  omega

theorem bytesAt_frame {m m' : Mem} {p base : Addr} (hf : Frame [⟨base, 8192⟩] m m')
    (hd : (⟨p, 64⟩ : Region).Disjoint ⟨base, 8192⟩) :
    Spec.Ed25519.bytesAt m' p 64 = Spec.Ed25519.bytesAt m p 64 := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, 64⟩) (by simpa only [List.mem_singleton, forall_eq])
    (by change 64 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = leBytes n x := by
  simp only [Spec.Ed25519.encodeLE, leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarStep`. -/
section

/-! The conditional subtraction of the Ed25519 order from a four-word value. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

def scalarValue (s : State) : Nat := val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
def savedValue (s : State) : Nat := val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem order_limbs : val4 orderLo orderHi 0 orderTop = L := by decide

theorem subtract_chain (a b c d : Word) :
    let c0 := carryOut a (~~~orderLo) true
    let c1 := carryOut b (~~~orderHi) c0
    let c2 := carryOut c (~~~0) c1
    let c3 := carryOut d (~~~orderTop) c2
    let v := val4 (addCarry a (~~~orderLo) true) (addCarry b (~~~orderHi) c0)
      (addCarry c (~~~0) c1) (addCarry d (~~~orderTop) c2)
    c3 = decide (L ≤ val4 a b c d) ∧
      v + L = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
  intro c0 c1 c2 c3 v
  have e : v + val4 orderLo orderHi 0 orderTop = val4 a b c d + 2 ^ 256 * (1 - c3.toNat) := by
    simpa only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] using
      sub4_value a b c d orderLo orderHi 0 orderTop true
  rw [VG.Proof.Ed25519.AArch64.order_limbs] at e
  have hv : v < 2 ^ 256 := val4_lt _ _ _ _
  have hx := val4_lt a b c d
  clear_value v c3 c2 c1 c0
  refine ⟨?_, e⟩
  cases c3 <;> simp only [Bool.toNat_false, Bool.toNat_true] at e
  · exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

theorem scalarSubtract_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSubtract) s fun t =>
      t.c = decide (L ≤ VG.Proof.Ed25519.AArch64.scalarValue s) ∧
      VG.Proof.Ed25519.AArch64.scalarValue t + L = VG.Proof.Ed25519.AArch64.scalarValue s + 2 ^ 256 * (1 - (decide (L ≤ VG.Proof.Ed25519.AArch64.scalarValue s)).toNat) ∧
      VG.Proof.Ed25519.AArch64.savedValue t = VG.Proof.Ed25519.AArch64.scalarValue s ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x3, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSubtract, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, mov, exec, VG.Proof.Ed25519.AArch64.read_x,
    show (0 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    VG.Proof.Ed25519.AArch64.scalarValue, VG.Proof.Ed25519.AArch64.savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    RegUpd.c_write, RegUpd.c_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    hz, ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  have H := VG.Proof.Ed25519.AArch64.subtract_chain (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  refine ⟨?_, ?_, True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · dsimp only [addCarry, carryOut, Size.bits, VG.Proof.Ed25519.AArch64.scalarValue] at H ⊢
    exact H.1
  · dsimp only [addCarry, carryOut, Size.bits, VG.Proof.Ed25519.AArch64.scalarValue] at H ⊢
    exact H.2.trans (congrArg (fun c : Bool =>
      val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 2 ^ 256 * (1 - c.toNat)) H.1)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem carry_mask (c : Bool) : addCarry 0 (~~~0) c = mask (!c) := by
  cases c <;> decide

theorem scalarSelect_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarSelect) s fun t =>
      VG.Proof.Ed25519.AArch64.scalarValue t = (if !s.c then VG.Proof.Ed25519.AArch64.savedValue s else VG.Proof.Ed25519.AArch64.scalarValue s) ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x8, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [scalarSelect, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    VG.Proof.Ed25519.AArch64.scalarValue, VG.Proof.Ed25519.AArch64.savedValue, RegUpd.gpr_write, RegUpd.gpr_addWithCarry,
    BitVec.setWidth_eq, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have hm := VG.Proof.Ed25519.AArch64.carry_mask s.c
  dsimp only [addCarry] at hm
  simp only [hm, xor_sel']
  refine ⟨by cases s.c <;> rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem select_remainder (x y : Nat) (hx : x < 2 * L)
    (he : y + L = x + 2 ^ 256 * (1 - (decide (L ≤ x)).toNat)) :
    (if L ≤ x then y else x) = x % L := by
  by_cases h : L ≤ x
  · simp only [h, decide_true, Bool.toNat_true, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_left h, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord`. -/
section

/-! Merged from `Proof.Ed25519.ScalarWord`. -/
section
/-!
# Ed25519 scalar arithmetic: reduction a word at a time

Untrusted and target-independent. With `L = 2^252 + c`, a remainder `r < L`
and the next 64-bit word `w` give `v = 2^64 r + w = h 2^252 + l`; then
`l + L - h c` is below `2L` and congruent to `v` modulo `L` (`fold_nat`), so
one conditional subtraction of `L` finishes the step. The input is consumed
from its top word down (`words_step`, `mod_step`).
-/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

/-- `L - 2^252`. -/
def cL : Nat := 27742317777372353535851937790883648493

theorem L_eq : L = 2 ^ 252 + VG.Proof.Ed25519.cL := by decide

/-- One word folded in: `l + L - h c` is below `2L` and congruent to `v = 2^64 r + w`. -/
theorem fold_nat (r w : Nat) (hr : r < L) (hw : w < 2 ^ 64) :
    (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.cL < L ∧
    (r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.cL) < 2 * L ∧
    ((r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * VG.Proof.Ed25519.cL)) % L =
      (r * 2 ^ 64 + w) % L := by
  rw [VG.Proof.Ed25519.L_eq] at hr ⊢
  generalize hv : r * 2 ^ 64 + w = v
  have hv' : v < 2 ^ 317 := by rw [← hv]; simp only [VG.Proof.Ed25519.cL] at hr; omega
  have hh : v / 2 ^ 252 < 2 ^ 65 := by omega
  have hc : v / 2 ^ 252 * VG.Proof.Ed25519.cL < 2 ^ 65 * VG.Proof.Ed25519.cL := Nat.mul_lt_mul_of_pos_right hh (by decide)
  have hd := Nat.div_add_mod v (2 ^ 252)
  simp only [VG.Proof.Ed25519.cL] at hc ⊢
  refine ⟨by omega, by omega, ?_⟩
  generalize v / 2 ^ 252 = h at hc hd
  generalize v % 2 ^ 252 = l at hd ⊢
  subst hd
  have e : l + (2 ^ 252 + 27742317777372353535851937790883648493 -
      h * 27742317777372353535851937790883648493) +
      h * (2 ^ 252 + 27742317777372353535851937790883648493) =
      2 ^ 252 * h + l + (2 ^ 252 + 27742317777372353535851937790883648493) := by
    rw [Nat.mul_add]; omega
  rw [← Nat.add_mul_mod_self_right _ h, e, Nat.add_mod_right]

/-- A remainder taken before the next word is shifted in. -/
theorem mod_step (a w : Nat) : (a % L * 2 ^ 64 + w) % L = (w + 2 ^ 64 * a) % L := by
  have hd := Nat.mod_add_div a L
  generalize a % L = r at hd ⊢
  generalize a / L = q at hd
  subst hd
  rw [← Nat.add_mul_mod_self_left (r * 2 ^ 64 + w) L (q * 2 ^ 64)]
  congr 1
  rw [Nat.mul_add, Nat.add_comm w, Nat.add_assoc, Nat.add_comm w, ← Nat.add_assoc,
    Nat.mul_comm (2 ^ 64) r, Nat.mul_left_comm (2 ^ 64) L q, Nat.mul_comm (2 ^ 64) q,
    ← Nat.mul_assoc]

/-- The 64-byte input from word `k` up: that word, and `2^64` times the words above it. -/
theorem words_step (m : Mem) (p : Addr) (k : Nat) (hk : k < 8) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (64 - 8 * (k + 1))) := by
  have e : 64 - 8 * k = 8 + (64 - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (64 - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (64 - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  have hl : (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8).length = 8 := by
    simp only [bytesAt, List.length_map, List.length_range]
  rw [e, hs, decodeLE_append, hl, hw, ha]

/-- `h₀ = r₂ >> 60 | 16 r₃`: the two parts have no bits in common. -/
theorem or_mul16 {a b : Nat} (h : a < 2 ^ 4) : a ||| 16 * b = a + 16 * b := by
  rw [show 16 * b = b * 2 ^ 4 by omega, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

/-- A four-word subtraction `L - T`, for `T < L`, cannot borrow. -/
theorem eq_sub_of_chain {u T c : Nat} (hu : u < 2 ^ 256) (hT : T < L)
    (e : u + T = L + 2 ^ 256 * c) : u = L - T := by
  have := order_bound
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

/-- A four-word sum below `2^256` does not carry out. -/
theorem eq_of_chain {u x c : Nat} (hx : x < 2 ^ 256) (e : u + 2 ^ 256 * c = x) : u = x := by
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

end VG.Proof.Ed25519
end

/-!
# Ed25519 scalar reduction: one word on AArch64

`wordFold` turns the remainder `r < L` and the next word `w` into `l + L - h
c` for `2^64 r + w = h 2^252 + l`, with `L = 2^252 + c`: below `2L` and
congruent to `2^64 r + w` modulo `L` (`fold_nat`). Each of its blocks is
checked against the numbers it computes.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64
open VG.Spec.Ed25519 (L)

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = VG.Proof.Ed25519.cL := by decide

theorem orderHi_lt : orderHi.toNat < 2 ^ 61 := by decide

theorem shr_or_shl (a b : Word) :
    (a >>> 60 ||| b <<< 4).toNat = a.toNat / 2 ^ 60 + 16 * (b.toNat % 2 ^ 60) := by
  have ha : a.toNat / 2 ^ 60 < 2 ^ 4 := by have := a.isLt; omega
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, show b.toNat * 2 ^ 4 % 2 ^ 64 = 16 * (b.toNat % 2 ^ 60) by omega]
  exact VG.Proof.Ed25519.or_mul16 ha

theorem shl_shr (x : Word) : ((x <<< 4) >>> 4).toNat = x.toNat % 2 ^ 60 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem shr60 (x : Word) : (x >>> 60).toNat = x.toNat / 2 ^ 60 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem foldPrep_ok (s : State) :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .x12).toNat = (s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) ∧
      (t.gpr .x13).toNat = (s.gpr .x7).toNat / 2 ^ 60 ∧
      t.gpr .x4 = s.gpr .x3 ∧ t.gpr .x5 = s.gpr .x4 ∧ t.gpr .x6 = s.gpr .x5 ∧
      (t.gpr .x7).toNat = (s.gpr .x6).toNat % 2 ^ 60 ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x12, .x13, .x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldPrep, mov, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    show 60 < Size.x.bits from by decide, show 4 < Size.x.bits from by decide,
    show (0 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed25519.AArch64.shr_or_shl _ _, VG.Proof.Ed25519.AArch64.shr60 _, trivial, trivial, trivial, VG.Proof.Ed25519.AArch64.shl_shr _, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2,
    ite_false]

theorem foldConst_ok (s : State) :
    WP isa (.block foldConst) s fun t =>
      t.gpr .x8 = orderLo ∧ t.gpr .x17 = orderHi ∧ VG.Proof.Ed25519.AArch64.Keeps [.x8, .x17] s t := by
  rw [foldConst, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.const64_ok s .x8 orderLo) fun a ⟨a8, ka⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.const64_ok a .x17 orderHi) fun t ⟨t17, kt⟩ => ?_
  exact ⟨(kt.gpr .x8 (by decide)).trans a8, t17, (ka.mono (by decide)).trans (kt.mono (by decide))⟩

theorem umulh_toNat (a b : Word) :
    (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_ofNat]
  omega

/-- `x (c₀ + 2^64 c₁)` from `mul`, `umulh` and one add with carry, for `c₁ < 2^61`. -/
theorem mul2_value (x c0 c1 : Word) (hc1 : c1.toNat < 2 ^ 61) :
    (x * c0).toNat +
        2 ^ 64 * (addCarry (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false).toNat +
        2 ^ 128 * (addCarry (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
          (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)).toNat =
      x.toNat * c0.toNat + 2 ^ 64 * (x.toNat * c1.toNat) := by
  have hp1 : x.toNat * c1.toNat < 2 ^ 64 * 2 ^ 61 := Nat.mul_lt_mul'' x.isLt hc1
  have hA := VG.Proof.Ed25519.AArch64.umulh_toNat x c0
  have hC := VG.Proof.Ed25519.AArch64.umulh_toNat x c1
  have hB := BitVec.toNat_mul x c1
  have hD := BitVec.toNat_mul x c0
  have e1 := addCarry_value (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false
  have e2 := addCarry_value (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false)
  have hcy2 := Bool.toNat_le (carryOut (BitVec.ofNat 64 (x.toNat * c1.toNat / 2 ^ 64)) 0
    (carryOut (BitVec.ofNat 64 (x.toNat * c0.toNat / 2 ^ 64)) (x * c1) false))
  simp only [Bool.toNat_false, Nat.add_zero, show (0 : Word).toNat = 0 from rfl] at e1 e2
  omega

/-- A two-word sum that cannot carry out of its top word. -/
theorem add2_value (a0 a1 b0 b1 : Word) (h : a1.toNat + b1.toNat + 1 < 2 ^ 64) :
    (addCarry a0 b0 false).toNat + 2 ^ 64 * (addCarry a1 b1 (carryOut a0 b0 false)).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) := by
  have e1 := addCarry_value a0 b0 false
  have e2 := addCarry_value a1 b1 (carryOut a0 b0 false)
  have hcy := Bool.toNat_le (carryOut a0 b0 false)
  have hcy2 := Bool.toNat_le (carryOut a1 b1 (carryOut a0 b0 false))
  simp only [Bool.toNat_false, Nat.add_zero] at e1
  omega

theorem foldMul_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x15).toNat + 2 ^ 128 * (t.gpr .x16).toNat =
        (s.gpr .x12).toNat * VG.Proof.Ed25519.cL ∧ VG.Proof.Ed25519.AArch64.Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldMul, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have hc : (s.gpr .x12).toNat * VG.Proof.Ed25519.cL =
        (s.gpr .x12).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x12).toNat * orderHi.toNat) := by
      rw [← VG.Proof.Ed25519.AArch64.c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have H := VG.Proof.Ed25519.AArch64.mul2_value (s.gpr .x12) orderLo orderHi VG.Proof.Ed25519.AArch64.orderHi_lt
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [hc]
    exact H
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem mul_bit (h v : Word) (hh : h.toNat ≤ 1) : (h * v).toNat = h.toNat * v.toNat := by
  rw [BitVec.toNat_mul]
  rcases (by omega : h.toNat = 0 ∨ h.toNat = 1) with e | e <;> rw [e]
  · rw [Nat.zero_mul, Nat.zero_mod]
  · rw [Nat.one_mul]; exact Nat.mod_eq_of_lt v.isLt

theorem foldHigh_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (h1 : (s.gpr .x13).toNat ≤ 1) (h16 : (s.gpr .x16).toNat < 2 ^ 62) :
    WP isa (.block foldHigh) s fun t => t.gpr .x14 = s.gpr .x14 ∧
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x16).toNat =
        (s.gpr .x15).toNat + 2 ^ 64 * (s.gpr .x16).toNat + (s.gpr .x13).toNat * VG.Proof.Ed25519.cL ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x9, .x13, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldHigh, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have mx := VG.Proof.Ed25519.AArch64.mul_bit (s.gpr .x13) orderLo h1
    have my := VG.Proof.Ed25519.AArch64.mul_bit (s.gpr .x13) orderHi h1
    have hc : (s.gpr .x13).toNat * VG.Proof.Ed25519.cL =
        (s.gpr .x13).toNat * orderLo.toNat + 2 ^ 64 * ((s.gpr .x13).toNat * orderHi.toNat) := by
      rw [← VG.Proof.Ed25519.AArch64.c_limbs, Nat.mul_add, Nat.mul_left_comm]
    have hy : (s.gpr .x13).toNat * orderHi.toNat < 2 ^ 61 := by
      have := VG.Proof.Ed25519.AArch64.orderHi_lt
      rcases (by omega : (s.gpr .x13).toNat = 0 ∨ (s.gpr .x13).toNat = 1) with e | e <;>
        rw [e] <;> omega
    have H := VG.Proof.Ed25519.AArch64.add2_value (s.gpr .x15) (s.gpr .x16) (s.gpr .x13 * orderLo) (s.gpr .x13 * orderHi)
      (by rw [my]; omega)
    dsimp only [addCarry, carryOut, Size.bits] at H ⊢
    rw [H, mx, my, hc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem orderTop_movz : (0x1000 : BitVec 16).setWidth 64 <<< (16 * 3) = orderTop := by decide

theorem foldSub_ok (s : State) (h8 : s.gpr .x8 = orderLo) (h17 : s.gpr .x17 = orderHi)
    (hz : s.gpr .x10 = 0)
    (ht : (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat < L) :
    WP isa (.block foldSub) s fun t =>
      val4 (t.gpr .x14) (t.gpr .x15) (t.gpr .x16) (t.gpr .x9) =
        L - ((s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat) ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x9, .x14, .x15, .x16] s t := by
  apply WP.of_runBlock
  simp only [foldSub, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, h8, h17, hz, VG.Proof.Ed25519.AArch64.orderTop_movz, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := sub4_value orderLo orderHi 0 orderTop (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 true
    simp only [VG.Proof.Ed25519.AArch64.order_limbs, Bool.toNat_true, Nat.sub_self, Nat.add_zero] at e
    have hT : val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) 0 =
        (s.gpr .x14).toNat + 2 ^ 64 * (s.gpr .x15).toNat + 2 ^ 128 * (s.gpr .x16).toNat := by
      simp only [val4, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    rw [hT] at e
    dsimp only [addCarry, carryOut, Size.bits] at e ⊢
    exact VG.Proof.Ed25519.eq_sub_of_chain (val4_lt _ _ _ _) ht e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
      ite_false]

theorem foldAdd_ok (s : State)
    (hs : VG.Proof.Ed25519.AArch64.scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) < 2 ^ 256) :
    WP isa (.block foldAdd) s fun t =>
      VG.Proof.Ed25519.AArch64.scalarValue t = VG.Proof.Ed25519.AArch64.scalarValue s + val4 (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [foldAdd, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := add4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
      (s.gpr .x14) (s.gpr .x15) (s.gpr .x16) (s.gpr .x9) false
    simp only [Bool.toNat_false, Nat.add_zero] at e
    dsimp only [addCarry, carryOut, Size.bits, VG.Proof.Ed25519.AArch64.scalarValue] at e hs ⊢
    exact VG.Proof.Ed25519.eq_of_chain hs e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The registers `wordFold` changes. -/
def foldClob : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17]

theorem wordFold_ok (s : State) (hr : VG.Proof.Ed25519.AArch64.scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block wordFold) s fun t => VG.Proof.Ed25519.AArch64.scalarValue t < 2 * L ∧
      VG.Proof.Ed25519.AArch64.scalarValue t % L = (VG.Proof.Ed25519.AArch64.scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % L ∧
      VG.Proof.Ed25519.AArch64.Keeps VG.Proof.Ed25519.AArch64.foldClob s t := by
  have hw := (s.gpr .x3).isLt
  obtain ⟨hlt, hlt2, hmod⟩ := VG.Proof.Ed25519.fold_nat (VG.Proof.Ed25519.AArch64.scalarValue s) (s.gpr .x3).toNat hr hw
  have h0 := (s.gpr .x4).isLt; have h1 := (s.gpr .x5).isLt; have h2 := (s.gpr .x6).isLt
  have h3 : (s.gpr .x7).toNat < 2 ^ 61 := by
    have hL : L < 2 ^ 253 := by decide
    have := hr; simp only [VG.Proof.Ed25519.AArch64.scalarValue, val4] at this; omega
  have eh : (VG.Proof.Ed25519.AArch64.scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) / 2 ^ 252 =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60)) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.AArch64.scalarValue, val4]; omega
  have el : (VG.Proof.Ed25519.AArch64.scalarValue s * 2 ^ 64 + (s.gpr .x3).toNat) % 2 ^ 252 =
      (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat + 2 ^ 128 * (s.gpr .x5).toNat +
        2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.AArch64.scalarValue, val4]; omega
  rw [eh] at hlt hlt2 hmod
  rw [el] at hlt2 hmod
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldPrep_ok s) fun a ⟨a12, a13, a4, a5, a6, a7, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldConst_ok a) fun b ⟨b8, b17, kb⟩ => ?_
  have hzb : b.gpr .x10 = 0 := by
    rw [kb.gpr .x10 (by decide), ka.gpr .x10 (by decide)]; exact hz
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldMul_ok b b8 b17 hzb) fun c ⟨ct, kc⟩ => ?_
  have c13 : c.gpr .x13 = a.gpr .x13 := by
    rw [kc.gpr .x13 (by decide), kb.gpr .x13 (by decide)]
  have c12 : c.gpr .x12 = a.gpr .x12 := by
    rw [kc.gpr .x12 (by decide), kb.gpr .x12 (by decide)]
  have hb1 : (c.gpr .x13).toNat ≤ 1 := by rw [c13, a13]; omega
  have hb16 : (c.gpr .x16).toNat < 2 ^ 62 := by
    have : (b.gpr .x12).toNat * VG.Proof.Ed25519.cL < 2 ^ 64 * VG.Proof.Ed25519.cL :=
      Nat.mul_lt_mul_of_pos_right (b.gpr .x12).isLt (by decide)
    simp only [VG.Proof.Ed25519.cL] at this ct; omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldHigh_ok c ((kc.gpr .x8 (by decide)).trans b8)
    ((kc.gpr .x17 (by decide)).trans b17) hb1 hb16) fun d ⟨d14, dt, kd⟩ => ?_
  have hT : (d.gpr .x14).toNat + 2 ^ 64 * (d.gpr .x15).toNat + 2 ^ 128 * (d.gpr .x16).toNat =
      ((s.gpr .x6).toNat / 2 ^ 60 + 16 * ((s.gpr .x7).toNat % 2 ^ 60) +
        2 ^ 64 * ((s.gpr .x7).toNat / 2 ^ 60)) * VG.Proof.Ed25519.cL := by
    have b12 : b.gpr .x12 = a.gpr .x12 := kb.gpr .x12 (by decide)
    rw [d14, Nat.add_mul, ← a12, ← a13, ← c13, ← b12, Nat.mul_assoc]
    omega
  have d8 : d.gpr .x8 = orderLo := by
    rw [kd.gpr .x8 (by decide), kc.gpr .x8 (by decide)]; exact b8
  have d17 : d.gpr .x17 = orderHi := by
    rw [kd.gpr .x17 (by decide), kc.gpr .x17 (by decide)]; exact b17
  have dz : d.gpr .x10 = 0 := by
    rw [kd.gpr .x10 (by decide), kc.gpr .x10 (by decide)]; exact hzb
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldSub_ok d d8 d17 dz (by rw [hT]; exact hlt)) fun e ⟨eu, ke⟩ => ?_
  have hl : VG.Proof.Ed25519.AArch64.scalarValue e = (s.gpr .x3).toNat + 2 ^ 64 * (s.gpr .x4).toNat +
      2 ^ 128 * (s.gpr .x5).toNat + 2 ^ 192 * ((s.gpr .x6).toNat % 2 ^ 60) := by
    simp only [VG.Proof.Ed25519.AArch64.scalarValue, val4]
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide),
      ke.gpr .x7 (by decide), kd.gpr .x4 (by decide), kd.gpr .x5 (by decide),
      kd.gpr .x6 (by decide), kd.gpr .x7 (by decide), kc.gpr .x4 (by decide),
      kc.gpr .x5 (by decide), kc.gpr .x6 (by decide), kc.gpr .x7 (by decide),
      kb.gpr .x4 (by decide), kb.gpr .x5 (by decide), kb.gpr .x6 (by decide),
      kb.gpr .x7 (by decide), a4, a5, a6, a7]
  rw [hT] at eu
  refine WP.mono (VG.Proof.Ed25519.AArch64.foldAdd_ok e (by rw [hl, eu]; have := order_bound; omega)) fun t ⟨tv, kt⟩ => ?_
  refine ⟨by rw [tv, hl, eu]; exact hlt2, by rw [tv, hl, eu]; exact hmod, ?_⟩
  exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    ((kc.mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
    (kt.mono (by decide))

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.ScalarLoop`. -/
section
/-!
# Scalar reduction: the eight-word loop

The invariant is the value modulo L of the already consumed top words of the
little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

def wordRead : List Instr :=
  [.subImm .x .x19 .x19 8, .add .x .x9 .x1 .x19, .ldr .x .x3 .x9 0]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block VG.Proof.Ed25519.AArch64.wordRead) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .x3 = s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64 ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x19, .x9, .x3] s t := by
  have hn : s.gpr .x19 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [VG.Proof.Ed25519.AArch64.wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.Ed25519.AArch64.read_x, addr, State.load,
    Size.bytes, show (8 : Nat) < 4096 from by decide, show (0 : Nat) % 8 = 0 from rfl,
    show (0 : Nat) < 4096 * 8 from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2, ite_false]

/-- The registers the loop changes. -/
def scalarBodyClob : List Reg :=
  [.x19, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24]

theorem scalarWord_ok (s : State) (k : Nat)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hv : VG.Proof.Ed25519.AArch64.scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      VG.Proof.Ed25519.AArch64.scalarValue t = (VG.Proof.Ed25519.AArch64.scalarValue s * 2 ^ 64 +
        (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64).toNat) % L ∧
      VG.Proof.Ed25519.AArch64.Keeps VG.Proof.Ed25519.AArch64.scalarBodyClob s t := by
  rw [show scalarWord = VG.Proof.Ed25519.AArch64.wordRead ++ (wordFold ++ (scalarSubtract ++ scalarSelect)) by
    simp only [scalarWord, VG.Proof.Ed25519.AArch64.wordRead, List.append_assoc, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : VG.Proof.Ed25519.AArch64.scalarValue a = VG.Proof.Ed25519.AArch64.scalarValue s := by
    simp only [VG.Proof.Ed25519.AArch64.scalarValue, ka.gpr .x4 (by decide), ka.gpr .x5 (by decide),
      ka.gpr .x6 (by decide), ka.gpr .x7 (by decide)]
  have az : a.gpr .x10 = 0 := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.wordFold_ok a (av ▸ hv) az) fun b ⟨b2, bm, kb⟩ => ?_
  have bz : b.gpr .x10 = 0 := (kb.gpr .x10 (by decide)).trans az
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarSubtract_ok b bz) fun c ⟨cc, cu, csaved, kc⟩ => ?_
  have cz : c.gpr .x10 = 0 := (kc.gpr .x10 (by decide)).trans bz
  refine WP.mono (VG.Proof.Ed25519.AArch64.scalarSelect_ok c cz) fun t ⟨tv, kt⟩ => ?_
  have he := VG.Proof.Ed25519.AArch64.select_remainder (VG.Proof.Ed25519.AArch64.scalarValue b) (VG.Proof.Ed25519.AArch64.scalarValue c) b2 cu
  refine ⟨?_, ?_, (((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr .x19 (by decide), kc.gpr .x19 (by decide), kb.gpr .x19 (by decide)]
    exact ab
  · rw [cc, csaved] at tv
    have hs : VG.Proof.Ed25519.AArch64.scalarValue t = if L ≤ VG.Proof.Ed25519.AArch64.scalarValue b then VG.Proof.Ed25519.AArch64.scalarValue c else VG.Proof.Ed25519.AArch64.scalarValue b := by
      by_cases h : L ≤ VG.Proof.Ed25519.AArch64.scalarValue b <;> simpa only [h, decide_true, decide_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using tv
    rw [hs, he, bm, av, ax]

theorem scalar_counter_test : ∀ n < 8,
    (BitVec.ofNat 64 (8 * n) != 0) = decide (n ≠ 0) := by decide

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  counter : s.gpr .x19 = BitVec.ofNat 64 (8 * n)
  value : VG.Proof.Ed25519.AArch64.scalarValue s =
    decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L
  keeps : VG.Proof.Ed25519.AArch64.Keeps VG.Proof.Ed25519.AArch64.scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .x19 = 64) (hz : VG.Proof.Ed25519.AArch64.scalarValue s₀ = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hz0 : s₀.gpr .x10 = 0) :
    WP isa (.loop (.block scalarWord) (.nonzero .x .x19)) s₀ fun t =>
      VG.Proof.Ed25519.AArch64.scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .x1) 64) % L ∧
      VG.Proof.Ed25519.AArch64.Keeps VG.Proof.Ed25519.AArch64.scalarBodyClob s₀ t := by
  apply WP.loop (VG.Proof.Ed25519.AArch64.ScalarInv s₀) (n := 8)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 8 := by have := hi.bound; omega
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k hk
    have hv : VG.Proof.Ed25519.AArch64.scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    have hzs := (hi.keeps.gpr .x10 (by decide)).trans hz0
    refine WP.mono (VG.Proof.Ed25519.AArch64.scalarWord_ok s k hi.counter hread hv hzs) fun t ⟨htb, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : VG.Proof.Ed25519.AArch64.scalarValue t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [htv, hi.value, hp, hi.keeps.mem, VG.Proof.Ed25519.words_step _ _ k hk, Nat.succ_eq_add_one, VG.Proof.Ed25519.mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, VG.Proof.Ed25519.AArch64.read_x, htb, VG.Proof.Ed25519.AArch64.scalar_counter_test 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, VG.Proof.Ed25519.AArch64.read_x, htb, VG.Proof.Ed25519.AArch64.scalar_counter_test k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    rw [hz]
    rfl

end VG.Proof.Ed25519.AArch64
end

/-! Scalar reducer saves, restores, and output stores. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- The six used callee-saved registers occupy scratch bytes 0–47. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ rd ∈ saved, VG.Proof.Ed25519.AArch64.word m base rd.2 = g rd.1

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      VG.Proof.Ed25519.AArch64.Outside base 0 48 s.mem t.mem ∧ VG.Proof.Ed25519.AArch64.Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (VG.Proof.Ed25519.AArch64.off base d) 8 :=
    fun d hd => ⟨_, hw, VG.Proof.Ed25519.AArch64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.store, VG.Proof.Ed25519.AArch64.read_x, hc, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega), w 40 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  · change VG.Proof.Ed25519.AArch64.word _ base rd.2 = s.gpr rd.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    simp only [VG.Proof.Ed25519.AArch64.write64_eq_writeW]
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [VG.Proof.Ed25519.AArch64.word_writeW_sep, VG.Proof.Ed25519.AArch64.word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : VG.Proof.Ed25519.AArch64.Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ VG.Proof.Ed25519.AArch64.Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (VG.Proof.Ed25519.AArch64.off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, VG.Proof.Ed25519.AArch64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, VG.Proof.Ed25519.AArch64.word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x0 0, .str .x .x5 .x0 8, .str .x .x6 .x0 16, .str .x .x7 .x0 24]) s
      fun t => t = { s with mem := VG.Proof.Ed25519.AArch64.st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (VG.Proof.Ed25519.AArch64.off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, VG.Proof.Ed25519.AArch64.read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl

theorem scalarInit_ok (s : State) :
    WP isa (.block scalarInit) s fun t =>
      t.gpr .x19 = 64 ∧ VG.Proof.Ed25519.AArch64.scalarValue t = 0 ∧ t.gpr .x10 = 0 ∧
      VG.Proof.Ed25519.AArch64.Keeps [.x4, .x5, .x6, .x7, .x10, .x19] s t := by
  apply WP.of_runBlock
  simp only [scalarInit, zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    VG.Proof.Ed25519.AArch64.scalarValue, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Ops`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Carry`. -/
section
/-! Reduction of the carry above four 64-bit field limbs. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

private theorem carry38_word (c : Bool) :
    addCarry 0 0 c * 38 = BitVec.ofNat 64 (38 * c.toNat) := by
  cases c <;> decide

private theorem carry38_arith (a0 a1 a2 a3 v : VG.Proof.Ed25519.Word64.Word) (hv : v.toNat < 2 ^ 58) :
    let c0 := carryOut a0 v false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let c3 := carryOut a3 0 c2
    toFe (val4 (addCarry a0 v false + addCarry 0 0 c3 * 38)
      (addCarry a1 0 c0) (addCarry a2 0 c1) (addCarry a3 0 c2)) =
      toFe (val4 a0 a1 a2 a3 + v.toNat) := by
  intro c0 c1 c2 c3
  rw [carry38_word]
  apply foldCarry_field _ _ _ _ _ (val4_lt a0 a1 a2 a3) hv
  simpa only [val4, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, show (0 : VG.Proof.Ed25519.Word64.Word).toNat = 0 from rfl] using
    add4_value a0 a1 a2 a3 v 0 0 0 false

theorem carry38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hv : (s.gpr .x8).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      toFe (val4 (s'.gpr .x4) (s'.gpr .x5) (s'.gpr .x6) (s'.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + (s.gpr .x8).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp only [carry38, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := carry38_arith (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) hv
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Memory and register frames for field operations. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

def clob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x20, .x21, .x22, .x23, .x24]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base large) :
    Scr t base large := ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.fe {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) {d : Nat}
    (hd : d + 32 ≤ o ∨ o + 32 ≤ d) (hd' : FieldRange d large) : fe t.mem base d = fe s.mem base d :=
  h.mem.fe hd (by have := hd'.2; have := workSize_le large; omega)

theorem Op.of_store {base : Addr} {o : Nat} {s t : State} (ho : FieldRange o large) (h : Keeps clob s t)
    (a b c d : VG.Proof.Ed25519.Word64.Word) : Op base o s { t with
                                            mem := st4 t.mem base o a b c d } := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem]
  exact st4_outside _ _ (by have := ho.2; omega) _ _ _ _

theorem fieldInit_ok (s : State) (v : BitVec 16 := 38) :
    WP isa (.block [.movz .w .x10 0 0, .movz .w .x11 v 0]) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x11 = v.setWidth 64 ∧ Keeps [.x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]
    rfl
  · rw [RegUpd.gpr_write_self, BitVec.shiftLeft_zero, BitVec.setWidth_setWidth (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

theorem zero4_ok (s : State) :
    WP isa (.block zero4) s fun t =>
      t.gpr .x4 = 0 ∧ t.gpr .x5 = 0 ∧ t.gpr .x6 = 0 ∧ t.gpr .x7 = 0 ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [zero4, runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    RegUpd.gpr_write, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc`. -/
section

/-! Rows of a four-by-four word product with the words of one
operand in registers (`rowFirst`, `rowAcc`), and the instances the field
multiplication and reduction use. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- The high word of a product, as `umulh` computes it. -/
abbrev mulHi (a b : VG.Proof.Ed25519.Word64.Word) : VG.Proof.Ed25519.Word64.Word := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

theorem mul_lo_hi (a b : VG.Proof.Ed25519.Word64.Word) :
    (a * b).toNat + 2 ^ 64 * (VG.Proof.Ed25519.AArch64.mulHi a b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  have h1 : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  have h2 : (VG.Proof.Ed25519.AArch64.mulHi a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
    simp only [VG.Proof.Ed25519.AArch64.mulHi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  omega

theorem mul_le (a b : VG.Proof.Ed25519.Word64.Word) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

theorem mul_val4 (a b0 b1 b2 b3 : Nat) :
    a * (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) =
      a * b0 + 2 ^ 64 * (a * b1) + 2 ^ 128 * (a * b2) + 2 ^ 192 * (a * b3) := by
  simp only [Nat.mul_add, Nat.mul_left_comm a]

/-- The carry chains of `rowAcc`, on natural numbers: the low halves `L`
of the products `P` added to `T`, then the high halves `H` one word up. -/
theorem rowAcc_arith {T0 T1 T2 T3 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    S0 S1 S2 S3 U R1 R2 R3 R4 C0 C1 C2 C3 C4 D1 D2 D3 D4 : Nat}
    (e0 : S0 + 2 ^ 64 * C0 = T0 + L0 + 0) (e1 : S1 + 2 ^ 64 * C1 = T1 + L1 + C0)
    (e2 : S2 + 2 ^ 64 * C2 = T2 + L2 + C1) (e3 : S3 + 2 ^ 64 * C3 = T3 + L3 + C2)
    (e4 : U + 2 ^ 64 * C4 = 0 + 0 + C3)
    (f1 : R1 + 2 ^ 64 * D1 = S1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = S2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = S3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = U + H3 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (t0 : T0 < 2 ^ 64) (t1 : T1 < 2 ^ 64) (t2 : T2 < 2 ^ 64) (t3 : T3 < 2 ^ 64) :
    S0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      T0 + 2 ^ 64 * T1 + 2 ^ 128 * T2 + 2 ^ 192 * T3 +
        (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) := by
  omega

/-- What `rowAcc` computes, word by word. -/
theorem rowAcc_value (a b0 b1 b2 b3 t0 t1 t2 t3 : VG.Proof.Ed25519.Word64.Word) :
    let c0 := carryOut t0 (a * b0) false
    let c1 := carryOut t1 (a * b1) c0
    let c2 := carryOut t2 (a * b2) c1
    let c3 := carryOut t3 (a * b3) c2
    let s1 := addCarry t1 (a * b1) c0
    let s2 := addCarry t2 (a * b2) c1
    let s3 := addCarry t3 (a * b3) c2
    let u := addCarry 0 0 c3
    let d1 := carryOut s1 (VG.Proof.Ed25519.AArch64.mulHi a b0) false
    let d2 := carryOut s2 (VG.Proof.Ed25519.AArch64.mulHi a b1) d1
    let d3 := carryOut s3 (VG.Proof.Ed25519.AArch64.mulHi a b2) d2
    val4 (addCarry t0 (a * b0) false) (addCarry s1 (VG.Proof.Ed25519.AArch64.mulHi a b0) false)
        (addCarry s2 (VG.Proof.Ed25519.AArch64.mulHi a b1) d1) (addCarry s3 (VG.Proof.Ed25519.AArch64.mulHi a b2) d2) +
        2 ^ 256 * (addCarry u (VG.Proof.Ed25519.AArch64.mulHi a b3) d3).toNat =
      val4 t0 t1 t2 t3 + a.toNat * val4 b0 b1 b2 b3 := by
  intro c0 c1 c2 c3 s1 s2 s3 u d1 d2 d3
  simp only [val4]
  rw [VG.Proof.Ed25519.AArch64.mul_val4]
  exact VG.Proof.Ed25519.AArch64.rowAcc_arith (addCarry_value t0 (a * b0) false) (addCarry_value t1 (a * b1) c0)
    (addCarry_value t2 (a * b2) c1) (addCarry_value t3 (a * b3) c2) (addCarry_value 0 0 c3)
    (addCarry_value s1 (VG.Proof.Ed25519.AArch64.mulHi a b0) false) (addCarry_value s2 (VG.Proof.Ed25519.AArch64.mulHi a b1) d1)
    (addCarry_value s3 (VG.Proof.Ed25519.AArch64.mulHi a b2) d2) (addCarry_value u (VG.Proof.Ed25519.AArch64.mulHi a b3) d3)
    (VG.Proof.Ed25519.AArch64.mul_lo_hi a b0) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b1) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b2) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b3)
    (VG.Proof.Ed25519.AArch64.mul_le a b0) (VG.Proof.Ed25519.AArch64.mul_le a b1) (VG.Proof.Ed25519.AArch64.mul_le a b2) (VG.Proof.Ed25519.AArch64.mul_le a b3) t0.isLt t1.isLt t2.isLt t3.isLt

/-- The carry chain of `rowFirst`, on natural numbers. -/
theorem rowFirst_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 R1 R2 R3 R4 D1 D2 D3 D4 : Nat}
    (f1 : R1 + 2 ^ 64 * D1 = L1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = L2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = L3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 := by
  omega

/-- What `rowFirst` computes, word by word. -/
theorem rowFirst_value (a b0 b1 b2 b3 : VG.Proof.Ed25519.Word64.Word) :
    let d1 := carryOut (a * b1) (VG.Proof.Ed25519.AArch64.mulHi a b0) false
    let d2 := carryOut (a * b2) (VG.Proof.Ed25519.AArch64.mulHi a b1) d1
    let d3 := carryOut (a * b3) (VG.Proof.Ed25519.AArch64.mulHi a b2) d2
    val4 (a * b0) (addCarry (a * b1) (VG.Proof.Ed25519.AArch64.mulHi a b0) false)
        (addCarry (a * b2) (VG.Proof.Ed25519.AArch64.mulHi a b1) d1) (addCarry (a * b3) (VG.Proof.Ed25519.AArch64.mulHi a b2) d2) +
        2 ^ 256 * (addCarry (VG.Proof.Ed25519.AArch64.mulHi a b3) 0 d3).toNat =
      a.toNat * val4 b0 b1 b2 b3 := by
  intro d1 d2 d3
  simp only [val4]
  rw [VG.Proof.Ed25519.AArch64.mul_val4]
  exact VG.Proof.Ed25519.AArch64.rowFirst_arith (addCarry_value (a * b1) (VG.Proof.Ed25519.AArch64.mulHi a b0) false)
    (addCarry_value (a * b2) (VG.Proof.Ed25519.AArch64.mulHi a b1) d1) (addCarry_value (a * b3) (VG.Proof.Ed25519.AArch64.mulHi a b2) d2)
    (addCarry_value (VG.Proof.Ed25519.AArch64.mulHi a b3) 0 d3)
    (VG.Proof.Ed25519.AArch64.mul_lo_hi a b0) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b1) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b2) (VG.Proof.Ed25519.AArch64.mul_lo_hi a b3)
    (VG.Proof.Ed25519.AArch64.mul_le a b0) (VG.Proof.Ed25519.AArch64.mul_le a b1) (VG.Proof.Ed25519.AArch64.mul_le a b2) (VG.Proof.Ed25519.AArch64.mul_le a b3)

/-- Run a straight block of register arithmetic, reading registers through
the writes (literal registers decide each `if`). -/
macro "reg_exec" hz:term : tactic => `(tactic| (
  apply WP.of_runBlock
  simp only [rowAcc, rowFirst, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, $hz:term,
    Option.some.injEq, exists_eq_left']))

/-- The registers but those written are kept. -/
macro "reg_keeps" : tactic => `(tactic| (
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]))

theorem rowFirst_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowFirst .x3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * (t.gpr .x21).toNat =
        (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x4, .x5, .x6, .x7, .x21] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.rowFirst_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 1 of the product, `a₁ · b`, into x5–x7, x21–x22. -/
theorem rowAcc1_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x5 .x6 .x7 .x21 .x22)) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) + 2 ^ 256 * (t.gpr .x22).toNat =
        val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x5, .x6, .x7, .x21, .x22] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 2 of the product, into x6–x7, x21–x23. -/
theorem rowAcc2_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x6 .x7 .x21 .x22 .x23)) s fun t =>
      val4 (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) (t.gpr .x22) + 2 ^ 256 * (t.gpr .x23).toNat =
        val4 (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x6, .x7, .x21, .x22, .x23] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- Row 3 of the product, into x7, x21–x24. -/
theorem rowAcc3_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x3 .x12 .x13 .x14 .x15 .x7 .x21 .x22 .x23 .x24)) s fun t =>
      val4 (t.gpr .x7) (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) + 2 ^ 256 * (t.gpr .x24).toNat =
        val4 (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) +
          (s.gpr .x3).toNat * val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) ∧
      Keeps [.x2, .x8, .x9, .x16, .x7, .x21, .x22, .x23, .x24] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.rowAcc_value (s.gpr .x3) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- 38 times the high half of a product added to its low half: x4–x7 and x20. -/
theorem rowAccReduce_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (rowAcc .x11 .x21 .x22 .x23 .x24 .x4 .x5 .x6 .x7 .x20)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * (t.gpr .x20).toNat =
        val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
          (s.gpr .x11).toNat * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) ∧
      Keeps [.x2, .x8, .x9, .x16, .x4, .x5, .x6, .x7, .x20] s t := by
  reg_exec hz
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.rowAcc_value (s.gpr .x11) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows`. -/
section

/-! The three blocks of a four-word squaring (`sqrCross`,
`sqrDouble`, `sqrDiag`), each run once on its registers. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- The products `aᵢ aⱼ` (`i < j`) of four words, at word `i + j - 1`. -/
abbrev cross (a0 a1 a2 a3 : Nat) : Nat :=
  a0 * a1 + 2 ^ 64 * (a0 * a2) + 2 ^ 128 * (a0 * a3 + a1 * a2) + 2 ^ 192 * (a1 * a3) +
    2 ^ 256 * (a2 * a3)

/-- The squares `aᵢ²` of four words, at word `2 i`. -/
abbrev diag (a0 a1 a2 a3 : Nat) : Nat :=
  a0 * a0 + 2 ^ 128 * (a1 * a1) + 2 ^ 256 * (a2 * a2 + 2 ^ 128 * (a3 * a3))

/-- The carry chains of `sqrCross`, on natural numbers. -/
theorem sqrCross_arith {L01 L02 L03 L12 L13 L23 H01 H02 H03 H12 H13 H23
    P01 P02 P03 P12 P13 P23 S6 S7 S21 S7b S21b S22 S21c S22b S22c S23
    K7 K8 K9 K14 K15 K16 K17 K18 K21 K22 : Nat}
    (e7 : S6 + 2 ^ 64 * K7 = L02 + H01 + 0) (e8 : S7 + 2 ^ 64 * K8 = L03 + H02 + K7)
    (e9 : S21 + 2 ^ 64 * K9 = H03 + 0 + K8)
    (e14 : S7b + 2 ^ 64 * K14 = S7 + L12 + 0) (e15 : S21b + 2 ^ 64 * K15 = S21 + L13 + K14)
    (e16 : S22 + 2 ^ 64 * K16 = H13 + 0 + K15)
    (e17 : S21c + 2 ^ 64 * K17 = S21b + H12 + 0) (e18 : S22b + 2 ^ 64 * K18 = S22 + 0 + K17)
    (e21 : S22c + 2 ^ 64 * K21 = S22b + L23 + 0) (e22 : S23 + 2 ^ 64 * K22 = H23 + 0 + K21)
    (m01 : L01 + 2 ^ 64 * H01 = P01) (m02 : L02 + 2 ^ 64 * H02 = P02)
    (m03 : L03 + 2 ^ 64 * H03 = P03) (m12 : L12 + 2 ^ 64 * H12 = P12)
    (m13 : L13 + 2 ^ 64 * H13 = P13) (m23 : L23 + 2 ^ 64 * H23 = P23)
    (p01 : P01 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p02 : P02 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p03 : P03 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p12 : P12 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p13 : P13 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p23 : P23 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L01 + 2 ^ 64 * S6 + 2 ^ 128 * S7b + 2 ^ 192 * S21c + 2 ^ 256 * (S22c + 2 ^ 64 * S23) =
      P01 + 2 ^ 64 * P02 + 2 ^ 128 * (P03 + P12) + 2 ^ 192 * P13 + 2 ^ 256 * P23 := by
  omega

/-- What `sqrCross` computes, word by word. -/
theorem sqrCross_value (a0 a1 a2 a3 : VG.Proof.Ed25519.Word64.Word) :
    let k7 := carryOut (a0 * a2) (VG.Proof.Ed25519.AArch64.mulHi a0 a1) false
    let s7 := addCarry (a0 * a3) (VG.Proof.Ed25519.AArch64.mulHi a0 a2) k7
    let k8 := carryOut (a0 * a3) (VG.Proof.Ed25519.AArch64.mulHi a0 a2) k7
    let s21 := addCarry (VG.Proof.Ed25519.AArch64.mulHi a0 a3) 0 k8
    let k14 := carryOut s7 (a1 * a2) false
    let s21b := addCarry s21 (a1 * a3) k14
    let k15 := carryOut s21 (a1 * a3) k14
    let s22 := addCarry (VG.Proof.Ed25519.AArch64.mulHi a1 a3) 0 k15
    let k17 := carryOut s21b (VG.Proof.Ed25519.AArch64.mulHi a1 a2) false
    let s22b := addCarry s22 0 k17
    let k21 := carryOut s22b (a2 * a3) false
    val4 (a0 * a1) (addCarry (a0 * a2) (VG.Proof.Ed25519.AArch64.mulHi a0 a1) false) (addCarry s7 (a1 * a2) false)
        (addCarry s21b (VG.Proof.Ed25519.AArch64.mulHi a1 a2) false) +
        2 ^ 256 * ((addCarry s22b (a2 * a3) false).toNat +
          2 ^ 64 * (addCarry (VG.Proof.Ed25519.AArch64.mulHi a2 a3) 0 k21).toNat) =
      VG.Proof.Ed25519.AArch64.cross a0.toNat a1.toNat a2.toNat a3.toNat := by
  intro k7 s7 k8 s21 k14 s21b k15 s22 k17 s22b k21
  simp only [val4, VG.Proof.Ed25519.AArch64.cross]
  exact VG.Proof.Ed25519.AArch64.sqrCross_arith (addCarry_value (a0 * a2) (VG.Proof.Ed25519.AArch64.mulHi a0 a1) false)
    (addCarry_value (a0 * a3) (VG.Proof.Ed25519.AArch64.mulHi a0 a2) k7) (addCarry_value (VG.Proof.Ed25519.AArch64.mulHi a0 a3) 0 k8)
    (addCarry_value s7 (a1 * a2) false) (addCarry_value s21 (a1 * a3) k14)
    (addCarry_value (VG.Proof.Ed25519.AArch64.mulHi a1 a3) 0 k15)
    (addCarry_value s21b (VG.Proof.Ed25519.AArch64.mulHi a1 a2) false) (addCarry_value s22 0 k17)
    (addCarry_value s22b (a2 * a3) false) (addCarry_value (VG.Proof.Ed25519.AArch64.mulHi a2 a3) 0 k21)
    (VG.Proof.Ed25519.AArch64.mul_lo_hi a0 a1) (VG.Proof.Ed25519.AArch64.mul_lo_hi a0 a2) (VG.Proof.Ed25519.AArch64.mul_lo_hi a0 a3) (VG.Proof.Ed25519.AArch64.mul_lo_hi a1 a2)
    (VG.Proof.Ed25519.AArch64.mul_lo_hi a1 a3) (VG.Proof.Ed25519.AArch64.mul_lo_hi a2 a3)
    (VG.Proof.Ed25519.AArch64.mul_le a0 a1) (VG.Proof.Ed25519.AArch64.mul_le a0 a2) (VG.Proof.Ed25519.AArch64.mul_le a0 a3) (VG.Proof.Ed25519.AArch64.mul_le a1 a2) (VG.Proof.Ed25519.AArch64.mul_le a1 a3) (VG.Proof.Ed25519.AArch64.mul_le a2 a3)

theorem sqrCross_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block sqrCross) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) +
          2 ^ 256 * ((t.gpr .x22).toNat + 2 ^ 64 * (t.gpr .x23).toNat) =
        VG.Proof.Ed25519.AArch64.cross (s.gpr .x12).toNat (s.gpr .x13).toNat (s.gpr .x14).toNat (s.gpr .x15).toNat ∧
      Keeps [.x2, .x8, .x9, .x16, .x5, .x6, .x7, .x21, .x22, .x23] s t := by
  apply WP.of_runBlock
  simp only [sqrCross, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.sqrCross_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- The carry chain of `sqrDouble`, on natural numbers. -/
theorem sqrDouble_arith {W1 W2 W3 W4 W5 W6 R1 R2 R3 R4 R5 R6 R7 K1 K2 K3 K4 K5 K6 K7 : Nat}
    (w1 : W1 < 2 ^ 64) (w2 : W2 < 2 ^ 64) (w3 : W3 < 2 ^ 64) (w4 : W4 < 2 ^ 64)
    (w5 : W5 < 2 ^ 64) (w6 : W6 < 2 ^ 64)
    (e1 : R1 + 2 ^ 64 * K1 = W1 + W1 + 0) (e2 : R2 + 2 ^ 64 * K2 = W2 + W2 + K1)
    (e3 : R3 + 2 ^ 64 * K3 = W3 + W3 + K2) (e4 : R4 + 2 ^ 64 * K4 = W4 + W4 + K3)
    (e5 : R5 + 2 ^ 64 * K5 = W5 + W5 + K4) (e6 : R6 + 2 ^ 64 * K6 = W6 + W6 + K5)
    (e7 : R7 + 2 ^ 64 * K7 = 0 + 0 + K6) :
    R1 + 2 ^ 64 * R2 + 2 ^ 128 * R3 + 2 ^ 192 * R4 + 2 ^ 256 * (R5 + 2 ^ 64 * R6 + 2 ^ 128 * R7) =
      2 * (W1 + 2 ^ 64 * W2 + 2 ^ 128 * W3 + 2 ^ 192 * W4 + 2 ^ 256 * (W5 + 2 ^ 64 * W6)) := by
  omega

/-- What `sqrDouble` computes, word by word. -/
theorem sqrDouble_value (w1 w2 w3 w4 w5 w6 : VG.Proof.Ed25519.Word64.Word) :
    let k1 := carryOut w1 w1 false
    let k2 := carryOut w2 w2 k1
    let k3 := carryOut w3 w3 k2
    let k4 := carryOut w4 w4 k3
    let k5 := carryOut w5 w5 k4
    let k6 := carryOut w6 w6 k5
    val4 (addCarry w1 w1 false) (addCarry w2 w2 k1) (addCarry w3 w3 k2) (addCarry w4 w4 k3) +
        2 ^ 256 * ((addCarry w5 w5 k4).toNat + 2 ^ 64 * (addCarry w6 w6 k5).toNat +
          2 ^ 128 * (addCarry 0 0 k6).toNat) =
      2 * (val4 w1 w2 w3 w4 + 2 ^ 256 * (w5.toNat + 2 ^ 64 * w6.toNat)) := by
  intro k1 k2 k3 k4 k5 k6
  simp only [val4]
  exact VG.Proof.Ed25519.AArch64.sqrDouble_arith w1.isLt w2.isLt w3.isLt w4.isLt w5.isLt w6.isLt
    (addCarry_value w1 w1 false) (addCarry_value w2 w2 k1)
    (addCarry_value w3 w3 k2) (addCarry_value w4 w4 k3) (addCarry_value w5 w5 k4)
    (addCarry_value w6 w6 k5) (addCarry_value 0 0 k6)

theorem sqrDouble_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block sqrDouble) s fun t =>
      val4 (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) (t.gpr .x21) +
          2 ^ 256 * ((t.gpr .x22).toNat + 2 ^ 64 * (t.gpr .x23).toNat +
            2 ^ 128 * (t.gpr .x24).toNat) =
        2 * (val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          2 ^ 256 * ((s.gpr .x22).toNat + 2 ^ 64 * (s.gpr .x23).toNat)) ∧
      Keeps [.x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  apply WP.of_runBlock
  simp only [sqrDouble, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := VG.Proof.Ed25519.AArch64.sqrDouble_value (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22)
      (s.gpr .x23)
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

/-- The carry chain of `sqrDiag`, on natural numbers. -/
theorem sqrDiag_arith {W1 W2 W3 W4 W5 W6 W7 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    R1 R2 R3 R4 R5 R6 R7 K1 K2 K3 K4 K5 K6 K7 : Nat}
    (e1 : R1 + 2 ^ 64 * K1 = W1 + H0 + 0) (e2 : R2 + 2 ^ 64 * K2 = W2 + L1 + K1)
    (e3 : R3 + 2 ^ 64 * K3 = W3 + H1 + K2) (e4 : R4 + 2 ^ 64 * K4 = W4 + L2 + K3)
    (e5 : R5 + 2 ^ 64 * K5 = W5 + H2 + K4) (e6 : R6 + 2 ^ 64 * K6 = W6 + L3 + K5)
    (e7 : R7 + 2 ^ 64 * K7 = W7 + H3 + K6)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 +
        2 ^ 256 * (R4 + 2 ^ 64 * R5 + 2 ^ 128 * R6 + 2 ^ 192 * R7 + 2 ^ 256 * K7) =
      2 ^ 64 * (W1 + 2 ^ 64 * W2 + 2 ^ 128 * W3 + 2 ^ 192 * W4 +
        2 ^ 256 * (W5 + 2 ^ 64 * W6 + 2 ^ 128 * W7)) +
        (P0 + 2 ^ 128 * P1 + 2 ^ 256 * (P2 + 2 ^ 128 * P3)) := by
  omega

/-- What `sqrDiag` computes, word by word. -/
theorem sqrDiag_value (a0 a1 a2 a3 w1 w2 w3 w4 w5 w6 w7 : VG.Proof.Ed25519.Word64.Word) :
    let k1 := carryOut w1 (VG.Proof.Ed25519.AArch64.mulHi a0 a0) false
    let k2 := carryOut w2 (a1 * a1) k1
    let k3 := carryOut w3 (VG.Proof.Ed25519.AArch64.mulHi a1 a1) k2
    let k4 := carryOut w4 (a2 * a2) k3
    let k5 := carryOut w5 (VG.Proof.Ed25519.AArch64.mulHi a2 a2) k4
    let k6 := carryOut w6 (a3 * a3) k5
    val4 (a0 * a0) (addCarry w1 (VG.Proof.Ed25519.AArch64.mulHi a0 a0) false) (addCarry w2 (a1 * a1) k1)
        (addCarry w3 (VG.Proof.Ed25519.AArch64.mulHi a1 a1) k2) +
        2 ^ 256 * val4 (addCarry w4 (a2 * a2) k3) (addCarry w5 (VG.Proof.Ed25519.AArch64.mulHi a2 a2) k4)
          (addCarry w6 (a3 * a3) k5) (addCarry w7 (VG.Proof.Ed25519.AArch64.mulHi a3 a3) k6) +
        2 ^ 256 * (2 ^ 256 * (carryOut w7 (VG.Proof.Ed25519.AArch64.mulHi a3 a3) k6).toNat) =
      2 ^ 64 * (val4 w1 w2 w3 w4 + 2 ^ 256 * (w5.toNat + 2 ^ 64 * w6.toNat +
        2 ^ 128 * w7.toNat)) + VG.Proof.Ed25519.AArch64.diag a0.toNat a1.toNat a2.toNat a3.toNat := by
  intro k1 k2 k3 k4 k5 k6
  simp only [val4, VG.Proof.Ed25519.AArch64.diag]
  have h := VG.Proof.Ed25519.AArch64.sqrDiag_arith (addCarry_value w1 (VG.Proof.Ed25519.AArch64.mulHi a0 a0) false)
    (addCarry_value w2 (a1 * a1) k1) (addCarry_value w3 (VG.Proof.Ed25519.AArch64.mulHi a1 a1) k2)
    (addCarry_value w4 (a2 * a2) k3) (addCarry_value w5 (VG.Proof.Ed25519.AArch64.mulHi a2 a2) k4)
    (addCarry_value w6 (a3 * a3) k5) (addCarry_value w7 (VG.Proof.Ed25519.AArch64.mulHi a3 a3) k6)
    (VG.Proof.Ed25519.AArch64.mul_lo_hi a0 a0) (VG.Proof.Ed25519.AArch64.mul_lo_hi a1 a1) (VG.Proof.Ed25519.AArch64.mul_lo_hi a2 a2) (VG.Proof.Ed25519.AArch64.mul_lo_hi a3 a3)
  omega_using [h]

theorem sqrDiag_ok (s : State) :
    WP isa (.block sqrDiag) s fun t => ∃ c : Nat,
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
          2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) +
          2 ^ 256 * (2 ^ 256 * c) =
        2 ^ 64 * (val4 (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) +
          2 ^ 256 * ((s.gpr .x22).toNat + 2 ^ 64 * (s.gpr .x23).toNat +
            2 ^ 128 * (s.gpr .x24).toNat)) +
          VG.Proof.Ed25519.AArch64.diag (s.gpr .x12).toNat (s.gpr .x13).toNat (s.gpr .x14).toNat (s.gpr .x15).toNat ∧
      Keeps [.x2, .x3, .x8, .x9, .x11, .x16, .x17, .x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24]
        s t := by
  apply WP.of_runBlock
  simp only [sqrDiag, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have h := VG.Proof.Ed25519.AArch64.sqrDiag_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) (s.gpr .x5)
    (s.gpr .x6) (s.gpr .x7) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
  dsimp only [addCarry, carryOut, VG.Proof.Ed25519.AArch64.mulHi, Size.bits] at h ⊢
  refine ⟨_, h, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  reg_keeps

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Mul`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Row`. -/
section
/-! One row of a four-by-four word multiplication. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

/-- One loaded operand and a multiply-accumulate step. -/
theorem mulLoad_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0)
    {d : Nat} (ha : d % 8 = 0) (hd : d + 8 ≤ workSize large) {t : Reg}
    (ht8 : t ≠ .x8) (ht2 : t ≠ .x2) (ht10 : t ≠ .x10)
    (ht20 : t ≠ .x20) (ht9 : t ≠ .x9) :
    WP isa (.block (([ld .x9 d] : List Instr) ++ mulStep t .x20 .x3 .x9)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr .x20).toNat =
        (s.gpr t).toNat + (s.gpr .x20).toNat + (s.gpr .x3).toNat * (word s.mem base d).toNat ∧
      Keeps [t, .x20, .x8, .x2, .x9] s s' := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs ha hd .x9) fun s₁ ⟨v1, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  refine WP.mono (mulStep_ok s₁ hz1 ht8 ht2 ht10 (by decide) (by decide)
    (by decide) (by decide) ht20) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, ?_⟩
  · rw [v1, k1.gpr t (by simpa only [List.mem_singleton] using ht9),
      k1.gpr .x20 (by decide), k1.gpr .x3 (by decide)] at e2
    exact e2
  · have h1 : Keeps [t, .x20, .x8, .x2, .x9] s s₁ := k1.mono (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simp)
    have h2 : Keeps [t, .x20, .x8, .x2, .x9] s₁ s₂ := k2.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
    exact h1.trans h2

def rowR (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  ([ld .x3 (a + 8 * i), .movz .w .x20 0 0] : List Instr) ++
    ((([ld .x9 (b + 8 * 0)] : List Instr) ++ mulStep r0 .x20 .x3 .x9) ++
      ((([ld .x9 (b + 8 * 1)] : List Instr) ++ mulStep r1 .x20 .x3 .x9) ++
        ((([ld .x9 (b + 8 * 2)] : List Instr) ++ mulStep r2 .x20 .x3 .x9) ++
          ((([ld .x9 (b + 8 * 3)] : List Instr) ++ mulStep r3 .x20 .x3 .x9) ++ [mov r4 .x20]))))

theorem row_eq (a b i : Nat) :
    row a b i = VG.Proof.Ed25519.AArch64.rowR a b i (wordReg i) (wordReg (i + 1)) (wordReg (i + 2))
      (wordReg (i + 3)) (wordReg (i + 4)) := by
  simp only [row, VG.Proof.Ed25519.AArch64.rowR, List.append_assoc]
  rfl

theorem rowStart_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d + 8 ≤ workSize large) :
    WP isa (.block [ld .x3 d, .movz .w .x20 0 0]) s fun t =>
      t.gpr .x3 = word s.mem base d ∧ t.gpr .x20 = 0 ∧ Keeps [.x3, .x20] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  apply WP.of_runBlock
  rw [runBlock_cons, load_sc hs ha hd, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec, show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · rw [RegUpd.gpr_write_self]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

/-- A row: `r0 + 2⁶⁴ r1 + 2¹²⁸ r2 + 2¹⁹² r3 + a_i · b`, into `r0`–`r4`. -/
theorem rowR_ok {s : State} {base : Addr} (hs : Scr s base large) {a b i : Nat}
    (ha : a + 8 * i + 8 ≤ workSize large) (hb : b + 32 ≤ workSize large)
    (haa : a % 8 = 0) (hba : b % 8 = 0) (hz : s.gpr .x10 = 0) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20, .x0, .x9, .x10] : List Reg).Nodup) :
    WP isa (.block (VG.Proof.Ed25519.AArch64.rowR a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (a + 8 * i)).toNat * fe s.mem base b ∧
      Keeps [r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20, .x9] s s' := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0d, h0c, h0b, h0i, h09, h0z⟩, ⟨h12, h13, h14, h1a, h1d, h1c, h1b, h1i, h19, h1z⟩,
    ⟨h23, h24, h2a, h2d, h2c, h2b, h2i, h29, h2z⟩, ⟨h34, h3a, h3d, h3c, h3b, h3i, h39, h3z⟩,
    ⟨h4a, h4d, h4c, h4b, h4i, h49, h4z⟩, -⟩ := hd
  rw [VG.Proof.Ed25519.AArch64.rowR, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowStart_ok hs (by omega) (by omega)) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulLoad_ok hs₁ hz1 (by omega) (by omega) h0a h0d h0z h0b h09) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by simp [Ne.symm h0i])
  have hz2 := (k2.gpr .x10 (by simp [Ne.symm h0z])).trans hz1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulLoad_ok hs₂ hz2 (by omega) (by omega) h1a h1d h1z h1b h19) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by simp [Ne.symm h1i])
  have hz3 := (k3.gpr .x10 (by simp [Ne.symm h1z])).trans hz2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulLoad_ok hs₃ hz3 (by omega) (by omega) h2a h2d h2z h2b h29) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by simp [Ne.symm h2i])
  have hz4 := (k4.gpr .x10 (by simp [Ne.symm h2z])).trans hz3
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulLoad_ok hs₄ hz4 (by omega) (by omega) h3a h3d h3z h3b h39) fun s₅ ⟨e5, k5⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x, show (0 : Nat) < 4096 from by decide, ite_true,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  -- The memory and the registers along the way.
  have M1 : s₁.mem = s.mem := k1.mem
  have M2 : s₂.mem = s.mem := k2.mem.trans M1
  have M3 : s₃.mem = s.mem := k3.mem.trans M2
  have M4 : s₄.mem = s.mem := k4.mem.trans M3
  have C2 : s₂.gpr .x3 = s₁.gpr .x3 := k2.gpr _ (by simp [Ne.symm h0c])
  have C3 : s₃.gpr .x3 = s₁.gpr .x3 := (k3.gpr _ (by simp [Ne.symm h1c])).trans C2
  have C4 : s₄.gpr .x3 = s₁.gpr .x3 := (k4.gpr _ (by simp [Ne.symm h2c])).trans C3
  have r0_1 : s₁.gpr r0 = s.gpr r0 := k1.gpr _ (by simp [h0c, h0b])
  have r0_5 : s₅.gpr r0 = s₂.gpr r0 := by
    rw [k5.gpr _ (by simp [h03, h0b, h0a, h0d, h09]), k4.gpr _ (by simp [h02, h0b, h0a, h0d, h09]),
      k3.gpr _ (by simp [h01, h0b, h0a, h0d, h09])]
  have r1_2 : s₂.gpr r1 = s.gpr r1 := by
    rw [k2.gpr _ (by simp [Ne.symm h01, h1b, h1a, h1d, h19]), k1.gpr _ (by simp [h1c, h1b])]
  have r1_5 : s₅.gpr r1 = s₃.gpr r1 := by
    rw [k5.gpr _ (by simp [h13, h1b, h1a, h1d, h19]), k4.gpr _ (by simp [h12, h1b, h1a, h1d, h19])]
  have r2_3 : s₃.gpr r2 = s.gpr r2 := by
    rw [k3.gpr _ (by simp [Ne.symm h12, h2b, h2a, h2d, h29]), k2.gpr _ (by simp [Ne.symm h02, h2b, h2a, h2d, h29]),
      k1.gpr _ (by simp [h2c, h2b])]
  have r2_5 : s₅.gpr r2 = s₄.gpr r2 := k5.gpr _ (by simp [h23, h2b, h2a, h2d, h29])
  have r3_4 : s₄.gpr r3 = s.gpr r3 := by
    rw [k4.gpr _ (by simp [Ne.symm h23, h3b, h3a, h3d, h39]), k3.gpr _ (by simp [Ne.symm h13, h3b, h3a, h3d, h39]),
      k2.gpr _ (by simp [Ne.symm h03, h3b, h3a, h3d, h39]), k1.gpr _ (by simp [h3c, h3b])]
  refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, r0_1, r1_2, r2_3, r3_4, z, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.reduceMul, word] at e2 e3 e4 e5
    simp only [val4, fe, word, RegUpd.gpr_write_of_ne _ _ _ h04, RegUpd.gpr_write_of_ne _ _ _ h14,
      RegUpd.gpr_write_of_ne _ _ _ h24, RegUpd.gpr_write_of_ne _ _ _ h34, r0_5, r1_5, r2_5]
    have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
        v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by
      intro x y z w v
      simp only [Nat.mul_add, Nat.mul_left_comm v]
    rw [hp]
    omega_using [e2, e3, e4, e5]
  · have h9 : r ≠ .x9 := fun he => hr (by simp [he])
    have hrOld : r ∉ [r0, r1, r2, r3, r4, .x8, .x2, .x3, .x20] :=
      fun hm => hr (List.mem_append_left _ hm)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrOld
    rw [RegUpd.gpr_write_of_ne _ _ _ hrOld.2.2.2.2.1]
    rw [k5.gpr _ (by simp [hrOld.2.2.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k4.gpr _ (by simp [hrOld.2.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k3.gpr _ (by simp [hrOld.2.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k2.gpr _ (by simp [hrOld.1, hrOld.2.2.2.2.2.2.2.2, hrOld.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.1, h9]),
      k1.gpr _ (by simp [hrOld.2.2.2.2.2.2.2.1, hrOld.2.2.2.2.2.2.2.2])]
  · exact k5.mem.trans M4
  · rw [RegUpd.rd_write, k5.rd, k4.rd, k3.rd, k2.rd, k1.rd]
  · rw [RegUpd.wr_write, k5.wr, k4.wr, k3.wr, k2.wr, k1.wr]

  · rw [RegUpd.sp_write, k5.sp, k4.sp, k3.sp, k2.sp, k1.sp]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.Reduce`. -/
section
/-! Reduction of an eight-word field product. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem fold_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hb : (s.gpr .x20).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 38 * (s.gpr .x20).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mul .x .x8 .x20 .x11]) s fun t =>
      (t.gpr .x8).toNat = 38 * (s.gpr .x20).toNat ∧ Keeps [.x8] s t from by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', h38]
    refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [BitVec.toNat_mul, show (38 : VG.Proof.Ed25519.Word64.Word).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · intro r hr
      exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr))
    fun s₁ ⟨e1, k1⟩ => ?_
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  have h381 := (k1.gpr .x11 (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by rw [e1]; omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans k2⟩
  rw [e2, e1, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide)]

/-- The eight words of a full product: x4–x7, then x21–x24. -/
abbrev wide (s : State) : Nat :=
  val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
    2 ^ 256 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem movz38_ok (s : State) :
    WP isa (.block [.movz .w .x11 38 0]) s fun t => t.gpr .x11 = 38 ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- `reduceWide`: the eight words of a product, reduced modulo p into x4–x7. -/
theorem reduceWide_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block reduceWide) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) = toFe (VG.Proof.Ed25519.AArch64.wide s) ∧
      t.gpr .x10 = 0 ∧
      Keeps [.x2, .x8, .x9, .x11, .x16, .x4, .x5, .x6, .x7, .x20] s t := by
  rw [reduceWide, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.movz38_ok s) fun s₁ ⟨h38, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowAccReduce_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans hz1
  have h382 : s₂.gpr .x11 = 38 := (k2.gpr _ (by decide)).trans h38
  have hc : (s₂.gpr .x20).toNat < 2 ^ 52 := by
    have hl := val4_lt (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7)
    have hh := val4_lt (s₁.gpr .x21) (s₁.gpr .x22) (s₁.gpr .x23) (s₁.gpr .x24)
    rw [h38, show (38 : VG.Proof.Ed25519.Word64.Word).toNat = 38 from rfl] at e2
    omega_using [e2, hl, hh]
  refine WP.mono (VG.Proof.Ed25519.AArch64.fold_ok s₂ hz2 h382 hc) fun s₃ ⟨e3, k3⟩ => ?_
  refine ⟨?_, (k3.gpr _ (by decide)).trans hz2,
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  rw [e3]
  rw [h38, show (38 : VG.Proof.Ed25519.Word64.Word).toNat = 38 from rfl, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide), k1.gpr .x21 (by decide),
    k1.gpr .x22 (by decide), k1.gpr .x23 (by decide), k1.gpr .x24 (by decide)] at e2
  apply toFe_congr
  rw [← fold256, e2, fold256]

end VG.Proof.Ed25519.AArch64
end

/-! Four-by-four word field multiplication and its memory frame. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem row0 (a b : Nat) : row a b 0 = VG.Proof.Ed25519.AArch64.rowR a b 0 .x4 .x5 .x6 .x7 .x21 := VG.Proof.Ed25519.AArch64.row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = VG.Proof.Ed25519.AArch64.rowR a b 1 .x5 .x6 .x7 .x21 .x22 := VG.Proof.Ed25519.AArch64.row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = VG.Proof.Ed25519.AArch64.rowR a b 2 .x6 .x7 .x21 .x22 .x23 := VG.Proof.Ed25519.AArch64.row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = VG.Proof.Ed25519.AArch64.rowR a b 3 .x7 .x21 .x22 .x23 .x24 := VG.Proof.Ed25519.AArch64.row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a B : Nat) :
    fe m base a * B = (word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((word m base (a + 8 * 3)).toNat * B) := by
  simp only [fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul,
    Nat.add_mul, Nat.mul_assoc]

def wideClob : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x20, .x21, .x22, .x23, .x24]

theorem rowsAccumulate_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
        2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
            fe s.mem base a * fe s.mem base b ∧ Keeps VG.Proof.Ed25519.AArch64.wideClob s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨haa, ha⟩ := ha
  obtain ⟨hba, hb⟩ := hb
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.gpr r h
  rw [WP.block_append_iff, VG.Proof.Ed25519.AArch64.row0]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowR_ok hs (by omega) hb haa hba hz (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 := (g k1 .x10 (by decide)).trans hz
  rw [WP.block_append_iff, VG.Proof.Ed25519.AArch64.row1]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowR_ok hs₁ (by omega) hb haa hba hz1 (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hz2 := (g k2 .x10 (by decide)).trans hz1
  rw [WP.block_append_iff, VG.Proof.Ed25519.AArch64.row2]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowR_ok hs₂ (by omega) hb haa hba hz2 (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  have hz3 := (g k3 .x10 (by decide)).trans hz2
  rw [VG.Proof.Ed25519.AArch64.row3]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowR_ok hs₃ (by omega) hb haa hba hz3 (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps VG.Proof.Ed25519.AArch64.wideClob s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans
      (k3.mono (by decide)) |>.trans (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [VG.Proof.Ed25519.AArch64.fe_mul_expand]
  rw [k1.mem] at e2
  rw [k2.mem, k1.mem] at e3
  rw [k3.mem, k2.mem, k1.mem] at e4
  have r1 := g k2 .x4 (by decide)
  have r2 := g k3 .x4 (by decide)
  have r3 := g k4 .x4 (by decide)
  have q2 := g k3 .x5 (by decide)
  have q3 := g k4 .x5 (by decide)
  have q4 := g k4 .x6 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Rows 1–3 and the loads keep the words of `b` (x12–x15), x4 and x10. -/
def mulRowClob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24]

theorem fe_mul_expand4 (A0 A1 A2 A3 B : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) * B =
      A0 * B + 2 ^ 64 * (A1 * B) + 2 ^ 128 * (A2 * B) + 2 ^ 192 * (A3 * B) := by
  simp only [Nat.add_mul, Nat.mul_assoc]

theorem mulWide_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (mulWide a b)) s fun t =>
      VG.Proof.Ed25519.AArch64.wide t = fe s.mem base a * fe s.mem base b ∧
      Keeps (.x12 :: .x13 :: .x14 :: .x15 :: VG.Proof.Ed25519.AArch64.mulRowClob) s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨haa, ha'⟩ := ha
  simp only [mulWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ⟨hb.1, hb.2⟩ (by decide)) fun s₁ ⟨b0, b1, b2, b3, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₁ (by omega) (by omega) .x3) fun s₂ ⟨a0, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowFirst_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e0, k3⟩ => ?_
  have K3 : Keeps VG.Proof.Ed25519.AArch64.mulRowClob s₁ s₃ := (k2.mono (by decide)).trans (k3.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K3 (by decide)) (by omega) (by omega) .x3)
    fun s₄ ⟨a1, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowAcc1_ok s₄ ((K3.trans (k4.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₅ ⟨e1, k5⟩ => ?_
  have K5 : Keeps VG.Proof.Ed25519.AArch64.mulRowClob s₁ s₅ := (K3.trans (k4.mono (by decide))).trans (k5.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K5 (by decide)) (by omega) (by omega) .x3)
    fun s₆ ⟨a2, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowAcc2_ok s₆ ((K5.trans (k6.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₇ ⟨e2, k7⟩ => ?_
  have K7 : Keeps VG.Proof.Ed25519.AArch64.mulRowClob s₁ s₇ := (K5.trans (k6.mono (by decide))).trans (k7.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K7 (by decide)) (by omega) (by omega) .x3)
    fun s₈ ⟨a3, k8⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowAcc3_ok s₈ ((K7.trans (k8.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₉ ⟨e3, k9⟩ => ?_
  have K9 : Keeps VG.Proof.Ed25519.AArch64.mulRowClob s₁ s₉ := (K7.trans (k8.mono (by decide))).trans (k9.mono (by decide))
  refine ⟨?_, (k1.mono (by decide)).trans (K9.mono (by decide))⟩
  -- The words of `a` and `b` at each row, and where each word of the result was last written.
  have B : ∀ (t : State), Keeps VG.Proof.Ed25519.AArch64.mulRowClob s₁ t →
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) = fe s.mem base b := by
    intro t k
    rw [k.gpr .x12 (by decide), k.gpr .x13 (by decide), k.gpr .x14 (by decide),
      k.gpr .x15 (by decide), b0, b1, b2, b3]
  rw [B s₂ (k2.mono (by decide)), a0, k1.mem] at e0
  rw [B s₄ (K3.trans (k4.mono (by decide))), a1, K3.mem, k1.mem, k4.gpr .x5 (by decide),
    k4.gpr .x6 (by decide), k4.gpr .x7 (by decide), k4.gpr .x21 (by decide)] at e1
  rw [B s₆ (K5.trans (k6.mono (by decide))), a2, K5.mem, k1.mem, k6.gpr .x6 (by decide),
    k6.gpr .x7 (by decide), k6.gpr .x21 (by decide), k6.gpr .x22 (by decide)] at e2
  rw [B s₈ (K7.trans (k8.mono (by decide))), a3, K7.mem, k1.mem, k8.gpr .x7 (by decide),
    k8.gpr .x21 (by decide), k8.gpr .x22 (by decide), k8.gpr .x23 (by decide)] at e3
  have K39 : Keeps [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₃ s₉ :=
    (((((k4.mono (by decide)).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))
  have K59 : Keeps [.x2, .x3, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₅ s₉ :=
    (((k6.mono (by decide)).trans (k7.mono (by decide))).trans (k8.mono (by decide))).trans
      (k9.mono (by decide))
  have K79 : Keeps [.x2, .x3, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₇ s₉ :=
    (k8.mono (by decide)).trans (k9.mono (by decide))
  have hf : fe s.mem base a * fe s.mem base b =
      (word s.mem base a).toNat * fe s.mem base b +
        2 ^ 64 * ((word s.mem base (a + 8)).toNat * fe s.mem base b) +
        2 ^ 128 * ((word s.mem base (a + 16)).toNat * fe s.mem base b) +
        2 ^ 192 * ((word s.mem base (a + 24)).toNat * fe s.mem base b) :=
    VG.Proof.Ed25519.AArch64.fe_mul_expand4 _ _ _ _ _
  dsimp only [VG.Proof.Ed25519.AArch64.wide]
  rw [hf, K39.gpr .x4 (by decide), K59.gpr .x5 (by decide), K79.gpr .x6 (by decide)]
  generalize fe s.mem base b = FB at e0 e1 e2 e3 ⊢
  simp only [val4] at e0 e1 e2 e3 ⊢
  omega_using [e0, e1, e2, e3]

theorem zeroReg_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .w r 0 0]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- Reduce the eight words of a product and store the result at `o`. -/
theorem fieldFinish_ok {s₀ s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ho : FieldRange o large) (hz : s.gpr .x10 = 0) (k : Keeps clob s₀ s) :
    WP isa (.block (reduceWide ++ store4 o)) s fun t =>
      Op base o s₀ t ∧ F t.mem base o = toFe (VG.Proof.Ed25519.AArch64.wide s) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.reduceWide_ok s hz) fun s₁ ⟨e1, _, k1⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps k1 (by decide)) ho) fun s₂ heq => ?_
  subst s₂
  refine ⟨Op.of_store ho (k.trans (k1.mono (by decide))) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  exact e1

/-- Multiplication modulo p, allowing the output to alias either input. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldMul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulWide_ok hs₀ ha hb hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Sub`. -/
section

/-! Four-word field subtraction. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem subWords_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldSubWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + fe s.mem base b =
          fe s.mem base a + 2 ^ 256 * (1 - c.toNat) ∧
        (t.gpr .x8).toNat = 38 * (1 - c.toNat) ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ workSize large → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) hd⟩
  have enc : ∀ d, d + 8 ≤ workSize large → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldSubWords, borrowValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, ld, exec, addr, State.load, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.mem_addWithCarry,
    BitVec.setWidth_eq, hs.x0, hz, h38, Size.bytes,
    Nat.add_mod, ha, hb, Nat.reduceMod, Nat.zero_add,
    enc a (by omega), enc b (by omega), enc (a + 8) (by omega), enc (b + 8) (by omega),
    enc (a + 16) (by omega), enc (b + 16) (by omega), enc (a + 24) (by omega), enc (b + 24) (by omega),
    w a (by omega), w b (by omega), w (a + 8) (by omega), w (b + 8) (by omega),
    w (a + 16) (by omega), w (b + 16) (by omega), w (a + 24) (by omega), w (b + 24) (by omega),
    and_self, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (word s.mem base (a + 24)) (~~~word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (~~~word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (~~~word s.mem base (b + 8))
        (carryOut (word s.mem base a) (~~~word s.mem base b) true))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sub4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) true
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact borrow38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem borrow38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block borrow38) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + (s.gpr .x8).toNat =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 2 ^ 256 * (1 - c.toNat) ∧
        (t.gpr .x8).toNat = 38 * (1 - c.toNat) ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  apply WP.of_runBlock
  simp only [borrow38, borrowValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (s.gpr .x7) (~~~0)
    (carryOut (s.gpr .x6) (~~~0) (carryOut (s.gpr .x5) (~~~0)
      (carryOut (s.gpr .x4) (~~~s.gpr .x8) true))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := sub4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) 0 0 0 true
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [carryOut, Size.bits]
    exact borrow38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem subLow_ok (s : State) (h : (s.gpr .x8).toNat ≤ (s.gpr .x4).toNat) :
    WP isa (.block [.sub .x .x4 .x4 .x8]) s fun t =>
      (t.gpr .x4).toNat + (s.gpr .x8).toNat = (s.gpr .x4).toNat ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.toNat_sub]
    have := (s.gpr .x4).isLt
    omega
  · intro r hr
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-- Subtraction modulo p, including both possible borrow corrections. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldSub o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldSub, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.subWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  refine WP.mono (VG.Proof.Ed25519.AArch64.borrow38_ok s₁ hz1 h381) fun s₂ ⟨c', e2, x2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hlow : (s₂.gpr .x8).toNat ≤ (s₂.gpr .x4).toNat := by
    rw [x2]
    have hc := Bool.toNat_le c
    have hc' := Bool.toNat_le c'
    have h5 := (s₂.gpr .x5).isLt
    have h6 := (s₂.gpr .x6).isLt
    have h7 := (s₂.gpr .x7).isLt
    have e := e2
    rw [x1] at e
    simp only [val4] at e
    omega_using [hc, hc', h5, h6, h7, e]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.subLow_ok s₂ hlow) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ heq => ?_
  subst s₄
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have k3' : Keeps clob s₂ s₃ := k3.mono (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans (k2'.trans k3'))) _ _ _ _, ?_⟩
  simp only [F]
  apply toFe_sub
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  have r5 := k3.gpr .x5 (by decide)
  have r6 := k3.gpr .x6 (by decide)
  have r7 := k3.gpr .x7 (by decide)
  rw [k0.mem] at e1
  simp only [val4] at e1 e2 ⊢
  rw [r5, r6, r7]
  rw [x1] at e2
  rw [x2] at e3
  simp only [VG.Spec.X25519.P]
  omega_using [e1, e2, e3]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.Field`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.Sqr`. -/
section
/-! Four-word field squaring. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem sq_expand_radix (R A0 A1 A2 A3 : Nat) :
    (A0 + R * A1 + R * R * A2 + R * R * R * A3) * (A0 + R * A1 + R * R * A2 + R * R * R * A3) =
      R * (2 * (A0 * A1 + R * (A0 * A2) + R * R * (A0 * A3 + A1 * A2) + R * R * R * (A1 * A3) +
        R * R * R * R * (A2 * A3))) +
        (A0 * A0 + R * R * (A1 * A1) + R * R * R * R * (A2 * A2 + R * R * (A3 * A3))) := by
  grind

/-- The square of four words: twice the products of distinct words, and the squares. -/
theorem sq_expand (A0 A1 A2 A3 : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) *
        (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) =
      2 ^ 64 * (2 * VG.Proof.Ed25519.AArch64.cross A0 A1 A2 A3) + VG.Proof.Ed25519.AArch64.diag A0 A1 A2 A3 := by
  have h := VG.Proof.Ed25519.AArch64.sq_expand_radix (2 ^ 64) A0 A1 A2 A3
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from rfl,
    show (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 from rfl,
    show (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 from rfl] at h
  exact h

theorem sqrWide_ok {s : State} {base : Addr} (hs : Scr s base large) {a : Nat}
    (ha : FieldRange a large) (hz : s.gpr .x10 = 0) :
    WP isa (.block (sqrWide a)) s fun t =>
      VG.Proof.Ed25519.AArch64.wide t = fe s.mem base a * fe s.mem base a ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x21, .x22, .x23, .x24] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  simp only [sqrWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ha (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrCross_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrDouble_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrDiag_ok s₃) fun s₄ ⟨c, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have A : ∀ (r : Reg), r ∈ [.x12, .x13, .x14, .x15] → s₃.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  rw [A .x12 (by decide), A .x13 (by decide), A .x14 (by decide), A .x15 (by decide),
    e3, e2, a0, a1, a2, a3] at e4
  have hlt : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  have hx := VG.Proof.Ed25519.AArch64.sq_expand (word s.mem base a).toNat (word s.mem base (a + 8)).toNat
    (word s.mem base (a + 16)).toNat (word s.mem base (a + 24)).toNat
  dsimp only [VG.Proof.Ed25519.AArch64.wide]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx] at hlt
  omega_using [e4, hlt]

/-- Squaring modulo p, allowing the output to alias the input. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base large) {o a : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) :
    WP isa (.block (fieldSqr o a)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldSqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.sqrWide_ok hs₀ ha hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.Add`. -/
section
/-! Four-word field addition. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

/-- Read both operands before any stores, so destination aliases are valid. -/
theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base large) {a b : Nat}
    (ha : FieldRange a large) (hb : FieldRange b large) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38) :
    WP isa (.block (fieldAddWords a b)) s fun t =>
      ∃ c : Bool,
        val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) + 2 ^ 256 * c.toNat =
          fe s.mem base a + fe s.mem base b ∧
        (t.gpr .x8).toNat = 38 * c.toNat ∧ Keeps [.x4, .x5, .x6, .x7, .x8, .x9] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have w : ∀ d, d + 8 ≤ workSize large → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) hd⟩
  have enc : ∀ d, d + 8 ≤ workSize large → d < 4096 * Size.x.bytes := by
    intro d hd
    change d < 32768
    omega
  apply WP.of_runBlock
  simp only [fieldAddWords, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, ld, exec, addr, State.load, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.mem_addWithCarry,
    BitVec.setWidth_eq, hs.x0, hz, h38, Size.bytes,
    Nat.add_mod, ha, hb, Nat.reduceMod, Nat.zero_add,
    enc a (by omega), enc b (by omega), enc (a + 8) (by omega), enc (b + 8) (by omega),
    enc (a + 16) (by omega), enc (b + 16) (by omega), enc (a + 24) (by omega), enc (b + 24) (by omega),
    w a (by omega), w b (by omega), w (a + 8) (by omega), w (b + 8) (by omega),
    w (a + 16) (by omega), w (b + 16) (by omega), w (a + 24) (by omega), w (b + 24) (by omega),
    and_self, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨carryOut (word s.mem base (a + 24)) (word s.mem base (b + 24))
    (carryOut (word s.mem base (a + 16)) (word s.mem base (b + 16))
      (carryOut (word s.mem base (a + 8)) (word s.mem base (b + 8))
        (carryOut (word s.mem base a) (word s.mem base b) false))),
    ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := add4_value (word s.mem base a) (word s.mem base (a + 8))
      (word s.mem base (a + 16)) (word s.mem base (a + 24))
      (word s.mem base b) (word s.mem base (b + 8))
      (word s.mem base (b + 16)) (word s.mem base (b + 24)) false
    dsimp only [fe, word, Mem.readW, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · dsimp only [word, Mem.readW, carryOut, Size.bits]
    exact carry38_value _
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- Addition modulo p, with memory and ABI frames. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : FieldRange o large) (ha : FieldRange a large) (hb : FieldRange b large) :
    WP isa (.block (fieldAdd o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [fieldAdd, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.addWords_ok hs₀ ha hb hz h38) fun s₁ ⟨c, e1, x1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  have h381 : s₁.gpr .x11 = 38 := (k1.gpr _ (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by
    rw [x1]
    have := Bool.toNat_le c
    omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ heq => ?_
  subst s₃
  have k0' : Keeps clob s s₀ := k0.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide)
  have k1' : Keeps clob s₀ s₁ := k1.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have k2' : Keeps clob s₁ s₂ := k2.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨Op.of_store ho (k0'.trans (k1'.trans k2')) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega), e2, x1]
  rw [k0.mem] at e1
  have hm : toFe (val4 (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7) + 38 * c.toNat) =
      toFe (fe s.mem base a + fe s.mem base b) := by
    apply toFe_congr
    rw [← e1]
    exact (fold256 _ _).symm
  exact hm.trans (toFe_add rfl)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.FieldMemory`. -/
section
/-! Constants and copies in the field workspace. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem slot_rangeWith (o : Slot) : FieldRange (offset o) large := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  constructor <;> simp only [offset] <;> omega

theorem slot_range (o : Slot) : FieldRange (offset o) := VG.Proof.Ed25519.AArch64.slot_rangeWith (large := true) o

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = v.val ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  rw [constWords, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (const64_ok s _ _) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₁ _ _) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok s₂ _ _) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (const64_ok s₃ _ _) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps [.x4, .x5, .x6, .x7] s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans
      (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [k4.gpr .x4 (by decide), k3.gpr .x4 (by decide), k2.gpr .x4 (by decide), e1,
    k4.gpr .x5 (by decide), k3.gpr .x5 (by decide), e2, k4.gpr .x6 (by decide), e3, e4]
  exact VG.Proof.Ed25519.AArch64.limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

theorem constField_op {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [constField, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o).2; omega), hv, toFe_self]

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base large) (a : Slot) :
    WP isa (.block (loads (offset a) .x4 .x5 .x6 .x7)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (offset a) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (loads_ok hs (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) a) (by decide)) fun t ⟨e1, e2, e3, e4, k⟩ => ?_
  exact ⟨by rw [e1, e2, e3, e4], k⟩

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  rw [copyField, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o)) fun u heq => ?_
  subst u
  refine ⟨Op.of_store (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (hk.mono (by decide)) _ _ _ _, ?_⟩
  rw [F, fe_st4 _ _ (by have := (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o).2; omega), hv]

theorem Outside_F {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 32 < 2 ^ 64)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) : F m' base d = F m base d :=
  congrArg toFe (h.fe hsep hd)

end VG.Proof.Ed25519.AArch64
end

/-!
# Ed25519 field programs: correctness of the lowering

Each arithmetic operation uses the A64 field arithmetic proof. An induction
composes these into a proof for any list of field operations.
-/

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}


open VG VG.AArch64 VG.Impl.Ed25519.AArch64

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (base : Addr) : VG.Proof.Ed25519.AArch64.Env := fun i => F m base (offset i)

def evalOp (op : FieldOp) (e : VG.Proof.Ed25519.AArch64.Env) : VG.Proof.Ed25519.AArch64.Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b => Function.update e o (e a * e b)
  | .sqr o a => Function.update e o (e a * e a)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

theorem evalOp_mul_apply (e : VG.Proof.Ed25519.AArch64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.AArch64.evalOp (.mul o a b) e i = if i = o then e a * e b else e i := by
  simp only [VG.Proof.Ed25519.AArch64.evalOp, Function.update_apply]

theorem evalOp_add_apply (e : VG.Proof.Ed25519.AArch64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.AArch64.evalOp (.add o a b) e i = if i = o then e a + e b else e i := by
  simp only [VG.Proof.Ed25519.AArch64.evalOp, Function.update_apply]

theorem evalOp_sub_apply (e : VG.Proof.Ed25519.AArch64.Env) (o a b i : Slot) :
    VG.Proof.Ed25519.AArch64.evalOp (.sub o a b) e i = if i = o then e a - e b else e i := by
  simp only [VG.Proof.Ed25519.AArch64.evalOp, Function.update_apply]

def evalOps (ops : List FieldOp) (e : VG.Proof.Ed25519.AArch64.Env) : VG.Proof.Ed25519.AArch64.Env := ops.foldl (fun e op => VG.Proof.Ed25519.AArch64.evalOp op e) e

structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outside base 64 704 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.Ed25519.AArch64.Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed25519.AArch64.Keep base s t) (k : VG.Proof.Ed25519.AArch64.Keep base t u) :
    VG.Proof.Ed25519.AArch64.Keep base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed25519.AArch64.Keep base s t) (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem env_update {base : Addr} {m m' : Mem} (o : Slot)
    (h : Outside base (offset o) 32 m m') :
    VG.Proof.Ed25519.AArch64.env m' base = Function.update (VG.Proof.Ed25519.AArch64.env m base) o (F m' base (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [VG.Proof.Ed25519.AArch64.env]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.Ed25519.AArch64.env, F]
    have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem op_keep {base : Addr} {o : Slot} {s t : State} (h : Op base (offset o) s t) :
    VG.Proof.Ed25519.AArch64.Keep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega)
    (by simp only [offset]; omega)⟩

theorem fieldOp_ok {s : State} {base : Addr} (hs : Scr s base large) (op : FieldOp) :
    WP isa (.block op.code) s fun t => VG.Proof.Ed25519.AArch64.Keep base s t ∧ VG.Proof.Ed25519.AArch64.env t.mem base = VG.Proof.Ed25519.AArch64.evalOp op (VG.Proof.Ed25519.AArch64.env s.mem base) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  cases op with
  | copy o a =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩
  | const o v =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.constField_op hs o v) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩
  | mul o a b =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.mul_ok hs (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) a) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩
  | sqr o a =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.sqr_ok hs (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) a)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩
  | add o a b =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.add_ok hs (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) a) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩
  | sub o a b =>
    refine WP.mono (VG.Proof.Ed25519.AArch64.sub_ok hs (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) o) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) a) (VG.Proof.Ed25519.AArch64.slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨VG.Proof.Ed25519.AArch64.op_keep h, by rw [VG.Proof.Ed25519.AArch64.env_update o h.mem, e]; rfl⟩

theorem fieldCode_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block (fieldCode ops)) s fun t =>
      VG.Proof.Ed25519.AArch64.Keep base s t ∧ VG.Proof.Ed25519.AArch64.env t.mem base = VG.Proof.Ed25519.AArch64.evalOps ops (VG.Proof.Ed25519.AArch64.env s.mem base) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.AArch64.fieldOp_ok hs op) fun t ⟨ht, et⟩ => ?_
    refine WP.mono (ih (ht.scr hs)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

theorem constField_ok {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      VG.Proof.Ed25519.AArch64.Keep base s t ∧ VG.Proof.Ed25519.AArch64.env t.mem base = Function.update (VG.Proof.Ed25519.AArch64.env s.mem base) o v := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (VG.Proof.Ed25519.AArch64.constField_op hs o v) fun t ⟨hk, hv⟩ => ?_
  exact ⟨VG.Proof.Ed25519.AArch64.op_keep hk, by rw [VG.Proof.Ed25519.AArch64.env_update o hk.mem, hv]⟩

theorem copyField_ok {s : State} {base : Addr} (hs : Scr s base large) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      VG.Proof.Ed25519.AArch64.Keep base s t ∧ VG.Proof.Ed25519.AArch64.env t.mem base = Function.update (VG.Proof.Ed25519.AArch64.env s.mem base) o (VG.Proof.Ed25519.AArch64.env s.mem base a) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine WP.mono (VG.Proof.Ed25519.AArch64.copyField_op hs o a) fun t ⟨hk, hv⟩ => ?_
  exact ⟨VG.Proof.Ed25519.AArch64.op_keep hk, by rw [VG.Proof.Ed25519.AArch64.env_update o hk.mem, hv]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : VG.Proof.Ed25519.AArch64.Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : VG.Proof.Ed25519.AArch64.Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega⟩
  let y := e ⟨q + 1, by omega⟩
  let z := e ⟨q + 2, by omega⟩
  let t := e ⟨q + 3, by omega⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : VG.Proof.Ed25519.AArch64.Env) :
    VG.Proof.Ed25519.AArch64.point (VG.Proof.Ed25519.AArch64.evalOps pointAddOps e) 0 1 2 3 = VG.Proof.Ed25519.AArch64.addResult e 4 (by decide) := by
  rfl

/-- What `pointDoubleOps` computes: the addition formula with `p = q`, its
products of equal factors as squares. -/
def doubleResult (e : VG.Proof.Ed25519.AArch64.Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 1 - e 0)
  let b := (e 1 + e 0) * (e 1 + e 0)
  let c := e 3 * e 3 * e 16 + e 3 * e 3 * e 16
  let dd := e 2 * e 2 + e 2 * e 2
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointDouble_formula (e : VG.Proof.Ed25519.AArch64.Env) :
    VG.Proof.Ed25519.AArch64.point (VG.Proof.Ed25519.AArch64.evalOps pointDoubleOps e) 0 1 2 3 = VG.Proof.Ed25519.AArch64.doubleResult e := by
  rfl

theorem doubleResult_eq (e : VG.Proof.Ed25519.AArch64.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.AArch64.doubleResult e = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point e 0 1 2 3) (VG.Proof.Ed25519.AArch64.point e 0 1 2 3) := by
  simp only [VG.Proof.Ed25519.AArch64.doubleResult, VG.Proof.Ed25519.AArch64.point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem addResult_eq (e : VG.Proof.Ed25519.AArch64.Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.AArch64.addResult e q hq = Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point e 0 1 2 3)
      (VG.Proof.Ed25519.AArch64.point e ⟨q, by omega⟩ ⟨q + 1, by omega⟩ ⟨q + 2, by omega⟩ ⟨q + 3, hq⟩) := by
  simp only [VG.Proof.Ed25519.AArch64.addResult, VG.Proof.Ed25519.AArch64.point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : VG.Proof.Ed25519.AArch64.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.AArch64.point (VG.Proof.Ed25519.AArch64.evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point e 0 1 2 3) (VG.Proof.Ed25519.AArch64.point e 4 5 6 7) :=
  (VG.Proof.Ed25519.AArch64.pointAdd_formula e).trans (VG.Proof.Ed25519.AArch64.addResult_eq e 4 (by decide) hd)

theorem pointDouble_eval (e : VG.Proof.Ed25519.AArch64.Env) (hd : e 16 = Spec.Ed25519.d) :
    VG.Proof.Ed25519.AArch64.point (VG.Proof.Ed25519.AArch64.evalOps pointDoubleOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (VG.Proof.Ed25519.AArch64.point e 0 1 2 3) (VG.Proof.Ed25519.AArch64.point e 0 1 2 3) :=
  (VG.Proof.Ed25519.AArch64.pointDouble_formula e).trans (VG.Proof.Ed25519.AArch64.doubleResult_eq e hd)

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep`. -/
section

/-! Field programs which also use the public loop counter x19. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

structure CounterKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CounterKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed25519.AArch64.CounterKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CounterKeep.trans {base : Addr} {s t u : State}
    (h : VG.Proof.Ed25519.AArch64.CounterKeep base s t) (k : VG.Proof.Ed25519.AArch64.CounterKeep base t u) : VG.Proof.Ed25519.AArch64.CounterKeep base s u :=
  ⟨fun r hr hb => (k.gpr r hr hb).trans (h.gpr r hr hb), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CounterKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r ∈ clob) : VG.Proof.Ed25519.AArch64.CounterKeep base s t := by
  refine ⟨fun r hr hb => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h
    · exact hb h
    · exact hr h
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem Keep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob) : VG.Proof.Ed25519.AArch64.Keep base s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (hrs r hm)), h.rd, h.wr, h.sp,
    by rw [h.mem]; exact Outside.refl _ _ _ _⟩

theorem CounterKeep.of_keep {base : Addr} {s t : State} (h : VG.Proof.Ed25519.AArch64.Keep base s t) : VG.Proof.Ed25519.AArch64.CounterKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem⟩

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.WideMul`. -/
section
/-! Full-width multiplication with an initial four-word addend. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

def wideValue (s : State) : Nat :=
  val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
    2 ^ 256 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem wideAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      VG.Proof.Ed25519.AArch64.wideValue t = val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
        fe s.mem base a * fe s.mem base b ∧ Keeps (.x10 :: VG.Proof.Ed25519.AArch64.wideClob) s t := by
  rw [wideAccumulate, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  refine WP.mono (VG.Proof.Ed25519.AArch64.rowsAccumulate_ok (hs.of_keeps k0 (by decide)) ha hb hz) fun t ⟨hv, kt⟩ => ?_
  refine ⟨?_, (k0.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [k0.gpr .x4 (by decide), k0.gpr .x5 (by decide), k0.gpr .x6 (by decide),
    k0.gpr .x7 (by decide), k0.mem] at hv
  exact hv

end VG.Proof.Ed25519.AArch64
end

/-! Loading scalar operands and saving the caller's registers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

theorem mulAddSave_ok {s : State} {base : Addr} (hc : s.gpr .x4 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 48 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [mulAddSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.store, read_x, hc, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega), w 40 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  · change word _ base rd.2 = s.gpr rd.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    simp only [write64_eq_writeW]
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem loadWords_ok (s : State) (src : Reg) (hsrc : src ∉ [Reg.x4, .x5, .x6, .x7])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8) :
    WP isa (.block (loadWords src)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem (s.gpr src) 0 ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hsrc
  apply WP.of_runBlock
  simp only [loadWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hsrc.1, hsrc.2.1, hsrc.2.2.1, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul,
    Nat.reduceLT, and_self, hr 0 (by decide), hr 8 (by decide), hr 16 (by decide), hr 24 (by decide),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem copyScalar_ok {s : State} {base : Addr} (hs : Scr s base)
    (src : Reg) (hsrc : src ∉ [Reg.x4, .x5, .x6, .x7])
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (s.gpr src) d) 8)
    (o : Nat) (ho : FieldRange o) :
    WP isa (.block (copyScalar src o)) s fun t =>
      fe t.mem base o = fe s.mem (s.gpr src) 0 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x7] → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base o 32 s.mem t.mem := by
  rw [copyScalar, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.loadWords_ok s src hsrc hr) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) ho) fun u hu => ?_
  subst u
  refine ⟨?_, hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩
  · rw [fe_st4 _ _ (by have hh := ho.2; change o + 32 ≤ 8192 at hh; omega)]; exact hv
  · rw [hk.mem]; exact st4_outside _ _ (by have hh := ho.2; change o + 32 ≤ 8192 at hh; omega) _ _ _ _

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (hn : 48 ≤ o) : Saved base g m' := by
  intro rd hr
  have hd : rd.2 + 8 ≤ 48 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [ho.word (Or.inl (by omega)) (by omega)]
  exact h rd hr

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec`. -/
section

/-! Full-width scalars and byte encodings in the working space. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt decodeLE)

theorem decodeLE_words (m : Mem) (base : Addr) (o : Nat) :
    decodeLE (bytesAt m (off base o) 32) = fe m base o := by
  rw [decodeLE_eq]
  change Proof.X25519.leNum (Spec.X25519.bytesAt m (off base o) 32) = _
  rw [Proof.X25519.leNum_bytesAt_words64]
  simp only [fe, val4, word, off]
  rw [show base + BitVec.ofNat 64 o + 8 = base + BitVec.ofNat 64 (o + 8) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 16 = base + BitVec.ofNat 64 (o + 16) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 24 = base + BitVec.ofNat 64 (o + 24) from Offset.add_add ..]

theorem decodeLE_wide (m : Mem) (base : Addr) :
    decodeLE (bytesAt m (off base 128) 64) = fe m base 128 + 2 ^ 256 * fe m base 160 := by
  have hb : bytesAt m (off base 128) 64 =
      bytesAt m (off base 128) 32 ++ bytesAt m (off base 160) 32 := by
    have h := Proof.X25519.bytesAt_add m (off base 128) 32 32
    rw [Offset.add_add] at h
    exact h
  rw [hb, decodeLE_append, bytesAt_length, VG.Proof.Ed25519.AArch64.decodeLE_words, VG.Proof.Ed25519.AArch64.decodeLE_words]

theorem scratchFrame {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn'
  simp only [ofs]
  omega

theorem fe_frame {base p : Addr} {m m' : Mem} (hf : Frame [⟨base, 8192⟩] m m')
    (hp : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) : fe m' p 0 = fe m p 0 := by
  have h : ∀ d, d + 8 ≤ 32 → m'.readW (off p d) 64 = m.readW (off p d) 64 := fun d hd =>
    hf.readW (r := ⟨p, 32⟩) (Offset.contains_base _ hd (by omega))
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  simp only [fe, val4, word, h 0 (by decide), h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem storeWide_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block storeWide) s fun t =>
      decodeLE (bytesAt t.mem (off base 128) 64) = VG.Proof.Ed25519.AArch64.wideValue s ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 128 64 s.mem t.mem := by
  rw [storeWide, WP.block_append_iff]
  refine WP.mono (stores_ok hs (by constructor <;> decide) .x4 .x5 .x6 .x7) fun t ht => ?_
  subst t
  refine WP.mono (stores_ok (hs.setMem _) (by constructor <;> decide) .x21 .x22 .x23 .x24) fun u hu => ?_
  subst u
  have ot := st4_outside s.mem base (show 128 + 32 < 2 ^ 64 by decide)
    (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  have ou := st4_outside (st4 s.mem base 128 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))
    base (show 160 + 32 < 2 ^ 64 by decide) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
  refine ⟨?_, rfl, rfl, rfl, rfl,
    (ot.mono (by decide) (by decide)).trans (ou.mono (by decide) (by decide))⟩
  rw [VG.Proof.Ed25519.AArch64.decodeLE_wide, ou.fe (by decide) (by decide), fe_st4 _ _ (by decide), fe_st4 _ _ (by decide)]
  rfl

theorem reduceArgs_ok (s : State) :
    WP isa (.block reduceArgs) s fun t =>
      t.gpr .x1 = off (s.gpr .x0) 128 ∧ t.gpr .x2 = s.gpr .x0 ∧
      t.gpr .x0 = s.gpr .x19 ∧ Keeps [.x1, .x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [reduceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x,
    show (128 : Nat) < 4096 from by decide, show (0 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarLit`. -/
section

/-! The kernel checks this literal once; taint and instruction checks reuse it. -/
namespace VG
materialize_code Impl.Ed25519.AArch64.scalarReduce
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain`. -/
section

/-! Complete scalar reduction, including preservation of the AAPCS64 ABI. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (bytesAt)

def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 64⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 32 =
    Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .x1) 64)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  refine WP.mono (scalarInit_ok s₁) fun s₂ ⟨b₂, v₂, z₂, k₂⟩ => ?_
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have x2₂ : s₂.gpr .x2 = s.gpr .x2 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have read₂ : ∀ k < 8,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .x1, 64⟩, ?_, ?_⟩
    · rw [k₂.rd, rd₁, hr]; simp
    · rw [x1₂]; exact Offset.contains_base _ (by omega) (by omega)
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₂ b₂ v₂ read₂ z₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  have x2₃ : s₃.gpr .x2 = s.gpr .x2 := (k₃.gpr _ (by decide)).trans x2₂
  have wr₃ : s₃.wr = s.wr := k₃.wr.trans (k₂.wr.trans wr₁)
  have sv₃ : Saved (s.gpr .x2) s.gpr s₃.mem := by rw [k₃.mem, k₂.mem]; exact sv₁
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok x2₃ (wr₃ ▸ hws) sv₃) fun s₄ ⟨r₄, k₄⟩ => ?_
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 :=
    (k₄.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans x0₂)
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ s₄.wr := by rw [k₄.wr, wr₃, hw]; simp
  refine WP.mono (scalarOut_ok x0₄ hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hpres => ?_, k₄.sp.trans (k₃.sp.trans (k₂.sp.trans sp₁))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₄ (.x19, 0) (by decide)
    · exact r₄ (.x20, 8) (by decide)
    · exact r₄ (.x21, 16) (by decide)
    · exact r₄ (.x22, 24) (by decide)
    · exact r₄ (.x23, 32) (by decide)
    · exact r₄ (.x24, 40) (by decide)
    all_goals
      rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarReduce, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    change scalarValue s₄ = _
    have val₄ : scalarValue s₄ = scalarValue s₃ := by
      simp only [scalarValue, k₄.gpr .x4 (by decide), k₄.gpr .x5 (by decide),
        k₄.gpr .x6 (by decide), k₄.gpr .x7 (by decide)]
    rw [val₄, v₃, x1₂, k₂.mem, bytesAt_frame (scalarSave_frame o₁) hd]

end VG.Proof.Ed25519.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified`. -/
section

/-! Merged from `Proof.Ed25519.AArch64.MulAddLit`. -/
section
/-! The kernel checks this literal once; taint and instruction checks reuse it. -/
namespace VG
materialize_code Impl.Ed25519.AArch64.scalarMulAdd
end VG
end

/-! Merged from `Proof.Ed25519.AArch64.MulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.MulAddSetup`. -/
section
/-! Save the caller's registers and prepare the scalar operands. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩]
  wr : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x4, 8192⟩]
  r_sc : (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  k_sc : (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  s_sc : (⟨s.gpr .x3, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  nowrap : (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64

structure MulAddReady (s₀ s : State) : Prop where
  base : s.gpr .x0 = s₀.gpr .x4
  out : s.gpr .x19 = s₀.gpr .x0
  sp : s.sp = s₀.sp
  preserved : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], s.gpr r = s₀.gpr r
  value : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = fe s₀.mem (s₀.gpr .x1) 0
  left : fe s.mem (s₀.gpr .x4) 64 = fe s₀.mem (s₀.gpr .x2) 0
  right : fe s.mem (s₀.gpr .x4) 96 = fe s₀.mem (s₀.gpr .x3) 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved (s₀.gpr .x4) s₀.gpr s.mem
  frame : Frame [⟨s₀.gpr .x4, 8192⟩] s₀.mem s.mem

theorem mulAddArgs_ok (s : State) :
    WP isa (.block [mov .x19 .x0, mov .x0 .x4]) s fun t =>
      t.gpr .x19 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x4 ∧ Keeps [.x19, .x0] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x,
    show (0 : Nat) < 4096 from by decide, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mulAddSetup_ok {s : State} (hs : VG.Proof.Ed25519.AArch64.MulAddPre s) :
    WP isa (.block mulAddSetup) s (VG.Proof.Ed25519.AArch64.MulAddReady s) := by
  have hw : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [show mulAddSetup = mulAddSave ++ (([mov .x19 .x0, mov .x0 .x4] :
    List Instr) ++ (copyScalar .x2 64 ++ (copyScalar .x3 96 ++ loadWords .x1))) by
    simp only [mulAddSetup, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulAddSave_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.mulAddArgs_ok s₁) fun s₂ ⟨out₂, base₂, k₂⟩ => ?_
  have hp₂ : s₂.gpr .x0 = s.gpr .x4 := base₂.trans (congrFun g₁ _)
  have hw₂ : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s₂.wr := by rw [k₂.wr, wr₁]; exact hw
  have g₂ : ∀ r, r ∉ [Reg.x19, .x0] → s₂.gpr r = s.gpr r :=
    fun r h => (k₂.gpr r h).trans (congrFun g₁ r)
  have fm₂ : Frame [⟨s.gpr .x4, 8192⟩] s.mem s₂.mem := by
    rw [k₂.mem]; exact VG.Proof.Ed25519.AArch64.scratchFrame o₁ (by decide)
  have hr₂ : ∀ d, d + 8 ≤ 32 → InRegions (s₂.rd ++ s₂.wr) (off (s₂.gpr .x2) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x2, 32⟩, ?_, ?_⟩
    · rw [k₂.rd, rd₁, hs.rd]; simp
    · rw [g₂ .x2 (by decide)]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.copyScalar_ok ⟨hp₂, hw₂, hs.nowrap⟩ .x2 (by decide) hr₂ 64 (by constructor <;> decide))
    fun s₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  have hp₃ : s₃.gpr .x0 = s.gpr .x4 := (g₃ _ (by decide)).trans hp₂
  have hw₃ : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s₃.wr := wr₃ ▸ hw₂
  have fm₃ := fm₂.trans (VG.Proof.Ed25519.AArch64.scratchFrame o₃ (by decide))
  have rcx₃ : s₃.gpr .x3 = s.gpr .x3 := (g₃ _ (by decide)).trans (g₂ _ (by decide))
  have hr₃ : ∀ d, d + 8 ≤ 32 → InRegions (s₃.rd ++ s₃.wr) (off (s₃.gpr .x3) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x3, 32⟩, ?_, ?_⟩
    · rw [rd₃, k₂.rd, rd₁, hs.rd]; simp
    · rw [rcx₃]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.copyScalar_ok ⟨hp₃, hw₃, hs.nowrap⟩ .x3 (by decide) hr₃ 96 (by constructor <;> decide))
    fun s₄ ⟨v₄, g₄, rd₄, wr₄, sp₄, o₄⟩ => ?_
  have fm₄ := fm₃.trans (VG.Proof.Ed25519.AArch64.scratchFrame o₄ (by decide))
  have rsi₄ : s₄.gpr .x1 = s.gpr .x1 :=
    (g₄ _ (by decide)).trans ((g₃ _ (by decide)).trans (g₂ _ (by decide)))
  have hr₄ : ∀ d, d + 8 ≤ 32 → InRegions (s₄.rd ++ s₄.wr) (off (s₄.gpr .x1) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x1, 32⟩, ?_, ?_⟩
    · rw [rd₄, rd₃, k₂.rd, rd₁, hs.rd]; simp
    · rw [rsi₄]; exact Offset.contains_base _ hd (by omega)
  refine WP.mono (VG.Proof.Ed25519.AArch64.loadWords_ok s₄ .x1 (by decide) hr₄) fun t ⟨vt, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kt.gpr _ (by decide), g₄ _ (by decide)]; exact hp₃
  · rw [kt.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide), out₂, g₁]
  · rw [kt.sp, sp₄, sp₃, k₂.sp, sp₁]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [kt.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]
  · rw [vt, rsi₄, VG.Proof.Ed25519.AArch64.fe_frame fm₄ hs.r_sc]
  · rw [kt.mem, o₄.fe (by decide) (by decide), v₃, g₂ _ (by decide), VG.Proof.Ed25519.AArch64.fe_frame fm₂ hs.k_sc]
  · rw [kt.mem, v₄, rcx₃, VG.Proof.Ed25519.AArch64.fe_frame fm₃ hs.s_sc]
  · rw [kt.rd, rd₄, rd₃, k₂.rd, rd₁]
  · rw [kt.wr, wr₄, wr₃, k₂.wr, wr₁]
  · have sv₂ : Saved (s.gpr .x4) s.gpr s₂.mem := by rw [k₂.mem]; exact sv₁
    rw [kt.mem]; exact (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
  · rw [kt.mem]; exact fm₄

end VG.Proof.Ed25519.AArch64
end

/-! Full-width multiply-add followed by subgroup reduction. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt decodeLE)

def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩] ∧
    s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarMulAdd
    (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x2) 32) (bytesAt s.mem (s.gpr .x3) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : VG.Proof.Ed25519.AArch64.MulAddPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem scalarMulAdd_correct {s : State} (hs : VG.Proof.Ed25519.AArch64.MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  have hw : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [scalarMulAdd]
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.mulAddSetup_ok hs) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.wideAccumulate_ok ⟨h₁.base, h₁.wr ▸ hw, hs.nowrap⟩
    (by constructor <;> decide) (by constructor <;> decide)) fun s₂ ⟨v₂, k₂⟩ => ?_)
  have prod₂ : VG.Proof.Ed25519.AArch64.wideValue s₂ = fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0 := by
    rw [v₂, h₁.value, h₁.left, h₁.right]
  have base₂ : s₂.gpr .x0 = s.gpr .x4 := (k₂.gpr _ (by decide)).trans h₁.base
  have wr₂ : s₂.wr = s.wr := k₂.wr.trans h₁.wr
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.storeWide_ok ⟨base₂, wr₂ ▸ hw, hs.nowrap⟩) fun s₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed25519.AArch64.reduceArgs_ok s₃) fun s₄ ⟨x1₄, x2₄, x0₄, k₄⟩ => ?_
  refine WP.mono (scalarInit_ok s₄) fun s₅ ⟨b₅, v₅, z₅, k₅⟩ => ?_
  have x1₅ : s₅.gpr .x1 = off (s.gpr .x4) 128 := by rw [k₅.gpr _ (by decide), x1₄, g₃, base₂]
  have x2₅ : s₅.gpr .x2 = s.gpr .x4 := by rw [k₅.gpr _ (by decide), x2₄, g₃, base₂]
  have x0₅ : s₅.gpr .x0 = s.gpr .x0 := by
    rw [k₅.gpr _ (by decide), x0₄, g₃, k₂.gpr _ (by decide), h₁.out]
  have wr₅ : s₅.wr = s.wr := by rw [k₅.wr, k₄.wr, wr₃, wr₂]
  have read₅ : ∀ k < 8,
      InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .x4, 8192⟩, List.mem_append_right _ (wr₅ ▸ hw), ?_⟩
    rw [x1₅, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have sv₅ : Saved (s.gpr .x4) s.gpr s₅.mem := by
    have sv₂ : Saved (s.gpr .x4) s.gpr s₂.mem := by rw [k₂.mem]; exact h₁.saved
    rw [k₅.mem, k₄.mem]; exact sv₂.outside o₃ (by decide)
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₅ b₅ v₅ read₅ z₅) fun s₆ ⟨v₆, k₆⟩ => ?_
  have wr₆ : s₆.wr = s.wr := k₆.wr.trans wr₅
  have val₆ : scalarValue s₆ = (fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0) % Spec.Ed25519.L := by
    rw [v₆, x1₅, k₅.mem, k₄.mem, v₃, prod₂]
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) ((k₆.gpr _ (by decide)).trans x2₅) (wr₆ ▸ hw)
    (by rw [k₆.mem]; exact sv₅)) fun s₇ ⟨rest₇, k₇⟩ => ?_
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 :=
    (k₇.gpr _ (by decide)).trans ((k₆.gpr _ (by decide)).trans x0₅)
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ s₇.wr := by rw [k₇.wr, wr₆, hs.wr]; simp
  refine WP.mono (scalarOut_ok x0₇ hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest₇ (.x19, 0) (by decide)
    · exact rest₇ (.x20, 8) (by decide)
    · exact rest₇ (.x21, 16) (by decide)
    · exact rest₇ (.x22, 24) (by decide)
    · exact rest₇ (.x23, 32) (by decide)
    · exact rest₇ (.x24, 40) (by decide)
    all_goals
      rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
        k₄.gpr _ (by decide), g₃, k₂.gpr _ (by decide), h₁.preserved _ (by decide)]
  · exact k₇.sp.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans (sp₃.trans (k₂.sp.trans h₁.sp)))))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarMulAdd, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    have v₇ : scalarValue s₇ = scalarValue s₆ := by
      simp only [scalarValue, k₇.gpr .x4 (by decide), k₇.gpr .x5 (by decide), k₇.gpr .x6 (by decide),
        k₇.gpr .x7 (by decide)]
    change scalarValue s₇ = _
    rw [v₇, val₆]
    have hd (p : Addr) : decodeLE (bytesAt s.mem p 32) = fe s.mem p 0 := by
      have h := VG.Proof.Ed25519.AArch64.decodeLE_words s.mem p 0
      rw [show off p 0 = p from BitVec.add_zero p] at h
      exact h
    rw [hd, hd, hd]

end VG.Proof.Ed25519.AArch64
end

/-! Scalar multiply-add satisfies the merged specification, ABI, and constant-time contract. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def mulAddSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x5000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  VG.Proof.Ed25519.AArch64.scalarMulAdd_correct (MulAddPre.of hs)

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem scalarMulAdd_verified : Verified AArch64.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Ed25519.AArch64.scalarMulAdd_ok VG.Proof.Ed25519.AArch64.scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, VG.Proof.Ed25519.AArch64.scalarMulAddLocal]
      [mulAddSatState] using VG.Proof.Ed25519.AArch64.mulAddSatState)

end VG.Proof.Ed25519.AArch64

end

end
