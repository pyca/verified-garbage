module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.X25519.AArch64
import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on AArch64: the steps of the field operations

The field operations read and write words of the working space (`x3`, 4096
bytes) at constant offsets; each lemma here runs a few instructions and states
their effect on the numbers in the registers and in the words of the working
space.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64

open VG VG.AArch64 VG.Impl.X25519.AArch64

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 64-bit word at `b + off`, as a number. -/
def wd (m : Mem) (b : Addr) (off : Nat) : Nat := (m.readW (b + BitVec.ofNat 64 off) 64).toNat

/-- The working space at `b`. -/
abbrev scR (b : Addr) : Region := ⟨b, 4096⟩

/-- The working space is at `b`, in `x3`, and writable. -/
structure Sc (b : Addr) (s : State) : Prop where
  x3 : s.gpr .x3 = b
  wr : scR b ∈ s.wr

/-- The registers but `W` are unchanged, and so are the regions. -/
structure Kp (W : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ W → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Kp.refl (W : List Reg) (s : State) : Kp W s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Kp.trans {W W' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Kp W s₁ s₂) (h₂ : Kp W' s₂ s₃) :
    Kp (W ++ W') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Kp.mono {W W' : List Reg} {s s' : State} (h : Kp W s s') (hs : ∀ r ∈ W, r ∈ W') :
    Kp W' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr⟩

theorem Kp.sub {W W' : List Reg} {s s' : State} (h : Kp W s s') (hs : W ⊆ W') : Kp W' s s' :=
  h.mono fun _ hr => hs hr

/-- Closes `W ⊆ W'` for lists of registers, some of them variables. -/
macro "sub_regs" : tactic => `(tactic| plain_simp_names simp only [List.cons_subset, List.append_subset, List.nil_subset,
                   List.mem_cons, List.mem_append, true_or, or_true, and_true, List.not_mem_nil, or_false, and_self,
                   List.cons_append, List.nil_append])

theorem Sc.of_kp {b : Addr} {W : List Reg} {s s' : State} (hs : Sc b s) (h : Kp W s s')
    (hW : Reg.x3 ∉ W) : Sc b s' :=
  ⟨by rw [h.gpr _ hW, hs.x3], by rw [h.wr]; exact hs.wr⟩

theorem Sc.mem {b : Addr} {s : State} (hs : Sc b s) (m : Mem) : Sc b { s with mem := m } :=
  ⟨hs.x3, hs.wr⟩

/-- An offset of a word in the working space. -/
def Off (off : Nat) : Prop := off % 8 = 0 ∧ off + 8 ≤ 4096

instance (off : Nat) : Decidable (Off off) := by unfold Off; infer_instance

/-! ## Registers after writes -/

section
variable (s : State)

theorem read_x (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

theorem gpr_wx (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write .x d x).gpr r = if r = d then x else s.gpr r := by
  simp only [State.write, BitVec.setWidth_eq]

theorem gpr_wx_self (d : Reg) (x : BitVec 64) : (s.write .x d x).gpr d = x := by
  simp only [gpr_wx, ite_true]

theorem gpr_wx_ne {d r : Reg} (x : BitVec 64) (h : r ≠ d) : (s.write .x d x).gpr r = s.gpr r := by
  simp only [gpr_wx, h, ite_false]

theorem gpr_ww_self (d : Reg) (x : BitVec 32) : (s.write .w d x).gpr d = x.setWidth 64 := by
  simp only [State.write, ite_true]

theorem gpr_ww_ne {d r : Reg} (x : BitVec 32) (h : r ≠ d) : (s.write .w d x).gpr r = s.gpr r := by
  simp only [State.write, h, ite_false]

theorem kp_ww (d : Reg) (x : BitVec 32) : Kp [d] s (s.write .w d x) :=
  ⟨fun r hr => gpr_ww_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_ww {b : Addr} {d : Reg} (x : BitVec 32) (hs : Sc b s) (hd : d ≠ .x3) :
    Sc b (s.write .w d x) :=
  ⟨by rw [gpr_ww_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

theorem mem_wx (d : Reg) (x : BitVec 64) : (s.write .x d x).mem = s.mem := rfl
theorem kp_wx (d : Reg) (x : BitVec 64) : Kp [d] s (s.write .x d x) :=
  ⟨fun r hr => gpr_wx_ne s x (by simpa using hr), rfl, rfl⟩

theorem sc_wx {b : Addr} {d : Reg} (x : BitVec 64) (hs : Sc b s) (hd : d ≠ .x3) :
    Sc b (s.write .x d x) :=
  ⟨by rw [gpr_wx_ne s x (Ne.symm hd), hs.x3], hs.wr⟩

end

/-! ## Instructions -/

theorem off_in {b : Addr} {s : State} (hs : Sc b s) {off : Nat} (ho : Off off) :
    InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 off) 8 :=
  ⟨scR b, hs.wr, by rw [hs.x3]; exact Offset.contains_base b ho.2 (by have := ho.2; omega_arith)⟩

theorem exec_st {b : Addr} {s : State} (hs : Sc b s) (t : Reg) {off : Nat} (ho : Off off) :
    exec (st t off) s = some { s with mem := s.mem.writeW (b + BitVec.ofNat 64 off) (s.gpr t) } := by
  rw [st, exec_str_x ⟨ho.1, by have := ho.2; omega_arith⟩ (off_in hs ho), hs.x3]

theorem exec_add_x {s : State} {d n m : Reg} :
    exec (.add .x d n m) s = some (s.write .x d (s.gpr n + s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_sub_x {s : State} {d n m : Reg} :
    exec (.sub .x d n m) s = some (s.write .x d (s.gpr n - s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_and_x {s : State} {d n m : Reg} :
    exec (.logic .and .x d n m) s = some (s.write .x d (s.gpr n &&& s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_eor_x {s : State} {d n m : Reg} :
    exec (.logic .eor .x d n m) s = some (s.write .x d (s.gpr n ^^^ s.gpr m)) := by
  simp only [exec, read_x]

theorem exec_lsr {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp only [exec, Size.bits, h, ite_true, read_x]

theorem exec_lsl {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.gpr n <<< sh)) := by
  simp only [exec, Size.bits, h, ite_true, read_x]

theorem exec_movz {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]

theorem exec_movk1 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movk .x d imm 1) s = some (s.write .x d
      ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< 16)) ||| (imm.setWidth 64 <<< 16))) := by
  simp only [exec, Size.bits, Nat.mul_one, show (16 : Nat) < 64 from by decide, ite_true, read_x]

theorem exec_ldrb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s = some (s.write .w t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, ho, true_and, ite_true, Option.bind_some,
    State.load, h, Option.map_some]

theorem exec_strb {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega_arith, true_and, ite_true, Option.bind_some,
    State.store, h]

theorem read1_toNat (m : Mem) (a : Addr) : ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Mem.read, BitVec.toNat_append, show (0#0).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  have := (m a).isLt
  omega_arith

/-! ## Numbers -/

theorem lsr_toNat (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Multiply-accumulate -/

/-- An element's offset: its fifteen words are in the working space. -/
def Slot (o : Nat) : Prop := o % 8 = 0 ∧ o + 120 ≤ 4096

instance (o : Nat) : Decidable (Slot o) := by unfold Slot; infer_instance

/-! ## Stores -/

theorem wd_writeW (m : Mem) (b : Addr) {o off : Nat} (x : BitVec 64) (ho : Off o) (hoff : Off off) :
    wd (m.writeW (b + BitVec.ofNat 64 o) x) b off = if off = o then x.toNat else wd m b off := by
  have := ho.2; have := hoff.2
  by_cases h : off = o
  · subst h; rw [ite_eq_left rfl, wd, Mem.readW_writeW_self64]
  · rw [ite_eq_right h, wd, wd, Mem.readW_writeW_sep (Offset.sep b (by have := ho.1; have := hoff.1; omega_arith)
      (by omega_arith) (by omega_arith)) (by decide)]

end VG.Proof.X25519.AArch64
