import VerifiedGarbage.Impl.Mont.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Montgomery arithmetic on AArch64: words in registers and in the working space

Numbers of several words: in registers (`regsVal`, little-endian over a list
of registers) and in the working space (`wordsVal`), which is `size` bytes at
`base`, the value of `x0` (`Scr`). The loads and stores of the arithmetic
(at offsets that are multiples of 8, as `ldr` and `str` encode them), and
what they leave unchanged.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The registers `rs` read as a little-endian number. -/
def regsVal (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * regsVal s rs

theorem regsVal_lt (s : State) (rs : List Reg) : regsVal s rs < 2 ^ (64 * rs.length) := by
  induction rs with
  | nil => exact Nat.one_pos
  | cons r rs ih =>
    rw [List.length_cons, pow64_succ]
    exact word_add_lt (s.gpr r).isLt ih

theorem regsVal_append (s : State) (rs qs : List Reg) :
    regsVal s (rs ++ qs) = regsVal s rs + 2 ^ (64 * rs.length) * regsVal s qs := by
  induction rs with
  | nil => simp only [List.nil_append, regsVal, List.length_nil, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons r rs ih =>
    rw [List.cons_append, regsVal, ih, regsVal, List.length_cons, pow64_succ, Nat.mul_add,
      Nat.mul_assoc]
    omega

theorem regsVal_congr {s s' : State} {rs : List Reg} (h : ∀ r ∈ rs, s'.gpr r = s.gpr r) :
    regsVal s' rs = regsVal s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The working space: `x0` holds its base `base`, it is writable, it does not
wrap around, and every offset in it can be encoded in a load or store. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  x0 : s.gpr .x0 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64
  enc : size ≤ 32768

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  rw [hs.x0]
  exact ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  rw [hs.x0]
  exact ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.enc8 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) : d % 8 = 0 ∧ d < 32768 :=
  ⟨ha, by have := hs.enc; omega⟩

/-- A load of the word at offset `d`. -/
theorem exec_ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    exec (ld t d) s = some (s.write .x t (word s.mem base d)) := by
  rw [ld, exec_ldr_x (hs.enc8 hd ha) (hs.ld hd), hs.x0]

/-- A store of a register at offset `d`. -/
theorem exec_st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    exec (st t d) s = some { s with mem := s.mem.writeW (off base d) (s.gpr t) } := by
  rw [st, exec_str_x (hs.enc8 hd ha) (hs.st hd), hs.x0]

/-- `t = [x0 + d]`. -/
theorem ld_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    WP isa (.block [ld t d]) s fun s' =>
      s'.gpr t = word s.mem base d ∧ Keeps [t] s s' ∧ s'.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_ld hs hd ha, runStep_some, runBlock_nil,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `[x0 + d] = t`. -/
theorem st_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    WP isa (.block [st t d]) s fun s' => s' = { s with mem := s.mem.writeW (off base d) (s.gpr t) } := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_st hs hd ha, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : Keeps rs s s') (hr : .x0 ∉ rs) : Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

/-- What an operation keeps: the registers but `rs`, and the regions; memory
may change. -/
structure KeepRegs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem KeepRegs.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepRegs rs s₁ s₂)
    (h₂ : KeepRegs rs s₂ s₃) : KeepRegs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem KeepRegs.mono {rs rs' : List Reg} {s s' : State} (h : KeepRegs rs s s')
    (hr : ∀ r ∈ rs, r ∈ rs') : KeepRegs rs' s s' :=
  ⟨fun r h' => h.gpr r fun hm => h' (hr r hm), h.rd, h.wr, h.sp⟩

theorem Keeps.regs {rs : List Reg} {s s' : State} (h : Keeps rs s s') : KeepRegs rs s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp⟩

theorem Scr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : KeepRegs rs s s') (hr : .x0 ∉ rs) : Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

end VG.Proof.Mont.AArch64
