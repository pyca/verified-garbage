module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Montgomery arithmetic on PPC64LE: the working space and its words

The working space is `size` bytes at `base` (`Ws`): a writable region that
does not wrap around the address space, whose offsets are below `2¹⁵`, so
that every offset in it is a displacement of `lwz` and `stw` (and of `ld`
and `std` at multiples of 4). Its numbers are read as 32-bit words (`w32`,
`val32`), which are the digits of the arithmetic. A register points into it
at an offset (`At`); loads and stores through it (`lwz_ok`, `stw_ok`), and
what an instruction keeps (`Kp`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, within a writable region,
not wrapping around, with offsets below `2¹⁵`. -/
structure Ws (s : State) (base : Addr) (size : Nat) : Prop where
  wr : ∃ len, size ≤ len ∧ (⟨base, len⟩ : Region) ∈ s.wr ∧ base.toNat + len ≤ 2 ^ 64
  small : size ≤ 2 ^ 15

/-- Register `r` points `K` bytes into the working space. -/
abbrev At (s : State) (base : Addr) (r : Reg) (K : Nat) : Prop := s.gpr r = off base K

theorem Ws.nowrap {s : State} {base : Addr} {size : Nat} (h : Ws s base size) :
    base.toNat + size ≤ 2 ^ 64 := by
  obtain ⟨len, hl, -, hn⟩ := h.wr; omega

theorem Ws.read {s : State} {base : Addr} {size : Nat} (h : Ws s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  have ⟨_, hl, hR, hn⟩ := h.wr
  have := h.small
  ⟨_, List.mem_append_right _ hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Ws.wrIn {s : State} {base : Addr} {size : Nat} (h : Ws s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n :=
  have ⟨_, hl, hR, hn⟩ := h.wr
  have := h.small
  ⟨_, hR, Offset.contains_base base (by omega) (by omega)⟩

theorem Ws.of_wr {s s' : State} {base : Addr} {size : Nat} (h : Ws s base size) (hw : s'.wr = s.wr) :
    Ws s' base size := ⟨hw ▸ h.wr, h.small⟩

/-! ## What changes -/

/-- `s'` agrees with `s` but on the registers `rs` and in memory, and has its
regions, stack pointer and link register. -/
structure Kp (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem Kp.refl (rs : List Reg) (s : State) : Kp rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Kp.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Kp rs s₁ s₂) (h₂ : Kp rs s₂ s₃) : Kp rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp, h₂.lr.trans h₁.lr⟩

theorem Kp.mono {rs rs' : List Reg} {s s' : State} (h : Kp rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Kp rs' s s' := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp, h.lr⟩

theorem Kp.g {rs : List Reg} {s s' : State} (h : Kp rs s s') {r : Reg} (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

theorem Kp.ws {rs : List Reg} {s s' : State} (h : Kp rs s s') {base : Addr} {size : Nat}
    (hs : Ws s base size) : Ws s' base size := hs.of_wr h.wr

theorem Kp.at {rs : List Reg} {s s' : State} (h : Kp rs s s') {base : Addr} {r : Reg} {K : Nat}
    (ha : At s base r K) (hr : r ∉ rs := by decide) : At s' base r K := by
  rw [At, h.gpr r hr]; exact ha

/-- A register outside a list is outside its sublists. -/
theorem not_mem_sub {r : Reg} {l : List Reg} (h : r ∉ l) {l' : List Reg} (hs : ∀ x ∈ l', x ∈ l := by decide) :
    r ∉ l' := fun h' => h (hs r h')

theorem ne_of_not_mem {r : Reg} {l : List Reg} (h : r ∉ l) {x : Reg} (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

theorem write_gpr (s : State) (d : Reg) (x : BitVec 64) (r : Reg) :
    (s.write d x).gpr r = if r = d then x else s.gpr r := rfl

@[simp] theorem write_rd (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).rd = s.rd := rfl
@[simp] theorem write_wr (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).wr = s.wr := rfl
@[simp] theorem write_sp (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).sp = s.sp := rfl
@[simp] theorem write_lr (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).lr = s.lr := rfl
@[simp] theorem write_mem (s : State) (d : Reg) (x : BitVec 64) : (s.write d x).mem = s.mem := rfl

theorem write_write (s : State) (d : Reg) (a b : BitVec 64) : (s.write d a).write d b = s.write d b := by
  simp only [State.write]
  congr 1
  funext r
  by_cases h : r = d <;> simp [h]

theorem Kp.write (s : State) {d : Reg} (x : BitVec 64) {rs : List Reg} (hd : d ∈ rs) :
    Kp rs s (s.write d x) :=
  ⟨fun r hr => by
    have : r ≠ d := fun h => hr (h ▸ hd)
    rw [write_gpr, ite_eq_right_iff.mpr (fun h => absurd h this)], rfl, rfl, rfl, rfl⟩

theorem Kp.store (s : State) (m : Mem) (rs : List Reg) : Kp rs s { s with mem := m } :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem At.write {s : State} {base : Addr} {r : Reg} {K : Nat} (h : At s base r K) {d : Reg}
    (x : BitVec 64) (hd : r ≠ d := by decide) : At (s.write d x) base r K := by
  rw [At, write_gpr, ite_eq_right_iff.mpr (fun e => absurd e hd)]; exact h

theorem At.store {s : State} {base : Addr} {r : Reg} {K : Nat} (h : At s base r K) (m : Mem) :
    At { s with mem := m } base r K := h

theorem Ws.write {s : State} {base : Addr} {size : Nat} (h : Ws s base size) (d : Reg) (x : BitVec 64) :
    Ws (s.write d x) base size := h.of_wr rfl

theorem Ws.store {s : State} {base : Addr} {size : Nat} (h : Ws s base size) (m : Mem) :
    Ws { s with mem := m } base size := h.of_wr rfl

/-! ## Loads and stores through a register -/

theorem off_add (base : Addr) (K d : Nat) : off base K + BitVec.ofNat 64 d = off base (K + d) :=
  Offset.add_add base K d

/-- `lwz t, d(r)` with `r` at `K` bytes into the working space. -/
theorem lwz_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 4 ≤ size) :
    exec (.load .w t r d) s = some (s.write t (BitVec.ofNat 64 (w32 s.mem base (K + d)))) := by
  have hs15 := hs.small
  rw [exec_load_w hr0 (by omega) (by rw [hr, off_add]; exact hs.read hd), hr, off_add]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]

/-- `stw t, d(r)` with `r` at `K` bytes into the working space. -/
theorem stw_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 4 ≤ size) :
    exec (.store .w t r d) s =
      some { s with mem := s.mem.writeW (off base (K + d)) (BitVec.ofNat 32 (s.gpr t).toNat) } := by
  have hs15 := hs.small
  rw [exec_store_w hr0 (by omega) (by rw [hr, off_add]; exact hs.wrIn hd), hr, off_add]
  congr 3

/-- `ld t, d(r)` with `r` at `K` bytes into the working space. -/
theorem ld_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd4 : d % 4 = 0) (hd : K + d + 8 ≤ size) :
    exec (.load .d t r d) s = some (s.write t (word s.mem base (K + d))) := by
  have hs15 := hs.small
  rw [exec_load_d hr0 ⟨by omega, hd4⟩ (by rw [hr, off_add]; exact hs.read hd), hr, off_add]

/-- `std t, d(r)` with `r` at `K` bytes into the working space. -/
theorem std_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd4 : d % 4 = 0) (hd : K + d + 8 ≤ size) :
    exec (.store .d t r d) s = some { s with mem := s.mem.writeW (off base (K + d)) (s.gpr t) } := by
  have hs15 := hs.small
  rw [exec_store_d hr0 ⟨by omega, hd4⟩ (by rw [hr, off_add]; exact hs.wrIn hd), hr, off_add]

theorem rotr0 (x : BitVec 32) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem lwz0_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {d : Nat}
    (hr : At s base r 0) (hr0 : r ≠ .r0) (hd : d + 4 ≤ size) :
    exec (.load .w t r d) s = some (s.write t (BitVec.ofNat 64 (w32 s.mem base d))) := by
  rw [lwz_ok hs hr hr0 (by omega), Nat.zero_add]

theorem stw0_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {d : Nat}
    (hr : At s base r 0) (hr0 : r ≠ .r0) (hd : d + 4 ≤ size) :
    exec (.store .w t r d) s =
      some { s with mem := s.mem.writeW (off base d) (BitVec.ofNat 32 (s.gpr t).toNat) } := by
  rw [stw_ok hs hr hr0 (by omega), Nat.zero_add]

theorem ld0_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {d : Nat}
    (hr : At s base r 0) (hr0 : r ≠ .r0) (hd4 : d % 4 = 0) (hd : d + 8 ≤ size) :
    exec (.load .d t r d) s = some (s.write t (word s.mem base d)) := by
  rw [ld_ok hs hr hr0 hd4 (by omega), Nat.zero_add]

/-! ## Words in memory, on a 64-bit address space -/

/-- A 32-bit store at offset `o` leaves the words apart from it. -/
theorem w32_write_ne {m : Mem} {base : Addr} {size o d : Nat} (hn : base.toNat + size ≤ 2 ^ 64)
    (ho : o + 4 ≤ size) (hd : d + 4 ≤ size) (hsep : d + 4 ≤ o ∨ o + 4 ≤ d) (v : BitVec 32) :
    w32 (m.writeW (off base o) v) base d = w32 m base d := by
  have := base.isLt
  rw [w32, Mem.readW_writeW_sep (Offset.sep base hsep (by omega) (by omega)) (by decide)]

/-- The number one word up. -/
theorem val32_succ' (m : Mem) (base : Addr) (d k : Nat) :
    val32 m base d (k + 1) = w32 m base d + 2 ^ 32 * val32 m base (d + 4) k := rfl

end VG.Proof.Mont.PPC64LE
