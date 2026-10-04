import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Rc2.PairMem

/-!
# Montgomery arithmetic on x86 (32-bit): words in the working space

The working space is `size` bytes at `base`, whose low 32 bits `edi` holds
(`Scr`), below `2³²`. Its numbers are read as 32-bit words (`w32`, `val32`):
`k` of them at an offset are the same bytes, and the same number, as
`k / 2` 64-bit words (`wordsVal_eq_val32`), in which the other targets and
the target-independent proofs state them. The loads and stores of the
arithmetic, through `edi` or through `ebp`, which the multiplication moves
by 4 bytes a row (`ea_at`), and what changes (`Keeps`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The 32-bit word at `base + d`. -/
abbrev w32 (m : Mem) (base : Addr) (d : Nat) : Nat := (m.readW (off base d) 32).toNat

/-- The `k` 32-bit words at `base + d`, as a little-endian number. -/
def val32 (m : Mem) (base : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => w32 m base d + 2 ^ 32 * val32 m base (d + 4) k

theorem pow32_succ (k : Nat) : 2 ^ (32 * (k + 1)) = 2 ^ 32 * 2 ^ (32 * k) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem val32_lt (m : Mem) (base : Addr) (d k : Nat) : val32 m base d k < 2 ^ (32 * k) := by
  induction k generalizing d with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [val32, pow32_succ]
    have h1 : w32 m base d < 2 ^ 32 := (m.readW (off base d) 32).isLt
    have h2 := ih (d + 4)
    have : 2 ^ 32 * (val32 m base (d + 4) k + 1) ≤ 2 ^ 32 * 2 ^ (32 * k) := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_succ] at this
    omega

theorem val32_append (m : Mem) (base : Addr) (d j k : Nat) :
    val32 m base d (j + k) = val32 m base d j + 2 ^ (32 * j) * val32 m base (d + 4 * j) k := by
  induction j generalizing d with
  | zero => simp only [val32, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, val32, ih, val32, pow32_succ, show d + 4 + 4 * j = d + 4 * (j + 1) by omega,
      Nat.mul_add, Nat.mul_assoc]
    omega

/-- The last word of a number. -/
theorem val32_succ (m : Mem) (base : Addr) (d k : Nat) :
    val32 m base d (k + 1) = val32 m base d k + 2 ^ (32 * k) * w32 m base (d + 4 * k) := by
  rw [val32_append, val32, val32, Nat.mul_zero, Nat.add_zero]

theorem val32_congr {m m' : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (d + 4 * j) = w32 m base (d + 4 * j)) →
      val32 m' base d k = val32 m base d k
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_succ, h k (Nat.lt_succ_self _), val32_congr fun j hj => h j (by omega)]

/-- A 64-bit word is two 32-bit words. -/
theorem word_eq_w32 (m : Mem) (base : Addr) (d : Nat) :
    (word m base d).toNat = w32 m base d + 2 ^ 32 * w32 m base (d + 4) := by
  rw [word, Rc2.Word32.read64_pair, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (m.readW (off base d) 32).isLt, Nat.shiftLeft_eq, Offset.add_add]
  simp only [w32, off]
  omega

/-- `n` 64-bit words are `2n` 32-bit words. -/
theorem wordsVal_eq_val32 (m : Mem) (base : Addr) (d n : Nat) :
    wordsVal m base d n = val32 m base d (2 * n) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [wordsVal, ih, word_eq_w32, show 2 * (n + 1) = 2 + 2 * n by omega, val32_append, val32, val32,
      val32, show d + 8 = d + 4 * 2 by omega, show (2 : Nat) ^ (32 * 2) = 2 ^ 64 by decide]
    omega

/-! ## The working space -/

/-- The working space: `edi` holds its base `base`, it is writable and it
lies below `2³²`. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  edi : (s.gpr .edi).setWidth 64 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

theorem Scr.edi_toNat {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    (s.gpr .edi).toNat = base.toNat := by
  rw [← hs.edi, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .edi).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- `[edi + d]`. -/
theorem Scr.ea {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d < size) : s.ea (sc d) = off base d := by
  change addr (s.gpr .edi) d = _
  rw [addr_eq (by have := hs.nowrap; have := hs.edi_toNat; omega), hs.edi]

/-- `[ebp + d]`, with `ebp` at `4i` bytes into the working space. -/
theorem Scr.ea_at {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    s.ea (at_ .ebp d) = off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem Scr.contains {base : Addr} {size d n : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (h : d + n ≤ size) :
    (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, Scr.contains hs.nowrap hd⟩

theorem Scr.write {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n := ⟨_, hs.wr, Scr.contains hs.nowrap hd⟩

/-- The registers and permissions that a piece of code preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : Keeps rs s s') (hr : .edi ∉ rs) : Scr s' base size :=
  ⟨by rw [h.1 _ hr]; exact hs.edi, h.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Stores -/

/-- A 32-bit store at offset `o` leaves the words apart from it. -/
theorem w32_write_ne {m : Mem} {base : Addr} {size o d : Nat} (hn : base.toNat + size ≤ 2 ^ 32)
    (ho : o + 4 ≤ size) (hd : d + 4 ≤ size) (hsep : d + 4 ≤ o ∨ o + 4 ≤ d) (v : BitVec 32) :
    w32 (m.writeW (off base o) v) base d = w32 m base d := by
  rw [w32, Mem.readW_writeW_sep (Offset.sep base hsep (by omega) (by omega)) (by decide)]

/-- A 32-bit store at offset `o` is read back. -/
theorem w32_write_self (m : Mem) (base : Addr) (o : Nat) (v : BitVec 32) :
    w32 (m.writeW (off base o) v) base o = v.toNat := by
  rw [w32, Mem.readW_writeW_self32]

/-- A 32-bit store changes only its 4 bytes. -/
theorem writeW32_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 2 ^ 64) :
    Outside base d 4 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- A word at an offset outside the bytes that changed. -/
theorem _root_.VG.Proof.Mont.Outside.w32 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d :=
  congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (by rw [ofs_off base (by omega)]; omega))

theorem _root_.VG.Proof.Mont.Outside.val32 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d k : Nat} (hd : d + 4 * k ≤ o ∨ o + n ≤ d) (hd' : d + 4 * k ≤ 2 ^ 64) :
    val32 m' base d k = val32 m base d k :=
  val32_congr fun j hj => h.w32 (by omega) (by omega)

end VG.Proof.Mont.X86
