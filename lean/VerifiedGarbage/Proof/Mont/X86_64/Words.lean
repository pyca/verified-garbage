import VerifiedGarbage.Impl.Mont.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Mont.Words

/-!
# Montgomery arithmetic on x86-64: words in registers and in the working space

Numbers of several words: in registers (`regsVal`, little-endian over a list
of registers) and in the working space (`wordsVal`), which is `size` bytes at
`base`, the value of `rdi` (`Scr`). The loads and stores of the arithmetic,
and what they leave unchanged.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

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

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = off (s.gpr .rdi) d := by
  simp only [State.ea, sc, BitVec.ofInt_natCast]

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem load_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [ea_sc, hs.rdi, State.load64, ite_eq_left ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩]

theorem readSrc_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : readSrc s (.mem (sc d)) = some (word s.mem base d) := load_sc hs hd

theorem store_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (v : BitVec 64) :
    s.store64 (s.ea (sc d)) v = some { s with mem := s.mem.writeW (off base d) v } := by
  rw [ea_sc, hs.rdi, State.store64, ite_eq_left ⟨_, hs.wr, hs.contains hd (by decide)⟩]

theorem ld_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem st_sc {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (h : Keeps rs s s') (hr : .rdi ∉ rs) : Scr s' base size :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

end VG.Proof.Mont.X86_64
