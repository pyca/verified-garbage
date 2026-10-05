import VerifiedGarbage.Impl.Bignum.X86_64.Adx
import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Impl.Rsa.X86_64

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Words`. -/
section

/-!
# Multiword arithmetic on x86-64: words in the working space

The working space is `size` bytes at `base` (`Scr`), writable and not
wrapping around. A number of `n` words at byte offset `d` of it is
`wv m base d n`, little-endian. The arrays' words are addressed as
`[b + 8 i + disp]` with a base `b = base + e` and an index `i` in registers
(`ea_ix`).

`Outside base o n m m'`: `m'` agrees with `m` but on the bytes at offsets
`[o, o + n)` of `base`, so a number elsewhere keeps its value
(`Outside.wv`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (load64_eq store64_eq)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The word at `p + d`. -/
abbrev word (m : Mem) (p : Addr) (d : Nat) : BitVec 64 := m.readW (VG.Proof.Bignum.X86_64.off p d) 64

/-- The `n` words at `p + d`, little-endian. -/
def wv (m : Mem) (p : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.Bignum.X86_64.wv m p d n + 2 ^ (64 * n) * (VG.Proof.Bignum.X86_64.word m p (d + 8 * n)).toNat

theorem pow64_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

theorem wv_lt (m : Mem) (p : Addr) (d n : Nat) : VG.Proof.Bignum.X86_64.wv m p d n < 2 ^ (64 * n) := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.pow64_succ]
    have hw := (VG.Proof.Bignum.X86_64.word m p (d + 8 * n)).isLt
    have : 2 ^ (64 * n) * (VG.Proof.Bignum.X86_64.word m p (d + 8 * n)).toNat ≤ 2 ^ (64 * n) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega

theorem wv_congr {m m' : Mem} {p : Addr} {d n : Nat}
    (h : ∀ i < n, VG.Proof.Bignum.X86_64.word m' p (d + 8 * i) = VG.Proof.Bignum.X86_64.word m p (d + 8 * i)) : VG.Proof.Bignum.X86_64.wv m' p d n = VG.Proof.Bignum.X86_64.wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.Bignum.X86_64.wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- A number of `n + k` words is its low `n` words and its high `k` words. -/
theorem wv_add (m : Mem) (p : Addr) (d n k : Nat) :
    VG.Proof.Bignum.X86_64.wv m p d (n + k) = VG.Proof.Bignum.X86_64.wv m p d n + 2 ^ (64 * n) * VG.Proof.Bignum.X86_64.wv m p (d + 8 * n) k := by
  induction k with
  | zero => simp [VG.Proof.Bignum.X86_64.wv]
  | succ k ih =>
    rw [← Nat.add_assoc, VG.Proof.Bignum.X86_64.wv, ih, VG.Proof.Bignum.X86_64.wv, show 64 * (n + k) = 64 * n + 64 * k by omega, Nat.pow_add,
      show d + 8 * (n + k) = d + 8 * n + 8 * k by omega, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- A number is zero iff its words are. -/
theorem wv_eq_zero_iff (m : Mem) (p : Addr) (d n : Nat) :
    VG.Proof.Bignum.X86_64.wv m p d n = 0 ↔ ∀ q < n, VG.Proof.Bignum.X86_64.word m p (d + 8 * q) = 0 := by
  induction n with
  | zero => simp [VG.Proof.Bignum.X86_64.wv]
  | succ n ih =>
    rw [VG.Proof.Bignum.X86_64.wv]
    constructor
    · intro h q hq
      have h1 : VG.Proof.Bignum.X86_64.wv m p d n = 0 := by omega
      have h2 : 2 ^ (64 * n) * (VG.Proof.Bignum.X86_64.word m p (d + 8 * n)).toNat = 0 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
      · exact ih.mp h1 q hq
      · subst hq
        rcases Nat.mul_eq_zero.mp h2 with h | h
        · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos _))
        · exact BitVec.eq_of_toNat_eq h
    · intro h
      rw [ih.mpr fun q hq => h q (by omega), h n (by omega)]
      rfl

/-- A number whose words but word `i` are zero. -/
theorem wv_single (m : Mem) (p : Addr) (d : Nat) {i : Nat} :
    ∀ n, i < n → (∀ q < n, q ≠ i → VG.Proof.Bignum.X86_64.word m p (d + 8 * q) = 0) →
      VG.Proof.Bignum.X86_64.wv m p d n = (VG.Proof.Bignum.X86_64.word m p (d + 8 * i)).toNat * 2 ^ (64 * i)
  | 0, hi, _ => absurd hi (by omega)
  | n + 1, hi, h => by
    rw [VG.Proof.Bignum.X86_64.wv]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [VG.Proof.Bignum.X86_64.wv_single m p d n hi fun q hq hne => h q (by omega) hne, h n (by omega) (by omega)]
      simp
    · subst hi
      rw [(VG.Proof.Bignum.X86_64.wv_eq_zero_iff m p d i).mpr fun q hq => h q (by omega) (by omega), Nat.zero_add, Nat.mul_comm]

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, within a writable region,
not wrapping around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wr : ∃ B₀ : Addr, ∃ o L : Nat, (⟨B₀, L⟩ : Region) ∈ s.wr ∧ base = VG.Proof.Bignum.X86_64.off B₀ o ∧ o + size ≤ L ∧ L ≤ 2 ^ 64
  nowrap : base.toNat + size ≤ 2 ^ 64

/-- A writable region is a working space. -/
theorem Scr.of_mem {s : State} {base : Addr} {size : Nat} (h : (⟨base, size⟩ : Region) ∈ s.wr)
    (hn : base.toNat + size ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.Scr s base size :=
  ⟨⟨base, 0, size, h, by simp [VG.Proof.Bignum.X86_64.off], by omega, by omega⟩, hn⟩

/-- `size` bytes at offset `o` of a working space. -/
theorem Scr.sub {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size) {o n : Nat}
    (h : o + n ≤ size) (hn0 : 0 < n) : VG.Proof.Bignum.X86_64.Scr s (VG.Proof.Bignum.X86_64.off base o) n := by
  obtain ⟨⟨B₀, o₀, L, hm, hb, hL, hL'⟩, hn⟩ := hs
  refine ⟨⟨B₀, o₀ + o, L, hm, ?_, by omega, hL'⟩, ?_⟩
  · subst hb; simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [show (VG.Proof.Bignum.X86_64.off base o).toNat = base.toNat + o by
      simp only [VG.Proof.Bignum.X86_64.off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]]
    omega

theorem Scr.region {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : ∃ r ∈ s.wr, r.Contains (VG.Proof.Bignum.X86_64.off base d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _⟩ := hs
  refine ⟨_, hm, ?_⟩
  rw [hb, show VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off B₀ o) d = VG.Proof.Bignum.X86_64.off B₀ (o + d) by simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact Offset.contains_base B₀ (by omega) (by omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (VG.Proof.Bignum.X86_64.off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.st8 {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size) {d : Nat}
    (hd : d + 1 ≤ size) : InRegions s.wr (VG.Proof.Bignum.X86_64.off base d) 1 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s base size)
    (h : s'.wr = s.wr) : VG.Proof.Bignum.X86_64.Scr s' base size :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, h ▸ hm, hb, hL, hL'⟩, hs.nowrap⟩

/-! ## Addresses -/

theorem off_off (p : Addr) (a b : Nat) : VG.Proof.Bignum.X86_64.off (VG.Proof.Bignum.X86_64.off p a) b = VG.Proof.Bignum.X86_64.off p (a + b) := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_mul8 (j : Nat) : BitVec.ofNat 64 j * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * j) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem ofInt_ofNat (d : Nat) : BitVec.ofInt 64 (Int.ofNat d) = BitVec.ofNat 64 d := by
  rw [Int.ofNat_eq_natCast, BitVec.ofInt_natCast]

/-- `[b + 8 i + d]` for `b = p + e` and `i = j`. -/
theorem ea_ix (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (d : Nat) :
    s.ea (ix b i (Int.ofNat d)) = VG.Proof.Bignum.X86_64.off p (e + 8 * j + d) := by
  simp only [State.ea, ix, hb, hi, VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.ofInt_ofNat, VG.Proof.Bignum.X86_64.ofNat_mul8, BitVec.add_assoc, BitVec.ofNat_add]

theorem ea_ix0 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i) = VG.Proof.Bignum.X86_64.off p (e + 8 * j) := by
  have := VG.Proof.Bignum.X86_64.ea_ix s hb hi 0
  rwa [Nat.add_zero] at this

theorem ea_ix8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i 8) = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8) :=
  VG.Proof.Bignum.X86_64.ea_ix s hb hi 8

/-- `[b + 8 i - 8]` for `b = p + e` and `i = j ≥ 1`. -/
theorem ea_ixm8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (hj : 1 ≤ j) :
    s.ea (ix b i (-8)) = VG.Proof.Bignum.X86_64.off p (e + 8 * (j - 1)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (8 * (j - 1)) := by
    rw [show (-8 : Int) = - ((8 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 1) + 8 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  simp only [State.ea, ix, hb, hi, VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.ofNat_mul8, BitVec.add_assoc, h8, BitVec.ofNat_add]

theorem ea_at0 (s : State) {b : Reg} {p : Addr} {e : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e) :
    s.ea (at0 b) = VG.Proof.Bignum.X86_64.off p e := by
  simp only [State.ea, at0, hb, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem ea_hdr (s : State) {p : Addr} (hb : s.gpr .rdi = p) (i : Nat) :
    s.ea (VG.Impl.Bignum.X86_64.hdr i) = VG.Proof.Bignum.X86_64.off p (8 * i) := by
  simp only [State.ea, VG.Impl.Bignum.X86_64.hdr, hb, VG.Proof.Bignum.X86_64.off]
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-! ## Memory outside a range of offsets -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.Bignum.X86_64.ofs base x < o ∨ o + n ≤ VG.Proof.Bignum.X86_64.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.Bignum.X86_64.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.Bignum.X86_64.Outside base o n m₂ m₃) : VG.Proof.Bignum.X86_64.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : VG.Proof.Bignum.X86_64.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.Bignum.X86_64.ofs base (VG.Proof.Bignum.X86_64.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.Bignum.X86_64.ofs, VG.Proof.Bignum.X86_64.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.word m' base d = VG.Proof.Bignum.X86_64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.Bignum.X86_64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.wv {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Outside base o n m m')
    {d k : Nat} (hd : d + 8 * k ≤ o ∨ o + n ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.wv m' base d k = VG.Proof.Bignum.X86_64.wv m base d k :=
  VG.Proof.Bignum.X86_64.wv_congr fun i hi => h.word (by omega) (by omega)

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.Outside base d 8 m (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [VG.Proof.Bignum.X86_64.ofs] at hx
  have : (x - VG.Proof.Bignum.X86_64.off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) base d = v := Mem.readW_writeW_self64 m _ v

/-- Writing word `n` of a number of `n + 1` words. -/
theorem wv_writeW_top (m : Mem) (base : Addr) (d n : Nat) (v : BitVec 64) (h : d + 8 * n + 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.wv (m.writeW (VG.Proof.Bignum.X86_64.off base (d + 8 * n)) v) base d (n + 1) = VG.Proof.Bignum.X86_64.wv m base d n + 2 ^ (64 * n) * v.toNat := by
  rw [VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.word_writeW_self, (VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega)).wv (Or.inl (Nat.le_refl _)) (by omega)]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AdxStep`. -/
section

/-!
# Multiword arithmetic on x86-64: the steps of the BMI2/ADX multiplication

The instructions of a block of `montMulAdx` (`Impl/Bignum/X86_64/Adx.lean`),
each run symbolically once, for any registers: `mulx`, `adcx` and `adox`
(`mulx_ok`, `adcx_ok`, `adox_ok`), and the shapes made of them, a word of
the block's first half (`wordA_ok`) and of its second (`wordB_ok`), and the
end of a chain (`close_ok`). Each states what it computes as an equation on
numbers, the carries in and out included, which `omega` composes.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Bignum.X86_64.Keeps rs s₁ s₂) (h₂ : VG.Proof.Bignum.X86_64.Keeps rs' s₂ s₃) :
    VG.Proof.Bignum.X86_64.Keeps (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r fun h => hr (List.mem_append_right _ h)).trans (h₁.1 r fun h => hr (List.mem_append_left _ h)),
    h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Bignum.X86_64.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Bignum.X86_64.Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.gpr {rs : List Reg} {s s' : State} (h : VG.Proof.Bignum.X86_64.Keeps rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

/-- A memory operand reads the same after registers other than its own change. -/
theorem Keeps.readMem {rs : List Reg} {s s' : State} (h : VG.Proof.Bignum.X86_64.Keeps rs s s') {m : MemOp} (hb : m.base ∉ rs)
    (hi : ∀ i, m.index = some i → i ∉ rs) : readSrc s' (.mem m) = readSrc s (.mem m) := by
  have hea : s'.ea m = s.ea m := by
    unfold State.ea
    cases e : m.index with
    | none => simp only [h.gpr hb]
    | some i => simp only [h.gpr hb, h.gpr (hi i e)]
  simp only [readSrc, State.load64, hea, h.2.1, h.2.2.1, h.2.2.2]

theorem toNat_ofBool64 (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

/-- The halves of a product of two words: `lo + 2⁶⁴ hi`. -/
theorem mulx_arith (d v : BitVec 64) :
    (BitVec.ofNat 64 (d.toNat * v.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (d.toNat * v.toNat / 2 ^ 64)).toNat = d.toNat * v.toNat := by
  have hd := d.isLt; have hv := v.isLt
  have hp : d.toNat * v.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hd hv
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, VG.Proof.Bignum.X86_64.toNat_ofBool64]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- `mulx hi, lo, src`: `lo + 2⁶⁴ hi = rdx · src`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo src]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ VG.Proof.Bignum.X86_64.Keeps [hi, lo] s s' := by
  have he : execMulx hi lo src s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execMulx, hsrc, Option.map_some]
    | mem m => simp only [execMulx, hsrc, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Bignum.X86_64.mulx_arith _ _, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adcx dst, src`: `dst + 2⁶⁴ CF' = dst + src + CF`, OF unchanged. -/
theorem adcx_ok (s : State) {dst : Reg} {src : Src} {v : BitVec 64} {c : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c) :
    WP isa (.block [.adcx dst src]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧ s'.of = s.of ∧
      (s'.gpr dst).toNat + 2 ^ 64 * c'.toNat = (s.gpr dst).toNat + v.toNat + c.toNat ∧ VG.Proof.Bignum.X86_64.Keeps [dst] s s' := by
  have he : execAdcx dst src s = some ((s.setFlags (some (2 ^ 64 ≤ (s.gpr dst).toNat + v.toNat + c.toNat))
      s.of s.zf s.sf).setReg dst (s.gpr dst + v + (BitVec.ofBool c).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdcx, hsrc, hc, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, Option.some.injEq, exists_eq_left']
  refine ⟨_, rfl, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    exact VG.Proof.Bignum.X86_64.adc_carry _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adox dst, src`: `dst + 2⁶⁴ OF' = dst + src + OF`, CF unchanged. -/
theorem adox_ok (s : State) {dst : Reg} {src : Src} {v : BitVec 64} {o : Bool}
    (hsrc : readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (ho : s.of = some o) :
    WP isa (.block [.adox dst src]) s fun s' => ∃ o' : Bool, s'.of = some o' ∧ s'.cf = s.cf ∧
      (s'.gpr dst).toNat + 2 ^ 64 * o'.toNat = (s.gpr dst).toNat + v.toNat + o.toNat ∧ VG.Proof.Bignum.X86_64.Keeps [dst] s s' := by
  have he : execAdox dst src s = some ((s.setFlags s.cf (some (2 ^ 64 ≤ (s.gpr dst).toNat + v.toNat + o.toNat))
      s.zf s.sf).setReg dst (s.gpr dst + v + (BitVec.ofBool o).setWidth 64)) := by
    cases src with
    | imm n => exact absurd rfl (himm n)
    | reg r => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
    | mem m => simp only [execAdox, hsrc, ho, Option.bind_some, Option.map_some]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, he, Option.some.injEq, exists_eq_left']
  refine ⟨_, rfl, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    exact VG.Proof.Bignum.X86_64.adc_carry _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `mov32 r, 0`: the flags unchanged. -/
theorem movZero_ok (s : State) (r : Reg) :
    WP isa (.block [.mov32 r (.imm 0)]) s fun s' =>
      s'.gpr r = 0 ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ VG.Proof.Bignum.X86_64.Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- A word of a block's first half: `col := lo(rdx · b_k) + T_k + CF`, then
`+ prev + OF`, the product's high half into `hi`. -/
theorem wordA_ok (s : State) {k : Nat} {hi col prev : Reg} {vb vt : BitVec 64} {c o : Bool}
    (hb : readSrc s (.mem (ix .r9 .r14 (8 * k))) = some vb) (ht : readSrc s (.mem (ix .r8 .r14 (8 * k))) = some vt)
    (hc : s.cf = some c) (ho : s.of = some o) (d1 : hi ≠ col) (d2 : prev ≠ hi) (d3 : prev ≠ col)
    (d4 : hi ≠ .r8) (d5 : col ≠ .r8) (d6 : hi ≠ .r14) (d7 : col ≠ .r14) :
    WP isa (.block (wordA k hi col prev)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr col).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (s.gpr .rdx).toNat * vb.toNat + vt.toNat + c.toNat + (s.gpr prev).toNat + o.toNat ∧
      VG.Proof.Bignum.X86_64.Keeps [hi, col] s s' := by
  rw [show wordA k hi col prev = ([.mulx hi col (.mem (ix .r9 .r14 (8 * k)))] : List Instr) ++
    (([.adcx col (.mem (ix .r8 .r14 (8 * k)))] : List Instr) ++ ([.adox col (.reg prev)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.mulx_ok s hb (fun _ h => nomatch h) d1) fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have ht₁ : readSrc s₁ (.mem (ix .r8 .r14 (8 * k))) = some vt := by
    rw [k₁.readMem (by simp [ix]; exact ⟨Ne.symm d4, Ne.symm d5⟩) (by
      intro i hi'; simp only [ix, Option.some.injEq] at hi'; subst hi'; simp; exact ⟨Ne.symm d6, Ne.symm d7⟩)]
    exact ht
  refine WP.mono (VG.Proof.Bignum.X86_64.adcx_ok s₁ ht₁ (fun _ h => nomatch h) (c₁.trans hc)) fun s₂ ⟨c', hc₂, ho₂, e₂, k₂⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.adox_ok s₂ (src := .reg prev) rfl (fun _ h => nomatch h) (ho₂.trans (o₁.trans ho)))
    fun s₃ ⟨o', ho₃, hc₃, e₃, k₃⟩ => ⟨c', o', hc₃.trans hc₂, ho₃, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have p₂ : s₂.gpr prev = s.gpr prev := (k₂.gpr (by simpa using d3)).trans (k₁.gpr (by simp [d2, d3]))
  have h₃ : s₃.gpr hi = s₁.gpr hi := (k₃.gpr (by simpa using d1)).trans (k₂.gpr (by simpa using d1))
  rw [h₃]
  rw [p₂] at e₃
  omega

/-- A word of a block's second half: `col += lo(rdx · m_k) + CF`, then
`+ prev + OF`, the product's high half into `hi`. -/
theorem wordB_ok (s : State) {k : Nat} {hi col prev : Reg} {vm : BitVec 64} {c o : Bool}
    (hm : readSrc s (.mem (ix .r10 .r14 (8 * k))) = some vm)
    (hc : s.cf = some c) (ho : s.of = some o) (d1 : hi ≠ col) (d2 : prev ≠ hi) (d3 : prev ≠ col)
    (d4 : hi ≠ .rsi) (d5 : col ≠ .rsi) (d6 : prev ≠ .rsi) :
    WP isa (.block (wordB k hi col prev)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr col).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (s.gpr col).toNat + (s.gpr .rdx).toNat * vm.toNat + c.toNat + (s.gpr prev).toNat + o.toNat ∧
      VG.Proof.Bignum.X86_64.Keeps [hi, .rsi, col] s s' := by
  rw [show wordB k hi col prev = ([.mulx hi .rsi (.mem (ix .r10 .r14 (8 * k)))] : List Instr) ++
    (([.adcx col (.reg .rsi)] : List Instr) ++ ([.adox col (.reg prev)] : List Instr)) from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.mulx_ok s hm (fun _ h => nomatch h) d4) fun s₁ ⟨e₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.adcx_ok s₁ (src := .reg .rsi) rfl (fun _ h => nomatch h) (c₁.trans hc))
    fun s₂ ⟨c', hc₂, ho₂, e₂, k₂⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.adox_ok s₂ (src := .reg prev) rfl (fun _ h => nomatch h) (ho₂.trans (o₁.trans ho)))
    fun s₃ ⟨o', ho₃, hc₃, e₃, k₃⟩ => ⟨c', o', hc₃.trans hc₂, ho₃, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have p₂ : s₂.gpr prev = s.gpr prev := (k₂.gpr (by simpa using d3)).trans (k₁.gpr (by simp [d2, d6]))
  have h₃ : s₃.gpr hi = s₁.gpr hi := (k₃.gpr (by simpa using d1)).trans (k₂.gpr (by simpa using d1))
  have r₁ : s₁.gpr col = s.gpr col := k₁.gpr (by simp [Ne.symm d1, d5])
  have i₂ : s₂.gpr .rsi = s₁.gpr .rsi := k₂.gpr (by simpa using Ne.symm d5)
  rw [h₃]
  rw [p₂] at e₃
  rw [r₁] at e₂
  omega

/-- The end of both chains: `h += OF + CF`. -/
theorem close_ok (s : State) {h : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o) (hh : h ≠ .rsi) :
    WP isa (.block (close h)) s fun s' => ∃ c' o' : Bool, s'.cf = some c' ∧ s'.of = some o' ∧
      (s'.gpr h).toNat + 2 ^ 64 * c'.toNat + 2 ^ 64 * o'.toNat = (s.gpr h).toNat + c.toNat + o.toNat ∧
      VG.Proof.Bignum.X86_64.Keeps [.rsi, h] s s' := by
  rw [show close h = ([.mov32 .rsi (.imm 0)] : List Instr) ++
    (([.adox h (.reg .rsi)] : List Instr) ++ ([.adcx h (.reg .rsi)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.movZero_ok s .rsi) fun s₁ ⟨z₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.adox_ok s₁ (src := .reg .rsi) rfl (fun _ h => nomatch h) (o₁.trans ho))
    fun s₂ ⟨o', ho₂, hc₂, e₂, k₂⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.adcx_ok s₂ (src := .reg .rsi) rfl (fun _ h => nomatch h) (hc₂.trans (c₁.trans hc)))
    fun s₃ ⟨c', hc₃, ho₃, e₃, k₃⟩ => ⟨c', o', hc₃, ho₃.trans ho₂, ?_, (k₁.trans (k₂.trans k₃)).mono (by simp)⟩
  have r₁ : s₁.gpr h = s.gpr h := k₁.gpr (by simpa using hh)
  have z₂ : s₂.gpr .rsi = 0 := (k₂.gpr (by simpa using Ne.symm hh)).trans z₁
  rw [r₁, z₁] at e₂
  rw [z₂] at e₃
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at e₂ e₃
  omega

/-- `xor esi, esi`: CF and OF clear. -/
theorem xorRsi_ok (s : State) :
    WP isa (.block [.alu32 .xor .rsi (.reg .rsi)]) s fun s' =>
      s'.gpr .rsi = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ VG.Proof.Bignum.X86_64.Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- `mov dst, [m]`: the flags unchanged. -/
theorem movMem_ok (s : State) {dst : Reg} {m : MemOp} {v : BitVec 64} (hsrc : readSrc s (.mem m) = some v) :
    WP isa (.block [.mov dst (.mem m)]) s fun s' =>
      s'.gpr dst = v ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ VG.Proof.Bignum.X86_64.Keeps [dst] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hsrc, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨RegUpd.gpr_setReg_self .., rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Loop`. -/
section

/-!
# Multiword arithmetic on x86-64: loops over the words

`wordLoop start body` runs `body` for `r14 = start, …, w - 1`, with `w` in
`r12`: each iteration ends with `add r14, 1; cmp r14, r12`, and the loop
continues while they differ. `wp_upto` is the loop rule for an invariant
indexed by the counter, and `count_ok` the effect of those two
instructions.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- A loop whose body ends with ZF set when its count `j + 1` reaches `N`:
from `j = a`, the body runs for `j = a, …, N - 1`. -/
theorem wp_upto {body : Prog isa} {a N : Nat} (haN : a < N) (Inv : Nat → State → Prop)
    {Q : State → Prop}
    (hbody : ∀ j, a ≤ j → j < N → ∀ s, Inv j s →
      WP isa body s fun s' => s'.zf = some (decide (j + 1 = N)) ∧ Inv (j + 1) s')
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv a s) : WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = N - j ∧ a ≤ j ∧ j < N ∧ Inv j s) ?_ (N - a) s
    ⟨a, rfl, Nat.le_refl _, haN, h0⟩
  rintro n s ⟨j, rfl, hj, hjN, hI⟩
  refine WP.mono (hbody j hj hjN s hI) fun s' ⟨hz, hI'⟩ => ?_
  by_cases he : j + 1 = N
  · exact .inl ⟨by simp [VG.X86_64.eval, hz, he], hQ s' (he ▸ hI')⟩
  · exact .inr ⟨by simp [VG.X86_64.eval, hz, he], N - (j + 1), by omega, j + 1, rfl, by omega, by omega, hI'⟩

theorem ofNat_add_one (j : Nat) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_beq_zero (a b : BitVec 64) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem ofNat_sub_beq {j N : Nat} (hj : j < 2 ^ 64) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 j - BitVec.ofNat 64 N == 0) = decide (j = N) := by
  rw [VG.Proof.Bignum.X86_64.sub_beq_zero]
  by_cases h : j = N
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hN] at this

/-- `add r14, 1; cmp r14, r12`. -/
theorem count_ok (s : State) {j N : Nat} (hj : s.gpr .r14 = BitVec.ofNat 64 j)
    (hN : s.gpr .r12 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)]) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r14] s s' := by
  refine WP.mono (WP.keep [.r14] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, VG.Proof.Bignum.X86_64.ofNat_add_one, VG.Proof.Bignum.X86_64.ofNat_sub_beq hjN hN']

/-- `add r13, 1; cmp r13, r12`. -/
theorem count13_ok (s : State) {j N : Nat} (hj : s.gpr .r13 = BitVec.ofNat 64 j)
    (hN : s.gpr .r12 = BitVec.ofNat 64 N) (hjN : j + 1 < 2 ^ 64) (hN' : N < 2 ^ 64) :
    WP isa (.block [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r12)]) s fun s' =>
      s'.zf = some (decide (j + 1 = N)) ∧ s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧
      s'.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r13] s s' := by
  refine WP.mono (WP.keep [.r13] (Q := fun s' => s'.zf = some (decide (j + 1 = N)) ∧
    s'.gpr .r13 = BitVec.ofNat 64 (j + 1) ∧ s'.mem = s.mem) ?_ rfl) fun s' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [hj, hN, VG.Proof.Bignum.X86_64.ofNat_add_one, VG.Proof.Bignum.X86_64.ofNat_sub_beq hjN hN']

/-- `wordLoop start body`: `r14 := start`, then the body and the count for
`r14 = start, …, N - 1`. -/
theorem wordLoop_ok {start N : Nat} {body : List Instr} (hst : start < N) (hN : N < 2 ^ 31)
    (Inv : Nat → State → Prop) {s : State}
    (h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 start → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      Inv start t)
    (hstep : ∀ j, start ≤ j → j < N → ∀ t, Inv j t →
      WP isa (.block (body ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
        t'.zf = some (decide (j + 1 = N)) ∧ Inv (j + 1) t') :
    WP isa (wordLoop start body) s (Inv N) := by
  unfold wordLoop
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 start ∧
    t.mem = s.mem ∧ t.cf = s.cf) (by xrun [sx_ofNat (show start < 2 ^ 31 by omega)]) rfl)
    fun t ⟨⟨h14, hm, hc⟩, k⟩ => ?_)
  exact VG.Proof.Bignum.X86_64.wp_upto hst Inv hstep (fun _ h => h) (h0 t h14 hm k hc)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock`. -/
section

/-!
# Multiword arithmetic on x86-64: a block of the BMI2/ADX multiplication

A block of `montMulAdx` (`Impl/Bignum/X86_64/Adx.lean`) adds `a_i` times
four words of `b` and `u` times four words of `m` to four words of the
window, with the carries `rcx` and `rbp` in and out (`block_ok`). Its first
half (`halfA_ok`) and its second (`halfB_ok`) each end their two chains in
their carry register, which their sums' bounds (`halfA_arith`,
`halfB_arith`) keep from overflowing, so the flags are clear after each.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep sx4)

/-! ## Addresses -/

theorem ea_ixk (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (k : Nat) :
    s.ea (ix b i (8 * (k : Int))) = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8 * k) := by
  rw [show (8 * (k : Int)) = Int.ofNat (8 * k) by rw [Int.ofNat_eq_natCast, Int.natCast_mul]; rfl]
  exact VG.Proof.Bignum.X86_64.ea_ix s hb hi _

theorem ea_below (s : State) {b : Reg} {p : Addr} {e d : Nat} (hb : s.gpr b = VG.Proof.Bignum.X86_64.off p e) (hd : d ≤ e) :
    s.ea { base := b, disp := -(d : Int) } = VG.Proof.Bignum.X86_64.off p (e - d) := by
  simp only [State.ea, hb, VG.Proof.Bignum.X86_64.off, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show e = (e - d) + d by omega, BitVec.ofNat_add,
    BitVec.add_sub_cancel, show e - d + d - d = e - d by omega]

/-- A word of the working space, read through a memory operand. -/
theorem readSrc_word {s : State} {B : Addr} {Z : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) {m : MemOp} {d : Nat}
    (he : s.ea m = VG.Proof.Bignum.X86_64.off B d) (hd : d + 8 ≤ Z) : readSrc s (.mem m) = some (VG.Proof.Bignum.X86_64.word s.mem B d) := by
  simp only [readSrc, State.load64, he, hs.ld hd, ite_true]

/-! ## The arithmetic -/

/-- A block's first half: `T + X B + h` over four words fits in five, so the
chains end with their carries zero. -/
theorem halfA_arith {X b₀ b₁ b₂ b₃ t₀ t₁ t₂ t₃ h C₀ C₁ C₂ C₃ H₀ H₁ H₂ H₃ h' : Nat}
    {c₁ c₂ c₃ c₄ o₁ o₂ o₃ o₄ c₅ o₅ : Nat}
    (hb₀ : X * b₀ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hb₁ : X * b₁ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hb₂ : X * b₂ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hb₃ : X * b₃ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (ht₀ : t₀ < 2 ^ 64) (ht₁ : t₁ < 2 ^ 64) (ht₂ : t₂ < 2 ^ 64) (ht₃ : t₃ < 2 ^ 64) (hh : h < 2 ^ 64)
    (hC₀ : C₀ < 2 ^ 64) (hC₁ : C₁ < 2 ^ 64) (hC₂ : C₂ < 2 ^ 64) (hC₃ : C₃ < 2 ^ 64) (hh' : h' < 2 ^ 64)
    (e₀ : C₀ + 2 ^ 64 * c₁ + 2 ^ 64 * o₁ + 2 ^ 64 * H₀ = X * b₀ + t₀ + 0 + h + 0)
    (e₁ : C₁ + 2 ^ 64 * c₂ + 2 ^ 64 * o₂ + 2 ^ 64 * H₁ = X * b₁ + t₁ + c₁ + H₀ + o₁)
    (e₂ : C₂ + 2 ^ 64 * c₃ + 2 ^ 64 * o₃ + 2 ^ 64 * H₂ = X * b₂ + t₂ + c₂ + H₁ + o₂)
    (e₃ : C₃ + 2 ^ 64 * c₄ + 2 ^ 64 * o₄ + 2 ^ 64 * H₃ = X * b₃ + t₃ + c₃ + H₂ + o₃)
    (e₄ : h' + 2 ^ 64 * c₅ + 2 ^ 64 * o₅ = H₃ + c₄ + o₄) :
    c₅ = 0 ∧ o₅ = 0 ∧
      C₀ + 2 ^ 64 * C₁ + 2 ^ 128 * C₂ + 2 ^ 192 * C₃ + 2 ^ 256 * h' =
        X * b₀ + 2 ^ 64 * (X * b₁) + 2 ^ 128 * (X * b₂) + 2 ^ 192 * (X * b₃) +
          (t₀ + 2 ^ 64 * t₁ + 2 ^ 128 * t₂ + 2 ^ 192 * t₃) + h := by
  omega

/-- A block's second half: `C + U M + h` over four words fits in five. -/
theorem halfB_arith {U m₀ m₁ m₂ m₃ C₀ C₁ C₂ C₃ h D₀ D₁ D₂ D₃ G₀ G₁ G₂ G₃ h' : Nat}
    {c₁ c₂ c₃ c₄ o₁ o₂ o₃ o₄ c₅ o₅ : Nat}
    (hm₀ : U * m₀ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hm₁ : U * m₁ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hm₂ : U * m₂ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hm₃ : U * m₃ ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (hC₀ : C₀ < 2 ^ 64) (hC₁ : C₁ < 2 ^ 64) (hC₂ : C₂ < 2 ^ 64) (hC₃ : C₃ < 2 ^ 64) (hh : h < 2 ^ 64)
    (hD₀ : D₀ < 2 ^ 64) (hD₁ : D₁ < 2 ^ 64) (hD₂ : D₂ < 2 ^ 64) (hD₃ : D₃ < 2 ^ 64) (hh' : h' < 2 ^ 64)
    (e₀ : D₀ + 2 ^ 64 * c₁ + 2 ^ 64 * o₁ + 2 ^ 64 * G₀ = C₀ + U * m₀ + 0 + h + 0)
    (e₁ : D₁ + 2 ^ 64 * c₂ + 2 ^ 64 * o₂ + 2 ^ 64 * G₁ = C₁ + U * m₁ + c₁ + G₀ + o₁)
    (e₂ : D₂ + 2 ^ 64 * c₃ + 2 ^ 64 * o₃ + 2 ^ 64 * G₂ = C₂ + U * m₂ + c₂ + G₁ + o₂)
    (e₃ : D₃ + 2 ^ 64 * c₄ + 2 ^ 64 * o₄ + 2 ^ 64 * G₃ = C₃ + U * m₃ + c₃ + G₂ + o₃)
    (e₄ : h' + 2 ^ 64 * c₅ + 2 ^ 64 * o₅ = G₃ + c₄ + o₄) :
    D₀ + 2 ^ 64 * D₁ + 2 ^ 128 * D₂ + 2 ^ 192 * D₃ + 2 ^ 256 * h' =
      (C₀ + 2 ^ 64 * C₁ + 2 ^ 128 * C₂ + 2 ^ 192 * C₃) +
        (U * m₀ + 2 ^ 64 * (U * m₁) + 2 ^ 128 * (U * m₂) + 2 ^ 192 * (U * m₃)) + h := by
  omega

/-! ## The first half -/

/-- `a_i` times four words of `b` added to four words of the window and the
carry `rcx`: the sum into `r11`, `r12`, `r13`, `r15` and `rcx`. -/
def halfA : List Instr :=
  [.alu32 .xor .rsi (.reg .rsi), .mov .rdx (.mem xSlot)] ++ (wordA 0 .rax .r11 .rcx ++
    (wordA 1 .rsi .r12 .rax ++ (wordA 2 .rax .r13 .rsi ++ (wordA 3 .rcx .r15 .rax ++ close .rcx))))

theorem halfA_ok {s : State} {B : Addr} {Z e eb j : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (he : 16 ≤ e) (hZ : e + 8 * j + 32 ≤ Z)
    (hZb : eb + 8 * j + 32 ≤ Z) :
    WP isa (.block VG.Proof.Bignum.X86_64.halfA) s fun t => t.cf = some false ∧ t.of = some false ∧
      t.gpr .rdx = VG.Proof.Bignum.X86_64.word s.mem B (e - 16) ∧
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .r13).toNat +
          2 ^ 192 * (t.gpr .r15).toNat + 2 ^ 256 * (t.gpr .rcx).toNat =
        (VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * 0)).toNat +
          2 ^ 64 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * 1)).toNat) +
          2 ^ 128 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * 2)).toNat) +
          2 ^ 192 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * 3)).toNat) +
          ((VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 0)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 1)).toNat +
            2 ^ 128 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 2)).toNat + 2 ^ 192 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 3)).toNat) +
          (s.gpr .rcx).toNat ∧
      VG.Proof.Bignum.X86_64.Keeps [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx] s t := by
  have rb : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * k)) :=
    fun k hk => VG.Proof.Bignum.X86_64.readSrc_word hs (VG.Proof.Bignum.X86_64.ea_ixk s h9 h14 k) (by omega)
  have rt : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * k)) :=
    fun k hk => VG.Proof.Bignum.X86_64.readSrc_word hs (VG.Proof.Bignum.X86_64.ea_ixk s h8 h14 k) (by omega)
  have rx : readSrc s (.mem xSlot) = some (VG.Proof.Bignum.X86_64.word s.mem B (e - 16)) :=
    VG.Proof.Bignum.X86_64.readSrc_word hs (VG.Proof.Bignum.X86_64.ea_below s (d := 16) h8 he) (by omega)
  -- Reads through registers the steps keep.
  have kr : ∀ {rs : List Reg} {t : State}, VG.Proof.Bignum.X86_64.Keeps rs s t → .r8 ∉ rs → .r9 ∉ rs → .r14 ∉ rs →
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r9 .r14 (8 * (k : Int)))) = some (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * k))) ∧
      (∀ k : Nat, k < 4 → readSrc t (.mem (ix .r8 .r14 (8 * (k : Int)))) = some (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * k))) :=
    fun K a b c => ⟨fun k hk => (K.readMem (by simpa [ix] using b) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rb k hk),
      fun k hk => (K.readMem (by simpa [ix] using a) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rt k hk)⟩
  unfold VG.Proof.Bignum.X86_64.halfA
  rw [WP.block_append_iff, show ([.alu32 .xor .rsi (.reg .rsi), .mov .rdx (.mem xSlot)] : List Instr) =
    [.alu32 .xor .rsi (.reg .rsi)] ++ [.mov .rdx (.mem xSlot)] from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.xorRsi_ok s) fun s₁ ⟨_, c₁, o₁, k₁⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.movMem_ok s₁ (dst := .rdx) ((k₁.readMem (by decide) (by intro i h; cases h)).trans rx))
    fun s₂ ⟨d₂, c₂, o₂, k₂⟩ => ?_
  have K₂ := (k₁.trans k₂)
  obtain ⟨rb₂, rt₂⟩ := kr K₂ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordA_ok s₂ (rb₂ 0 (by decide)) (rt₂ 0 (by decide)) (c₂.trans c₁) (o₂.trans o₁)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨a₁, p₁, ca₁, oa₁, e₀, k₃⟩ => ?_
  have K₃ := K₂.trans k₃
  obtain ⟨rb₃, rt₃⟩ := kr K₃ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordA_ok s₃ (rb₃ 1 (by decide)) (rt₃ 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₂, p₂, ca₂, oa₂, e₁, k₄⟩ => ?_
  have K₄ := K₃.trans k₄
  obtain ⟨rb₄, rt₄⟩ := kr K₄ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordA_ok s₄ (rb₄ 2 (by decide)) (rt₄ 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₃, p₃, ca₃, oa₃, e₂, k₅⟩ => ?_
  have K₅ := K₄.trans k₅
  obtain ⟨rb₅, rt₅⟩ := kr K₅ (by decide) (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordA_ok s₅ (rb₅ 3 (by decide)) (rt₅ 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₆ ⟨a₄, p₄, ca₄, oa₄, e₃, k₆⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.close_ok s₆ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₇⟩ => ?_
  have K := (K₅.trans k₆).trans k₇
  -- The registers along the way.
  have x₂ : s₂.gpr .rdx = VG.Proof.Bignum.X86_64.word s.mem B (e - 16) := d₂
  have x₃ : s₃.gpr .rdx = s₂.gpr .rdx := k₃.gpr (by decide)
  have x₄ : s₄.gpr .rdx = s₂.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  have x₅ : s₅.gpr .rdx = s₂.gpr .rdx := (k₅.gpr (by decide)).trans x₄
  have c₀ : s₂.gpr .rcx = s.gpr .rcx := K₂.gpr (by decide)
  have r11 : t.gpr .r11 = s₃.gpr .r11 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans
    ((k₅.gpr (by decide)).trans (k₄.gpr (by decide))))
  have r12 : t.gpr .r12 = s₄.gpr .r12 := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans (k₅.gpr (by decide)))
  have r13 : t.gpr .r13 = s₅.gpr .r13 := (k₇.gpr (by decide)).trans (k₆.gpr (by decide))
  have r15 : t.gpr .r15 = s₆.gpr .r15 := k₇.gpr (by decide)
  rw [x₂] at e₀
  rw [x₃, x₂] at e₁
  rw [x₄, x₂] at e₂
  rw [x₅, x₂] at e₃
  rw [c₀] at e₀
  simp only [Bool.toNat_false] at e₀
  have hb : ∀ k, (VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).isLt; omega)
        (by have := (VG.Proof.Bignum.X86_64.word s.mem B (eb + 8 * j + 8 * k)).isLt; omega)
  obtain ⟨z₁, z₂, e⟩ := VG.Proof.Bignum.X86_64.halfA_arith (hb 0) (hb 1) (hb 2) (hb 3) (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 0)).isLt
    (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 1)).isLt (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 2)).isLt
    (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * j + 8 * 3)).isLt (s.gpr .rcx).isLt (s₃.gpr .r11).isLt (s₄.gpr .r12).isLt
    (s₅.gpr .r13).isLt (s₆.gpr .r15).isLt (t.gpr .rcx).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, ?_, ?_, ?_, K.mono (by simp)⟩
  · rw [ca₅]; cases a₅ <;> simp_all
  · rw [oa₅]; cases p₅ <;> simp_all
  · rw [(k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans x₅)]
    exact x₂
  · rw [r11, r12, r13, r15]; exact e

/-! ## The second half -/

/-- `u` times four words of `m` added to `r11`, `r12`, `r13`, `r15` and the
carry `rbp`. -/
def halfB : List Instr :=
  [.mov .rdx (.mem uSlot)] ++ (wordB 0 .rax .r11 .rbp ++
    (wordB 1 .rbp .r12 .rax ++ (wordB 2 .rax .r13 .rbp ++ (wordB 3 .rbp .r15 .rax ++ close .rbp))))

theorem halfB_ok {s : State} {B : Addr} {Z e eN j : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (he : 16 ≤ e) (hZ : e ≤ Z)
    (hZN : eN + 8 * j + 32 ≤ Z) (hc : s.cf = some false) (ho : s.of = some false) :
    WP isa (.block VG.Proof.Bignum.X86_64.halfB) s fun t =>
      (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (t.gpr .r13).toNat +
          2 ^ 192 * (t.gpr .r15).toNat + 2 ^ 256 * (t.gpr .rbp).toNat =
        ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat + 2 ^ 128 * (s.gpr .r13).toNat +
          2 ^ 192 * (s.gpr .r15).toNat) +
        ((VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * 0)).toNat +
          2 ^ 64 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * 1)).toNat) +
          2 ^ 128 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * 2)).toNat) +
          2 ^ 192 * ((VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * 3)).toNat)) +
        (s.gpr .rbp).toNat ∧
      VG.Proof.Bignum.X86_64.Keeps [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rbp] s t := by
  have rm : ∀ k : Nat, k < 4 → readSrc s (.mem (ix .r10 .r14 (8 * (k : Int)))) =
      some (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * k)) :=
    fun k hk => VG.Proof.Bignum.X86_64.readSrc_word hs (VG.Proof.Bignum.X86_64.ea_ixk s h10 h14 k) (by omega)
  have ru : readSrc s (.mem uSlot) = some (VG.Proof.Bignum.X86_64.word s.mem B (e - 8)) :=
    VG.Proof.Bignum.X86_64.readSrc_word hs (VG.Proof.Bignum.X86_64.ea_below s (d := 8) h8 (by omega)) (by omega)
  have kr : ∀ {rs : List Reg} {t : State}, VG.Proof.Bignum.X86_64.Keeps rs s t → .r10 ∉ rs → .r14 ∉ rs →
      ∀ k : Nat, k < 4 → readSrc t (.mem (ix .r10 .r14 (8 * (k : Int)))) = some (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * k)) :=
    fun K a c k hk => (K.readMem (by simpa [ix] using a) (by
        intro i hi; simp only [ix, Option.some.injEq] at hi; subst hi; exact c)).trans (rm k hk)
  unfold VG.Proof.Bignum.X86_64.halfB
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.movMem_ok s (dst := .rdx) ru) fun s₁ ⟨d₁, c₁, o₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordB_ok s₁ (kr k₁ (by decide) (by decide) 0 (by decide)) (c₁.trans hc) (o₁.trans ho)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₂ ⟨a₁, p₁, ca₁, oa₁, e₀, k₂⟩ => ?_
  have K₂ := k₁.trans k₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordB_ok s₂ (kr K₂ (by decide) (by decide) 1 (by decide)) ca₁ oa₁
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₃ ⟨a₂, p₂, ca₂, oa₂, e₁, k₃⟩ => ?_
  have K₃ := K₂.trans k₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordB_ok s₃ (kr K₃ (by decide) (by decide) 2 (by decide)) ca₂ oa₂
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₄ ⟨a₃, p₃, ca₃, oa₃, e₂, k₄⟩ => ?_
  have K₄ := K₃.trans k₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.wordB_ok s₄ (kr K₄ (by decide) (by decide) 3 (by decide)) ca₃ oa₃
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s₅ ⟨a₄, p₄, ca₄, oa₄, e₃, k₅⟩ => ?_
  refine WP.mono (VG.Proof.Bignum.X86_64.close_ok s₅ ca₄ oa₄ (by decide)) fun t ⟨a₅, p₅, ca₅, oa₅, e₄, k₆⟩ => ?_
  have K := (K₄.trans k₅).trans k₆
  have x₂ : s₂.gpr .rdx = s₁.gpr .rdx := k₂.gpr (by decide)
  have x₃ : s₃.gpr .rdx = s₁.gpr .rdx := (k₃.gpr (by decide)).trans x₂
  have x₄ : s₄.gpr .rdx = s₁.gpr .rdx := (k₄.gpr (by decide)).trans x₃
  have i11 : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  have i12 : s₂.gpr .r12 = s.gpr .r12 := K₂.gpr (by decide)
  have i13 : s₃.gpr .r13 = s.gpr .r13 := K₃.gpr (by decide)
  have i15 : s₄.gpr .r15 = s.gpr .r15 := K₄.gpr (by decide)
  have ib : s₁.gpr .rbp = s.gpr .rbp := k₁.gpr (by decide)
  have r11 : t.gpr .r11 = s₂.gpr .r11 := (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans
    ((k₄.gpr (by decide)).trans (k₃.gpr (by decide))))
  have r12 : t.gpr .r12 = s₃.gpr .r12 := (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans (k₄.gpr (by decide)))
  have r13 : t.gpr .r13 = s₄.gpr .r13 := (k₆.gpr (by decide)).trans (k₅.gpr (by decide))
  have r15 : t.gpr .r15 = s₅.gpr .r15 := k₆.gpr (by decide)
  rw [d₁, i11, ib] at e₀
  rw [x₂, d₁, i12] at e₁
  rw [x₃, d₁, i13] at e₂
  rw [x₄, d₁, i15] at e₃
  simp only [Bool.toNat_false] at e₀
  have hm : ∀ k, (VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * k)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun k => Nat.mul_le_mul (by have := (VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).isLt; omega)
        (by have := (VG.Proof.Bignum.X86_64.word s.mem B (eN + 8 * j + 8 * k)).isLt; omega)
  have e := VG.Proof.Bignum.X86_64.halfB_arith (hm 0) (hm 1) (hm 2) (hm 3) (s.gpr .r11).isLt (s.gpr .r12).isLt (s.gpr .r13).isLt
    (s.gpr .r15).isLt (s.gpr .rbp).isLt (s₂.gpr .r11).isLt (s₃.gpr .r12).isLt (s₄.gpr .r13).isLt
    (s₅.gpr .r15).isLt (t.gpr .rbp).isLt e₀ e₁ e₂ e₃ e₄
  refine ⟨?_, K.mono (by simp)⟩
  rw [r11, r12, r13, r15]; exact e

/-! ## The stores and the count -/

/-- `b + 8 i + 16`, `b + 8 i + 24`, as `xrun` leaves them. -/
theorem addrD {p : Addr} {e j : Nat} (d : Nat) :
    VG.Proof.Bignum.X86_64.off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 (d : Int) = VG.Proof.Bignum.X86_64.off p (e + 8 * j + d) := by
  rw [VG.Proof.Bignum.X86_64.ofNat_mul8, BitVec.ofInt_natCast, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
    ← BitVec.ofNat_add, Nat.add_assoc]

theorem addrK0 {p : Addr} {e j : Nat} :
    VG.Proof.Bignum.X86_64.off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8 * 0) := VG.Proof.Bignum.X86_64.addrD 0
theorem addrK1 {p : Addr} {e j : Nat} :
    VG.Proof.Bignum.X86_64.off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8 * 1) := VG.Proof.Bignum.X86_64.addrD 8
theorem addrK2 {p : Addr} {e j : Nat} :
    VG.Proof.Bignum.X86_64.off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 16 = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8 * 2) := VG.Proof.Bignum.X86_64.addrD 16
theorem addrK3 {p : Addr} {e j : Nat} :
    VG.Proof.Bignum.X86_64.off p e + BitVec.ofNat 64 j * BitVec.ofNat 64 8 + BitVec.ofInt 64 24 = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8 * 3) := VG.Proof.Bignum.X86_64.addrD 24

theorem ofNat_add_four (j : Nat) : BitVec.ofNat 64 j + 4 = BitVec.ofNat 64 (j + 4) := by
  rw [BitVec.ofNat_add]; rfl

/-- The block's last six instructions. -/
def tail : List Instr :=
  [.store (ix .r8 .r14) .r11, .store (ix .r8 .r14 8) .r12, .store (ix .r8 .r14 16) .r13,
    .store (ix .r8 .r14 24) .r15, .alu .add .r14 (.imm 4), .alu .cmp .r14 (.reg .rbx)]

theorem tail_ok {s : State} {B : Addr} {Z e j w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hZ : e + 8 * j + 32 ≤ Z)
    (hjw : j + 4 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block VG.Proof.Bignum.X86_64.tail) s fun t =>
      t.mem = (((s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 0)) (s.gpr .r11)).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 1))
        (s.gpr .r12)).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 2)) (s.gpr .r13)).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 3))
        (s.gpr .r15) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧ t.zf = some (decide (j + 4 = w)) ∧ VG.Proof.MlKem.X86_64.Keep [.r14] s t := by
  have hst : ∀ k, k < 4 → InRegions s.wr (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * k)) 8 := fun k hk => hs.st (by omega)
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.mem = (((s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 0)) (s.gpr .r11)).writeW
      (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 1)) (s.gpr .r12)).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 2)) (s.gpr .r13)).writeW
      (VG.Proof.Bignum.X86_64.off B (e + 8 * j + 8 * 3)) (s.gpr .r15) ∧
      t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧ t.zf = some (decide (j + 4 = w))) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold VG.Proof.Bignum.X86_64.tail
  xrun [State.ea, ix, h8, h14, hbx, VG.Proof.Bignum.X86_64.addrK0, VG.Proof.Bignum.X86_64.addrK1, VG.Proof.Bignum.X86_64.addrK2, VG.Proof.Bignum.X86_64.addrK3, hst 0 (by decide), hst 1 (by decide), hst 2 (by decide), hst 3 (by decide), VG.Proof.Bignum.X86_64.ofNat_add_four,
    VG.Proof.Bignum.X86_64.ofNat_sub_beq hjw hw]

/-! ## The block -/

theorem wv4 (m : Mem) (p : Addr) (d : Nat) :
    VG.Proof.Bignum.X86_64.wv m p d 4 = (VG.Proof.Bignum.X86_64.word m p (d + 8 * 0)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word m p (d + 8 * 1)).toNat +
      2 ^ 128 * (VG.Proof.Bignum.X86_64.word m p (d + 8 * 2)).toNat + 2 ^ 192 * (VG.Proof.Bignum.X86_64.word m p (d + 8 * 3)).toNat := by
  simp only [VG.Proof.Bignum.X86_64.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]

theorem mul_w4 (X a b c d : Nat) : X * (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d) =
    X * a + 2 ^ 64 * (X * b) + 2 ^ 128 * (X * c) + 2 ^ 192 * (X * d) := by
  simp only [Nat.mul_add, Nat.mul_left_comm X]

theorem Keeps.keep {rs : List Reg} {s t : State} (h : VG.Proof.Bignum.X86_64.Keeps rs s t) : VG.Proof.MlKem.X86_64.Keep rs s t := ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Four words written at `d`: the number they make, and nothing else changed. -/
theorem write4 (m : Mem) (B : Addr) (d : Nat) (v₀ v₁ v₂ v₃ : BitVec 64) (hd : d + 32 ≤ 2 ^ 64) :
    let m' := (((m.writeW (VG.Proof.Bignum.X86_64.off B (d + 8 * 0)) v₀).writeW (VG.Proof.Bignum.X86_64.off B (d + 8 * 1)) v₁).writeW (VG.Proof.Bignum.X86_64.off B (d + 8 * 2)) v₂).writeW
      (VG.Proof.Bignum.X86_64.off B (d + 8 * 3)) v₃
    VG.Proof.Bignum.X86_64.wv m' B d 4 = v₀.toNat + 2 ^ 64 * v₁.toNat + 2 ^ 128 * v₂.toNat + 2 ^ 192 * v₃.toNat ∧ VG.Proof.Bignum.X86_64.Outside B d 32 m m' := by
  intro m'
  refine ⟨?_, ?_⟩
  · rw [show (4 : Nat) = 3 + 1 from rfl, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), show (3 : Nat) = 2 + 1 from rfl,
      VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), show (2 : Nat) = 1 + 1 from rfl, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega),
      show (1 : Nat) = 0 + 1 from rfl, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [VG.Proof.Bignum.X86_64.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]
  · exact (((VG.Proof.Bignum.X86_64.writeW_outside m B v₀ (d := d + 8 * 0) (by omega)).mono (by omega) (by omega)).trans
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B v₁ (d := d + 8 * 1) (by omega)).mono (by omega) (by omega))).trans
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B v₂ (d := d + 8 * 2) (by omega)).mono (by omega) (by omega)) |>.trans
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B v₃ (d := d + 8 * 3) (by omega)).mono (by omega) (by omega))

/-- A block: `a_i` times four words of `b` and `u` times four words of `m`
added to four words of the window and the carries. -/
theorem block_ok {s : State} {B : Addr} {Z e eb eN j w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (he : 16 ≤ e) (hZ : e + 8 * j + 32 ≤ Z) (hZb : eb + 8 * j + 32 ≤ Z)
    (hZN : eN + 8 * j + 32 ≤ Z) (hjw : j + 4 ≤ w) (hw : w < 2 ^ 60) :
    WP isa (.block Adx.block) s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B (e + 8 * j) 4 + 2 ^ 256 * ((t.gpr .rcx).toNat + (t.gpr .rbp).toNat) =
        VG.Proof.Bignum.X86_64.wv s.mem B (e + 8 * j) 4 + (VG.Proof.Bignum.X86_64.word s.mem B (e - 16)).toNat * VG.Proof.Bignum.X86_64.wv s.mem B (eb + 8 * j) 4 +
          (VG.Proof.Bignum.X86_64.word s.mem B (e - 8)).toNat * VG.Proof.Bignum.X86_64.wv s.mem B (eN + 8 * j) 4 + (s.gpr .rcx).toNat + (s.gpr .rbp).toNat ∧
      VG.Proof.Bignum.X86_64.Outside B (e + 8 * j) 32 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 4) ∧
      t.zf = some (decide (j + 4 = w)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  rw [show Adx.block = VG.Proof.Bignum.X86_64.halfA ++ (VG.Proof.Bignum.X86_64.halfB ++ VG.Proof.Bignum.X86_64.tail) from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.halfA_ok hs h8 h9 h14 he hZ hZb) fun a ⟨ca, oa, _, ea, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hsa : VG.Proof.Bignum.X86_64.Scr a B Z := hs.congr ka.2.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.halfB_ok hsa ((ka.gpr (by decide)).trans h8) ((ka.gpr (by decide)).trans h10)
    ((ka.gpr (by decide)).trans h14) he (by omega) hZN ca oa) fun b ⟨eb', kb⟩ => ?_
  have hsb : VG.Proof.Bignum.X86_64.Scr b B Z := hsa.congr kb.2.2.2
  have kab := ka.trans kb
  refine WP.mono (VG.Proof.Bignum.X86_64.tail_ok hsb ((kab.gpr (by decide)).trans h8) ((kab.gpr (by decide)).trans h14)
    ((kab.gpr (by decide)).trans hbx) hZ (by omega) (by omega)) fun t ⟨hm, h14', hz, kt⟩ => ?_
  obtain ⟨hv, ho⟩ := VG.Proof.Bignum.X86_64.write4 b.mem B (e + 8 * j) (b.gpr .r11) (b.gpr .r12) (b.gpr .r13) (b.gpr .r15) (by omega)
  have mb : b.mem = s.mem := kab.2.1
  have ma : a.mem = s.mem := ka.2.1
  rw [← hm] at hv ho
  rw [mb] at ho
  rw [ma] at eb'
  have rcx : t.gpr .rcx = a.gpr .rcx := (kt.gpr (by decide)).trans (kb.gpr (by decide))
  have rbp : t.gpr .rbp = b.gpr .rbp := kt.gpr (by decide)
  have rbp₀ : a.gpr .rbp = s.gpr .rbp := ka.gpr (by decide)
  rw [rbp₀] at eb'
  refine ⟨?_, ho, h14', hz, (kab.keep.trans kt).mono (by simp)⟩
  rw [hv, rcx, rbp, VG.Proof.Bignum.X86_64.wv4 s.mem B (e + 8 * j), VG.Proof.Bignum.X86_64.wv4 s.mem B (eb + 8 * j), VG.Proof.Bignum.X86_64.wv4 s.mem B (eN + 8 * j), VG.Proof.Bignum.X86_64.mul_w4, VG.Proof.Bignum.X86_64.mul_w4]
  omega

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.MulAdd`. -/
section

/-!
# Multiword arithmetic on x86-64: multiply-accumulate steps

A step of `mulAddRow` (and of `reduceRow`): with a word `x` of the
accumulator at `aA`, a word `y` of the operand at `aB`, the multiplier
`rcx` and the carry `rbp`, it stores the low word of `rcx y + rbp + x` at
`aA'` (`aA` itself, or the word below) and leaves its high word in `rbp`
(`macStep_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Poly1305.Limbs64 (add_adc_toNat)

theorem sx0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := rfl

/-- `lo + 2⁶⁴ hi = lo + c` with the carry into `hi`. -/
theorem addc_toNat (lo hi c : BitVec 64) (h : lo.toNat + c.toNat + 2 ^ 64 * hi.toNat < 2 ^ 128) :
    (lo + c).toNat + 2 ^ 64 * (hi + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64).toNat =
      lo.toNat + c.toNat + 2 ^ 64 * hi.toNat := by
  have := add_adc_toNat lo c hi 0 (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  rwa [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this

/-- The product `rdx:rax` of `mul`, as a number. -/
theorem mul_toNat (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a.toNat * b.toNat / 2 ^ 64) (by omega)]
  exact Nat.mod_add_div _ _

theorem mul_le (a b : BitVec 64) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

/-- A multiply-accumulate step (`mac src d`) whose operand word is at `aS`,
accumulator word at `aX`, and destination at `aD`. -/
theorem mac_ok (s : State) {src : Reg} {d : Int} {aS aX aD : Addr}
    (eS : s.gpr src + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aS)
    (eX : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = aX)
    (eD : s.gpr .r8 + s.gpr .r14 * BitVec.ofNat 64 8 + BitVec.ofInt 64 d = aD)
    (hS : InRegions (s.rd ++ s.wr) aS 8) (hX : InRegions (s.rd ++ s.wr) aX 8)
    (hD : InRegions s.wr aD 8) :
    WP isa (.block (mac src d)) s fun t =>
      ∃ lo : BitVec 64, t.mem = s.mem.writeW aD lo ∧
        lo.toNat + 2 ^ 64 * (t.gpr .rbp).toNat = (s.gpr .rcx).toNat * (s.mem.readW aS 64).toNat +
          (s.gpr .rbp).toNat + (s.mem.readW aX 64).toNat := by
  unfold mac
  xrun [State.ea, ix, eS, eX, eD, hS, hX, hD, VG.Proof.Bignum.X86_64.sx0]
  refine ⟨_, rfl, ?_⟩
  have hm := VG.Proof.Bignum.X86_64.mul_toNat (s.mem.readW aS 64) (s.gpr .rcx)
  have hl := VG.Proof.Bignum.X86_64.mul_le (s.mem.readW aS 64) (s.gpr .rcx)
  have hc := (s.gpr .rbp).isLt
  have hx := (s.mem.readW aX 64).isLt
  have e1 := VG.Proof.Bignum.X86_64.addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat))
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat / 2 ^ 64)) (s.gpr .rbp) (by omega)
  have e2 := VG.Proof.Bignum.X86_64.addc_toNat (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat) + s.gpr .rbp)
    (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat * (s.gpr .rcx).toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 ((s.mem.readW aS 64).toNat *
        (s.gpr .rcx).toNat)).toNat + (s.gpr .rbp).toNat))).setWidth 64) (s.mem.readW aX 64) (by omega)
  rw [e2, Nat.mul_comm (s.gpr .rcx).toNat]
  omega

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Row`. -/
section

/-!
# Multiword arithmetic on x86-64: `acc += a_i B`

`mulAddRow` adds `rcx · B` (the `w` words at `r9`) into the accumulator
(the `w + 2` words at `r8`): a loop of multiply-accumulate steps over the
`w` words of `B`, then the last carry into words `w` and `w + 1`
(`mulAddRow_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `b + 8 i + 0` for `b = p + e`, `i = j`, as `xrun` leaves it. -/
theorem addr0 {b i p : Addr} {e j : Nat} (hb : b = VG.Proof.Bignum.X86_64.off p e) (hi : i = BitVec.ofNat 64 j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = VG.Proof.Bignum.X86_64.off p (e + 8 * j) := by
  subst hb hi
  rw [VG.Proof.Bignum.X86_64.ofNat_mul8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- `b + 8 i - 8` for `i = j ≥ 1`. -/
theorem addrm8 {b i p : Addr} {e j : Nat} (hb : b = VG.Proof.Bignum.X86_64.off p e) (hi : i = BitVec.ofNat 64 j) (hj : 1 ≤ j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = VG.Proof.Bignum.X86_64.off p (e + 8 * (j - 1)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (8 * (j - 1)) := by
    rw [show (-8 : Int) = - ((8 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 1) + 8 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  subst hb hi
  rw [VG.Proof.Bignum.X86_64.ofNat_mul8, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- `b + 8 i + 8`. -/
theorem addr8 {b i p : Addr} {e j : Nat} (hb : b = VG.Proof.Bignum.X86_64.off p e) (hi : i = BitVec.ofNat 64 j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = VG.Proof.Bignum.X86_64.off p (e + 8 * j + 8) := by
  subst hb hi
  rw [VG.Proof.Bignum.X86_64.ofNat_mul8, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc,
    BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]

/-! ## The loop of `mulAddRow` -/

/-- After `j` steps of `mulAddRow`'s loop from the state `s₀`. -/
structure RowInv (s₀ : State) (B : Addr) (Z eA eb : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * j) s₀.mem t.mem
  val : VG.Proof.Bignum.X86_64.wv t.mem B eA j + 2 ^ (64 * j) * (t.gpr .rbp).toNat =
    VG.Proof.Bignum.X86_64.wv s₀.mem B eA j + (s₀.gpr .rcx).toNat * VG.Proof.Bignum.X86_64.wv s₀.mem B eb j

theorem rowStep_ok {s₀ : State} {B : Addr} {Z w eA eb : Nat}
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h9 : s₀.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eb ∨ eb + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.RowInv s₀ B Z eA eb j t) :
    WP isa (.block (mac .r9 0 ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.RowInv s₀ B Z eA eb (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t9 : t.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb := (hI.keep.gpr (by decide)).trans h9
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₀.gpr .rcx := hI.keep.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (VG.Proof.Bignum.X86_64.mac_ok t (src := .r9) (d := 0)
    (VG.Proof.Bignum.X86_64.addr0 t9 hI.r14) (VG.Proof.Bignum.X86_64.addr0 t8 hI.r14) (VG.Proof.Bignum.X86_64.addr0 t8 hI.r14) (hI.scr.ld (by omega))
    (hI.scr.ld (by omega)) (hI.scr.st (by omega))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₀ t' :=
    ((hI.keep.trans k₁).trans k').mono (by decide)
  have hbp : t'.gpr .rbp = t₁.gpr .rbp := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) lo := hm'.trans hm
  -- The words read: `x` of the accumulator and `y` of `B`, both as on entry.
  have hx : t.mem.readW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) 64 = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : t.mem.readW (VG.Proof.Bignum.X86_64.off B (eb + 8 * j)) 64 = VG.Proof.Bignum.X86_64.word s₀.mem B (eb + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), hbp]
    simp only [VG.Proof.Bignum.X86_64.wv]
    rw [hx, hy, tcx] at hv
    have hval := hI.val
    rw [VG.Proof.Bignum.X86_64.pow64_succ]
    grind

theorem rowTop_ok {t : State} {B : Addr} {Z w eA : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z)
    (h8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hA : eA + 8 * w + 16 ≤ Z) :
    WP isa (.block rowTop) t fun t' =>
      t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w)) (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) + t.gpr .rbp)).writeW
        (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8) + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w)).toNat +
            (t.gpr .rbp).toNat))).setWidth 64) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have hn := hs.nowrap
  have hX : (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w)) (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) + t.gpr .rbp)).readW
      (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) 64 = VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8) :=
    (VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega)).word (Or.inr (Nat.le_refl _)) (by omega)
  refine WP.keep [.rax] ?_ rfl
  unfold rowTop
  xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 h8 h12, VG.Proof.Bignum.X86_64.addr8 h8 h12, hs.ld (show eA + 8 * w + 8 ≤ Z by omega),
    hs.st (show eA + 8 * w + 8 ≤ Z by omega), hs.ld (show eA + 8 * w + 8 + 8 ≤ Z by omega),
    hs.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hX, VG.Proof.Bignum.X86_64.sx0]

/-- The value after `rowTop`: `X + c` and `Y` plus its carry, if they fit. -/
theorem rowTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    VG.Proof.Bignum.X86_64.wv ((m.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w)) (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w) + c)).writeW
        (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8) + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64))
        B eA (w + 2) =
      VG.Proof.Bignum.X86_64.wv m B eA w + 2 ^ (64 * w) * ((VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8)).toNat) := by
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside m B (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w) + c) (d := eA + 8 * w) (by omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (m.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w)) (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w) + c)) B
    (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64)
    (d := eA + 8 * w + 8) (by omega)
  have hc := VG.Proof.Bignum.X86_64.addc_toNat (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)) (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8)) c (by omega)
  rw [show w + 2 = w + 1 + 1 from rfl, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega,
    VG.Proof.Bignum.X86_64.word_writeW_self, o2.word (Or.inl (Nat.le_refl _)) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self,
    o2.wv (Or.inl (by omega)) (by omega), o1.wv (Or.inl (Nat.le_refl _)) (by omega), VG.Proof.Bignum.X86_64.pow64_succ, ← hc]
  grind

/-- `acc += rcx · B` (`mulAddRow`), if the sum fits in `w + 2` words. -/
theorem mulAddRow_ok {s : State} {B : Addr} {Z w eA eb : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA)
    (hbound : VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) + (s.gpr .rcx).toNat * VG.Proof.Bignum.X86_64.wv s.mem B eb w < 2 ^ (64 * (w + 2))) :
    WP isa mulAddRow s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) + (s.gpr .rcx).toNat * VG.Proof.Bignum.X86_64.wv s.mem B eb w ∧
      VG.Proof.Bignum.X86_64.Outside B eA (8 * (w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold mulAddRow
  -- `rbp := 0`.
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hbp, hm₁⟩, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (k₁.gpr (by decide)).trans h8
  have s₁9 : s₁.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb := (k₁.gpr (by decide)).trans h9
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have s₁cx : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr (by decide)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.RowInv s₁ B Z eA eb 0 t := by
    intro t h14 hm k _
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by simp), h14, by rw [hm]; exact Outside.refl _ _ _ _, ?_⟩
    rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
    rfl
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (VG.Proof.Bignum.X86_64.RowInv s₁ B Z eA eb) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.rowStep_ok s₁8 s₁9 s₁12 (by omega) (by omega) hb (by omega) hj hI))
    fun t hI => ?_)
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  refine WP.mono (VG.Proof.Bignum.X86_64.rowTop_ok hI.scr t8 t12 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  -- The words above the loop's, as on entry.
  have hX : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
  have hY : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁, s₁cx] at hval
  have e2 : VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B eA w + 2 ^ (64 * w) *
      ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8)).toNat) := by
    rw [show w + 2 = w + 1 + 1 from rfl, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.pow64_succ, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega]
    grind
  -- The sum fits: `X + c + 2⁶⁴ Y < 2¹²⁸`.
  have hfit : (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
      2 ^ 64 * (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
        2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega]
      have := VG.Proof.Bignum.X86_64.wv_lt t.mem B eA w
      grind
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', VG.Proof.Bignum.X86_64.rowTop_val t.mem B hn (show eA + 8 * w + 16 ≤ Z by omega) _ hfit, hX, hY, e2]
    grind
  · rw [hm']
    intro x hx
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega)]
    exact (hI.out x (by omega)).trans (by rw [hm₁])

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Reduce`. -/
section

/-!
# Multiword arithmetic on x86-64: `acc := (acc + u m) / 2⁶⁴`

`reduceRow` adds `u m` to the accumulator `T` (`w + 2` words at `r8`),
`u = T₀ (-m⁻¹) mod 2⁶⁴` (`-m⁻¹` in `r15`, `m` the `w` words at `r10`), so
that the low word is zero, and stores the sum shifted down one word:
`2⁶⁴ T' = T + u m` (`reduceRow_ok`).

* `redHead` computes `u` into `rcx` and the carry of `T₀ + u m₀`.
* The loop, for `j = 1, …, w - 1`, is a multiply-accumulate step storing
  word `j - 1` (`RedInv`).
* `redTop` adds the carry into words `w` and `w + 1`, stored one down.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `t₀ + (t₀ m' mod 2⁶⁴) m ≡ 0 (mod 2⁶⁴)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (t0 * minv % 2 ^ 64 * m + t0) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show t0 * minv * m + t0 = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

theorem redHead_ok {s : State} {B : Addr} {Z eA eN : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (hA : eA + 8 ≤ Z) (hN : eN + 8 ≤ Z)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block redHead) s fun t =>
      t.mem = s.mem ∧
      (t.gpr .rcx).toNat = (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 ∧
      2 ^ 64 * (t.gpr .rbp).toNat = (t.gpr .rcx).toNat * (VG.Proof.Bignum.X86_64.word s.mem B eN).toNat + (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbp] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp] (c := .block redHead) (Q := fun t => t.mem = s.mem ∧
      (t.gpr .rcx).toNat = (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 ∧
      2 ^ 64 * (t.gpr .rbp).toNat = (t.gpr .rcx).toNat * (VG.Proof.Bignum.X86_64.word s.mem B eN).toNat + (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat)
    ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold redHead
  xrun [State.ea, at0, h8, h10, VG.Proof.Bignum.X86_64.off, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    hs.ld hA, hs.ld hN, VG.Proof.Bignum.X86_64.sx0]
  dsimp only [VG.Proof.Bignum.X86_64.word, VG.Proof.Bignum.X86_64.off] at hinv ⊢
  generalize s.mem.readW (B + BitVec.ofNat 64 eA) 64 = T0 at hinv ⊢
  generalize s.mem.readW (B + BitVec.ofNat 64 eN) 64 = N0 at hinv ⊢
  generalize s.gpr .r15 = mi at hinv ⊢
  refine ⟨BitVec.toNat_ofNat _ _, ?_⟩
  have hu : (BitVec.ofNat 64 (T0.toNat * mi.toNat)).toNat = T0.toNat * mi.toNat % 2 ^ 64 :=
    BitVec.toNat_ofNat _ _
  generalize hU : BitVec.ofNat 64 (T0.toNat * mi.toNat) = u at hu ⊢
  have hm := VG.Proof.Bignum.X86_64.mul_toNat N0 u
  have hl := VG.Proof.Bignum.X86_64.mul_le N0 u
  have hT := T0.isLt
  have hc := VG.Proof.Bignum.X86_64.addc_toNat (BitVec.ofNat 64 (N0.toNat * u.toNat)) (BitVec.ofNat 64 (N0.toNat * u.toNat / 2 ^ 64))
    T0 (by omega)
  have hlow : (BitVec.ofNat 64 (N0.toNat * u.toNat) + T0).toNat = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, hu, Nat.mul_comm N0.toNat]
    exact VG.Proof.Bignum.X86_64.mont_low _ _ _ hinv
  rw [hlow] at hc
  rw [Nat.mul_comm u.toNat]
  omega

/-! ## The loop -/

/-- After the steps up to `j - 1` of `reduceRow`'s loop from the state `s₁`
(after `redHead`): words `0, …, j - 2` hold the low words of
`(T + u m) / 2⁶⁴` so far, and `rbp` the carry. -/
structure RedInv (s₁ : State) (B : Addr) (Z eA eN : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₁ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * (j - 1)) s₁.mem t.mem
  val : 2 ^ 64 * (VG.Proof.Bignum.X86_64.wv t.mem B eA (j - 1) + 2 ^ (64 * (j - 1)) * (t.gpr .rbp).toNat) =
    VG.Proof.Bignum.X86_64.wv s₁.mem B eA j + (s₁.gpr .rcx).toNat * VG.Proof.Bignum.X86_64.wv s₁.mem B eN j

theorem redStep_ok {s₁ : State} {B : Addr} {Z w eA eN : Nat}
    (h8 : s₁.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s₁.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h12 : s₁.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eN ∨ eN + 8 * w ≤ eA) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State}
    (hI : VG.Proof.Bignum.X86_64.RedInv s₁ B Z eA eN j t) :
    WP isa (.block (mac .r10 (-8) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.RedInv s₁ B Z eA eN (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₁.gpr .rcx := hI.keep.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (VG.Proof.Bignum.X86_64.mac_ok t (src := .r10) (d := -8)
    (VG.Proof.Bignum.X86_64.addr0 t10 hI.r14) (VG.Proof.Bignum.X86_64.addr0 t8 hI.r14) (VG.Proof.Bignum.X86_64.addrm8 t8 hI.r14 hj1) (hI.scr.ld (by omega))
    (hI.scr.ld (by omega)) (hI.scr.st (by omega))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rbp, .r14] s₁ t' := ((hI.keep.trans k₁).trans k').mono (by decide)
  have hbp : t'.gpr .rbp = t₁.gpr .rbp := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * (j - 1))) lo := hm'.trans hm
  have hx : t.mem.readW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) 64 = VG.Proof.Bignum.X86_64.word s₁.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (by omega)) (by omega)
  have hy : t.mem.readW (VG.Proof.Bignum.X86_64.off B (eN + 8 * j)) 64 = VG.Proof.Bignum.X86_64.word s₁.mem B (eN + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, show j + 1 - 1 = j - 1 + 1 by omega, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), hbp]
    simp only [VG.Proof.Bignum.X86_64.wv]
    rw [hx, hy, tcx] at hv
    have hval := hI.val
    have hp : 2 ^ 64 * 2 ^ (64 * (j - 1)) = 2 ^ (64 * j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [show 64 * (j - 1 + 1) = 64 * j by omega]
    grind

/-! ## The top words -/

/-- The memory `redTop` leaves: `X + c` at word `w - 1`, `Y` plus the carry
at word `w`, 0 at word `w + 1`, for the words `X`, `Y` at `w`, `w + 1`. -/
def redTopMem (m : Mem) (B : Addr) (eA w : Nat) (c : BitVec 64) : Mem :=
  ((m.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * (w - 1))) (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w) + c)).writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w))
    (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64)).writeW
    (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) (0 : BitVec 64)

theorem redTop_ok {t : State} {B : Addr} {Z w eA : Nat} (hs : VG.Proof.Bignum.X86_64.Scr t B Z) (hw : 1 ≤ w)
    (h8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hA : eA + 8 * w + 16 ≤ Z) :
    WP isa (.block redTop) t fun t' => t'.mem = VG.Proof.Bignum.X86_64.redTopMem t.mem B eA w (t.gpr .rbp) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have hn := hs.nowrap
  have hY : (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * (w - 1))) (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) + t.gpr .rbp)).readW
      (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) 64 = VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8) :=
    (VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega)).word (Or.inr (by omega)) (by omega)
  refine WP.mono (WP.keep [.rax] (c := .block redTop) (Q := fun t' =>
    t'.mem = VG.Proof.Bignum.X86_64.redTopMem t.mem B eA w (t.gpr .rbp)) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold redTop VG.Proof.Bignum.X86_64.redTopMem
  xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 h8 h12, VG.Proof.Bignum.X86_64.addr8 h8 h12, VG.Proof.Bignum.X86_64.addrm8 h8 h12 hw,
    hs.ld (show eA + 8 * w + 8 ≤ Z by omega), hs.st (show eA + 8 * w + 8 ≤ Z by omega),
    hs.st (show eA + 8 * (w - 1) + 8 ≤ Z by omega),
    hs.ld (show eA + 8 * w + 8 + 8 ≤ Z by omega), hs.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hY, VG.Proof.Bignum.X86_64.sx0]
  rfl

/-- The value after `redTop`, times `2⁶⁴`, if the top fits. -/
theorem redTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64) (hw : 1 ≤ w)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    2 ^ 64 * VG.Proof.Bignum.X86_64.wv (VG.Proof.Bignum.X86_64.redTopMem m B eA w c) B eA (w + 2) =
      2 ^ 64 * VG.Proof.Bignum.X86_64.wv m B eA (w - 1) + 2 ^ (64 * w) * ((VG.Proof.Bignum.X86_64.word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8)).toNat) := by
  unfold VG.Proof.Bignum.X86_64.redTopMem
  generalize hX : VG.Proof.Bignum.X86_64.word m B (eA + 8 * w) = X at hfit
  generalize hY : VG.Proof.Bignum.X86_64.word m B (eA + 8 * w + 8) = Y at hfit
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside m B (X + c) (d := eA + 8 * (w - 1)) (by omega)
  have o2 := VG.Proof.Bignum.X86_64.writeW_outside (m.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * (w - 1))) (X + c)) B
    (Y + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ X.toNat + c.toNat))).setWidth 64) (d := eA + 8 * w) (by omega)
  have o3 := VG.Proof.Bignum.X86_64.writeW_outside ((m.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * (w - 1))) (X + c)).writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w))
    (Y + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ X.toNat + c.toNat))).setWidth 64)) B (0 : BitVec 64)
    (d := eA + 8 * w + 8) (by omega)
  have hc := VG.Proof.Bignum.X86_64.addc_toNat X Y c (by omega)
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
  rw [show w + 2 = w - 1 + 1 + 1 + 1 by omega, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, show eA + 8 * (w - 1 + 1 + 1) = eA + 8 * w + 8 by omega,
    show eA + 8 * (w - 1 + 1) = eA + 8 * w by omega, VG.Proof.Bignum.X86_64.word_writeW_self,
    o3.word (Or.inl (Nat.le_refl _)) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self,
    o3.word (Or.inl (by omega)) (by omega), o2.word (Or.inl (by omega)) (by omega), VG.Proof.Bignum.X86_64.word_writeW_self,
    o3.wv (Or.inl (by omega)) (by omega), o2.wv (Or.inl (by omega)) (by omega),
    o1.wv (Or.inl (Nat.le_refl _)) (by omega), show 64 * (w - 1 + 1 + 1) = 64 * w + 64 by omega,
    show 64 * (w - 1 + 1) = 64 * w by omega, Nat.pow_add]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, ← hc]
  grind

/-! ## The row -/

/-- `2⁶⁴ T' = T + u m` (`reduceRow`), for `u = T₀ (-m⁻¹) mod 2⁶⁴`, if `T + u m`
fits in `w + 2` words. -/
theorem reduceRow_ok {s : State} {B : Addr} {Z w eA eN : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (hbound : ∀ u < 2 ^ 64, VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) + u * VG.Proof.Bignum.X86_64.wv s.mem B eN w < 2 ^ (64 * (w + 2))) :
    WP isa reduceRow s fun t =>
      2 ^ 64 * VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) +
        (VG.Proof.Bignum.X86_64.word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 * VG.Proof.Bignum.X86_64.wv s.mem B eN w ∧
      VG.Proof.Bignum.X86_64.Outside B eA (8 * (w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold reduceRow
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.redHead_ok hs h8 h10 (by omega) (by omega) hinv)
    fun s₁ ⟨hm₁, hu, hc₁, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (k₁.gpr (by decide)).trans h8
  have s₁10 : s₁.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (k₁.gpr (by decide)).trans h10
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.RedInv s₁ B Z eA eN 1 t := by
    intro t h14 hm k _
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, ?_⟩
    rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp)]
    simp only [VG.Proof.Bignum.X86_64.wv, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
    rw [hc₁, hm₁]
    omega
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 1) (N := w) (by omega) hw'
    (VG.Proof.Bignum.X86_64.RedInv s₁ B Z eA eN) h0
    (fun j hj1 hj t hI => VG.Proof.Bignum.X86_64.redStep_ok s₁8 s₁10 s₁12 (by omega) (by omega) hN (by omega) hj1 hj hI))
    fun t hI => ?_)
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  refine WP.mono (VG.Proof.Bignum.X86_64.redTop_ok hI.scr (by omega) t8 t12 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  have hX : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hY : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁] at hval
  have hb := hbound _ (s₁.gpr .rcx).isLt
  have e2 : VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B eA w + 2 ^ (64 * w) *
      ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8)).toNat) := by
    rw [show w + 2 = w + 1 + 1 from rfl, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.pow64_succ, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega]
    grind
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
  -- The top fits.
  have hfit : (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
      2 ^ 64 * (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
        2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega, Nat.mul_add, Nat.mul_add]
      rw [Nat.mul_add, ← Nat.mul_assoc (2 ^ 64), hp] at hval
      rw [Nat.mul_add] at e2
      omega_using [hval, hb, e2]
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', VG.Proof.Bignum.X86_64.redTop_val t.mem B hn (by omega) (show eA + 8 * w + 16 ≤ Z by omega) _ hfit, hX, hY, e2, ← hu]
    grind
  · rw [hm']
    intro x hx
    unfold VG.Proof.Bignum.X86_64.redTopMem
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega)]
    exact (hI.out x (by omega)).trans (by rw [hm₁])

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Rounds`. -/
section

/-!
# Multiword arithmetic on x86-64: the rounds of a Montgomery multiplication

`zeroAccLoop` clears the accumulator (`w + 2` words at `r8`); `round`
(for `i = r13`) adds `a_i B` and reduces (`round_ok`); `rounds` runs it for
`i = 0, …, w - 1`, keeping the accumulator `T < 2m` and
`T 2^(64 i) ≡ (a mod 2^(64 i)) B (mod m)` (`rounds_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum (round_lt round_mod round_sum_lt)

/-! ## Clearing the accumulator -/

structure ZeroInv (s : State) (B : Addr) (Z eA : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s t
  rax : t.gpr .rax = 0
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * j) s.mem t.mem
  val : VG.Proof.Bignum.X86_64.wv t.mem B eA j = 0

theorem zeroAccLoop_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) :
    WP isa zeroAccLoop s fun t => VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) = 0 ∧ VG.Proof.Bignum.X86_64.Outside B eA (8 * (w + 2)) s.mem t.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s t := by
  have hn := hs.nowrap
  unfold zeroAccLoop
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.ZeroInv s B Z eA 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), (k₁.trans k).mono (by decide),
      (k.gpr (by decide)).trans hax, h14, by rw [hm, hm₁]; exact Outside.refl _ _ _ _, rfl⟩
  have hstep : ∀ j, 0 ≤ j → j < w → ∀ t, VG.Proof.Bignum.X86_64.ZeroInv s B Z eA j t →
      WP isa (.block ([.store (ix .r8 .r14) .rax] ++ [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) t
        fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.ZeroInv s B Z eA (j + 1) t' := by
    intro j _ hj t hI
    have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
    have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [] (Q := fun t₁ => t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * j)) (0 : BitVec 64))
      (by xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 hI.r14, hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega), hI.rax]) rfl)
      fun t₁ ⟨hm, k₁⟩ => ?_
    have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
    have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
    refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
    refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
      (k'.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hI.rax), h14, ?_, ?_⟩
    · rw [hm', hm]
      intro x hx
      rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x (by omega)
    · rw [hm', hm, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), hI.val]
      rfl
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.ZeroInv s B Z eA) h0 hstep)
    fun t hI => ?_)
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = (t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eA + 8 * w)) (0 : BitVec 64)).writeW
      (VG.Proof.Bignum.X86_64.off B (eA + 8 * w + 8)) (0 : BitVec 64))
    (by xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 t12, VG.Proof.Bignum.X86_64.addr8 t8 t12, hI.scr.st (show eA + 8 * w + 8 ≤ Z by omega),
      hI.scr.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hI.rax]) rfl) fun t' ⟨hm, k'⟩ => ?_
  refine ⟨?_, ?_, (hI.keep.trans k').mono (by decide)⟩
  · rw [hm, show w + 2 = w + 1 + 1 from rfl, show eA + 8 * w + 8 = eA + 8 * (w + 1) by omega,
      VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    rfl
  · rw [hm]
    intro x hx
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega) x (by omega)]
    exact hI.out x (by omega)

/-! ## A round -/

/-- Round `i` (`r13`): `rcx := a_i`, `T += a_i B`, `T := (T + u m) / 2⁶⁴`. -/
theorem round_ok {s : State} {B : Addr} {Z w eA eb eN ea i : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (h11 : s.gpr .r11 = VG.Proof.Bignum.X86_64.off B ea) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hi : i < w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (hT : VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) < 2 * VG.Proof.Bignum.X86_64.wv s.mem B eN w) (hB : VG.Proof.Bignum.X86_64.wv s.mem B eb w < VG.Proof.Bignum.X86_64.wv s.mem B eN w) :
    WP isa round s fun t =>
      (∃ u < 2 ^ 64, 2 ^ 64 * VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) +
        (VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i)).toNat * VG.Proof.Bignum.X86_64.wv s.mem B eb w + u * VG.Proof.Bignum.X86_64.wv s.mem B eN w) ∧
      VG.Proof.Bignum.X86_64.Outside B eA (8 * (w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have hNw : VG.Proof.Bignum.X86_64.wv s.mem B eN w < 2 ^ (64 * w) := VG.Proof.Bignum.X86_64.wv_lt _ _ _ _
  unfold round
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i) ∧ t.mem = s.mem)
    (by xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 h11 h13, hs.ld (show ea + 8 * i + 8 ≤ Z by omega)]) rfl)
    fun s₁ ⟨⟨hcx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hai := (VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i)).isLt
  have hbB : (VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i)).toNat * VG.Proof.Bignum.X86_64.wv s.mem B eb w ≤ (2 ^ 64 - 1) * VG.Proof.Bignum.X86_64.wv s.mem B eN w :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.mulAddRow_ok hs₁ ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)
    ((k₁.gpr (by decide)).trans h12) (by omega) hw' hA hb sb (by
      rw [hm₁, hcx]
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this, Nat.sub_mul, Nat.one_mul] at *
      omega)) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hcx] at hv₂
  rw [hm₁] at ho₂
  have hNeq : VG.Proof.Bignum.X86_64.wv s₂.mem B eN w = VG.Proof.Bignum.X86_64.wv s.mem B eN w := ho₂.wv (by omega) (by omega)
  have hN0 : VG.Proof.Bignum.X86_64.word s₂.mem B eN = VG.Proof.Bignum.X86_64.word s.mem B eN := ho₂.word (by omega) (by omega)
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := (k₁.trans k₂)
  refine WP.mono (VG.Proof.Bignum.X86_64.reduceRow_ok hs₂ ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h10)
    ((k12.gpr (by decide)).trans h12) hw hw' hA hN sN (by
      rw [hN0, (k12.gpr (by decide) : s₂.gpr .r15 = s.gpr .r15)]; exact hinv) (by
      intro u hu
      rw [hv₂, hNeq]
      have hu' : u * VG.Proof.Bignum.X86_64.wv s.mem B eN w ≤ (2 ^ 64 - 1) * VG.Proof.Bignum.X86_64.wv s.mem B eN w := Nat.mul_le_mul_right _ (by omega)
      have : 2 ^ (64 * (w + 2)) = 2 ^ 128 * 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [this]
      rw [Nat.sub_mul, Nat.one_mul] at hbB hu'
      have : 4 * 2 ^ (64 * w) ≤ 2 ^ 128 * 2 ^ (64 * w) - 2 ^ 66 * 2 ^ (64 * w) := by
        rw [← Nat.sub_mul]; exact Nat.mul_le_mul_right _ (by decide)
      omega)) fun t ⟨hv, ho, k₃⟩ => ?_
  refine ⟨⟨(VG.Proof.Bignum.X86_64.word s₂.mem B eA).toNat * (s₂.gpr .r15).toNat % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩,
    ho₂.trans ho, (k12.trans k₃).mono (by decide)⟩
  rw [hv, hv₂, hNeq]

/-! ## The rounds -/

/-- After rounds `0, …, i - 1` from `s₀`: the accumulator `T < 2m` and
`2^(64 i) T ≡ (a mod 2^(64 i)) B (mod m)`. -/
structure RoundsInv (s₀ : State) (B : Addr) (Z w eA eb eN ea : Nat) (i : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rbp, .r14, .r13] s₀ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  out : VG.Proof.Bignum.X86_64.Outside B eA (8 * (w + 2)) s₀.mem t.mem
  lt : VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) < 2 * VG.Proof.Bignum.X86_64.wv s₀.mem B eN w
  cong : 2 ^ (64 * i) * VG.Proof.Bignum.X86_64.wv t.mem B eA (w + 2) % VG.Proof.Bignum.X86_64.wv s₀.mem B eN w =
    VG.Proof.Bignum.X86_64.wv s₀.mem B ea i * VG.Proof.Bignum.X86_64.wv s₀.mem B eb w % VG.Proof.Bignum.X86_64.wv s₀.mem B eN w

theorem rounds_ok {s : State} {B : Addr} {Z w eA eb eN ea : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (h11 : s.gpr .r11 = VG.Proof.Bignum.X86_64.off B ea) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (ha : ea + 8 * w ≤ Z)
    (sb : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA) (sN : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (sa : eA + 8 * (w + 2) ≤ ea ∨ ea + 8 * w ≤ eA)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (h0 : VG.Proof.Bignum.X86_64.wv s.mem B eA (w + 2) = 0) (hB : VG.Proof.Bignum.X86_64.wv s.mem B eb w < VG.Proof.Bignum.X86_64.wv s.mem B eN w) :
    WP isa rounds s (VG.Proof.Bignum.X86_64.RoundsInv s B Z w eA eb eN ea w) := by
  have hn := hs.nowrap
  have hN0 : 0 < VG.Proof.Bignum.X86_64.wv s.mem B eN w := by omega
  unfold rounds
  refine WP.seq (WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨h13, hm₁⟩, k₁⟩ => ?_)
  refine VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := w) (by omega) (VG.Proof.Bignum.X86_64.RoundsInv s B Z w eA eb eN ea) ?_ (fun _ h => h)
    ⟨hs.congr k₁.2.2, k₁.mono (by decide), h13, by rw [hm₁]; exact Outside.refl _ _ _ _,
      by rw [hm₁, h0]; omega, by rw [hm₁, h0]; simp [VG.Proof.Bignum.X86_64.wv]⟩
  intro i _ hi t hI
  have hk := hI.keep
  have frame : ∀ {d k}, d + 8 * k ≤ Z → (d + 8 * k ≤ eA ∨ eA + 8 * (w + 2) ≤ d) →
      VG.Proof.Bignum.X86_64.wv t.mem B d k = VG.Proof.Bignum.X86_64.wv s.mem B d k := fun h1 h2 => hI.out.wv h2 (by omega)
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.round_ok hI.scr ((hk.gpr (by decide)).trans h8) ((hk.gpr (by decide)).trans h9)
    ((hk.gpr (by decide)).trans h10) ((hk.gpr (by decide)).trans h11) ((hk.gpr (by decide)).trans h12)
    hI.r13 hi hw hw' hA hb hN ha sb sN sa (by
      rw [hI.out.word (by omega) (by omega), (hk.gpr (by decide) : t.gpr .r15 = s.gpr .r15)]; exact hinv)
    (by rw [frame hN (by omega)]; exact hI.lt) (by rw [frame hb (by omega), frame hN (by omega)]; exact hB))
    fun t₁ ⟨⟨u, hu, hv⟩, ho, k₁'⟩ => ?_)
  have t₁13 : t₁.gpr .r13 = BitVec.ofNat 64 i := (k₁'.gpr (by decide)).trans hI.r13
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁'.gpr (by decide)).trans ((hk.gpr (by decide)).trans h12)
  refine WP.mono (VG.Proof.Bignum.X86_64.count13_ok t₁ t₁13 t₁12 (by omega) (by omega)) fun t' ⟨hz, h13', hm', k'⟩ => ⟨hz, ?_⟩
  rw [frame hN (by omega), frame hb (by omega)] at hv
  have hai : (VG.Proof.Bignum.X86_64.word t.mem B (ea + 8 * i)).toNat = (VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i)).toNat := by
    rw [hI.out.word (by omega) (by omega)]
  rw [hai] at hv
  refine ⟨hI.scr.congr (k'.2.2.trans k₁'.2.2), ((hk.trans k₁').trans k').mono (by decide), h13',
    by rw [hm']; exact hI.out.trans ho, ?_, ?_⟩
  · rw [hm']
    exact VG.Proof.Bignum.round_lt hv hI.lt (VG.Proof.Bignum.X86_64.word s.mem B (ea + 8 * i)).isLt hB hu
  · rw [hm', show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add,
      VG.Proof.Bignum.round_step hv hI.cong]
    congr 1

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Csub`. -/
section

/-!
# Multiword arithmetic on x86-64: the conditional subtraction

`subMod` computes `T - m` into the temporary array (`rsi`) over `w` words,
with the borrow between iterations kept in `rbp` as a mask (`mask`), and
then the borrow of `T - m` with the top word of `T` counted: `rbp` all
ones iff `T < m` (`subMod_ok`). `selectAcc` then stores `T` or `T - m` by
the mask (`selectAcc_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The mask of a borrow, as `sbb rbp, rbp` leaves it. -/
def mask (c : Bool) : BitVec 64 := 0 - (BitVec.ofBool c).setWidth 64

theorem mask_false : VG.Proof.Bignum.X86_64.mask false = 0 := rfl
theorem mask_true : VG.Proof.Bignum.X86_64.mask true = BitVec.allOnes 64 := rfl

/-- `add rbp, rbp` sets the carry from the mask. -/
theorem cf_mask (c : Bool) : decide (2 ^ 64 ≤ (VG.Proof.Bignum.X86_64.mask c).toNat + (VG.Proof.Bignum.X86_64.mask c).toNat) = c := by
  cases c <;> decide

/-- `sbb`, as numbers: `a - b - c`, plus `2⁶⁴` if it borrows. -/
theorem sbb_toNat (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The selection: `((a ^ b) & m) ^ b` is `a` for the mask of `true`, `b`
for that of `false`. -/
theorem select_mask (a b : BitVec 64) (c : Bool) :
    ((a ^^^ b) &&& VG.Proof.Bignum.X86_64.mask c) ^^^ b = if c then a else b := by
  cases c
  · simp [VG.Proof.Bignum.X86_64.mask_false]
  · simp only [VG.Proof.Bignum.X86_64.mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ## `T - m` -/

/-- After `j` words of `subMod`'s loop from `s₀`: `D_j + m_j = T_j + 2^(64 j) c`
for the low `j` words `D_j` of the difference, `m_j` of `m`, `T_j` of `T`,
and the borrow `c` (as `mask c` in `rbp`). -/
structure SubInv (s₀ : State) (B : Addr) (Z eA eN eT : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eT (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧
    VG.Proof.Bignum.X86_64.wv t.mem B eT j + VG.Proof.Bignum.X86_64.wv s₀.mem B eN j = VG.Proof.Bignum.X86_64.wv s₀.mem B eA j + 2 ^ (64 * j) * c.toNat

theorem subStep_ok {s₀ : State} {B : Addr} {Z w eA eN eT : Nat}
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (hsi : s₀.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z)
    (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * w ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Bignum.X86_64.SubInv s₀ B Z eA eN eT j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        .store (ix .rsi .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.SubInv s₀ B Z eA eN eT (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (hI.keep.gpr (by decide)).trans h10
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eT + 8 * j)) r ∧
        r.toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j)).toNat + c.toNat =
          (VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl) fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 hI.r14, VG.Proof.Bignum.X86_64.addr0 t10 hI.r14, VG.Proof.Bignum.X86_64.addr0 tsi hI.r14, hbp, VG.Proof.Bignum.X86_64.cf_mask,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eT + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, VG.Proof.Bignum.X86_64.sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [VG.Proof.Bignum.X86_64.wv]
    rw [VG.Proof.Bignum.X86_64.pow64_succ]
    grind

/-- `subMod`: `D = T - m` over `w` words into the array at `rsi`, its borrow
`c`, and `rbp` the mask of `T_w < c` for the word `w` of `T` (that is, of
`T < m` when `T < 2 · 2^(64 w)`). -/
theorem subMod_ok {s : State} {B : Addr} {Z w eA eN eT : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN) (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 1) ≤ Z)
    (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT) :
    WP isa subMod s fun t => ∃ c lt : Bool, t.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt ∧
      lt = decide ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat < c.toNat) ∧
      VG.Proof.Bignum.X86_64.wv t.mem B eT w + VG.Proof.Bignum.X86_64.wv s.mem B eN w = VG.Proof.Bignum.X86_64.wv s.mem B eA w + 2 ^ (64 * w) * c.toNat ∧
      VG.Proof.Bignum.X86_64.Outside B eT (8 * w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold subMod
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = VG.Proof.Bignum.X86_64.mask false ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hbp, hm₁⟩, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (k₁.gpr (by decide)).trans h8
  have s₁10 : s₁.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (k₁.gpr (by decide)).trans h10
  have s₁si : s₁.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT := (k₁.gpr (by decide)).trans hsi
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s₁ t → t.cf = s₁.cf →
      VG.Proof.Bignum.X86_64.SubInv s₁ B Z eA eN eT 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.SubInv s₁ B Z eA eN eT) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.subStep_ok s₁8 s₁10 s₁si s₁12 (by omega) (by omega) hN hT (by omega) sN hj hI))
    fun t hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  have hX : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * w) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (by omega) (by omega), hm₁]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide ((VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * w)).toNat < c.toNat)))
    (by
      unfold cfFromRbp cfToRbp
      xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 t12, hc, VG.Proof.Bignum.X86_64.cf_mask, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega), hX, VG.Proof.Bignum.X86_64.sx0]
      simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
      rfl) rfl) fun t' ⟨⟨hm', hbp'⟩, k'⟩ => ?_
  refine ⟨c, _, hbp', rfl, ?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', ← hm₁]; exact hval
  · rw [hm', ← hm₁]; exact hI.out

/-! ## The selection -/

structure SelInv (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B eo (8 * j) s₀.mem t.mem
  val : VG.Proof.Bignum.X86_64.wv t.mem B eo j = if lt then VG.Proof.Bignum.X86_64.wv s₀.mem B eA j else VG.Proof.Bignum.X86_64.wv s₀.mem B eT j

theorem selectAcc_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA) (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B eo w = (if lt then VG.Proof.Bignum.X86_64.wv s.mem B eA w else VG.Proof.Bignum.X86_64.wv s.mem B eT w) ∧
      VG.Proof.Bignum.X86_64.Outside B eo (8 * w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .r14] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Bignum.X86_64.SelInv s B Z eA eT eo lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      cases lt <;> rfl⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.SelInv s B Z eA eT eo lt) h0 ?_)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbp : t.gpr .rbp = VG.Proof.Bignum.X86_64.mask lt := (hI.keep.gpr (by decide)).trans hbp
  have hx : VG.Proof.Bignum.X86_64.word t.mem B (eA + 8 * j) = VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : VG.Proof.Bignum.X86_64.word t.mem B (eT + 8 * j) = VG.Proof.Bignum.X86_64.word s.mem B (eT + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (eo + 8 * j))
      (if lt then VG.Proof.Bignum.X86_64.word s.mem B (eA + 8 * j) else VG.Proof.Bignum.X86_64.word s.mem B (eT + 8 * j))) (by
      xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 hI.r14, VG.Proof.Bignum.X86_64.addr0 tsi hI.r14, VG.Proof.Bignum.X86_64.addr0 tbx hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy, VG.Proof.Bignum.X86_64.select_mask]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, VG.Proof.Bignum.X86_64.wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    cases lt <;> simp [VG.Proof.Bignum.X86_64.wv]

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.MontMul`. -/
section

/-!
# Multiword arithmetic on x86-64: Montgomery multiplication

The working space at `B` (`rdi`) holds the header and, after it, eight
arrays of `w + 2` words (`slot w j`). The header (`Hdr`) gives `w`,
`-m⁻¹ mod 2⁶⁴` and the arrays' bases. `montMul mo acc tmp o a b` leaves
`[o] < m` with `[o] R ≡ [a] [b] (mod m)` for `R = 2^(64 w)` and `m = [mo]`
(`montMul_ok`), changing only the arrays `acc`, `tmp` and `o`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The offset of array `j`. -/
def slot (w j : Nat) : Nat := hdrBytes + j * (8 * (w + 2))

theorem slot_sep {w j k : Nat} (h : j ≠ k) :
    VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j := by
  unfold VG.Proof.Bignum.X86_64.slot
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right (8 * (w + 2)) (show k + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem slot_le {w j : Nat} (h : j < 8) : VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w 8 := by
  unfold VG.Proof.Bignum.X86_64.slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ 8 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem hdr_lt_slot (w j : Nat) {i : Nat} (hi : i < 32) : 8 * i + 8 ≤ VG.Proof.Bignum.X86_64.slot w j := by
  unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega

/-- The header: `w`, `-m⁻¹` and the arrays' bases. -/
structure Hdr (m : Mem) (B : Addr) (w : Nat) (minv : BitVec 64) : Prop where
  hw : VG.Proof.Bignum.X86_64.word m B (8 * sW) = BitVec.ofNat 64 w
  hminv : VG.Proof.Bignum.X86_64.word m B (8 * sMinv) = minv
  harr : ∀ j < 8, VG.Proof.Bignum.X86_64.word m B (8 * sArr j) = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w j)

/-- Memory that changes only in the arrays `js`. -/
def Arrays (B : Addr) (w : Nat) (js : List Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ j ∈ js, VG.Proof.Bignum.X86_64.ofs B x < VG.Proof.Bignum.X86_64.slot w j ∨ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.ofs B x) → m' x = m x

theorem Arrays.of_outside {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} {j : Nat} (hj : j ∈ js)
    {o n : Nat} (h : VG.Proof.Bignum.X86_64.Outside B o n m m') (ho : VG.Proof.Bignum.X86_64.slot w j ≤ o) (hn : o + n ≤ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2)) :
    VG.Proof.Bignum.X86_64.Arrays B w js m m' := fun x hx => h x (by have := hx j hj; omega)

theorem Arrays.trans {B : Addr} {w : Nat} {js : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : VG.Proof.Bignum.X86_64.Arrays B w js m₁ m₂) (h₂ : VG.Proof.Bignum.X86_64.Arrays B w js m₂ m₃) : VG.Proof.Bignum.X86_64.Arrays B w js m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Arrays.mono {B : Addr} {w : Nat} {js js' : List Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Arrays B w js m m')
    (hs : ∀ j ∈ js, j ∈ js') : VG.Proof.Bignum.X86_64.Arrays B w js' m m' := fun x hx => h x fun j hj => hx j (hs j hj)

theorem Arrays.word_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Arrays B w js m m')
    {d : Nat} (hd : ∀ j ∈ js, d + 8 ≤ VG.Proof.Bignum.X86_64.slot w j ∨ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun j hj => by
    have := hd j hj; rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega).symm).symm

theorem Arrays.wv_eq {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Arrays B w js m m')
    {d k : Nat} (hd : ∀ j ∈ js, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot w j ∨ VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ d)
    (hd' : d + 8 * k ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.wv m' B d k = VG.Proof.Bignum.X86_64.wv m B d k :=
  VG.Proof.Bignum.X86_64.wv_congr fun i hi => h.word_eq (fun j hj => by have := hd j hj; omega) (by omega)

theorem Arrays.hdr {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Arrays B w js m m')
    {minv : BitVec 64} (hH : VG.Proof.Bignum.X86_64.Hdr m B w minv) : VG.Proof.Bignum.X86_64.Hdr m' B w minv := by
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := fun i hi =>
    h.word_eq (fun j _ => Or.inl (VG.Proof.Bignum.X86_64.hdr_lt_slot w j hi)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- Memory that changes only in the byte ranges `rs` (offsets and lengths
from `B`). -/
def Frm (B : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, VG.Proof.Bignum.X86_64.ofs B x < r.1 ∨ r.1 + r.2 ≤ VG.Proof.Bignum.X86_64.ofs B x) → m' x = m x

theorem Frm.refl (B : Addr) (rs : List (Nat × Nat)) (m : Mem) : VG.Proof.Bignum.X86_64.Frm B rs m m := fun _ _ => rfl

theorem Frm.trans {B : Addr} {rs : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.Frm B rs m₁ m₂)
    (h₂ : VG.Proof.Bignum.X86_64.Frm B rs m₂ m₃) : VG.Proof.Bignum.X86_64.Frm B rs m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Frm.mono {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Frm B rs m m')
    (hs : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Bignum.X86_64.Frm B rs' m m' := fun x hx => h x fun r hr => hx r (hs r hr)

theorem Frm.of_outside {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {o n : Nat} (h : VG.Proof.Bignum.X86_64.Outside B o n m m')
    (hr : (o, n) ∈ rs) : VG.Proof.Bignum.X86_64.Frm B rs m m' := fun x hx => h x (hx _ hr)

theorem Frm.of_arrays {B : Addr} {w : Nat} {js : List Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : VG.Proof.Bignum.X86_64.Arrays B w js m m') (hr : ∀ j ∈ js, (VG.Proof.Bignum.X86_64.slot w j, 8 * (w + 2)) ∈ rs) : VG.Proof.Bignum.X86_64.Frm B rs m m' :=
  fun x hx => h x fun j hj => hx _ (hr j hj)

theorem Frm.word_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Frm B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) : VG.Proof.Bignum.X86_64.word m' B d = VG.Proof.Bignum.X86_64.word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr => by
    have := hd r hr; rw [VG.Proof.Bignum.X86_64.ofs_off B (by omega)]; omega).symm).symm

theorem Frm.wv_eq {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.Frm B rs m m') {d k : Nat}
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.wv m' B d k = VG.Proof.Bignum.X86_64.wv m B d k :=
  VG.Proof.Bignum.X86_64.wv_congr fun i hi => h.word_eq (fun r hr => by have := hd r hr; omega) (by omega)

/-- The header, after a store to a slot of the functions' own (`sFn`). -/
theorem Hdr.store {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : VG.Proof.Bignum.X86_64.Hdr m B w minv) {i : Nat}
    (hi : 16 ≤ i) (hi' : i < 32) (v : BitVec 64) : VG.Proof.Bignum.X86_64.Hdr (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B w minv := by
  have hh : ∀ k < 16, VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off B (8 * i)) v) B (8 * k) = VG.Proof.Bignum.X86_64.word m B (8 * k) := fun k hk =>
    (VG.Proof.Bignum.X86_64.writeW_outside m B v (by omega)).word (by omega) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- A header slot's address, as `xrun` leaves it. -/
theorem hdrOff (B : Addr) (i : Nat) : B + BitVec.ofInt 64 (8 * (i : Int)) = VG.Proof.Bignum.X86_64.off B (8 * i) := by
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- `bases o a b mo acc tmp`: the bases from the header, and `w` and `-m⁻¹`. -/
theorem bases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {o a b mo acc tmp : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) :
    WP isa (.block (bases o a b mo acc tmp)) s fun t =>
      t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w mo) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rbx, .r11, .r9, .r10, .r8, .r12, .r15, .rsi] (c := .block (bases o a b mo acc tmp))
    (Q := fun t => t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) ∧
      t.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w mo) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r15 = minv ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, k⟩
  unfold bases
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hl (sArr o) (by unfold sArr; omega), hl (sArr a) (by unfold sArr; omega),
    hl (sArr b) (by unfold sArr; omega), hl (sArr mo) (by unfold sArr; omega),
    hl (sArr acc) (by unfold sArr; omega), hl (sArr tmp) (by unfold sArr; omega), hl sW (by decide),
    hl sMinv (by decide), hH.harr o ho, hH.harr a ha, hH.harr b hb, hH.harr mo hmo, hH.harr acc hacc,
    hH.harr tmp htmp, hH.hw, hH.hminv]

/-- The registers `montMul` may change: all but `rdi` and `rsp`. -/
def mmRegs : List Reg :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A number of `w + 2` words: its low `w` words and the two above. -/
theorem wv_top2 (m : Mem) (B : Addr) (d w : Nat) :
    VG.Proof.Bignum.X86_64.wv m B d (w + 2) = VG.Proof.Bignum.X86_64.wv m B d w + 2 ^ (64 * w) *
      ((VG.Proof.Bignum.X86_64.word m B (d + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word m B (d + 8 * w + 8)).toNat) := by
  rw [show w + 2 = w + 1 + 1 from rfl, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.wv, VG.Proof.Bignum.X86_64.pow64_succ, show d + 8 * (w + 1) = d + 8 * w + 8 by omega]
  grind

/-- Montgomery multiplication: `[o] = [a] [b] R⁻¹ mod m` for `m = [mo]`, if
`[b] < m` and `-m⁻¹` is right. -/
theorem montMul_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8) (ha : a < 8)
    (hb : b < 8) (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d4 : acc ≠ a) (d5 : acc ≠ b)
    (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w mo)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) :
    WP isa (montMul mo acc tmp o a b) s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w ∧
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w =
        VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [acc, tmp, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (VG.Proof.Bignum.X86_64.slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w k ∨ VG.Proof.Bignum.X86_64.slot w k + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w j :=
    fun h => VG.Proof.Bignum.X86_64.slot_sep h
  have hN0 : 0 < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w := by omega
  unfold montMul
  -- The bases.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.bases_ok hs hdi hH hZ ho ha hb hmo hacc htmp)
    fun s₁ ⟨hbx, h11, h9, h10, h8, h12, h15, hsi₁, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- The accumulator := 0.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.zeroAccLoop_ok hs₁ h8 h12 (by omega) hw' (sl acc hacc))
    fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have fr₂ : ∀ {j}, j < 8 → j ≠ acc → VG.Proof.Bignum.X86_64.wv s₂.mem B (VG.Proof.Bignum.X86_64.slot w j) w = VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w :=
    fun hj hne => ho₂.wv (by have := sp hne; omega) (by have := sl _ hj; omega)
  have fw₂ : VG.Proof.Bignum.X86_64.word s₂.mem B (VG.Proof.Bignum.X86_64.slot w mo) = VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w mo) :=
    ho₂.word (by have := sp (Ne.symm d1); have := sl _ hmo; omega) (by have := sl _ hmo; omega)
  -- The rounds.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rounds_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h9)
    ((k₂.gpr (by decide)).trans h10) ((k₂.gpr (by decide)).trans h11) ((k₂.gpr (by decide)).trans h12)
    hw hw' (sl acc hacc) (by have := sl b hb; omega) (by have := sl mo hmo; omega)
    (by have := sl a ha; omega) (by have := sp (Ne.symm d5); omega) (by have := sp (Ne.symm d1); omega)
    (by have := sp (Ne.symm d4); omega)
    (by rw [fw₂, (k₂.gpr (by decide) : s₂.gpr .r15 = s₁.gpr .r15), h15]; exact hinv) hz₂
    (by rw [fr₂ hb (Ne.symm d5), fr₂ hmo (Ne.symm d1)]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [fr₂ hmo (Ne.symm d1)] at hTlt hTc
  rw [fr₂ ha (Ne.symm d4), fr₂ hb (Ne.symm d5)] at hTc
  have k123 := k12.trans hR.keep
  have hs₃ := hR.scr
  have fr₃ : ∀ {j}, j < 8 → j ≠ acc → VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w j) w = VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w j) w := fun hj hne =>
    (hR.out.wv (by have := sp hne; omega) (by have := sl _ hj; omega)).trans (fr₂ hj hne)
  have k14 := k₂.trans hR.keep
  have hsi : s₃.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w tmp) := (k14.gpr (by decide)).trans hsi₁
  -- `T - m`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.subMod_ok hs₃ ((k14.gpr (by decide)).trans h8) ((k14.gpr (by decide)).trans h10)
    hsi ((k14.gpr (by decide)).trans h12) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₅ ⟨c, lt, hbp, hlt, hD, ho₅, k₅⟩ => ?_)
  have k5 := k123.trans k₅
  have k15 := k14.trans k₅
  -- The selection.
  have hs₅ := hs₃.congr k₅.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.selectAcc_ok hs₅ ((k15.gpr (by decide)).trans h8) ((k₅.gpr (by decide)).trans hsi)
    ((k15.gpr (by decide)).trans hbx) ((k15.gpr (by decide)).trans h12) hbp (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  -- The words of `T` in `s₅`, as after the rounds.
  have hacc₅ : VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w acc) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w :=
    ho₅.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  have hD' : VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w tmp) w + VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w +
      2 ^ (64 * w) * c.toNat := by
    rw [← fr₃ hmo (Ne.symm d1)]; exact hD
  have hres : VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) (w + 2) % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w := by
    rw [hv, hacc₅, hlt, VG.Proof.Bignum.X86_64.wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc) w)
      (Tw := (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc + 8 * w)).toNat)
      (Tw1 := (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc + 8 * w + 8)).toNat) (D := VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w tmp) w)
      (m := VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := VG.Proof.Bignum.X86_64.wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w mo) w; omega) (VG.Proof.Bignum.X86_64.wv_lt _ _ _ _) (Bool.toNat_le c) (VG.Proof.Bignum.X86_64.wv_lt _ _ _ _)
      (by rw [← VG.Proof.Bignum.X86_64.wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w acc + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, (k5.trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have a3 : VG.Proof.Bignum.X86_64.Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) (ho₂.trans hR.out) (Nat.le_refl _) (Nat.le_refl _)
    have a5 : VG.Proof.Bignum.X86_64.Arrays B w [acc, tmp, o] s₃.mem s₅.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₅ (Nat.le_refl _) (by omega)
    have a6 : VG.Proof.Bignum.X86_64.Arrays B w [acc, tmp, o] s₅.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a5).trans a6

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AdxRow`. -/
section

/-!
# Multiword arithmetic on x86-64: a row of the BMI2/ADX multiplication

The blocks of a row (`blocks_ok`) add `a_i b + u m` to the window's `w` low
words and the carries, four words at a time.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## The blocks -/

/-- After `k` blocks of a row from `s₀`, the window at `e`: its `4 k` low
words and the carries are its old ones plus `X b + U m` over them. -/
structure BlkInv (s₀ : State) (B : Addr) (Z e eb eN : Nat) (k : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rsi, .rdx, .rax, .r11, .r12, .r13, .r15, .rcx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 (4 * k)
  out : VG.Proof.Bignum.X86_64.Outside B e (8 * (4 * k)) s₀.mem t.mem
  val : VG.Proof.Bignum.X86_64.wv t.mem B e (4 * k) + 2 ^ (64 * (4 * k)) * ((t.gpr .rcx).toNat + (t.gpr .rbp).toNat) =
    VG.Proof.Bignum.X86_64.wv s₀.mem B e (4 * k) + (VG.Proof.Bignum.X86_64.word s₀.mem B (e - 16)).toNat * VG.Proof.Bignum.X86_64.wv s₀.mem B eb (4 * k) +
      (VG.Proof.Bignum.X86_64.word s₀.mem B (e - 8)).toNat * VG.Proof.Bignum.X86_64.wv s₀.mem B eN (4 * k) + (s₀.gpr .rcx).toNat + (s₀.gpr .rbp).toNat

theorem blkStep_ok {s₀ t : State} {B : Addr} {Z e eb eN w k : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s₀ B Z)
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B e) (h9 : s₀.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (hbx : s₀.gpr .rbx = BitVec.ofNat 64 w) (he : 16 ≤ e) (hw4 : w % 4 = 0) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z) (hZN : eN + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) (sN : eN + 8 * w ≤ e ∨ e + 8 * w ≤ eN) (hk : k < w / 4)
    (hI : VG.Proof.Bignum.X86_64.BlkInv s₀ B Z e eb eN k t) :
    WP isa (.block Adx.block) t fun t' => t'.zf = some (decide (k + 1 = w / 4)) ∧ VG.Proof.Bignum.X86_64.BlkInv s₀ B Z e eb eN (k + 1) t' := by
  have hn := hs.nowrap
  have hk4 : 4 * k + 4 ≤ w := by omega
  have kp := hI.keep
  refine WP.mono (VG.Proof.Bignum.X86_64.block_ok (j := 4 * k) (w := w) hI.scr ((kp.gpr (by decide)).trans h8) ((kp.gpr (by decide)).trans h9)
    ((kp.gpr (by decide)).trans h10) hI.r14 ((kp.gpr (by decide)).trans hbx) he (by omega) (by omega) (by omega)
    (by omega) hw) fun t' ⟨hv, ho, h14, hz, k'⟩ => ⟨?_, ?_⟩
  · rw [hz]; congr 1; exact decide_eq_decide.mpr (by omega)
  -- The words the block read, as in `s₀`.
  have rX : VG.Proof.Bignum.X86_64.word t.mem B (e - 16) = VG.Proof.Bignum.X86_64.word s₀.mem B (e - 16) := hI.out.word (by omega) (by omega)
  have rU : VG.Proof.Bignum.X86_64.word t.mem B (e - 8) = VG.Proof.Bignum.X86_64.word s₀.mem B (e - 8) := hI.out.word (by omega) (by omega)
  have rT : VG.Proof.Bignum.X86_64.wv t.mem B (e + 8 * (4 * k)) 4 = VG.Proof.Bignum.X86_64.wv s₀.mem B (e + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rB : VG.Proof.Bignum.X86_64.wv t.mem B (eb + 8 * (4 * k)) 4 = VG.Proof.Bignum.X86_64.wv s₀.mem B (eb + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rN : VG.Proof.Bignum.X86_64.wv t.mem B (eN + 8 * (4 * k)) 4 = VG.Proof.Bignum.X86_64.wv s₀.mem B (eN + 8 * (4 * k)) 4 := hI.out.wv (by omega) (by omega)
  have rL : VG.Proof.Bignum.X86_64.wv t'.mem B e (4 * k) = VG.Proof.Bignum.X86_64.wv t.mem B e (4 * k) := ho.wv (by omega) (by omega)
  rw [rX, rU, rT, rB, rN] at hv
  refine ⟨hI.scr.congr k'.2.2, (kp.trans k').mono (by simp), by rw [h14]; congr 1, ?_, ?_⟩
  · exact (hI.out.mono (o' := e) (n' := 8 * (4 * (k + 1))) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := e) (n' := 8 * (4 * (k + 1))) (by omega) (by omega))
  · have hval := hI.val
    rw [show 4 * (k + 1) = 4 * k + 4 by omega, VG.Proof.Bignum.X86_64.wv_add, VG.Proof.Bignum.X86_64.wv_add s₀.mem B e, VG.Proof.Bignum.X86_64.wv_add s₀.mem B eb, VG.Proof.Bignum.X86_64.wv_add s₀.mem B eN, rL,
      show 64 * (4 * k + 4) = 64 * (4 * k) + 256 by omega, Nat.pow_add]
    grind

/-- The blocks: from `r14 = 0` and the carries 0, `X b + U m` added to the
window's `w` low words, with the carries out. -/
theorem blocks_ok {s₀ : State} {B : Addr} {Z e eb eN w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s₀ B Z)
    (h8 : s₀.gpr .r8 = VG.Proof.Bignum.X86_64.off B e) (h9 : s₀.gpr .r9 = VG.Proof.Bignum.X86_64.off B eb) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (hbx : s₀.gpr .rbx = BitVec.ofNat 64 w) (h14 : s₀.gpr .r14 = BitVec.ofNat 64 0) (he : 16 ≤ e)
    (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z) (hZN : eN + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) (sN : eN + 8 * w ≤ e ∨ e + 8 * w ≤ eN) :
    WP isa (.loop (.block Adx.block) .ne) s₀ (VG.Proof.Bignum.X86_64.BlkInv s₀ B Z e eb eN (w / 4)) :=
  VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := w / 4) (by omega) (VG.Proof.Bignum.X86_64.BlkInv s₀ B Z e eb eN)
    (fun k _ hk t hI => VG.Proof.Bignum.X86_64.blkStep_ok hs h8 h9 h10 hbx he hw4 hw hZ hZb hZN sb sN hk hI) (fun _ h => h)
    ⟨hs, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [VG.Proof.Bignum.X86_64.wv]⟩

/-! ## The row's start -/

theorem off_add16 (B : Addr) (q : Nat) : VG.Proof.Bignum.X86_64.off B q + 16 = VG.Proof.Bignum.X86_64.off B (q + 16) := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `a`'s base less the first window's: `rowBase`. -/
theorem rowBase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {a : Nat} (ha : a < 8) :
    WP isa (.block (rowBase a)) s fun t =>
      t.gpr .rax = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) - VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) - VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16) ∧
    t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold rowBase
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hl (sArr a) (by unfold sArr; omega), hl (sArr aAcc) (by decide),
    hH.harr a ha, hH.harr aAcc (by decide), VG.Proof.Bignum.X86_64.off_add16]

/-- `[rax + r8]` is `a_i`. -/
theorem rowX_addr (B : Addr) (p q d : Nat) :
    VG.Proof.Bignum.X86_64.off B p - VG.Proof.Bignum.X86_64.off B (q + 16) + VG.Proof.Bignum.X86_64.off B (q + 16 + d) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = VG.Proof.Bignum.X86_64.off B (p + d) := by
  rw [BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    show VG.Proof.Bignum.X86_64.off B (q + 16 + d) = VG.Proof.Bignum.X86_64.off B (q + 16) + BitVec.ofNat 64 d by simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add],
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]

theorem rowX_addr' (B : Addr) {p q d e : Nat} (he : e = q + 16 + d) :
    VG.Proof.Bignum.X86_64.off B p - VG.Proof.Bignum.X86_64.off B (q + 16) + VG.Proof.Bignum.X86_64.off B e * 1#64 = VG.Proof.Bignum.X86_64.off B (p + d) := by
  have := VG.Proof.Bignum.X86_64.rowX_addr B p q d
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  subst he; exact this

theorem off_below (B : Addr) {e d : Nat} (hd : d ≤ e) : VG.Proof.Bignum.X86_64.off B e + BitVec.ofInt 64 (-(d : Int)) = VG.Proof.Bignum.X86_64.off B (e - d) := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.sub_eq_add_neg, show e = (e - d) + d by omega, BitVec.ofNat_add,
    BitVec.add_sub_cancel, show e - d + d - d = e - d by omega]

theorem off_m16 (B : Addr) {e : Nat} (hd : 16 ≤ e) : VG.Proof.Bignum.X86_64.off B e + BitVec.ofInt 64 (-16) = VG.Proof.Bignum.X86_64.off B (e - 16) :=
  VG.Proof.Bignum.X86_64.off_below B (d := 16) hd
theorem off_m8 (B : Addr) {e : Nat} (hd : 8 ≤ e) : VG.Proof.Bignum.X86_64.off B e + BitVec.ofInt 64 (-8) = VG.Proof.Bignum.X86_64.off B (e - 8) :=
  VG.Proof.Bignum.X86_64.off_below B (d := 8) hd

/-- `u` for the row's multiplier `X`, `b₀`, the window's low word `T₀` and
`-m⁻¹`. -/
def rowU (X b₀ T₀ minv : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.ofNat 64 (X.toNat * b₀.toNat) + T₀).toNat * minv.toNat)

/-- `rowHead`: `a_i` and `u` below the window, the carries and the word 0. -/
theorem rowHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {a b i e : Nat} (ha : a < 8) (hb : b < 8)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (he : e = VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i) (hi : i < w)
    (hax : s.gpr .rax = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w a) - VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16)) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b)) :
    WP isa (.block rowHead) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e - 16)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i))).writeW (VG.Proof.Bignum.X86_64.off B (e - 8))
        (VG.Proof.Bignum.X86_64.rowU (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)) (VG.Proof.Bignum.X86_64.word s.mem B e) minv) ∧
      t.gpr .rcx = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧
      VG.Proof.MlKem.X86_64.Keep [.rdx, .rsi, .rax, .rcx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  have hA := VG.Proof.Bignum.X86_64.slot_le (w := w) ha
  have hB := VG.Proof.Bignum.X86_64.slot_le (w := w) hb
  have hT := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aTmp := by unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp; omega
  have hge := VG.Proof.Bignum.X86_64.hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have sbX : VG.Proof.Bignum.X86_64.slot w b + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w b := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have o1 := VG.Proof.Bignum.X86_64.writeW_outside s.mem B (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i)) (d := e - 16) (by omega)
  have r1 : (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e - 16)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i))).readW (VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b)) 64 =
      VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b) := o1.word (by omega) (by omega)
  have r2 : (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e - 16)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i))).readW (VG.Proof.Bignum.X86_64.off B e) 64 =
      VG.Proof.Bignum.X86_64.word s.mem B e := o1.word (by omega) (by omega)
  have r3 : (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e - 16)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i))).readW (VG.Proof.Bignum.X86_64.off B (8 * sMinv)) 64 = minv :=
    (o1.word (by unfold sMinv; omega) (by unfold sMinv; omega)).trans hH.hminv
  refine WP.mono (WP.keep [.rdx, .rsi, .rax, .rcx, .rbp, .r14] (Q := fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e - 16)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i))).writeW (VG.Proof.Bignum.X86_64.off B (e - 8))
        (VG.Proof.Bignum.X86_64.rowU (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i)) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)) (VG.Proof.Bignum.X86_64.word s.mem B e) minv) ∧
      t.gpr .rcx = 0 ∧ t.gpr .rbp = 0 ∧ t.gpr .r14 = BitVec.ofNat 64 0) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold rowHead
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, at0, xSlot, uSlot, hdi, VG.Proof.Bignum.X86_64.hdrOff, hax, h8, h9, execMulx, VG.Proof.Bignum.X86_64.rowX_addr' B (p := VG.Proof.Bignum.X86_64.slot w a) he,
    VG.Proof.Bignum.X86_64.off_m16 B (show 16 ≤ e by omega), VG.Proof.Bignum.X86_64.off_m8 B (show 8 ≤ e by omega),
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld (show VG.Proof.Bignum.X86_64.slot w a + 8 * i + 8 ≤ Z by omega),
    hs.st (show e - 16 + 8 ≤ Z by omega), hs.st (show e - 8 + 8 ≤ Z by omega), hs.ld (show VG.Proof.Bignum.X86_64.slot w b + 8 ≤ Z by omega),
    hs.ld (show e + 8 ≤ Z by omega), hs.ld (show 8 * sMinv + 8 ≤ Z by unfold sMinv; omega), r1, r2, r3, VG.Proof.Bignum.X86_64.rowU]

/-! ## The row's end -/

theorem off_add8 (B : Addr) (q : Nat) : VG.Proof.Bignum.X86_64.off B q + 8 = VG.Proof.Bignum.X86_64.off B (q + 8) := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem off_sub_beq (B : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (VG.Proof.Bignum.X86_64.off B x - VG.Proof.Bignum.X86_64.off B y == 0) = decide (x = y) := by
  rw [VG.Proof.Bignum.X86_64.sub_beq_zero]
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have ox := VG.Proof.Bignum.X86_64.ofs_off B (d := x) (i := 0) (by omega)
    have oy := VG.Proof.Bignum.X86_64.ofs_off B (d := y) (i := 0) (by omega)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at ox oy
    rw [← h', ox] at oy
    omega

/-- `rowTail`: the carries added into the window's words `w` and `w + 1`, and
the window up a word. -/
theorem rowTail_ok {s : State} {B : Addr} {Z e w : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 w) (hZ : e + 8 * w + 16 ≤ Z) :
    WP isa (.block rowTail) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * w)) lo).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * w + 8)) hi ∧
      ((VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8)).toNat +
          (s.gpr .rcx).toNat + (s.gpr .rbp).toNat < 2 ^ 128 →
        lo.toNat + 2 ^ 64 * hi.toNat = (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w)).toNat +
          2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8)).toNat + (s.gpr .rcx).toNat + (s.gpr .rbp).toNat) ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (e + 8) ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rsi, .r8] s t := by
  have hn := hs.nowrap
  generalize hTw : VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w) = Tw
  generalize hT1 : VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8) = T1
  generalize hc : s.gpr .rcx = c
  generalize hp : s.gpr .rbp = p
  have hX : ∀ v, (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * w)) v).readW (VG.Proof.Bignum.X86_64.off B (e + 8 * w + 8)) 64 = T1 := fun v =>
    ((VG.Proof.Bignum.X86_64.writeW_outside s.mem B v (by omega)).word (Or.inr (Nat.le_refl _)) (by omega)).trans hT1
  refine WP.mono (WP.keep [.rax, .rsi, .r8] (Q := fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * w)) (Tw + c + p)).writeW (VG.Proof.Bignum.X86_64.off B (e + 8 * w + 8))
        (T1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ Tw.toNat + c.toNat))).setWidth 64 + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (Tw + c).toNat + p.toNat))).setWidth 64) ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (e + 8)) ?_ rfl) fun t ⟨⟨hm, h8'⟩, k⟩ => ⟨_, _, hm, fun hfit => by
      have e1 := VG.Proof.Bignum.X86_64.addc_toNat Tw T1 c (by omega)
      have e2 := VG.Proof.Bignum.X86_64.addc_toNat (Tw + c) (T1 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ Tw.toNat + c.toNat))).setWidth 64) p
        (by omega)
      omega, h8', k⟩
  unfold rowTail
  xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 h8 h14, VG.Proof.Bignum.X86_64.addr8 h8 h14, hs.ld (show e + 8 * w + 8 ≤ Z by omega),
    hs.st (show e + 8 * w + 8 ≤ Z by omega), hs.ld (show e + 8 * w + 8 + 8 ≤ Z by omega),
    hs.st (show e + 8 * w + 8 + 8 ≤ Z by omega), hTw, hT1, hc, hp, VG.Proof.Bignum.X86_64.sx0, show s.gpr .r8 + 8 = VG.Proof.Bignum.X86_64.off B (e + 8) by rw [h8, VG.Proof.Bignum.X86_64.off_add8]]

/-- `rowEnd`: ZF set when the window `r8 = e` has reached `aTmp`. -/
theorem rowEnd_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {e : Nat} (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e) (heZ : e < Z) :
    WP isa (.block rowEnd) s fun t =>
      t.zf = some (decide (e = VG.Proof.Bignum.X86_64.slot w aTmp)) ∧ t.mem = s.mem ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B e ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r8] s t := by
  have hn := hs.nowrap
  have hT := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aTmp < 8 by decide)
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.zf = some (decide (e = VG.Proof.Bignum.X86_64.slot w aTmp)) ∧ t.mem = s.mem ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B e) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold rowEnd
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hs.ld (show 8 * sArr aTmp + 8 ≤ Z by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega),
    hH.harr aTmp (by decide), h8, VG.Proof.Bignum.X86_64.off_sub_beq B (show e < 2 ^ 64 by omega) (show VG.Proof.Bignum.X86_64.slot w aTmp < 2 ^ 64 by omega)]

/-! ## A row -/

/-- `u` makes the low word of `T + X b + u m` zero. -/
theorem rowU_low (X b₀ T₀ m₀ minv : BitVec 64) (h : (m₀.toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    (T₀.toNat + X.toNat * b₀.toNat + (VG.Proof.Bignum.X86_64.rowU X b₀ T₀ minv).toNat * m₀.toNat) % 2 ^ 64 = 0 := by
  have hl := VG.Proof.Bignum.X86_64.mont_low ((X.toNat * b₀.toNat % 2 ^ 64 + T₀.toNat) % 2 ^ 64) minv.toNat m₀.toNat h
  simp only [VG.Proof.Bignum.X86_64.rowU, BitVec.toNat_ofNat, BitVec.toNat_add] at hl ⊢
  generalize X.toNat * b₀.toNat = P at hl ⊢
  generalize ((P % 2 ^ 64 + T₀.toNat) % 2 ^ 64 * minv.toNat % 2 ^ 64) * m₀.toNat = Q at hl ⊢
  omega

/-- A number's low word and the rest. -/
theorem wv_low (m : Mem) (B : Addr) (d n : Nat) :
    VG.Proof.Bignum.X86_64.wv m B d (n + 1) = (VG.Proof.Bignum.X86_64.word m B d).toNat + 2 ^ 64 * VG.Proof.Bignum.X86_64.wv m B (d + 8) n := by
  rw [Nat.add_comm n 1, VG.Proof.Bignum.X86_64.wv_add]; simp [VG.Proof.Bignum.X86_64.wv]

/-- The header, after changes above it. -/
theorem Hdr.of_outside {m m' : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : VG.Proof.Bignum.X86_64.Hdr m B w minv) {o n : Nat}
    (h : VG.Proof.Bignum.X86_64.Outside B o n m m') (ho : hdrBytes ≤ o) : VG.Proof.Bignum.X86_64.Hdr m' B w minv := by
  have hh : ∀ i < 32, VG.Proof.Bignum.X86_64.word m' B (8 * i) = VG.Proof.Bignum.X86_64.word m B (8 * i) := fun i hi =>
    h.word (Or.inl (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 0 hi; unfold VG.Proof.Bignum.X86_64.slot at this; omega)) (by omega)
  exact ⟨(hh _ (by decide)).trans hH.hw, (hh _ (by decide)).trans hH.hminv,
    fun j hj => (hh _ (by unfold sArr; omega)).trans (hH.harr j hj)⟩

/-- Row `i` of `a`, with the window at `e`: `2⁶⁴ T' = T + a_i b + u m` for the
window `T'` a word up, if the word above the window is zero. -/
theorem row_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {a b i e : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (he : e = VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i) (hi : i < w) (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B e) (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b)) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN))
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) :
    WP isa (VG.Impl.Bignum.X86_64.Adx.row a) s fun t =>
      (((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
        VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * (w + 2)) = 0 →
        VG.Proof.Bignum.X86_64.wv s.mem B e (w + 2) < 2 * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w →
        VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w → ∃ u < 2 ^ 64, 2 ^ 64 * VG.Proof.Bignum.X86_64.wv t.mem B (e + 8) (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B e (w + 2) +
        (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i)).toNat * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w + u * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) ∧
      VG.Proof.Bignum.X86_64.Outside B (e - 16) (8 * (w + 4)) s.mem t.mem ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (e + 8) ∧
      t.zf = some (decide (i + 1 = w)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rsi, .rcx, .rbp, .r14, .r11, .r12, .r13, .r15, .r8] s t := by
  have hn := hs.nowrap
  have hA := VG.Proof.Bignum.X86_64.slot_le (w := w) ha
  have hBs := VG.Proof.Bignum.X86_64.slot_le (w := w) hb
  have hNs := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aN < 8 by decide)
  have hTs := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aTmp := by unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp; omega
  have hge := VG.Proof.Bignum.X86_64.hdr_lt_slot w aAcc (show 31 < 32 by decide)
  have hg0 : hdrBytes ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have sbX : VG.Proof.Bignum.X86_64.slot w b + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w b := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have saX : VG.Proof.Bignum.X86_64.slot w a + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w a := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have sNX : VG.Proof.Bignum.X86_64.slot w aN + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot aN aAcc; omega
  have hw4' : 4 * (w / 4) = w := by omega
  unfold VG.Impl.Bignum.X86_64.Adx.row
  -- `a`'s base.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rowBase_ok hs hdi hH hZ ha) fun s₁ ⟨hax, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- `a_i`, `u`.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rowHead_ok hs₁ ((k₁.gpr (by decide)).trans hdi) (hm₁ ▸ hH) hZ ha hb hb1 hb2 he hi hax
    ((k₁.gpr (by decide)).trans h8) ((k₁.gpr (by decide)).trans h9)) fun s₂ ⟨hm₂, hcx, hbp, h14, k₂⟩ => ?_)
  rw [hm₁] at hm₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  generalize hX : VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i) = X at hm₂
  generalize hU : VG.Proof.Bignum.X86_64.rowU X (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)) (VG.Proof.Bignum.X86_64.word s.mem B e) minv = U at hm₂
  have o₂ : VG.Proof.Bignum.X86_64.Outside B (e - 16) 16 s.mem s₂.mem := by
    rw [hm₂]
    exact ((VG.Proof.Bignum.X86_64.writeW_outside s.mem B X (d := e - 16) (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B U (d := e - 8) (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have wX : VG.Proof.Bignum.X86_64.word s₂.mem B (e - 16) = X := by
    rw [hm₂, (VG.Proof.Bignum.X86_64.writeW_outside _ B U (d := e - 8) (by omega_arith)).word (by omega_arith) (by omega_arith), VG.Proof.Bignum.X86_64.word_writeW_self]
  have wU : VG.Proof.Bignum.X86_64.word s₂.mem B (e - 8) = U := by rw [hm₂, VG.Proof.Bignum.X86_64.word_writeW_self]
  -- The blocks.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.blocks_ok hs₂ ((k12.gpr (by decide)).trans h8) ((k12.gpr (by decide)).trans h9)
    ((k12.gpr (by decide)).trans h10) ((k12.gpr (by decide)).trans hbx) h14 (by omega_arith) hw4 hw1 hw (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ hI => ?_)
  have hval := hI.val
  rw [hw4', wX, wU, hcx, hbp, o₂.wv (by omega_arith) (by omega_arith), o₂.wv (by omega_arith) (by omega_arith),
    o₂.wv (by omega_arith) (by omega_arith), show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at hval
  have k3 := hI.keep
  have o₃ : VG.Proof.Bignum.X86_64.Outside B (e - 16) (8 * (w + 4)) s.mem s₃.mem :=
    (o₂.mono (o' := e - 16) (n' := 8 * (w + 4)) (Nat.le_refl _) (by omega_arith)).trans
      (hI.out.mono (o' := e - 16) (n' := 8 * (w + 4)) (by omega_arith) (by rw [hw4']; omega))
  have wTw : VG.Proof.Bignum.X86_64.word s₃.mem B (e + 8 * w) = VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w) :=
    (hI.out.word (by rw [hw4']; omega) (by omega_arith)).trans (o₂.word (by omega_arith) (by omega_arith))
  have wT1 : VG.Proof.Bignum.X86_64.word s₃.mem B (e + 8 * w + 8) = VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8) :=
    (hI.out.word (by rw [hw4']; omega) (by omega_arith)).trans (o₂.word (by omega_arith) (by omega_arith))
  -- The bound: the sum fits in `w + 2` words.
  have hN := VG.Proof.Bignum.X86_64.wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w
  have hXl := X.isLt
  have hUl := U.isLt
  have h2 := VG.Proof.Bignum.X86_64.wv_top2 s.mem B e w
  have hR : 2 ^ (64 * w) * ((VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8)).toNat +
      (s₃.gpr .rcx).toNat + (s₃.gpr .rbp).toNat) + VG.Proof.Bignum.X86_64.wv s₃.mem B e w =
      VG.Proof.Bignum.X86_64.wv s.mem B e (w + 2) + X.toNat * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w + U.toNat * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := by
    rw [h2]; grind
  -- The carries into words `w` and `w + 1`.
  have hs₃ := hI.scr
  have k123 := k12.trans k3
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rowTail_ok (w := w) hs₃ ((k123.gpr (by decide)).trans h8) (by rw [hI.r14, hw4'])
    (by omega_arith)) fun s₄ ⟨lo, hi', hm₄, hlh, h8₄, k₄⟩ => ?_)
  rw [wTw, wT1] at hlh
  have o₄ : VG.Proof.Bignum.X86_64.Outside B (e + 8 * w) 16 s₃.mem s₄.mem := by
    rw [hm₄]
    exact ((VG.Proof.Bignum.X86_64.writeW_outside s₃.mem B lo (d := e + 8 * w) (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have o₄' : VG.Proof.Bignum.X86_64.Outside B (e - 16) (8 * (w + 4)) s.mem s₄.mem :=
    o₃.trans (o₄.mono (o' := e - 16) (n' := 8 * (w + 4)) (by omega_arith) (by omega_arith))
  -- The test.
  have hs₄ := hs₃.congr k₄.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.rowEnd_ok hs₄ ((k123.trans k₄).gpr (by decide) |>.trans hdi) (hH.of_outside o₄' (by omega_arith)) hZ
    h8₄ (by omega_arith)) fun t ⟨hz, hmt, h8t, k₅⟩ => ?_
  have ot : VG.Proof.Bignum.X86_64.Outside B (e - 16) (8 * (w + 4)) s.mem t.mem := hmt ▸ o₄'
  refine ⟨fun hinv htop hT hB => ⟨U.toNat, hUl, ?_⟩, ot, h8t, by rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_arith)),
    (((k123.trans k₄).trans k₅)).mono (by decide)⟩
  have hsum := VG.Proof.Bignum.round_sum_lt hT hXl hB hUl
  have hfit : (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w)).toNat + 2 ^ 64 * (VG.Proof.Bignum.X86_64.word s.mem B (e + 8 * w + 8)).toNat +
      (s₃.gpr .rcx).toNat + (s₃.gpr .rbp).toNat < 2 ^ 128 := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * w)) ?_
    have : 2 ^ 65 * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ≤ 2 ^ (64 * w) * 2 ^ 128 := by
      rw [Nat.mul_comm (2 ^ (64 * w))]; exact Nat.mul_le_mul (by decide) (by omega_arith)
    omega
  replace hlh := hlh hfit
  have hV : VG.Proof.Bignum.X86_64.wv s₄.mem B e (w + 2) = VG.Proof.Bignum.X86_64.wv s.mem B e (w + 2) + X.toNat * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w +
      U.toNat * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := by
    rw [VG.Proof.Bignum.X86_64.wv_top2, hm₄, VG.Proof.Bignum.X86_64.word_writeW_self,
      (VG.Proof.Bignum.X86_64.writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega_arith)).word (Or.inl (Nat.le_refl _)) (by omega_arith),
      VG.Proof.Bignum.X86_64.word_writeW_self, (VG.Proof.Bignum.X86_64.writeW_outside _ B hi' (d := e + 8 * w + 8) (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith),
      (VG.Proof.Bignum.X86_64.writeW_outside _ B lo (d := e + 8 * w) (by omega_arith)).wv (Or.inl (Nat.le_refl _)) (by omega_arith), hlh, ← hR]
    grind
  rw [← hmt] at hV
  -- The low word is zero, and the word above the window too.
  have hlow : VG.Proof.Bignum.X86_64.wv t.mem B e (w + 2) % 2 ^ 64 = 0 := by
    rw [hV]
    have dT := VG.Proof.Bignum.X86_64.wv_low s.mem B e (w + 1)
    have dB := VG.Proof.Bignum.X86_64.wv_low s.mem B (VG.Proof.Bignum.X86_64.slot w b) (w - 1)
    have dN := VG.Proof.Bignum.X86_64.wv_low s.mem B (VG.Proof.Bignum.X86_64.slot w aN) (w - 1)
    rw [show w - 1 + 1 = w by omega] at dB dN
    rw [dT, dB, dN]
    have := VG.Proof.Bignum.X86_64.rowU_low X (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)) (VG.Proof.Bignum.X86_64.word s.mem B e) (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)) minv hinv
    rw [hU] at this
    generalize VG.Proof.Bignum.X86_64.wv s.mem B (e + 8) (w + 1) = A' at *
    generalize VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b + 8) (w - 1) = B' at *
    generalize VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN + 8) (w - 1) = N' at *
    rw [show (VG.Proof.Bignum.X86_64.word s.mem B e).toNat + 2 ^ 64 * A' + X.toNat * ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)).toNat + 2 ^ 64 * B') +
        U.toNat * ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat + 2 ^ 64 * N') =
        (VG.Proof.Bignum.X86_64.word s.mem B e).toNat + X.toNat * (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w b)).toNat +
          U.toNat * (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat + 2 ^ 64 * (A' + X.toNat * B' + U.toNat * N') by grind,
      Nat.add_mul_mod_self_left, this]
  have htop' : VG.Proof.Bignum.X86_64.word t.mem B (e + 8 * (w + 2)) = 0 := (ot.word (by omega_arith) (by omega_arith)).trans htop
  have d3 := VG.Proof.Bignum.X86_64.wv_low t.mem B e (w + 2)
  rw [VG.Proof.Bignum.X86_64.wv, htop'] at d3
  have := (VG.Proof.Bignum.X86_64.word t.mem B e).isLt
  rw [← hV]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at d3
  omega

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AdxFused`. -/
section

/-!
# Multiword arithmetic on x86-64: the BMI2/ADX Montgomery multiplication

`zeroWin` clears the `2 w + 2` words from the first window (`zeroWin_ok`);
the rows (`rows_ok`) keep the window `T < 2m` and
`2^(64 i) T ≡ (a mod 2^(64 i)) b (mod m)`, as the baseline's rounds do, the
window moving up a word a row; `montMulAdx_ok` is `montMul_ok` for it.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## Clearing the windows -/

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat} (h : ∀ k < n, VG.Proof.Bignum.X86_64.word m B (d + 8 * k) = 0) : VG.Proof.Bignum.X86_64.wv m B d n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Bignum.X86_64.wv, ih fun k hk => h k (by omega), h n (by omega)]; rfl

structure ZwInv (s₀ : State) (B : Addr) (Z A : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : VG.Proof.Bignum.X86_64.Outside B A (8 * j) s₀.mem t.mem
  val : ∀ k < j, VG.Proof.Bignum.X86_64.word t.mem B (A + 8 * k) = 0

/-- `zeroWin`: the `2 w + 2` words from `r8` cleared. -/
theorem zeroWin_ok {s : State} {B : Addr} {Z w A : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B A)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hA : A + 8 * (2 * w + 2) ≤ Z) :
    WP isa zeroWin s fun t => (∀ k < 2 * w + 2, VG.Proof.Bignum.X86_64.word t.mem B (A + 8 * k) = 0) ∧
      VG.Proof.Bignum.X86_64.Outside B A (8 * (2 * w + 2)) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .r14] s t := by
  have hn := hs.nowrap
  unfold zeroWin
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .r14] (Q := fun t => t.gpr .rax = 0 ∧
      t.gpr .rcx = BitVec.ofNat 64 (2 * w + 2) ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ?_ rfl)
    fun s₁ ⟨⟨hax, hcx, h14, hm₁⟩, k₁⟩ => ?_)
  · have : BitVec.ofNat 64 w + BitVec.ofNat 64 w + 2 = BitVec.ofNat 64 (2 * w + 2) := by
      rw [← BitVec.ofNat_add, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
      congr 1; omega
    xrun [hbx, this]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := 2 * w + 2) (by omega) (VG.Proof.Bignum.X86_64.ZwInv s₁ B Z A) ?_ (fun _ h => h)
    ⟨hs₁, Keep.refl _ _, h14, Outside.refl _ _ _ _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩)
    fun t hI => ⟨hI.val, hm₁ ▸ hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B A := (hI.keep.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h8)
  have tax : t.gpr .rax = 0 := (hI.keep.gpr (by decide)).trans hax
  have tcx : t.gpr .rcx = BitVec.ofNat 64 (2 * w + 2) := (hI.keep.gpr (by decide)).trans hcx
  refine WP.mono (WP.keep [.r14] (Q := fun t' => t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off B (A + 8 * j)) (0 : BitVec 64) ∧
      t'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = 2 * w + 2)))
    (by xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 t8 hI.r14, hI.scr.st (show A + 8 * j + 8 ≤ Z by omega), tax, tcx,
      show t.gpr .r14 + 1 = BitVec.ofNat 64 (j + 1) by rw [hI.r14, VG.Proof.Bignum.X86_64.ofNat_add_one],
      VG.Proof.Bignum.X86_64.ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show 2 * w + 2 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm, h14', hz⟩, k'⟩ => ⟨hz, ?_⟩
  have o' := VG.Proof.Bignum.X86_64.writeW_outside t.mem B (0 : BitVec 64) (d := A + 8 * j) (by omega)
  refine ⟨hI.scr.congr k'.2.2, (hI.keep.trans k').mono (by decide), h14', ?_, fun k hk => ?_⟩
  · rw [hm]
    exact (hI.out.mono (o' := A) (n' := 8 * (j + 1)) (Nat.le_refl _) (by omega)).trans
      (o'.mono (o' := A) (n' := 8 * (j + 1)) (by omega) (by omega))
  · rw [hm]
    by_cases hkj : k = j
    · subst hkj; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
    · rw [o'.word (by omega) (by omega)]; exact hI.val k (by omega)

/-! ## The rows -/

/-- After rows `0, …, i - 1` from `s₀`: the window `T < 2m` at `A + 8 i`
(`A` the first), `2^(64 i) T ≡ (a mod 2^(64 i)) b (mod m)`, and the words
above the window zero. -/
structure RowsInv (s₀ : State) (B : Addr) (Z w a b : Nat) (i : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rdx, .rsi, .rcx, .rbp, .r14, .r11, .r12, .r13, .r15, .r8] s₀ t
  r8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i)
  out : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (16 * (w + 2)) s₀.mem t.mem
  zero : ∀ j, i + w + 2 ≤ j → j < 2 * w + 2 → VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * j) = 0
  lt : VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i) (w + 2) < 2 * VG.Proof.Bignum.X86_64.wv s₀.mem B (VG.Proof.Bignum.X86_64.slot w aN) w
  cong : 2 ^ (64 * i) * VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i) (w + 2) % VG.Proof.Bignum.X86_64.wv s₀.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
    VG.Proof.Bignum.X86_64.wv s₀.mem B (VG.Proof.Bignum.X86_64.slot w a) i * VG.Proof.Bignum.X86_64.wv s₀.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s₀.mem B (VG.Proof.Bignum.X86_64.slot w aN) w

theorem rows_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (h8 : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16)) (h9 : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b))
    (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN)) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h0 : ∀ k < 2 * w + 2, VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * k) = 0)
    (hB : VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) :
    WP isa (.loop (VG.Impl.Bignum.X86_64.Adx.row a) .ne) s (VG.Proof.Bignum.X86_64.RowsInv s B Z w a b w) := by
  have hn := hs.nowrap
  have hA := VG.Proof.Bignum.X86_64.slot_le (w := w) ha
  have hBs := VG.Proof.Bignum.X86_64.slot_le (w := w) hb
  have hNs := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aN < 8 by decide)
  have hTs := VG.Proof.Bignum.X86_64.slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aTmp := by unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp; omega
  have hg0 : hdrBytes ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have sbX : VG.Proof.Bignum.X86_64.slot w b + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w b := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have saX : VG.Proof.Bignum.X86_64.slot w a + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w a := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have sNX : VG.Proof.Bignum.X86_64.slot w aN + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot aN aAcc; omega
  have hN0 : 0 < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := by omega
  refine VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := w) (by omega) (VG.Proof.Bignum.X86_64.RowsInv s B Z w a b) ?_ (fun _ h => h)
    ⟨hs, Keep.refl _ _, by rw [h8], Outside.refl _ _ _ _, fun j _ hj => h0 j hj,
      by rw [Nat.mul_zero, Nat.add_zero, VG.Proof.Bignum.X86_64.wv_zero fun k hk => h0 k (by omega)]; omega,
      by rw [Nat.mul_zero, Nat.add_zero, VG.Proof.Bignum.X86_64.wv_zero fun k hk => h0 k (by omega)]; simp [VG.Proof.Bignum.X86_64.wv]⟩
  intro i _ hi t hI
  have hk := hI.keep
  have fw : ∀ {d}, d + 8 ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aAcc + 16 * (w + 2) ≤ d → d + 8 ≤ Z →
      VG.Proof.Bignum.X86_64.word t.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun h1 h2 => hI.out.word h1 (by omega)
  have fv : ∀ {d k}, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aAcc + 16 * (w + 2) ≤ d → d + 8 * k ≤ Z →
      VG.Proof.Bignum.X86_64.wv t.mem B d k = VG.Proof.Bignum.X86_64.wv s.mem B d k := fun h1 h2 => hI.out.wv h1 (by omega)
  have vN := fv (d := VG.Proof.Bignum.X86_64.slot w aN) (k := w) (by omega) (by omega)
  have vB := fv (d := VG.Proof.Bignum.X86_64.slot w b) (k := w) (by omega) (by omega)
  refine WP.mono (VG.Proof.Bignum.X86_64.row_ok hI.scr ((hk.gpr (by decide)).trans hdi) (hH.of_outside hI.out hg0) hZ ha hb ha1 ha2 hb1
    hb2 rfl hi hw4 hw1 hw hI.r8 ((hk.gpr (by decide)).trans h9) ((hk.gpr (by decide)).trans h10)
    ((hk.gpr (by decide)).trans hbx)) fun t' ⟨hval, ho, h8', hz, k'⟩ => ⟨hz, ?_⟩
  obtain ⟨u, hu, hv⟩ := hval (by rw [fw (by omega) (by omega)]; exact hinv)
    (by rw [show VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * (i + w + 2) by omega];
        exact hI.zero _ (Nat.le_refl _) (by omega))
    (by rw [vN]; exact hI.lt) (by rw [vB, vN]; exact hB)
  rw [vN, vB, fw (by omega) (by omega)] at hv
  have e8 : VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * i + 8 = VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * (i + 1) := by omega
  rw [e8] at hv h8'
  refine ⟨hI.scr.congr k'.2.2, (hk.trans k').mono (by simp), h8',
    hI.out.trans (ho.mono (o' := VG.Proof.Bignum.X86_64.slot w aAcc) (n' := 16 * (w + 2)) (by omega) (by omega)), fun j hj hj' => ?_,
    VG.Proof.Bignum.round_lt hv hI.lt (VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w a + 8 * i)).isLt hB hu, ?_⟩
  · rw [ho.word (by omega) (by omega)]; exact hI.zero j (by omega) hj'
  · rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add, VG.Proof.Bignum.round_step hv hI.cong]
    congr 1

/-! ## The multiplication -/

/-- `setup b`: `b`, `m`, the first window and `w` from the header. -/
theorem adxSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {b : Nat} (hb : b < 8) :
    WP isa (.block (VG.Impl.Bignum.X86_64.Adx.setup b)) s fun t => t.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r9, .r10, .r8, .rbx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r9, .r10, .r8, .rbx] (Q := fun t => t.gpr .r9 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w b) ∧
      t.gpr .r10 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aN) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc + 16) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold VG.Impl.Bignum.X86_64.Adx.setup
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hl (sArr b) (by unfold sArr; omega), hl (sArr aN) (by decide),
    hl (sArr aAcc) (by decide), hl sW (by decide), hH.harr b hb, hH.harr aN (by decide), hH.harr aAcc (by decide),
    hH.hw, VG.Proof.Bignum.X86_64.off_add16]

/-- `finishBases o`: `w`, the result `aTmp`, `aAcc` and `o` from the header. -/
theorem finishBases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) {o : Nat} (ho : o < 8) :
    WP isa (.block (finishBases o)) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aTmp) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧
      t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.r12, .r8, .rsi, .rbx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r12, .r8, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aTmp) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w aAcc) ∧ t.gpr .rbx = VG.Proof.Bignum.X86_64.off B (VG.Proof.Bignum.X86_64.slot w o) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold finishBases
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hl sW (by decide), hl (sArr aTmp) (by decide), hl (sArr aAcc) (by decide),
    hl (sArr o) (by unfold sArr; omega), hH.hw, hH.harr aTmp (by decide), hH.harr aAcc (by decide), hH.harr o ho]

/-- `fused o a b`, for `w` a multiple of 4: what `montMul_ok` says of `montMul`. -/
theorem fused_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw4 : w % 4 = 0) (hw1 : 4 ≤ w)
    (hw : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) :
    WP isa (fused o a b) s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, VG.Proof.Bignum.X86_64.slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (VG.Proof.Bignum.X86_64.slot_le hj) hZ
  have hAT : VG.Proof.Bignum.X86_64.slot w aAcc + 8 * (w + 2) = VG.Proof.Bignum.X86_64.slot w aTmp := by unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp; omega
  have hg0 : hdrBytes ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  have hTs := sl aTmp (by decide)
  have sNX : VG.Proof.Bignum.X86_64.slot w aN + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc := by unfold VG.Proof.Bignum.X86_64.slot aN aAcc; omega
  have soX : VG.Proof.Bignum.X86_64.slot w o + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w o := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ho1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ho2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have sbX : VG.Proof.Bignum.X86_64.slot w b + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w b := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) hb2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have saX : VG.Proof.Bignum.X86_64.slot w a + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aTmp + 8 * (w + 2) ≤ VG.Proof.Bignum.X86_64.slot w a := by
    have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha1; have := VG.Proof.Bignum.X86_64.slot_sep (w := w) ha2; unfold VG.Proof.Bignum.X86_64.slot aAcc aTmp at *; omega
  have hN0 : 0 < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := by omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 hi; omega)
  unfold fused
  -- The bases.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.adxSetup_ok hs hdi hH hZ hb) fun s₁ ⟨h9, h10, h8, hbx, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- The windows := 0.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.zeroWin_ok hs₁ h8 hbx (by omega) (by omega)) fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have fw₂ : ∀ {d}, d + 8 ≤ VG.Proof.Bignum.X86_64.slot w aAcc + 16 ∨ VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * (2 * w + 2) ≤ d → d + 8 ≤ Z →
      VG.Proof.Bignum.X86_64.word s₂.mem B d = VG.Proof.Bignum.X86_64.word s.mem B d := fun h1 h2 => ho₂.word h1 (by omega)
  have fv₂ : ∀ {d k}, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot w aAcc + 16 ∨ VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * (2 * w + 2) ≤ d → d + 8 * k ≤ Z →
      VG.Proof.Bignum.X86_64.wv s₂.mem B d k = VG.Proof.Bignum.X86_64.wv s.mem B d k := fun h1 h2 => ho₂.wv h1 (by omega)
  have hH₂ : VG.Proof.Bignum.X86_64.Hdr s₂.mem B w minv := hH.of_outside ho₂ (by omega)
  have vN := fv₂ (d := VG.Proof.Bignum.X86_64.slot w aN) (k := w) (by omega) (by omega)
  have vA := fv₂ (d := VG.Proof.Bignum.X86_64.slot w a) (k := w) (by omega) (by have := sl a ha; omega)
  have vB := fv₂ (d := VG.Proof.Bignum.X86_64.slot w b) (k := w) (by omega) (by have := sl b hb; omega)
  -- The rows.
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.rows_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ ha hb ha1 ha2 hb1 hb2 hw4 hw1 (by omega)
    ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h9) ((k₂.gpr (by decide)).trans h10)
    ((k₂.gpr (by decide)).trans hbx) (by rw [fw₂ (by omega) (by omega)]; exact hinv) hz₂
    (by rw [vB, vN]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [show VG.Proof.Bignum.X86_64.slot w aAcc + 16 + 8 * w = VG.Proof.Bignum.X86_64.slot w aTmp by omega, vN] at hTlt hTc
  rw [vA, vB] at hTc
  have k123 := k12.trans hR.keep
  have hs₃ := hR.scr
  have fr₃ : ∀ {d k}, d + 8 * k ≤ VG.Proof.Bignum.X86_64.slot w aAcc ∨ VG.Proof.Bignum.X86_64.slot w aAcc + 16 * (w + 2) ≤ d → d + 8 * k ≤ Z →
      VG.Proof.Bignum.X86_64.wv s₃.mem B d k = VG.Proof.Bignum.X86_64.wv s.mem B d k := fun h1 h2 =>
    (hR.out.wv h1 (by omega)).trans (fv₂ (by omega) (by omega))
  have hH₃ : VG.Proof.Bignum.X86_64.Hdr s₃.mem B w minv := hH₂.of_outside hR.out hg0
  -- `T - m` into `aAcc`, and the one below `m` into `o`.
  unfold VG.Impl.Bignum.X86_64.Adx.finish
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.finishBases_ok hs₃ ((k123.gpr (by decide)).trans hdi) hH₃ hZ ho)
    fun s₄ ⟨h12₄, h8₄, hsi₄, hbx₄, hm₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k123.trans k₄
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.subMod_ok hs₄ h8₄ ((((k₂.trans hR.keep).trans k₄).gpr (by decide)).trans h10) hsi₄ h12₄ (by omega) hw
    (by omega) (by have := sl aN (by decide); omega) (by omega) (by omega) (by omega))
    fun s₅ ⟨c, lt, hbp, hlt, hD, ho₅, k₅⟩ => ?_)
  rw [hm₄] at hlt hD ho₅
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.mono (VG.Proof.Bignum.X86_64.selectAcc_ok hs₅ ((k₅.gpr (by decide)).trans h8₄) ((k₅.gpr (by decide)).trans hsi₄)
    ((k₅.gpr (by decide)).trans hbx₄) ((k₅.gpr (by decide)).trans h12₄) hbp (by omega) hw (by omega) (by omega)
    (by have := sl o ho; omega) (by omega) (by omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  have hT₅ : VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w aTmp) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp) w := ho₅.wv (by omega) (by omega)
  have hN₃ : VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := fr₃ (by omega) (by omega)
  have hD' : VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) w + VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp) w +
      2 ^ (64 * w) * c.toNat := by rw [← hN₃]; exact hD
  have hres : VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w = VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp) (w + 2) % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w := by
    rw [hv, hT₅, hlt, VG.Proof.Bignum.X86_64.wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := VG.Proof.Bignum.X86_64.wv s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp) w)
      (Tw := (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp + 8 * w)).toNat)
      (Tw1 := (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp + 8 * w + 8)).toNat) (D := VG.Proof.Bignum.X86_64.wv s₅.mem B (VG.Proof.Bignum.X86_64.slot w aAcc) w)
      (m := VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := VG.Proof.Bignum.X86_64.wv_lt s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w; omega) (VG.Proof.Bignum.X86_64.wv_lt _ _ _ _) (Bool.toNat_le c) (VG.Proof.Bignum.X86_64.wv_lt _ _ _ _)
      (by rw [← VG.Proof.Bignum.X86_64.wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (VG.Proof.Bignum.X86_64.word s₃.mem B (VG.Proof.Bignum.X86_64.slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, ((k14.trans k₅).trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have o₃ : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (16 * (w + 2)) s.mem s₃.mem := fun x hx =>
      (hR.out x hx).trans (ho₂ x (by omega))
    have o₅ : VG.Proof.Bignum.X86_64.Outside B (VG.Proof.Bignum.X86_64.slot w aAcc) (16 * (w + 2)) s.mem s₅.mem := fun x hx =>
      (ho₅ x (by omega)).trans (o₃ x hx)
    intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    exact (hot x (by omega)).trans (o₅ x (by omega))

theorem rotr2_toNat (x : BitVec 64) : (x.rotateRight 2).toNat = x.toNat / 4 + x.toNat % 4 * 2 ^ 62 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reduceSub]
  have hx := x.isLt
  rw [Nat.shiftLeft_eq, show x.toNat * 2 ^ 62 % 2 ^ 64 = (x.toNat % 4) <<< 62 by rw [Nat.shiftLeft_eq]; omega,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- What `sizeTest` tests. -/
def SizeOk (w : Nat) : Prop := w % 4 = 0 ∧ 4 ≤ w ∧ w < 2 ^ 30 + 4

instance (w : Nat) : Decidable (VG.Proof.Bignum.X86_64.SizeOk w) := inferInstanceAs (Decidable (_ ∧ _))

theorem sizeTest_beq (w : Nat) (hw : w < 2 ^ 64) :
    ((BitVec.ofNat 64 w - 4).rotateRight 2 >>> 28 == 0) = decide (VG.Proof.Bignum.X86_64.SizeOk w) := by
  have h : ((BitVec.ofNat 64 w - 4).rotateRight 2 >>> 28).toNat =
      ((2 ^ 64 - 4 + w) % 2 ^ 64 / 4 + (2 ^ 64 - 4 + w) % 2 ^ 64 % 4 * 2 ^ 62) / 2 ^ 28 := by
    rw [BitVec.toNat_ushiftRight, VG.Proof.Bignum.X86_64.rotr2_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (4 : BitVec 64).toNat = 4 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  generalize hv : (2 ^ 64 - 4 + w) % 2 ^ 64 = v at h
  have h1 : v % 4 = w % 4 := by omega
  have h3 : 4 ≤ w → v = w - 4 := by omega
  have h4 : w < 4 → v = 2 ^ 64 - 4 + w := by omega
  unfold VG.Proof.Bignum.X86_64.SizeOk
  by_cases h0 : w % 4 = 0 ∧ 4 ≤ w ∧ w < 2 ^ 30 + 4
  · simp only [h0, and_self, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; have := congrArg BitVec.toNat he; rw [h, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega

/-- `sizeTest`: ZF set when `fused` applies. -/
theorem sizeTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) :
    WP isa (.block sizeTest) s fun t => t.zf = some (decide (VG.Proof.Bignum.X86_64.SizeOk w)) ∧ t.mem = s.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (VG.Proof.Bignum.X86_64.SizeOk w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold sizeTest
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdi, VG.Proof.Bignum.X86_64.hdrOff, hs.ld (show 8 * sW + 8 ≤ Z by have := VG.Proof.Bignum.X86_64.hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    hH.hw, VG.Proof.Bignum.X86_64.sizeTest_beq w (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes at hZ; omega)]

/-- `montMulAdx o a b`: what `montMul_ok` says of `montMul aN aAcc aTmp o a b`, if
neither `a` nor `b` is `aTmp` either. -/
theorem montMulAdx_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : VG.Proof.Bignum.X86_64.Hdr s.mem B w minv) (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((VG.Proof.Bignum.X86_64.word s.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) :
    WP isa (montMulAdx o a b) s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s t := by
  have hn := hs.nowrap
  unfold montMulAdx
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s₁ t) →
      (VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv s₁.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h4 : VG.Proof.Bignum.X86_64.SizeOk w
  · refine WP.ite true (by simp [VG.X86_64.eval, hz, h4]) (fun _ => WP.mono (VG.Proof.Bignum.X86_64.fused_ok hs₁ hdi₁ hH hZ h4.1 h4.2.1 hw' ho ha hb
      ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [VG.X86_64.eval, hz, h4]) (by simp) (fun _ => WP.mono (VG.Proof.Bignum.X86_64.montMul_ok hs₁ hdi₁ hH hZ hw hw'
      (by decide) (by decide) (by decide) ho ha hb (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1)
      (by decide) (Ne.symm ho2) hinv hB) post)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Mont`. -/
section

/-!
# Multiword arithmetic on x86-64: constant time

Two runs are related by `Two Φ` when both satisfy `Φ a` for the same public
data `a` (whatever their secrets). The pieces of code whose addresses and
branches depend only on registers that `Φ a` fixes are checked by the taint
analysis (`two_taint`); what each run satisfies afterwards follows from
correctness (`two_post`). Branches and loops whose conditions come from
public data the taint analysis cannot track (it is loaded from memory) agree
since `Φ a` fixes them (`two_ite`, `two_loop`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The working space at `B`, its base in `rdi`, and the header. -/
structure Good (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : VG.Proof.Bignum.X86_64.Hdr t.mem B w minv

theorem execBlock_append {M : ISA} (l₁ l₂ : List M.Instr) (s : M.State) :
    execBlock M (l₁ ++ l₂) s = (execBlock M l₁ s).bind fun p =>
      (execBlock M l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock M is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_append {M : ISA} {P Q : M.State → M.State → Prop} {l₁ l₂ : List M.Instr}
    (h : RelCT M P (.seq (.block l₁) (.block l₂)) Q) : RelCT M P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec M (.block (l₁ ++ l₂)) s t s' → Exec M (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, VG.Proof.Bignum.X86_64.execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) c (VG.Proof.Bignum.X86_64.Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : VG.Proof.Bignum.X86_64.Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨a, h₁, h₂⟩ => Taint.agree_ofRegs (hpin a _ _ h₁ h₂)) h

/-- A piece checked by the taint analysis, with what correctness gives after it. -/
theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : VG.Proof.Bignum.X86_64.Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) c (VG.Proof.Bignum.X86_64.Two Ψ) :=
  VG.Proof.Bignum.X86_64.two_post (VG.Proof.Bignum.X86_64.two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (VG.Proof.Bignum.X86_64.Two Φ') c Q) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨g a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

theorem two_mono {α : Type} {Φ Φ' : α → State → Prop} (h : ∀ a s, Φ a s → Φ' a s) {s₁ s₂ : State}
    (hp : VG.Proof.Bignum.X86_64.Two Φ s₁ s₂) : VG.Proof.Bignum.X86_64.Two Φ' s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := hp; ⟨a, h a _ h₁, h a _ h₂⟩

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (VG.Proof.Bignum.X86_64.Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (VG.Proof.Bignum.X86_64.Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h) (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

/-- A loop of `N a` iterations, its `j`-th from a state satisfying `Φ a j`,
whose condition after iteration `j` is whether `j + 1 < N a`. -/
theorem two_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop} (N : α → Nat)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (VG.Proof.Bignum.X86_64.Two fun (p : α × Nat) s => p.2 < N p.1 ∧ Φ p.1 p.2 s) body fun _ _ => True)
    (hw : ∀ a j s, j < N a → Φ a j s → WP isa body s fun s' =>
      isa.eval cond s' = some (decide (j + 1 < N a)) ∧ (j + 1 < N a → Φ a (j + 1) s') ∧
      (j + 1 = N a → Ψ a s')) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two fun a s => 0 < N a ∧ Φ a 0 s) (.loop body cond) (VG.Proof.Bignum.X86_64.Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := VG.Proof.Bignum.X86_64.Two Ψ)
    (fun n s₁ s₂ => ∃ a j, n = N a - j ∧ j < N a ∧ Φ a j s₁ ∧ Φ a j s₂) (fun n => by
      have hp := VG.Proof.Bignum.X86_64.two_post (Φ := fun (p : α × Nat) s => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ Φ p.1 p.2 s)
        (Ψ := fun p s' => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ isa.eval cond s' = some (decide (p.2 + 1 < N p.1)) ∧
          (p.2 + 1 < N p.1 → Φ p.1 (p.2 + 1) s') ∧ (p.2 + 1 = N p.1 → Ψ p.1 s'))
        (VG.Proof.Bignum.X86_64.two_map id (fun p s h => ⟨h.1, h.2.2⟩) hct)
        fun p s h => WP.mono (hw p.1 p.2 s h.1 h.2.2) fun s' h' => ⟨h.1, h.2.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, j, hn, hj, h₁, h₂⟩ => ⟨(a, j), ⟨hj, hn, h₁⟩, hj, hn, h₂⟩) ?_
      rintro s₁ s₂ ⟨⟨a, j⟩, ⟨hj, hn, e₁, f₁, g₁⟩, ⟨-, -, e₂, f₂, g₂⟩⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have : ¬ j + 1 < N a := by rw [e₁] at h; simpa using h
        have hjN : j + 1 = N a := by simp only at hj this; omega
        exact ⟨a, g₁ hjN, g₂ hjN⟩
      · have hlt : j + 1 < N a := by rw [e₁] at h; simpa using h
        exact ⟨N a - (j + 1), by simp only at hn; omega, a, j + 1, rfl, hlt, f₁ hlt, f₂ hlt⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, ⟨h0, h₁⟩, ⟨-, h₂⟩⟩ := hp
  exact key (N a - 0) _ _ _ _ _ _ ⟨a, 0, rfl, h0, h₁, h₂⟩ e₁ e₂

/-! ## Montgomery multiplication -/

/-- The working space, its header and its size: the public data of
`montMul`. -/
structure Lay where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64

/-- The working space and its header, for `montMul`. -/
def GoodL (L : VG.Proof.Bignum.X86_64.Lay) (s : State) : Prop := VG.Proof.Bignum.X86_64.Good s L.B L.Z L.w L.minv ∧ VG.Proof.Bignum.X86_64.slot L.w 8 ≤ L.Z

/-- The working space and its size, without `-m⁻¹`: what `montMul`'s
timing depends on, so that runs with different (secret) moduli agree. -/
structure Ws where
  B : Addr
  Z : Nat
  w : Nat

/-- The working space and its header, for some `-m⁻¹`. -/
def GoodW (L : VG.Proof.Bignum.X86_64.Ws) (s : State) : Prop := ∃ minv, VG.Proof.Bignum.X86_64.Good s L.B L.Z L.w minv ∧ VG.Proof.Bignum.X86_64.slot L.w 8 ≤ L.Z

/-- The working space of a layout. -/
abbrev Lay.ws (L : VG.Proof.Bignum.X86_64.Lay) : VG.Proof.Bignum.X86_64.Ws := ⟨L.B, L.Z, L.w⟩

theorem GoodL.goodW {L : VG.Proof.Bignum.X86_64.Lay} {s : State} (h : VG.Proof.Bignum.X86_64.GoodL L s) : VG.Proof.Bignum.X86_64.GoodW L.ws s := ⟨L.minv, h⟩

/-- A multiplication constant time for any `-m⁻¹` is for a fixed one. -/
theorem RelCT.ofW {c : Prog isa} (h : RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodW) c fun _ _ => True) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodL) c fun _ _ => True :=
  VG.Proof.Bignum.X86_64.two_map Lay.ws (fun _ _ h => h.goodW) h

/-- After `bases`: the bases, `w` and `-m⁻¹` in registers. -/
def BasesL (mo acc tmp o a b : Nat) (L : VG.Proof.Bignum.X86_64.Ws) (t : State) : Prop :=
  t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o) ∧ t.gpr .r11 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w a) ∧ t.gpr .r9 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w b) ∧
  t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w mo) ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w acc) ∧
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w tmp)

theorem pins_bases (mo acc tmp o a b : Nat) :
    VG.Proof.Bignum.X86_64.Pins (VG.Proof.Bignum.X86_64.BasesL mo acc tmp o a b) [.rbx, .r11, .r9, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem pins_good : VG.Proof.Bignum.X86_64.Pins VG.Proof.Bignum.X86_64.GoodL [.rdi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.1.rdi, h₂.1.rdi]

theorem pins_goodW : VG.Proof.Bignum.X86_64.Pins VG.Proof.Bignum.X86_64.GoodW [.rdi] := by
  intro L s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.rdi, h₂.rdi]

/-- What `montMul` does after its bases, checked by the taint analysis. -/
theorem mmTail_ct (mo acc tmp o a b : Nat) : RelCT isa (VG.Proof.Bignum.X86_64.Two (VG.Proof.Bignum.X86_64.BasesL mo acc tmp o a b)) (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc)))
    fun _ _ => True :=
  VG.Proof.Bignum.X86_64.two_taint _ (VG.Proof.Bignum.X86_64.pins_bases mo acc tmp o a b) (by taint_decide)

/-- `montMul` is constant time, given that the taint analysis checks its
`bases` from `rdi`. -/
theorem montMul_ctW {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b mo acc tmp)) hc).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodW) (montMul mo acc tmp o a b) fun _ _ => True := by
  unfold montMul
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := VG.Proof.Bignum.X86_64.BasesL mo acc tmp o a b) _ VG.Proof.Bignum.X86_64.pins_goodW h fun L s ⟨_, hs, hZ⟩ => ?_)
    (VG.Proof.Bignum.X86_64.mmTail_ct mo acc tmp o a b)
  exact WP.mono (VG.Proof.Bignum.X86_64.bases_ok hs.scr hs.rdi hs.hdr hZ ho ha hb hmo hacc htmp)
    fun t ⟨h1, h2, h3, h4, h5, h6, _, h8, _⟩ => ⟨h1, h2, h3, h4, h5, h6, h8⟩

theorem montMul_ct {mo acc tmp o a b : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b mo acc tmp)) hc).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodL) (montMul mo acc tmp o a b) fun _ _ => True :=
  RelCT.ofW (VG.Proof.Bignum.X86_64.montMul_ctW hmo hacc htmp ho ha hb h)

/-! ## Implementations of Montgomery multiplication -/

open VG.Impl.Bignum.X86_64.Public in
/-- The multiplications RSA makes, `[o] = [a] [b] R⁻¹ mod m`: those of
`vg_rsa_public`, then the others of `vg_rsa_private_crt` (whose prime
workspaces name arrays 1, 4 and 5 differently: its chunk, `x` and `T`; the
last builds the exponentiation's table, `T := T x`). -/
def MmUse (o a b : Nat) : Prop :=
  (o = aR2 ∧ a = aR2 ∧ b = aR2) ∨ (o = aY ∧ a = aY ∧ b = aY) ∨ (o = aY ∧ a = aY ∧ b = aXm) ∨
  (o = aY ∧ a = aR2 ∧ b = aOne) ∨ (o = aXm ∧ a = aX ∧ b = aR2) ∨ (o = aY ∧ a = aY ∧ b = aOne) ∨
  (o = aR2 ∧ a = aR2 ∧ b = aOne) ∨ (o = aXm ∧ a = aX ∧ b = aOne) ∨ (o = aXm ∧ a = aY ∧ b = aR2) ∨
  (o = aY ∧ a = aXm ∧ b = aY) ∨ (o = aX ∧ a = aX ∧ b = aR2) ∨ (o = aX ∧ a = aX ∧ b = aY) ∨
  (o = aY ∧ a = aXm ∧ b = aX) ∨ (o = aXm ∧ a = aXm ∧ b = aR2)

open VG.Impl.Bignum.X86_64.Public in
/-- An implementation `mm o a b` of Montgomery multiplication in the working
space of `vg_rsa_public` (with `m` in array `aN` and working arrays `aAcc`
and `aTmp`), what RSA's proofs need of it: `[o] = [a] [b] R⁻¹ mod m`
changing only `aAcc`, `aTmp` and `o`, and constant time for each
multiplication RSA makes, whatever the modulus. The baseline `montMul`
(`Mont.base`), or one for other CPU features. -/
structure Mont where
  mm : Nat → Nat → Nat → Prog isa
  ok : ∀ {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}, VG.Proof.Bignum.X86_64.Good t B Z w minv → VG.Proof.Bignum.X86_64.slot w 8 ≤ Z → 2 ≤ w →
    w < 2 ^ 31 → ∀ {o a b : Nat}, o < 8 → a < 8 → b < 8 → o ≠ aAcc → o ≠ aTmp → a ≠ aAcc → a ≠ aTmp →
    b ≠ aAcc → b ≠ aTmp → ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
    VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w →
    WP isa (mm o a b) t fun t' =>
      VG.Proof.Bignum.X86_64.Good t' B Z w minv ∧ VG.Proof.Bignum.X86_64.wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs t t'
  ct : ∀ {o a b : Nat}, VG.Proof.Bignum.X86_64.MmUse o a b → RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodW) (mm o a b) fun _ _ => True

open VG.Impl.Bignum.X86_64.Public

/-- `M.mm o a b` is constant time for a fixed modulus. -/
theorem Mont.ctL (M : VG.Proof.Bignum.X86_64.Mont) {o a b : Nat} (h : VG.Proof.Bignum.X86_64.MmUse o a b) : RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodL) (M.mm o a b) fun _ _ => True :=
  RelCT.ofW (M.ct h)

/-- `M.mm o a b`, for arrays that are not `aAcc` or `aTmp`. -/
theorem Mont.mm_ok (M : VG.Proof.Bignum.X86_64.Mont) {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : VG.Proof.Bignum.X86_64.Good t B Z w minv)
    (hZ : VG.Proof.Bignum.X86_64.slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc)
    (hinv : ((VG.Proof.Bignum.X86_64.word t.mem B (VG.Proof.Bignum.X86_64.slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w < VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w) (d5 : a ≠ aTmp := by decide)
    (d6 : b ≠ aTmp := by decide) :
    WP isa (M.mm o a b) t fun t' =>
      VG.Proof.Bignum.X86_64.Good t' B Z w minv ∧ VG.Proof.Bignum.X86_64.wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w < VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.wv t'.mem B (VG.Proof.Bignum.X86_64.slot w o) w * 2 ^ (64 * w) % VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w =
        VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w a) w * VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w b) w % VG.Proof.Bignum.X86_64.wv t.mem B (VG.Proof.Bignum.X86_64.slot w aN) w ∧
      VG.Proof.Bignum.X86_64.Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.Bignum.X86_64.mmRegs t t' :=
  M.ok hg hZ hw hw' ho ha hb d1 d2 d3 d5 d4 d6 hinv hB

theorem mm_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodW) (mm o a b) fun _ _ => True :=
  VG.Proof.Bignum.X86_64.montMul_ctW (by decide) (by decide) (by decide) ho ha hb h

/-- The baseline: `montMul` with `m`, the accumulator and the temporary of
`vg_rsa_public` (`mm`). -/
def Mont.base : VG.Proof.Bignum.X86_64.Mont where
  mm := VG.Impl.Bignum.X86_64.Public.mm
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 _ d4 _ hinv hB :=
    WP.mono (VG.Proof.Bignum.X86_64.montMul_ok hg.scr hg.rdi hg.hdr hZ hw hw' (by decide) (by decide) (by decide) ho ha hb (by decide)
      (by decide) (Ne.symm d1) (Ne.symm d3) (Ne.symm d4) (by decide) (Ne.symm d2) hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact VG.Proof.Bignum.X86_64.mm_ct (by decide) (by decide) (by decide) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AdxCT`. -/
section

/-!
# Multiword arithmetic on x86-64: the BMI2/ADX multiplication in constant time

As for `montMul_ct`, the pieces that load from the header are checked by the
taint analysis from `rdi`, and what follows them from the registers they set,
which `Two` fixes. The size test, the rows' loop and the end of each row
compare with values from the header, so the branch and the loop are taken
alike in both runs because `Ws` fixes `w` (`two_ite`, `two_loop`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64

/-- Before row `i` of `b`'s multiplication: the window and the bases. -/
def FW (b : Nat) (L : VG.Proof.Bignum.X86_64.Ws) (i : Nat) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.GoodW L t ∧ VG.Proof.Bignum.X86_64.SizeOk L.w ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aAcc + 16 + 8 * i) ∧
  t.gpr .r9 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w b) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aN) ∧ t.gpr .rbx = BitVec.ofNat 64 L.w

theorem FW.pins {b : Nat} {L : VG.Proof.Bignum.X86_64.Ws} {i : Nat} {s₁ s₂ : State} (h₁ : VG.Proof.Bignum.X86_64.FW b L i s₁) (h₂ : VG.Proof.Bignum.X86_64.FW b L i s₂) :
    ∀ r ∈ [Reg.rdi, .r8, .r9, .r10, .rbx], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.Bignum.X86_64.pins_goodW L s₁ s₂ h₁.1 h₂.1 .rdi (by simp)
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

/-- After `rowBase`: `rax` too. -/
def FR (a b : Nat) (p : VG.Proof.Bignum.X86_64.Ws × Nat) (t : State) : Prop :=
  VG.Proof.Bignum.X86_64.FW b p.1 p.2 t ∧ t.gpr .rax = VG.Proof.Bignum.X86_64.off p.1.B (VG.Proof.Bignum.X86_64.slot p.1.w a) - VG.Proof.Bignum.X86_64.off p.1.B (VG.Proof.Bignum.X86_64.slot p.1.w aAcc + 16)

theorem pins_fr (a b : Nat) : VG.Proof.Bignum.X86_64.Pins (VG.Proof.Bignum.X86_64.FR a b) [.rdi, .r8, .r9, .r10, .rbx, .rax] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · exact h₁.1.pins h₂.1 r (by simp [h])
  · subst h; rw [h₁.2, h₂.2]

/-- After `finishBases`: the registers of `subMod` and `selectAcc`. -/
def FF (o : Nat) (L : VG.Proof.Bignum.X86_64.Ws) (t : State) : Prop :=
  t.gpr .r12 = BitVec.ofNat 64 L.w ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aTmp) ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aAcc) ∧
  t.gpr .rbx = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w o) ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off L.B (VG.Proof.Bignum.X86_64.slot L.w aN)

theorem pins_ff (o : Nat) : VG.Proof.Bignum.X86_64.Pins (VG.Proof.Bignum.X86_64.FF o) [.r12, .r8, .rsi, .rbx, .r10] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

theorem SizeOk.lt {w : Nat} (h : VG.Proof.Bignum.X86_64.SizeOk w) : w < 2 ^ 31 := by unfold VG.Proof.Bignum.X86_64.SizeOk at h; omega

/-- A row keeps the bases and the header, and moves the window. -/
theorem row_fw {a b : Nat} (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc)
    (hb2 : b ≠ aTmp) (L : VG.Proof.Bignum.X86_64.Ws) (j : Nat) (s : State) (hj : j < L.w) (h : VG.Proof.Bignum.X86_64.FW b L j s) :
    WP isa (VG.Impl.Bignum.X86_64.Adx.row a) s fun s' => isa.eval .ne s' = some (decide (j + 1 < L.w)) ∧
      (j + 1 < L.w → VG.Proof.Bignum.X86_64.FW b L (j + 1) s') ∧ (j + 1 = L.w → VG.Proof.Bignum.X86_64.FW b L L.w s') := by
  obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  have hn := hg.scr.nowrap
  have hg0 : hdrBytes ≤ VG.Proof.Bignum.X86_64.slot L.w aAcc := by unfold VG.Proof.Bignum.X86_64.slot; omega
  refine WP.mono (VG.Proof.Bignum.X86_64.row_ok hg.scr hg.rdi hg.hdr hZ ha hb ha1 ha2 hb1 hb2 rfl hj hsz.1 hsz.2.1
    (by have := hsz.lt; omega) h8 h9 h10 hbx) fun s' ⟨_, ho, h8', hz, k⟩ => ?_
  have hg' : VG.Proof.Bignum.X86_64.GoodW L s' := ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.of_outside ho (by omega)⟩, hZ⟩
  have hfw : VG.Proof.Bignum.X86_64.FW b L (j + 1) s' := ⟨hg', hsz, by rw [h8', show VG.Proof.Bignum.X86_64.slot L.w aAcc + 16 + 8 * j + 8 = VG.Proof.Bignum.X86_64.slot L.w aAcc + 16 + 8 * (j + 1) by omega], (k.gpr (by decide)).trans h9,
    (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans hbx⟩
  refine ⟨?_, fun _ => hfw, fun he => he ▸ hfw⟩
  simp only [VG.X86_64.eval, hz, Option.map_some]
  congr 1
  by_cases he : j + 1 = L.w
  · simp [he]
  · simp [he]; omega

/-- The fused multiplication is constant time, given that the taint analysis
checks its header loads from `rdi`. -/
theorem fused_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Bignum.X86_64.Adx.setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two fun L s => VG.Proof.Bignum.X86_64.GoodW L s ∧ VG.Proof.Bignum.X86_64.SizeOk L.w) (fused o a b) fun _ _ => True := by
  unfold fused
  -- The bases.
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := fun L s => VG.Proof.Bignum.X86_64.FW b L 0 s) [.rdi]
    (fun L s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_goodW L s₁ s₂ h₁.1 h₂.1) hS fun L s ⟨⟨mi, hg, hZ⟩, hsz⟩ =>
      WP.mono (VG.Proof.Bignum.X86_64.adxSetup_ok hg.scr hg.rdi hg.hdr hZ hb) fun t ⟨h9, h10, h8, hbx, hm, k⟩ =>
        ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz, h8, h9, h10, hbx⟩) ?_
  -- The windows := 0.
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := fun L s => 0 < L.w ∧ VG.Proof.Bignum.X86_64.FW b L 0 s) [.rdi, .r8, .r9, .r10, .rbx]
    (fun L s₁ s₂ h₁ h₂ => h₁.pins h₂) (by taint_decide) fun L s h => ?_) ?_
  · obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    have hn := hg.scr.nowrap
    refine WP.mono (VG.Proof.Bignum.X86_64.zeroWin_ok (A := VG.Proof.Bignum.X86_64.slot L.w aAcc + 16) hg.scr (by rw [h8, Nat.mul_zero, Nat.add_zero]) hbx (by have := hsz.lt; omega)
      (by unfold VG.Proof.Bignum.X86_64.slot aAcc at *; omega)) fun t ⟨_, ho', k⟩ => ⟨by have := hsz.2.1; omega, ⟨mi, ⟨hg.scr.congr k.2.2,
        (k.gpr (by decide)).trans hg.rdi, hg.hdr.of_outside ho' (by unfold VG.Proof.Bignum.X86_64.slot hdrBytes; omega)⟩, hZ⟩, hsz,
      (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
      (k.gpr (by decide)).trans hbx⟩
  -- The rows.
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_loop (fun L => L.w) (Φ := fun L j s => VG.Proof.Bignum.X86_64.FW b L j s) (Ψ := fun L s => VG.Proof.Bignum.X86_64.FW b L L.w s) ?_
    (VG.Proof.Bignum.X86_64.row_fw ha hb ha1 ha2 hb1 hb2)) ?_
  · unfold VG.Impl.Bignum.X86_64.Adx.row
    refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := VG.Proof.Bignum.X86_64.FR a b) [.rdi] (fun p s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_goodW p.1 s₁ s₂ h₁.2.1 h₂.2.1)
      hR fun p s ⟨_, h⟩ => ?_) (VG.Proof.Bignum.X86_64.two_taint _ (VG.Proof.Bignum.X86_64.pins_fr a b) (by taint_decide))
    obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
    exact WP.mono (VG.Proof.Bignum.X86_64.rowBase_ok hg.scr hg.rdi hg.hdr hZ ha) fun t ⟨hax, hm, k⟩ =>
      ⟨⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hsz,
        (k.gpr (by decide)).trans h8, (k.gpr (by decide)).trans h9, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans hbx⟩, hax⟩
  -- `T - m`, and the selection.
  unfold VG.Impl.Bignum.X86_64.Adx.finish
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := VG.Proof.Bignum.X86_64.FF o) [.rdi] (fun L s₁ s₂ h₁ h₂ => VG.Proof.Bignum.X86_64.pins_goodW L s₁ s₂ h₁.1 h₂.1) hF
    fun L s h => ?_) (VG.Proof.Bignum.X86_64.two_taint _ (VG.Proof.Bignum.X86_64.pins_ff o) (by taint_decide))
  obtain ⟨⟨mi, hg, hZ⟩, hsz, h8, h9, h10, hbx⟩ := h
  exact WP.mono (VG.Proof.Bignum.X86_64.finishBases_ok hg.scr hg.rdi hg.hdr hZ ho) fun t ⟨h12, h8', hsi, hbx', _, k⟩ =>
    ⟨h12, h8', hsi, hbx', (k.gpr (by decide)).trans h10⟩

/-- `montMulAdx` is constant time, given that the taint analysis checks its
header loads from `rdi` (and `montMul`'s). -/
theorem montMulAdx_ct {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    {hc₀ hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hM : (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc₀).isSome = true)
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (VG.Impl.Bignum.X86_64.Adx.setup b)) hc₁).isSome = true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (rowBase a)) hc₂).isSome = true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (finishBases o)) hc₃).isSome = true) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two VG.Proof.Bignum.X86_64.GoodW) (montMulAdx o a b) fun _ _ => True := by
  unfold montMulAdx
  refine RelCT.seq (VG.Proof.Bignum.X86_64.two_piece (Ψ := fun L s => VG.Proof.Bignum.X86_64.GoodW L s ∧ s.zf = some (decide (VG.Proof.Bignum.X86_64.SizeOk L.w))) [.rdi] VG.Proof.Bignum.X86_64.pins_goodW
    (by taint_decide) fun L s ⟨mi, hg, hZ⟩ => WP.mono (VG.Proof.Bignum.X86_64.sizeTest_ok hg.scr hg.rdi hg.hdr hZ) fun t ⟨hz, hm, k⟩ =>
      ⟨⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, hm ▸ hg.hdr⟩, hZ⟩, hz⟩) ?_
  refine VG.Proof.Bignum.X86_64.two_ite (fun L s₁ s₂ h₁ h₂ => by simp only [VG.X86_64.eval, h₁.2, h₂.2]) ?_ ?_
  · refine VG.Proof.Bignum.X86_64.two_map id (fun L s ⟨⟨hg, hz⟩, he⟩ => ⟨hg, ?_⟩) (VG.Proof.Bignum.X86_64.fused_ct ho ha hb ha1 ha2 hb1 hb2 hS hR hF)
    simp only [VG.X86_64.eval, hz, Option.some.injEq, decide_eq_true_eq] at he
    exact he
  · exact VG.Proof.Bignum.X86_64.two_map id (fun L s h => h.1.1) (VG.Proof.Bignum.X86_64.montMul_ctW (by decide) (by decide) (by decide) ho ha hb hM)

/-- Montgomery multiplication with BMI2 and ADX (`montMulAdx`), for RSA. -/
def Mont.adx : VG.Proof.Bignum.X86_64.Mont where
  mm := montMulAdx
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d4 d5 d6 hinv hB :=
    WP.mono (VG.Proof.Bignum.X86_64.montMulAdx_ok hg.scr hg.rdi hg.hdr hZ hw hw' ho ha hb d1 d2 d3 d4 d5 d6 hinv hB)
      fun t' ⟨h1, h2, h3, k⟩ => ⟨⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, h3.hdr hg.hdr⟩,
        h1, h2, h3, k⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact VG.Proof.Bignum.X86_64.montMulAdx_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmSym`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: straight-line vector code, lane by lane

A step of the almost Montgomery multiplication (`CrtIfma.ammStep`) computes
on the quadwords (lanes) of `ymm` registers, from 32-byte memory operands
and a quadword loaded into `rax`, all at constant offsets from the
general-purpose registers `r8`, `r9` and `r10`, which it does not change.
`Sym.run` computes each quadword after such a block as a term (`A`) in the
quadwords, general-purpose registers and memory before it; `run_ok` proves
the machine agrees. The quadword lemmas of the instructions are those of
Poly1305 and X25519 (`Proof/Poly1305/X86_64/Avx2/Sym.lean`,
`Proof/X25519/X86_64/Ifma/Sym.lean`), and `qw_madd52m` that of the memory
form of `vpmadd52luq` and `vpmadd52huq`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj qw qword_paddq qword_psrlq pick2 sel4 sel4_lt
  qw_setV256 qw_lane lane_sel qw_vbin qw_vshift qw_vpblendd qw_vpbroadcastq qw_vmovq qw_vpermq hv_of
  mod2_lt qword256_eq)
open VG.Proof.X25519.X86_64.Ifma (mad52 qword_madd52)

/-! ## Quadwords of the memory form of `vpmadd52luq` and `vpmadd52huq` -/

theorem qw_madd52m (h : Bool) (s : VG.X86_64.State) (d a r : XReg) (v : BitVec 256) {k : Nat} (hk : k < 4) :
    qw (s.setV .l256 d (madd52 h (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128))
        (madd52 h (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128))) r k =
      if r = d then mad52 h (qw s d k) (qw s a k) (v.extractLsb' (64 * k) 64) else qw s r k := by
  rw [qw_setV256]
  split
  · have e : (if k / 2 = 0 then madd52 h (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128)
        else madd52 h (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128)) =
        madd52 h (s.lane d (k / 2)) (s.lane a (k / 2)) (v.extractLsb' (128 * (k / 2)) 128) := by
      rcases VG.X86_64.cases4 hk with rfl | rfl | rfl | rfl <;> rfl
    rw [e, qword_madd52 _ _ _ _ (mod2_lt k), qw_lane, qw_lane]
    congr 1
    rw [← qword256_eq, qword256]
  · rfl

/-! ## Terms -/

/-- A quadword of a general-purpose register, in terms of the start. -/
inductive G
  | gpr (r : Reg)
  /-- The quadword at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  deriving DecidableEq, Repr

/-- A quadword of a vector register, in terms of the start. -/
inductive A
  /-- Quadword `k` of the vector register numbered `r`. -/
  | reg (r : Nat)
  | zero
  /-- `g` in quadword 0, zero elsewhere. -/
  | lane0 (g : VG.Proof.Bignum.X86_64.AmmSym.G)
  /-- Quadword 0 of `a`, in every quadword. -/
  | bc (a : VG.Proof.Bignum.X86_64.AmmSym.A)
  /-- Quadword `k` of the 32 bytes at `b + d`. -/
  | ld (b : Reg) (d : Nat)
  /-- `vpmadd52luq`, `vpmadd52huq` (`h`). -/
  | mad (h : Bool) (c a b : VG.Proof.Bignum.X86_64.AmmSym.A)
  | add (a b : VG.Proof.Bignum.X86_64.AmmSym.A)
  | shr (a : VG.Proof.Bignum.X86_64.AmmSym.A) (n : Nat)
  | perm (a : VG.Proof.Bignum.X86_64.AmmSym.A) (o : Nat)
  | blend (a b : VG.Proof.Bignum.X86_64.AmmSym.A) (sel : Nat)
  deriving DecidableEq, Repr

def G.eval (s₀ : VG.X86_64.State) : VG.Proof.Bignum.X86_64.AmmSym.G → BitVec 64
  | .gpr r => s₀.gpr r
  | .ld b d => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64

def A.eval (s₀ : VG.X86_64.State) : VG.Proof.Bignum.X86_64.AmmSym.A → Nat → BitVec 64
  | .reg r, k => qw s₀ (xr r) k
  | .zero, _ => 0
  | .lane0 g, k => if k = 0 then g.eval s₀ else 0
  | .bc a, _ => a.eval s₀ 0
  | .ld b d, k => s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (d + 8 * k)) 64
  | .mad h c a b, k => mad52 h (c.eval s₀ k) (a.eval s₀ k) (b.eval s₀ k)
  | .add a b, k => a.eval s₀ k + b.eval s₀ k
  | .shr a n, k => a.eval s₀ k >>> n
  | .perm a o, k => a.eval s₀ (sel4 o k)
  | .blend a b sel, k => pick2 (a.eval s₀ k) (b.eval s₀ k) (sel.testBit (2 * k)) (sel.testBit (2 * k + 1))

/-! ## The machine -/

/-- The terms of the vector registers (by number) and of `rax`. -/
structure Sym where
  reg : Nat → VG.Proof.Bignum.X86_64.AmmSym.A
  rax : VG.Proof.Bignum.X86_64.AmmSym.G

def Sym.init : VG.Proof.Bignum.X86_64.AmmSym.Sym := ⟨.reg, .gpr .rax⟩

def Sym.set (σ : VG.Proof.Bignum.X86_64.AmmSym.Sym) (d : XReg) (t : VG.Proof.Bignum.X86_64.AmmSym.A) : VG.Proof.Bignum.X86_64.AmmSym.Sym := { σ with
                                                           reg := fun r => if r = xi d then t else σ.reg r }

/-- The base and offset of `[b + d]`. -/
def baseOff (m : MemOp) : Option (Reg × Nat) :=
  if m.index = none then
    match m.disp with
    | .ofNat n => some (m.base, n)
    | _ => none
  else none

def Sym.vop (σ : VG.Proof.Bignum.X86_64.AmmSym.Sym) : VOp → Option VG.Proof.Bignum.X86_64.AmmSym.Sym
  | .vbin .vpxor .l256 d a b => if a = b then some (σ.set d .zero) else none
  | .vbin .vpaddq .l256 d a b => some (σ.set d (.add (σ.reg (xi a)) (σ.reg (xi b))))
  | .vshift .psrlq .l256 d a n =>
    if n.toNat < 64 then some (σ.set d (.shr (σ.reg (xi a)) n.toNat)) else none
  | .vpblendd .l256 d a b sel => some (σ.set d (.blend (σ.reg (xi a)) (σ.reg (xi b)) sel.toNat))
  | .vpbroadcastq .l256 d a => some (σ.set d (.bc (σ.reg (xi a))))
  | .vmovq d r => if r = .rax then some (σ.set d (.lane0 σ.rax)) else none
  | .vpermq d a o => some (σ.set d (.perm (σ.reg (xi a)) o.toNat))
  | _ => none

/-- One instruction, with `lim b` the bytes readable from each base `b`
(which no instruction here changes, but `rax`). -/
def Sym.step (lim : Reg → Nat) (σ : VG.Proof.Bignum.X86_64.AmmSym.Sym) : Instr → Option VG.Proof.Bignum.X86_64.AmmSym.Sym
  | .vop o => σ.vop o
  | .mov .rax (.mem m) => (VG.Proof.Bignum.X86_64.AmmSym.baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 8 ≤ lim bo.1 then some { σ with rax := .ld bo.1 bo.2 } else none
  | .vpmadd52Load h d a m => (VG.Proof.Bignum.X86_64.AmmSym.baseOff m).bind fun bo =>
    if bo.1 ≠ .rax ∧ bo.2 + 32 ≤ lim bo.1 then
      some (σ.set d (.mad h (σ.reg (xi d)) (σ.reg (xi a)) (.ld bo.1 bo.2)))
    else none
  | _ => none

def Sym.run (lim : Reg → Nat) (σ : VG.Proof.Bignum.X86_64.AmmSym.Sym) : List Instr → Option VG.Proof.Bignum.X86_64.AmmSym.Sym
  | [] => some σ
  | i :: is => (σ.step lim i).bind fun σ' => σ'.run lim is

/-! ## The machine agrees -/

/-- `s₀` with the vector registers and `rax` of `s`. -/
def vr (s₀ s : VG.X86_64.State) : VG.X86_64.State :=
  { s₀ with xmm := s.xmm, ymmHi := s.ymmHi, zmmHi := s.zmmHi, gpr := fun r => if r = .rax then s.gpr .rax else s₀.gpr r }

/-- The terms `σ` hold in `s`, which differs from `s₀` only in its vector
registers and `rax`. -/
structure SRel (σ : VG.Proof.Bignum.X86_64.AmmSym.Sym) (s₀ s : VG.X86_64.State) : Prop where
  reg : ∀ r k, k < 4 → qw s r k = (σ.reg (xi r)).eval s₀ k
  rax : s.gpr .rax = σ.rax.eval s₀
  eq : VG.Proof.Bignum.X86_64.AmmSym.vr s₀ s = s

theorem SRel.gpr {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) {r : Reg} (hr : r ≠ .rax) : s.gpr r = s₀.gpr r := by
  rw [← h.eq]; simp only [VG.Proof.Bignum.X86_64.AmmSym.vr, hr, ite_false]
theorem SRel.mem {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) : s.mem = s₀.mem := by rw [← h.eq]; rfl
theorem SRel.rd {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) : s.rd = s₀.rd := by rw [← h.eq]; rfl
theorem SRel.wr {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) : s.wr = s₀.wr := by rw [← h.eq]; rfl
theorem SRel.mxcsr {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) : s.mxcsr = s₀.mxcsr := by rw [← h.eq]; rfl
theorem SRel.flags {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) :
    s.cf = s₀.cf ∧ s.zf = s₀.zf ∧ s.sf = s₀.sf ∧ s.of = s₀.of := by
  rw [← h.eq]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem vr_self (s : VG.X86_64.State) : VG.Proof.Bignum.X86_64.AmmSym.vr s s = s := by
  simp only [VG.Proof.Bignum.X86_64.AmmSym.vr]
  congr 1
  funext r
  split <;> simp_all

theorem SRel.init (s₀ : VG.X86_64.State) : VG.Proof.Bignum.X86_64.AmmSym.SRel Sym.init s₀ s₀ :=
  ⟨fun r k _ => by simp only [Sym.init, A.eval, xr_xi], rfl, VG.Proof.Bignum.X86_64.AmmSym.vr_self s₀⟩

theorem vr_vop {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.vr s₀ s = s) (o : VOp) : VG.Proof.Bignum.X86_64.AmmSym.vr s₀ (o.exec s) = o.exec s := by
  rw [← h]
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

theorem vr_setV {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.vr s₀ s = s) (len : VLen) (d : XReg) (lo hi : BitVec 128) :
    VG.Proof.Bignum.X86_64.AmmSym.vr s₀ (s.setV len d lo hi) = s.setV len d lo hi := by
  rw [← h]; rfl

theorem SRel.set {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s₀ s : VG.X86_64.State} (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) {d : XReg} {t : VG.Proof.Bignum.X86_64.AmmSym.A} {s' : VG.X86_64.State}
    (hv : ∀ r k, k < 4 → qw s' r k = if r = d then t.eval s₀ k else qw s r k)
    (he : VG.Proof.Bignum.X86_64.AmmSym.vr s₀ s' = s') (hg : s'.gpr .rax = s.gpr .rax) : VG.Proof.Bignum.X86_64.AmmSym.SRel (σ.set d t) s₀ s' := by
  refine ⟨fun r k hk => ?_, hg.trans h.rax, he⟩
  rw [hv r k hk]
  simp only [Sym.set, xi_inj]
  split
  · rfl
  · exact h.reg r k hk

/-- The bytes the code may load: `lim b` bytes from each base `b`. -/
def Ctx (lim : Reg → Nat) (s₀ : VG.X86_64.State) : Prop :=
  ∀ b d n, 0 < n → d + n ≤ lim b → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 d) n

theorem baseOff_ok {m : MemOp} {b : Reg} {o : Nat} (h : VG.Proof.Bignum.X86_64.AmmSym.baseOff m = some (b, o)) (s : VG.X86_64.State) :
    s.ea m = s.gpr b + BitVec.ofNat 64 o := by
  unfold VG.Proof.Bignum.X86_64.AmmSym.baseOff at h
  split at h
  · rename_i hi
    split at h
    · rename_i n hn
      cases h
      simp only [State.ea, hi, hn]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    · cases h
  · cases h

theorem sstep_ok {lim : Reg → Nat} {s₀ : VG.X86_64.State} (hc : VG.Proof.Bignum.X86_64.AmmSym.Ctx lim s₀) {σ σ' : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s : VG.X86_64.State}
    (h : VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s) {i : Instr} (e : σ.step lim i = some σ') :
    ∃ s', exec i s = some s' ∧ VG.Proof.Bignum.X86_64.AmmSym.SRel σ' s₀ s' := by
  have hR : ∀ a k, k < 4 → (σ.reg (xi a)).eval s₀ k = qw s a k := fun a k hk => (h.reg a k hk).symm
  unfold Sym.step at e
  split at e
  · rename_i o
    refine ⟨o.exec s, rfl, ?_⟩
    have he := VG.Proof.Bignum.X86_64.AmmSym.vr_vop h.eq o
    have hg : (o.exec s).gpr .rax = s.gpr .rax := by cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
    unfold Sym.vop at e
    split at e
    · rename_i d a b
      split at e
      · rename_i hab
        cases e
        subst hab
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hg
        rw [qw_vbin, ite_eq_left rfl]
        simp [VBinOp.sse, XBinOp.eval, qword, A.eval]
      · cases e
    · rename_i d a b
      cases e
      refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vbin, ite_eq_right hr])) he hg
      rw [qw_vbin, ite_eq_left rfl]
      simp only [VBinOp.sse, A.eval]
      rw [qword_paddq _ _ (mod2_lt k), qw_lane, qw_lane, hR a k hk, hR b k hk]
    · rename_i d a n
      split at e
      · rename_i hn
        cases e
        refine h.set (hv_of (fun k hk => ?_) (fun r hr k _ => by rw [qw_vshift, ite_eq_right hr])) he hg
        rw [qw_vshift, ite_eq_left rfl]
        simp only [A.eval]
        rw [qword_psrlq _ hn (mod2_lt k), qw_lane, hR a k hk]
      · cases e
    · rename_i d a b n
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval]; rw [hR a k hk, hR b k hk])
        (fun r hr k hk => by rw [qw_vpblendd _ _ _ _ _ _ hk, ite_eq_right hr])) he hg
    · rename_i d a
      cases e
      exact h.set (hv_of (fun k _ => by rw [qw_vpbroadcastq, ite_eq_left rfl]; exact (hR a 0 (by decide)).symm)
        (fun r hr k _ => by rw [qw_vpbroadcastq, ite_eq_right hr])) he hg
    · rename_i d g
      split at e
      · rename_i hgr
        cases e
        subst hgr
        exact h.set (hv_of (fun k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval, h.rax])
          (fun r hr k hk => by rw [qw_vmovq _ _ _ _ hk, ite_eq_right hr])) he hg
      · cases e
    · rename_i d a o
      cases e
      exact h.set (hv_of (fun k hk => by
          rw [qw_vpermq _ _ _ _ _ hk, ite_eq_left rfl]; simp only [A.eval]; rw [hR a _ (sel4_lt _ _)])
        (fun r hr k hk => by rw [qw_vpermq _ _ _ _ _ hk, ite_eq_right hr])) he hg
    · cases e
  · rename_i m
    obtain ⟨⟨b, d⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 d := by rw [VG.Proof.Bignum.X86_64.AmmSym.baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 d) 8 := by
      rw [h.rd, h.wr]; exact hc b d 8 (by decide) hlt.2
    refine ⟨s.setReg .rax (s.mem.readW (s₀.gpr b + BitVec.ofNat 64 d) 64), ?_, ?_⟩
    · simp only [exec, readSrc, State.load64, ea, hin, ite_true, Option.map_some]
    · refine ⟨fun r k hk => h.reg r k hk, ?_, ?_⟩
      · simp only [State.setReg, ite_true, G.eval, h.mem]
      · rw [← h.eq]; simp only [VG.Proof.Bignum.X86_64.AmmSym.vr, State.setReg]; congr 1; funext r; split <;> simp_all
  · rename_i hh d a m
    obtain ⟨⟨b, o⟩, hbo, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    case isFalse => cases e
    rename_i hlt
    cases e
    have ea : s.ea m = s₀.gpr b + BitVec.ofNat 64 o := by rw [VG.Proof.Bignum.X86_64.AmmSym.baseOff_ok hbo, h.gpr hlt.1]
    have hin : InRegions (s.rd ++ s.wr) (s₀.gpr b + BitVec.ofNat 64 o) 32 := by
      rw [h.rd, h.wr]; exact hc b o 32 (by decide) hlt.2
    let v := s.mem.readW (s₀.gpr b + BitVec.ofNat 64 o) 256
    refine ⟨s.setV .l256 d (madd52 hh (s.lane d 0) (s.lane a 0) (v.extractLsb' 0 128))
      (madd52 hh (s.lane d 1) (s.lane a 1) (v.extractLsb' 128 128)),
      by simp only [exec, ea, State.load256, hin, ite_true, Option.map_some, v], ?_⟩
    refine h.set (hv_of (fun k hk => ?_) (fun r hr k hk => by rw [VG.Proof.Bignum.X86_64.AmmSym.qw_madd52m _ _ _ _ _ _ hk, ite_eq_right hr]))
      (VG.Proof.Bignum.X86_64.AmmSym.vr_setV h.eq _ _ _ _) rfl
    rw [VG.Proof.Bignum.X86_64.AmmSym.qw_madd52m _ _ _ _ _ _ hk, ite_eq_left rfl]
    simp only [A.eval]
    rw [hR d k hk, hR a k hk]
    congr 1
    have r1 := readW_extract s.mem (s₀.gpr b + BitVec.ofNat 64 o) (w := 256) (k := 8 * k)
      (n := 8) (by omega)
    rw [show 64 * k = 8 * (8 * k) by omega, r1, h.mem, BitVec.add_assoc, ← BitVec.ofNat_add]
  · cases e

/-- A block of instructions. -/
theorem srun_ok {lim : Reg → Nat} {s₀ : VG.X86_64.State} (hc : VG.Proof.Bignum.X86_64.AmmSym.Ctx lim s₀) :
    ∀ (is : List Instr) {σ σ' : VG.Proof.Bignum.X86_64.AmmSym.Sym} {s : VG.X86_64.State}, VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀ s → σ.run lim is = some σ' →
      WP isa (.block is) s (VG.Proof.Bignum.X86_64.AmmSym.SRel σ' s₀)
  | [], _, _, _, h, e => by cases e; exact WP.block_nil h
  | i :: is, _, _, _, h, e => by
    simp only [Sym.run, Option.bind_eq_some_iff] at e
    obtain ⟨σ₁, e₁, e₂⟩ := e
    obtain ⟨s₁, hx, h₁⟩ := VG.Proof.Bignum.X86_64.AmmSym.sstep_ok hc h e₁
    exact WP.block_cons_iff.2 ⟨s₁, hx, VG.Proof.Bignum.X86_64.AmmSym.srun_ok hc is h₁ e₂⟩

/-- A block from its start. -/
theorem run_ok {lim : Reg → Nat} {s₀ : VG.X86_64.State} (hc : VG.Proof.Bignum.X86_64.AmmSym.Ctx lim s₀) {is : List Instr} {σ : VG.Proof.Bignum.X86_64.AmmSym.Sym}
    (e : Sym.init.run lim is = some σ) : WP isa (.block is) s₀ (VG.Proof.Bignum.X86_64.AmmSym.SRel σ s₀) :=
  VG.Proof.Bignum.X86_64.AmmSym.srun_ok hc is (SRel.init s₀) e

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmTerms`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the terms of a step

The terms `Sym.run` computes for step `i` of a block (`ammStep i`), written
for any `i` (`expReg`), and checked against the run for each `i < 5`
(`run_ammStep`).

For each prime `p` (0 or 1, at `D p` from each base): `bT` the limb of the
second operand, broadcast; `a1` the accumulator of role `k` plus the low
halves of `a b`; `a1h` plus, for `k ≥ 1`, the high halves of role `k - 1`
of `a b`; `uT` the factor `u`, broadcast; `a2` plus the low halves of
`u m`; `cT` the carry of role 0's lane 0, in lane 0; `nT` role `k` after the
shift (role `k + 1`, with the carry for role 0, and role 0's lanes shifted
down for role 4); `hT` plus the high halves of `u m` (and, for role 4, of
`a b`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma

/-- The bytes each base may be loaded from: the operands and the modulus' region. -/
def lim : Reg → Nat := fun b =>
  if b = .r8 then VG.Impl.Rsa.X86_64.CrtIfma.D + 160 else if b = .r9 then VG.Impl.Rsa.X86_64.CrtIfma.D + 136 else if b = .r10 then VG.Impl.Rsa.X86_64.CrtIfma.D + 192 else 0

/-- The register number of role `k` of prime `p` at step `i`. -/
def regOf (p k i : Nat) : Nat := 5 * p + (k + i) % 5

def bT (p i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A := .bc (.lane0 (.ld .r9 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * i)))
def a1T (p k i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A := .mad false (.reg (VG.Proof.Bignum.X86_64.AmmSym.regOf p k i)) (VG.Proof.Bignum.X86_64.AmmSym.bT p i) (.ld .r8 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * k))
/-- Role `k` plus the high halves of `a b` of role `k - 1` (for `k ≥ 1`). -/
def a1hT (p k i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A :=
  if k = 0 then VG.Proof.Bignum.X86_64.AmmSym.a1T p 0 i else .mad true (VG.Proof.Bignum.X86_64.AmmSym.a1T p k i) (VG.Proof.Bignum.X86_64.AmmSym.bT p i) (.ld .r8 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * (k - 1)))
def uT (p i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A := .bc (.mad false .zero (VG.Proof.Bignum.X86_64.AmmSym.a1T p 0 i) (.ld .r10 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oK0)))
def a2T (p k i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A := .mad false (VG.Proof.Bignum.X86_64.AmmSym.a1hT p k i) (VG.Proof.Bignum.X86_64.AmmSym.uT p i) (.ld .r10 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 32 * k))
def cT (p i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A := .blend (.reg 14) (.shr (VG.Proof.Bignum.X86_64.AmmSym.a2T p 0 i) 52) 3
def nT (p k i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A :=
  if k = 4 then .blend (.perm (VG.Proof.Bignum.X86_64.AmmSym.a2T p 0 i) 57) (.reg 14) 192
  else if k = 0 then .add (VG.Proof.Bignum.X86_64.AmmSym.a2T p 1 i) (VG.Proof.Bignum.X86_64.AmmSym.cT p i) else VG.Proof.Bignum.X86_64.AmmSym.a2T p (k + 1) i
def hT (p k i : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A :=
  if k = 4 then
    .mad true (.mad true (VG.Proof.Bignum.X86_64.AmmSym.nT p 4 i) (VG.Proof.Bignum.X86_64.AmmSym.bT p i) (.ld .r8 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 128))) (VG.Proof.Bignum.X86_64.AmmSym.uT p i) (.ld .r10 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 128))
  else .mad true (VG.Proof.Bignum.X86_64.AmmSym.nT p k i) (VG.Proof.Bignum.X86_64.AmmSym.uT p i) (.ld .r10 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 32 * k))

/-- The role at step `i + 1` of register `r % 5`. -/
def roleOf (r i : Nat) : Nat := (r % 5 + 5 - (i + 1) % 5) % 5

/-- The terms after step `i`. -/
def expReg (i r : Nat) : VG.Proof.Bignum.X86_64.AmmSym.A :=
  if r < 10 then VG.Proof.Bignum.X86_64.AmmSym.hT (r / 5) (VG.Proof.Bignum.X86_64.AmmSym.roleOf r i) i
  else if r = 10 then VG.Proof.Bignum.X86_64.AmmSym.bT 0 i else if r = 11 then VG.Proof.Bignum.X86_64.AmmSym.bT 1 i
  else if r = 12 then VG.Proof.Bignum.X86_64.AmmSym.uT 0 i else if r = 13 then VG.Proof.Bignum.X86_64.AmmSym.uT 1 i
  else if r = 15 then VG.Proof.Bignum.X86_64.AmmSym.cT 1 i else .reg r

/-- The run of step `i` gives `expReg i` in the 16 registers and loads `rax`. -/
def checkStep (i : Nat) : Bool :=
  match Sym.init.run VG.Proof.Bignum.X86_64.AmmSym.lim (ammStep i) with
  | some σ => (List.range 16).all (fun r => decide (σ.reg r = VG.Proof.Bignum.X86_64.AmmSym.expReg i r)) && decide (σ.rax = .ld .r9 (VG.Impl.Rsa.X86_64.CrtIfma.D + 32 * i))
  | none => false

theorem checkStep_ok : ∀ i < 5, VG.Proof.Bignum.X86_64.AmmSym.checkStep i = true := by decide +kernel

theorem run_ammStep {i : Nat} (hi : i < 5) :
    ∃ σ, Sym.init.run VG.Proof.Bignum.X86_64.AmmSym.lim (ammStep i) = some σ ∧ ∀ r < 16, σ.reg r = VG.Proof.Bignum.X86_64.AmmSym.expReg i r := by
  have h := VG.Proof.Bignum.X86_64.AmmSym.checkStep_ok i hi
  unfold VG.Proof.Bignum.X86_64.AmmSym.checkStep at h
  split at h
  · rename_i σ hσ
    refine ⟨σ, hσ, fun r hr => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h.1 r hr
  · cases h

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmLane`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the lanes of a step

The terms of step `i` (`AmmTerms.lean`) evaluated lane by lane: under
`StepIn` (the lanes of the roles hold the limbs `L p`, below `2⁶¹`; the
operands' limbs, `k₀` and the limb `b p` in memory, below `2⁵²`; register
14 zero), role `k`'s lane `t` after the step holds limb `k + 5 t` of
`Amm52.step` (`hT_eval`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw pick2 sel4)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)

theorem halves (x : BitVec 64) : x.extractLsb' 32 32 ++ x.extractLsb' 0 32 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 32
  · simp [h]
  · simp [h, show j - 32 < 32 by omega, show 32 + (j - 32) = j by omega]

theorem pick2_tt (a b : BitVec 64) : pick2 a b true true = b := by
  simp only [pick2, ite_true, VG.Proof.Bignum.X86_64.AmmSym.halves]

theorem pick2_ff (a b : BitVec 64) : pick2 a b false false = a := by
  simp only [pick2, Bool.false_eq_true, ite_false, VG.Proof.Bignum.X86_64.AmmSym.halves]

/-- The machine before step `i`, for limbs `L p`, operand limbs `a p`,
modulus limbs `m p`, `k₀` `k p` and second-operand limb `b p`. -/
structure StepIn (s : VG.X86_64.State) (i : Nat) (L a m : Nat → Nat → Nat) (k b : Nat → Nat) : Prop where
  z : ∀ t < 4, qw s .xmm14 t = 0
  lanes : ∀ p < 2, ∀ kk < 5, ∀ t < 4, qw s (xr (VG.Proof.Bignum.X86_64.AmmSym.regOf p kk i)) t = BitVec.ofNat 64 (L p (kk + 5 * t))
  lt : ∀ p < 2, ∀ j < 20, L p j < 2 ^ 61
  ina : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + 5 * t))
  inm : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + 5 * t))
  ink : ∀ p < 2, ∀ t < 4, s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * i)) 64 = BitVec.ofNat 64 (b p)
  alt : ∀ p < 2, ∀ j < 20, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < 20, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, b p < 2 ^ 52

/-- The operands of prime `p`. -/
def ops (a m : Nat → Nat → Nat) (k : Nat → Nat) (p : Nat) : Ops := ⟨a p, m p, k p⟩

theorem lo_comm (x y : Nat) : VG.Proof.Bignum.Amm52.lo x y = VG.Proof.Bignum.Amm52.lo y x := by unfold VG.Proof.Bignum.Amm52.lo; rw [Nat.mul_comm]
theorem hi_comm (x y : Nat) : VG.Proof.Bignum.Amm52.hi x y = VG.Proof.Bignum.Amm52.hi y x := by unfold VG.Proof.Bignum.Amm52.hi; rw [Nat.mul_comm]

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mad_lo {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 false (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + VG.Proof.Bignum.Amm52.lo y x) := by
  apply BitVec.eq_of_toNat_eq
  have := lo_lt y x
  rw [mad52_toNat]
  simp only [Bool.false_eq_true, ite_false, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) % 2 ^ 52 = VG.Proof.Bignum.Amm52.lo y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + VG.Proof.Bignum.Amm52.lo y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + VG.Proof.Bignum.Amm52.lo y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

theorem mad_hi {c x y : Nat} (hc : c + 2 ^ 52 < 2 ^ 64) :
    mad52 true (BitVec.ofNat 64 c) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      BitVec.ofNat 64 (c + VG.Proof.Bignum.Amm52.hi y x) := by
  apply BitVec.eq_of_toNat_eq
  have := hi_lt y x
  rw [mad52_toNat]
  simp only [ite_true, BitVec.toNat_ofNat]
  have e : ∀ v : Nat, v % 2 ^ 64 % 2 ^ 52 = v % 2 ^ 52 := fun v => Nat.mod_mod_of_dvd _ (by decide)
  rw [e, e, Nat.mul_comm, show y % 2 ^ 52 * (x % 2 ^ 52) / 2 ^ 52 = VG.Proof.Bignum.Amm52.hi y x from rfl]
  rw [Nat.mod_eq_of_lt (show c % 2 ^ 64 + VG.Proof.Bignum.Amm52.hi y x < 2 ^ 64 by
    have := Nat.mod_le c (2 ^ 64); omega), Nat.mod_eq_of_lt (show c + VG.Proof.Bignum.Amm52.hi y x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]

section
variable {s : VG.X86_64.State} {i : Nat} {L a m : Nat → Nat → Nat} {k b : Nat → Nat}

theorem bT_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p : Nat} (hp : p < 2) (t : Nat) :
    (VG.Proof.Bignum.X86_64.AmmSym.bT p i).eval s t = BitVec.ofNat 64 (b p) := by
  simp only [VG.Proof.Bignum.X86_64.AmmSym.bT, A.eval, ite_true, G.eval]; exact h.inb p hp

theorem ld_a (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (A.ld .r8 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * kk)).eval s t = BitVec.ofNat 64 (a p (kk + 5 * t)) := by
  simp only [A.eval]; exact h.ina p hp kk hk t ht

theorem ld_m (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (A.ld .r10 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 32 * kk)).eval s t = BitVec.ofNat 64 (m p (kk + 5 * t)) := by
  simp only [A.eval]; exact h.inm p hp kk hk t ht

theorem a1T_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.a1T p kk i).eval s t = BitVec.ofNat 64 (L p (kk + 5 * t) + VG.Proof.Bignum.Amm52.lo (a p (kk + 5 * t)) (b p)) := by
  have hl := h.lt p hp (kk + 5 * t) (by omega)
  simp only [VG.Proof.Bignum.X86_64.AmmSym.a1T, A.eval]
  rw [h.lanes p hp kk hk t ht, VG.Proof.Bignum.X86_64.AmmSym.bT_eval h hp, h.ina p hp kk hk t ht, VG.Proof.Bignum.X86_64.AmmSym.mad_lo (by omega)]

theorem uT_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p : Nat} (hp : p < 2) (t : Nat) :
    (VG.Proof.Bignum.X86_64.AmmSym.uT p i).eval s t = BitVec.ofNat 64 (stepU (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p)) := by
  have hl := h.lt p hp 0 (by decide)
  have := lo_lt (a p 0) (b p)
  simp only [VG.Proof.Bignum.X86_64.AmmSym.uT, A.eval]
  rw [VG.Proof.Bignum.X86_64.AmmSym.a1T_eval h hp (by decide) (by decide), show (0 : Nat) + 5 * 0 = 0 from rfl,
    h.ink p hp 0 (by decide),
    show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, VG.Proof.Bignum.X86_64.AmmSym.mad_lo (by omega), Nat.zero_add, VG.Proof.Bignum.X86_64.AmmSym.lo_comm]
  rfl

theorem a2T_eval0 (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p t : Nat} (hp : p < 2) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.a2T p 0 i).eval s t = BitVec.ofNat 64 (low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) (0 + 5 * t)) := by
  have hl := h.lt p hp (0 + 5 * t) (by omega)
  have := lo_lt (a p (0 + 5 * t)) (b p)
  simp only [VG.Proof.Bignum.X86_64.AmmSym.a2T, VG.Proof.Bignum.X86_64.AmmSym.a1hT, ite_true, A.eval]
  rw [VG.Proof.Bignum.X86_64.AmmSym.a1T_eval h hp (by decide) ht, VG.Proof.Bignum.X86_64.AmmSym.uT_eval h hp, h.inm p hp 0 (by decide) t ht, VG.Proof.Bignum.X86_64.AmmSym.mad_lo (by omega)]
  simp only [low, VG.Proof.Bignum.X86_64.AmmSym.ops]

/-- Role `kk + 1` after the low halves: plus the high halves of role `kk` of `a b`. -/
theorem a2T_evalS (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk + 1 < 5) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.a2T p (kk + 1) i).eval s t =
      BitVec.ofNat 64 (low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) (kk + 1 + 5 * t) + VG.Proof.Bignum.Amm52.hi (a p (kk + 5 * t)) (b p)) := by
  have hl := h.lt p hp (kk + 1 + 5 * t) (by omega)
  have := lo_lt (a p (kk + 1 + 5 * t)) (b p)
  have := hi_lt (a p (kk + 5 * t)) (b p)
  have := lo_lt (m p (kk + 1 + 5 * t)) (stepU (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p))
  simp only [VG.Proof.Bignum.X86_64.AmmSym.a2T, VG.Proof.Bignum.X86_64.AmmSym.a1hT, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, A.eval]
  rw [VG.Proof.Bignum.X86_64.AmmSym.a1T_eval h hp hk ht, VG.Proof.Bignum.X86_64.AmmSym.bT_eval h hp, h.ina p hp kk (by omega) t ht, VG.Proof.Bignum.X86_64.AmmSym.mad_hi (by omega), VG.Proof.Bignum.X86_64.AmmSym.uT_eval h hp,
    h.inm p hp (kk + 1) hk t ht, VG.Proof.Bignum.X86_64.AmmSym.mad_lo (by omega)]
  exact congrArg (BitVec.ofNat 64) (by simp only [low, VG.Proof.Bignum.X86_64.AmmSym.ops]; omega)

theorem low_lt (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p j : Nat} (hp : p < 2) (hj : j < 20) :
    low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) j < 2 ^ 61 + 2 ^ 53 := by
  have := h.lt p hp j hj
  have := lo_lt (a p j) (b p)
  have := lo_lt (m p j) (stepU (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p))
  show L p j + VG.Proof.Bignum.Amm52.lo (a p j) (b p) + VG.Proof.Bignum.Amm52.lo (m p j) (stepU (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p)) < _
  omega

theorem shr_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 52 = BitVec.ofNat 64 (x / 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem add_ofNat {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]

theorem cT_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p t : Nat} (hp : p < 2) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.cT p i).eval s t =
      BitVec.ofNat 64 (if t = 0 then low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) 0 / 2 ^ 52 else 0) := by
  have h0 := VG.Proof.Bignum.X86_64.AmmSym.low_lt h hp (j := 0) (by decide)
  simp only [VG.Proof.Bignum.X86_64.AmmSym.cT, A.eval]
  rw [show (VG.Proof.Poly1305.X86_64.Avx2.xr 14) = .xmm14 from rfl, h.z t ht]
  rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl
  · rw [VG.Proof.Bignum.X86_64.AmmSym.a2T_eval0 h hp (by decide), show (0 : Nat) + 5 * 0 = 0 from rfl, VG.Proof.Bignum.X86_64.AmmSym.shr_ofNat (by omega),
      show Nat.testBit 3 (2 * 0) = true by decide, show Nat.testBit 3 (2 * 0 + 1) = true by decide, VG.Proof.Bignum.X86_64.AmmSym.pick2_tt]
    rfl
  · rw [show Nat.testBit 3 (2 * 1) = false by decide, show Nat.testBit 3 (2 * 1 + 1) = false by decide, VG.Proof.Bignum.X86_64.AmmSym.pick2_ff]
    rfl
  · rw [show Nat.testBit 3 (2 * 2) = false by decide, show Nat.testBit 3 (2 * 2 + 1) = false by decide, VG.Proof.Bignum.X86_64.AmmSym.pick2_ff]
    rfl
  · rw [show Nat.testBit 3 (2 * 3) = false by decide, show Nat.testBit 3 (2 * 3 + 1) = false by decide, VG.Proof.Bignum.X86_64.AmmSym.pick2_ff]
    rfl

/-- Role `kk` after the shift: for `kk < 4`, with the high halves of role `kk` of `a b`. -/
theorem nT_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.nT p kk i).eval s t = BitVec.ofNat 64 (shifted (low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p)) (kk + 5 * t) +
      if kk = 4 then 0 else VG.Proof.Bignum.Amm52.hi (a p (kk + 5 * t)) (b p)) := by
  by_cases h4 : kk = 4
  · subst h4
    simp only [VG.Proof.Bignum.X86_64.AmmSym.nT, ite_true, A.eval, Nat.add_zero]
    rw [show (VG.Proof.Poly1305.X86_64.Avx2.xr 14) = .xmm14 from rfl, h.z t ht]
    rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl
    · rw [show Nat.testBit 192 (2 * 0) = false by decide, show Nat.testBit 192 (2 * 0 + 1) = false by decide,
        VG.Proof.Bignum.X86_64.AmmSym.pick2_ff, show sel4 57 0 = 1 from rfl, VG.Proof.Bignum.X86_64.AmmSym.a2T_eval0 h hp (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 1) = false by decide, show Nat.testBit 192 (2 * 1 + 1) = false by decide,
        VG.Proof.Bignum.X86_64.AmmSym.pick2_ff, show sel4 57 1 = 2 from rfl, VG.Proof.Bignum.X86_64.AmmSym.a2T_eval0 h hp (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 2) = false by decide, show Nat.testBit 192 (2 * 2 + 1) = false by decide,
        VG.Proof.Bignum.X86_64.AmmSym.pick2_ff, show sel4 57 2 = 3 from rfl, VG.Proof.Bignum.X86_64.AmmSym.a2T_eval0 h hp (by decide)]; rfl
    · rw [show Nat.testBit 192 (2 * 3) = true by decide, show Nat.testBit 192 (2 * 3 + 1) = true by decide,
        VG.Proof.Bignum.X86_64.AmmSym.pick2_tt]; rfl
  · simp only [VG.Proof.Bignum.X86_64.AmmSym.nT, h4, ite_false]
    by_cases h0 : kk = 0
    · subst h0
      simp only [ite_true]
      simp only [A.eval]
      rw [VG.Proof.Bignum.X86_64.AmmSym.a2T_evalS (kk := 0) h hp (by decide) ht, VG.Proof.Bignum.X86_64.AmmSym.cT_eval h hp ht]
      have h1 := VG.Proof.Bignum.X86_64.AmmSym.low_lt h hp (j := 0 + 1 + 5 * t) (by omega)
      have h2 := VG.Proof.Bignum.X86_64.AmmSym.low_lt h hp (j := 0) (by decide)
      have := hi_lt (a p (0 + 5 * t)) (b p)
      have hc : low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) 0 / 2 ^ 52 < 2 ^ 10 := Nat.div_lt_of_lt_mul (by omega)
      rw [VG.Proof.Bignum.X86_64.AmmSym.add_ofNat (by split <;> omega)]
      simp only [shifted, show 0 + 5 * t < 19 by omega, ite_true, show 0 + 5 * t + 1 = 0 + 1 + 5 * t by omega]
      refine congrArg (BitVec.ofNat 64) ?_
      rcases VG.X86_64.cases4 ht with rfl | rfl | rfl | rfl <;> simp <;> omega
    · simp only [h0, ite_false]
      obtain ⟨kk', rfl⟩ : ∃ kk', kk = kk' + 1 := ⟨kk - 1, by omega⟩
      rw [show kk' + 1 + 1 = (kk' + 1) + 1 from rfl, VG.Proof.Bignum.X86_64.AmmSym.a2T_evalS h hp (by omega) ht]
      simp only [shifted, show kk' + 1 + 5 * t < 19 by omega, ite_true,
        show kk' + 1 + 1 + 5 * t = kk' + 1 + 5 * t + 1 by omega, show kk' + 1 + 5 * t ≠ 0 by omega, ite_false,
        Nat.add_zero]

theorem hT_eval (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) {p kk t : Nat} (hp : p < 2) (hk : kk < 5) (ht : t < 4) :
    (VG.Proof.Bignum.X86_64.AmmSym.hT p kk i).eval s t = BitVec.ofNat 64 (VG.Proof.Bignum.Amm52.step (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) (kk + 5 * t)) := by
  have hs : shifted (low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p)) (kk + 5 * t) < 2 ^ 61 + 2 ^ 54 := by
    unfold shifted
    split
    · have := VG.Proof.Bignum.X86_64.AmmSym.low_lt h hp (j := kk + 5 * t + 1) (by omega)
      have := VG.Proof.Bignum.X86_64.AmmSym.low_lt h hp (j := 0) (by decide)
      have := Nat.div_le_self (low (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) 0) (2 ^ 52)
      split <;> omega
    · omega
  have := hi_lt (a p (kk + 5 * t)) (b p)
  have := hi_lt (m p (kk + 5 * t)) (stepU (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p))
  by_cases h4 : kk = 4
  · subst h4
    simp only [VG.Proof.Bignum.X86_64.AmmSym.hT, ite_true, A.eval]
    have ha : s.mem.readW (s.gpr .r8 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 128 + 8 * t)) 64 =
        BitVec.ofNat 64 (a p (4 + 5 * t)) := h.ina p hp 4 hk t ht
    have hm : s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 128 + 8 * t)) 64 =
        BitVec.ofNat 64 (m p (4 + 5 * t)) := h.inm p hp 4 hk t ht
    rw [VG.Proof.Bignum.X86_64.AmmSym.nT_eval h hp hk ht]
    simp only [↓reduceIte, Nat.add_zero]
    rw [VG.Proof.Bignum.X86_64.AmmSym.bT_eval h hp, ha, VG.Proof.Bignum.X86_64.AmmSym.mad_hi (by omega), VG.Proof.Bignum.X86_64.AmmSym.uT_eval h hp, hm, VG.Proof.Bignum.X86_64.AmmSym.mad_hi (by omega)]
    rfl
  · simp only [VG.Proof.Bignum.X86_64.AmmSym.hT, h4, ite_false, A.eval]
    rw [VG.Proof.Bignum.X86_64.AmmSym.nT_eval h hp hk ht]
    simp only [h4, ite_false]
    rw [VG.Proof.Bignum.X86_64.AmmSym.uT_eval h hp, h.inm p hp kk hk t ht, VG.Proof.Bignum.X86_64.AmmSym.mad_hi (by omega)]
    rfl

end

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmBlock`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: a step on the machine

`ammStep_ok`: from a state with `StepIn`, the code of step `i` leaves in
role `k`'s lanes at step `i + 1` the limbs of `Amm52.step`, register 14
still zero, and changes nothing but the vector registers and `rax`.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 ammStep)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem xi_xr : ∀ r < 16, xi (xr r) = r := by decide

theorem regOf_lt {p k i : Nat} (hp : p < 2) : VG.Proof.Bignum.X86_64.AmmSym.regOf p k i < 10 := by unfold VG.Proof.Bignum.X86_64.AmmSym.regOf; omega

theorem expReg_regOf {p kk i : Nat} (hp : p < 2) (hk : kk < 5) :
    VG.Proof.Bignum.X86_64.AmmSym.expReg i (VG.Proof.Bignum.X86_64.AmmSym.regOf p kk (i + 1)) = VG.Proof.Bignum.X86_64.AmmSym.hT p kk i := by
  have hr := VG.Proof.Bignum.X86_64.AmmSym.regOf_lt (k := kk) (i := i + 1) hp
  simp only [VG.Proof.Bignum.X86_64.AmmSym.expReg, hr, ite_true]
  congr 1
  · unfold VG.Proof.Bignum.X86_64.AmmSym.regOf; omega
  · unfold VG.Proof.Bignum.X86_64.AmmSym.roleOf VG.Proof.Bignum.X86_64.AmmSym.regOf; omega

/-- What a step keeps: everything but the vector registers and `rax`. -/
structure Keeps (s s' : VG.X86_64.State) : Prop where
  gpr : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of

theorem Keeps.trans {s₁ s₂ s₃ : VG.X86_64.State} (h₁ : VG.Proof.Bignum.X86_64.AmmSym.Keeps s₁ s₂) (h₂ : VG.Proof.Bignum.X86_64.AmmSym.Keeps s₂ s₃) : VG.Proof.Bignum.X86_64.AmmSym.Keeps s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₂.mxcsr.trans h₁.mxcsr,
    ⟨h₂.flags.1.trans h₁.flags.1, h₂.flags.2.1.trans h₁.flags.2.1, h₂.flags.2.2.1.trans h₁.flags.2.2.1,
      h₂.flags.2.2.2.trans h₁.flags.2.2.2⟩⟩

theorem ammStep_ok {s : VG.X86_64.State} {i : Nat} (hi : i < 5) {L a m : Nat → Nat → Nat} {k b : Nat → Nat}
    (h : VG.Proof.Bignum.X86_64.AmmSym.StepIn s i L a m k b) (hc : VG.Proof.Bignum.X86_64.AmmSym.Ctx VG.Proof.Bignum.X86_64.AmmSym.lim s) :
    WP isa (.block (ammStep i)) s fun s' =>
      (∀ p < 2, ∀ kk < 5, ∀ t < 4, qw s' (xr (VG.Proof.Bignum.X86_64.AmmSym.regOf p kk (i + 1))) t =
        BitVec.ofNat 64 (VG.Proof.Bignum.Amm52.step (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (L p) (b p) (kk + 5 * t))) ∧
      (∀ t < 4, qw s' .xmm14 t = 0) ∧ VG.Proof.Bignum.X86_64.AmmSym.Keeps s s' := by
  obtain ⟨σ, e, hσ⟩ := VG.Proof.Bignum.X86_64.AmmSym.run_ammStep hi
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.run_ok hc e) fun s' hs => ⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_⟩
  · have hr := VG.Proof.Bignum.X86_64.AmmSym.regOf_lt (k := kk) (i := i + 1) hp
    rw [hs.reg _ t ht, VG.Proof.Bignum.X86_64.AmmSym.xi_xr _ (by omega), hσ _ (by omega), VG.Proof.Bignum.X86_64.AmmSym.expReg_regOf hp hk]
    exact VG.Proof.Bignum.X86_64.AmmSym.hT_eval h hp hk ht
  · rw [hs.reg _ t ht, show xi .xmm14 = 14 from rfl, hσ 14 (by decide)]
    simp only [VG.Proof.Bignum.X86_64.AmmSym.expReg, show ¬ (14 : Nat) < 10 by decide, ite_false, show (14 : Nat) ≠ 10 by decide,
      show (14 : Nat) ≠ 11 by decide, show (14 : Nat) ≠ 12 by decide, show (14 : Nat) ≠ 13 by decide,
      show (14 : Nat) ≠ 15 by decide, A.eval]
    exact h.z t ht
  · exact ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩

/-! ## The steps of a block -/

/-- What the multiplication reads, from the state `s₀` where it starts: the
operand `a` at `r8`, the modulus and `k₀` at `r10`, the second operand `bl`
at `r9` (each prime's at `D` further), all readable. -/
structure Env (s₀ : VG.X86_64.State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) : Prop where
  ina : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r8 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * kk + 8 * t)) 64 = BitVec.ofNat 64 (a p (kk + 5 * t))
  inm : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM + 32 * kk + 8 * t)) 64 =
      BitVec.ofNat 64 (m p (kk + 5 * t))
  ink : ∀ p < 2, ∀ t < 4, s₀.mem.readW (s₀.gpr .r10 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oK0 + 8 * t)) 64 = BitVec.ofNat 64 (k p)
  inb : ∀ p < 2, ∀ l < 20,
    s₀.mem.readW (s₀.gpr .r9 + BitVec.ofNat 64 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l)) 64 = BitVec.ofNat 64 (bl p l)
  alt : ∀ p < 2, ∀ j < 20, a p j < 2 ^ 52
  mlt : ∀ p < 2, ∀ j < 20, m p j < 2 ^ 52
  klt : ∀ p < 2, k p < 2 ^ 52
  blt : ∀ p < 2, ∀ l < 20, bl p l < 2 ^ 52
  rd8 : ∀ d n, 0 < n → d + n ≤ VG.Proof.Bignum.X86_64.AmmSym.lim .r8 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r8 + BitVec.ofNat 64 d) n
  rd9 : ∀ d n, 0 < n → d + n ≤ VG.Proof.Bignum.X86_64.AmmSym.lim .r9 + 24 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r9 + BitVec.ofNat 64 d) n
  rd10 : ∀ d n, 0 < n → d + n ≤ VG.Proof.Bignum.X86_64.AmmSym.lim .r10 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r10 + BitVec.ofNat 64 d) n

/-- The limbs of prime `p` after `n` steps. -/
def lm (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat) (p n : Nat) : Nat → Nat :=
  steps (VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (bl p) n fun _ => 0

theorem lm_lt {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat} {p n j : Nat} (hn : n ≤ 20)
    (hj : j < 20) : VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl p n j < 2 ^ 61 := by
  have := steps_lt (o := VG.Proof.Bignum.X86_64.AmmSym.ops a m k p) (b := bl p) (L := fun _ => 0) (fun _ _ => by decide) n hn j hj
  unfold VG.Proof.Bignum.X86_64.AmmSym.lm
  omega

/-- The machine within block `blk`, before step `i`: the lanes after
`5 blk + i` steps, `r9` at the block's limbs, register 14 zero. -/
structure InBlk (s₀ s : VG.X86_64.State) (a m : Nat → Nat → Nat) (k : Nat → Nat) (bl : Nat → Nat → Nat)
    (blk i : Nat) : Prop where
  lanes : ∀ p < 2, ∀ kk < 5, ∀ t < 4,
    qw s (xr (VG.Proof.Bignum.X86_64.AmmSym.regOf p kk i)) t = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl p (5 * blk + i) (kk + 5 * t))
  z : ∀ t < 4, qw s .xmm14 t = 0
  r8 : s.gpr .r8 = s₀.gpr .r8
  r9 : s.gpr .r9 = s₀.gpr .r9 + BitVec.ofNat 64 (8 * blk)
  r10 : s.gpr .r10 = s₀.gpr .r10
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem lim9 : VG.Proof.Bignum.X86_64.AmmSym.lim .r9 = VG.Impl.Rsa.X86_64.CrtIfma.D + 136 := rfl
theorem lim_other {b : Reg} (h8 : b ≠ .r8) (h9 : b ≠ .r9) (h10 : b ≠ .r10) : VG.Proof.Bignum.X86_64.AmmSym.lim b = 0 := by
  simp only [VG.Proof.Bignum.X86_64.AmmSym.lim, h8, h9, h10, ite_false]

theorem ofNat_add64 (x : BitVec 64) (c d : Nat) :
    x + BitVec.ofNat 64 c + BitVec.ofNat 64 d = x + BitVec.ofNat 64 (c + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem InBlk.stepIn {s₀ s : VG.X86_64.State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk i : Nat} (hb : blk < 4) (hi : i < 5) (e : VG.Proof.Bignum.X86_64.AmmSym.Env s₀ a m k bl) (h : VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s a m k bl blk i) :
    VG.Proof.Bignum.X86_64.AmmSym.StepIn s i (fun p => VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl p (5 * blk + i)) a m k (fun p => bl p (5 * blk + i)) ∧ VG.Proof.Bignum.X86_64.AmmSym.Ctx VG.Proof.Bignum.X86_64.AmmSym.lim s := by
  refine ⟨⟨h.z, h.lanes, fun p _ j hj => VG.Proof.Bignum.X86_64.AmmSym.lm_lt (by omega) hj, fun p hp kk hk t ht => ?_,
    fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp => ?_, e.alt, e.mlt, e.klt,
    fun p hp => e.blt p hp _ (by omega)⟩, ?_⟩
  · rw [h.mem, h.r8]; exact e.ina p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.inm p hp kk hk t ht
  · rw [h.mem, h.r10]; exact e.ink p hp t ht
  · rw [h.mem, h.r9, VG.Proof.Bignum.X86_64.AmmSym.ofNat_add64, ← e.inb p hp (5 * blk + i) (by omega)]
    congr 3
    unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega
  · intro b d n hn hdn
    rw [h.rd, h.wr]
    by_cases b8 : b = .r8
    · subst b8; rw [h.r8]; exact e.rd8 d n hn hdn
    by_cases b9 : b = .r9
    · subst b9; rw [h.r9, VG.Proof.Bignum.X86_64.AmmSym.ofNat_add64]; exact e.rd9 _ n hn (by rw [VG.Proof.Bignum.X86_64.AmmSym.lim9] at hdn ⊢; omega)
    by_cases b10 : b = .r10
    · subst b10; rw [h.r10]; exact e.rd10 d n hn hdn
    · rw [VG.Proof.Bignum.X86_64.AmmSym.lim_other b8 b9 b10] at hdn
      omega

theorem steps_chain {s₀ : VG.X86_64.State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk : Nat} (hb : blk < 4) (e : VG.Proof.Bignum.X86_64.AmmSym.Env s₀ a m k bl) :
    ∀ i ≤ 5, ∀ s, VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s a m k bl blk 0 →
      WP isa (.block ((List.range i).flatMap ammStep)) s fun s' =>
        VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s' a m k bl blk i ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mxcsr = s.mxcsr := by
  intro i
  induction i with
  | zero => intro _ s h; exact WP.block_nil ⟨h, fun _ _ => rfl, rfl⟩
  | succ i ih =>
    intro hi s h
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
    obtain ⟨hst, hc⟩ := h₁.stepIn hb (by omega) e
    refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.ammStep_ok (by omega) hst hc) fun s₂ ⟨l₂, z₂, k₂⟩ => ?_
    refine ⟨⟨fun p hp kk hk t ht => ?_, z₂, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => (k₂.gpr r hr).trans (g₁ r hr),
      k₂.mxcsr.trans x₁⟩
    · rw [l₂ p hp kk hk t ht]; rfl
    · rw [k₂.gpr _ (by decide)]; exact h₁.r8
    · rw [k₂.gpr _ (by decide)]; exact h₁.r9
    · rw [k₂.gpr _ (by decide)]; exact h₁.r10
    · rw [k₂.mem]; exact h₁.mem
    · rw [k₂.rd]; exact h₁.rd
    · rw [k₂.wr]; exact h₁.wr

theorem regOf_five (p kk : Nat) : VG.Proof.Bignum.X86_64.AmmSym.regOf p kk 5 = VG.Proof.Bignum.X86_64.AmmSym.regOf p kk 0 := by unfold VG.Proof.Bignum.X86_64.AmmSym.regOf; omega

/-- A block: five steps, `r9` to the next block's limbs, the count down. -/
theorem ammBlock_ok {s₀ s : VG.X86_64.State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    {blk : Nat} (hb : blk < 4) (e : VG.Proof.Bignum.X86_64.AmmSym.Env s₀ a m k bl) (h : VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s a m k bl blk 0)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (4 - blk)) :
    WP isa (.block VG.Impl.Rsa.X86_64.CrtIfma.ammBlock) s fun s' =>
      VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s' a m k bl (blk + 1) 0 ∧ s'.gpr .rcx = BitVec.ofNat 64 (4 - (blk + 1)) ∧
      s'.zf = some (decide (blk + 1 = 4)) ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr := by
  rw [show VG.Impl.Rsa.X86_64.CrtIfma.ammBlock = (List.range 5).flatMap ammStep ++
    ([.alu .add .r9 (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr) from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.steps_chain hb e 5 (Nat.le_refl _) s h) fun s₁ ⟨h₁, g₁, x₁⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have r9₁ := h₁.r9
  have cx₁ : s₁.gpr .rcx = BitVec.ofNat 64 (4 - blk) := by rw [g₁ _ (by decide)]; exact hcx
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := rfl
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := rfl
  have hc : BitVec.ofNat 64 (4 - blk) - 1 = BitVec.ofNat 64 (4 - (blk + 1)) := by
    rw [show 4 - blk = (4 - (blk + 1)) + 1 by omega, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  simp only [e8, e1]
  generalize hS₂ : (arithFlags s₁ (s₁.gpr .r9 + BitVec.ofNat 64 8) _ _).setReg .r9 (s₁.gpr .r9 + BitVec.ofNat 64 8) = S₂
  have g₂ : ∀ r, r ≠ .r9 → S₂.gpr r = s₁.gpr r := fun r hr => by
    rw [← hS₂, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have r9₂ : S₂.gpr .r9 = s₁.gpr .r9 + BitVec.ofNat 64 8 := by rw [← hS₂, RegUpd.gpr_setReg_self]
  have q₂ : ∀ r t, qw S₂ r t = qw s₁ r t := fun r t => by rw [← hS₂]; rfl
  have v₂ : S₂.mem = s₁.mem ∧ S₂.rd = s₁.rd ∧ S₂.wr = s₁.wr ∧ S₂.mxcsr = s₁.mxcsr := by
    rw [← hS₂]; exact ⟨rfl, rfl, rfl, rfl⟩
  generalize hS₃ : (arithFlags S₂ (S₂.gpr .rcx - 1) _ _).setReg .rcx (S₂.gpr .rcx - 1) = S₃
  have g₃ : ∀ r, r ≠ .rcx → S₃.gpr r = S₂.gpr r := fun r hr => by
    rw [← hS₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  have cx₃ : S₃.gpr .rcx = S₂.gpr .rcx - 1 := by rw [← hS₃, RegUpd.gpr_setReg_self]
  have z₃ : S₃.zf = some (S₂.gpr .rcx - 1 == 0) := by rw [← hS₃]; rfl
  have q₃ : ∀ r t, qw S₃ r t = qw S₂ r t := fun r t => by rw [← hS₃]; rfl
  have v₃ : S₃.mem = S₂.mem ∧ S₃.rd = S₂.rd ∧ S₃.wr = S₂.wr ∧ S₃.mxcsr = S₂.mxcsr := by
    rw [← hS₃]; exact ⟨rfl, rfl, rfl, rfl⟩
  have cx₂ : S₂.gpr .rcx = BitVec.ofNat 64 (4 - blk) := by rw [g₂ _ (by decide), cx₁]
  refine ⟨⟨fun p hp kk hk t ht => ?_, fun t ht => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    fun r h1 h2 h3 => ?_, ?_⟩
  · rw [q₃, q₂, ← VG.Proof.Bignum.X86_64.AmmSym.regOf_five p kk, show 5 * (blk + 1) + 0 = 5 * blk + 5 by omega]
    exact h₁.lanes p hp kk hk t ht
  · rw [q₃, q₂]; exact h₁.z t ht
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r8
  · rw [g₃ _ (by decide), r9₂, r9₁, BitVec.add_assoc, show 8 * (blk + 1) = 8 * blk + 8 by omega, BitVec.ofNat_add]
  · rw [g₃ _ (by decide), g₂ _ (by decide)]; exact h₁.r10
  · rw [v₃.1, v₂.1]; exact h₁.mem
  · rw [v₃.2.1, v₂.2.1]; exact h₁.rd
  · rw [v₃.2.2.1, v₂.2.2.1]; exact h₁.wr
  · rw [cx₃, cx₂, hc]
  · rw [z₃, cx₂, hc]
    rcases (by omega : blk = 0 ∨ blk = 1 ∨ blk = 2 ∨ blk = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [g₃ _ h2, g₂ _ h3]; exact g₁ r h1
  · rw [v₃.2.2.2, v₂.2.2.2]; exact x₁

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmCore`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication's loop

The start of `ammCore` (`r10 := rbx`, the count of blocks, the accumulators
and register 14 zeroed) gives `InBlk` for block 0 (`init_ok`), and the loop
of four blocks `InBlk` for block 4: the lanes after twenty steps
(`loop_ok`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 ammStep ammBlock)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw)

theorem xr_eq : ∀ r < 16, VG.Impl.Rsa.X86_64.CrtIfma.xr r = xr r := by decide

/-- The zeroing of the accumulators and register 14. -/
def zeros : List Instr :=
  (List.range 15).map fun r => .vop (.vbin .vpxor .l256 (VG.Impl.Rsa.X86_64.CrtIfma.xr r)
    (VG.Impl.Rsa.X86_64.CrtIfma.xr r) (VG.Impl.Rsa.X86_64.CrtIfma.xr r))

def checkZeros : Bool :=
  match Sym.init.run (fun _ => 0) VG.Proof.Bignum.X86_64.AmmSym.zeros with
  | some σ => (List.range 15).all fun r => decide (σ.reg r = .zero)
  | none => false

theorem checkZeros_ok : VG.Proof.Bignum.X86_64.AmmSym.checkZeros = true := by decide +kernel

theorem zeros_ok {s : VG.X86_64.State} :
    WP isa (.block VG.Proof.Bignum.X86_64.AmmSym.zeros) s fun s' => (∀ r < 15, ∀ t < 4, qw s' (xr r) t = 0) ∧ VG.Proof.Bignum.X86_64.AmmSym.Keeps s s' := by
  have h := VG.Proof.Bignum.X86_64.AmmSym.checkZeros_ok
  unfold VG.Proof.Bignum.X86_64.AmmSym.checkZeros at h
  split at h
  · rename_i σ hσ
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.run_ok (fun b d n hn hd => absurd hd (by omega)) hσ) fun s' hs => ⟨fun r hr t ht => ?_,
      ⟨fun r hr => hs.gpr hr, hs.mem, hs.rd, hs.wr, hs.mxcsr, hs.flags⟩⟩
    · rw [hs.reg _ t ht, VG.Proof.Bignum.X86_64.AmmSym.xi_xr r (by omega), h r hr]; rfl
  · cases h

/-- The loop of four blocks, from block `4 - n`. -/
theorem loop_ok {s₀ : VG.X86_64.State} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : VG.Proof.Bignum.X86_64.AmmSym.Env s₀ a m k bl) :
    ∀ n s, 1 ≤ n → n ≤ 4 → VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s a m k bl (4 - n) 0 → s.gpr .rcx = BitVec.ofNat 64 n →
      WP isa (.loop (.block ammBlock) .ne) s fun s' =>
        VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
        s'.mxcsr = s.mxcsr := by
  intro n s h1 h4 hi hc
  refine WP.loop (M := isa) (body := .block ammBlock) (c := .ne)
    (Q := fun s' => VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ s' a m k bl 4 0 ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mxcsr = s.mxcsr)
    (fun n (t : VG.X86_64.State) => 1 ≤ n ∧ n ≤ 4 ∧ VG.Proof.Bignum.X86_64.AmmSym.InBlk s₀ t a m k bl (4 - n) 0 ∧ t.gpr .rcx = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.mxcsr = s.mxcsr) ?_ n s
    ⟨h1, h4, hi, hc, fun _ _ _ _ => rfl, rfl⟩
  intro n t ⟨h1, h4, hi, hc, hg, hx⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.ammBlock_ok (blk := 4 - n) (by omega) e hi (by rw [hc]; congr 1; omega))
    fun t' ⟨hi', hc', hz, hg', hx'⟩ => ?_
  simp only [VG.X86_64.eval, hz, Option.map_some]
  rcases Nat.eq_or_lt_of_le h1 with rfl | hn
  · refine .inl ⟨by simp, ?_, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩
    exact hi'
  · refine .inr ⟨by simp only [decide_eq_false (show ¬ (4 - n + 1 = 4) by omega), Bool.not_false], n - 1,
      by omega, by omega, by omega, by rw [show 4 - (n - 1) = 4 - n + 1 by omega]; exact hi',
      by rw [hc']; congr 1; omega, fun r r1 r2 r3 => (hg' r r1 r2 r3).trans (hg r r1 r2 r3), hx'.trans hx⟩

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmOut`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication's result

After the loop, `ammCore` stores the five accumulators of each prime at
`r11` (and `r11 + D`), then carries the twenty limbs of each in order
(`carryOut`), the two chains interleaved: each limb keeps its low 52 bits
and passes the rest on. `stores_ok` and `carry_ok` give the memory after
each, as numbers (`Amm52.carried`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside ofs_off writeW_outside word_writeW_self)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 carryOut mask52)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi qw qword256_ymm)

/-! ## Writes of 32 bytes -/

/-- Writes `(e, v)` at `B + e`, the first first. -/
def wrList (m : Mem) (B : Addr) : List (Nat × BitVec 256) → Mem
  | [] => m
  | (e, v) :: rest => VG.Proof.Bignum.X86_64.AmmSym.wrList (m.writeW (VG.Proof.Bignum.X86_64.off B e) v) B rest

theorem writeW256_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 256) (h : d + 32 ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.Outside base d 32 m (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) := by
  intro x hx
  apply Mem.write_apply
  simp only [VG.Proof.Bignum.X86_64.ofs] at hx
  have : (x - VG.Proof.Bignum.X86_64.off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A word that no write of the list touches. -/
theorem word_wrList_other (B : Addr) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem) {d : Nat}, d + 8 ≤ 2 ^ 63 →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (d + 8 ≤ x.1 ∨ x.1 + 32 ≤ d)) → VG.Proof.Bignum.X86_64.word (VG.Proof.Bignum.X86_64.AmmSym.wrList m B l) B d = VG.Proof.Bignum.X86_64.word m B d
  | [], _, _, _, _ => rfl
  | (e, v) :: rest, m, d, hd, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    rw [VG.Proof.Bignum.X86_64.AmmSym.wrList, VG.Proof.Bignum.X86_64.AmmSym.word_wrList_other B rest _ hd fun x hx => h x (List.mem_cons_of_mem _ hx)]
    exact (VG.Proof.Bignum.X86_64.AmmSym.writeW256_outside m B v (by omega)).word (by omega) (by omega)

/-- The word at `e + 8 t` of the write `(e, v)`, after writes elsewhere. -/
theorem word_wrList_hit (B : Addr) (m : Mem) (l₁ l₂ : List (Nat × BitVec 256)) {e t : Nat} (v : BitVec 256)
    (ht : t < 4) (he : e + 32 ≤ 2 ^ 63)
    (h : ∀ x ∈ l₂, x.1 + 32 ≤ 2 ^ 63 ∧ (e + 8 * t + 8 ≤ x.1 ∨ x.1 + 32 ≤ e + 8 * t)) :
    VG.Proof.Bignum.X86_64.word (VG.Proof.Bignum.X86_64.AmmSym.wrList m B (l₁ ++ (e, v) :: l₂)) B (e + 8 * t) = v.extractLsb' (64 * t) 64 := by
  induction l₁ generalizing m with
  | nil =>
    rw [List.nil_append, VG.Proof.Bignum.X86_64.AmmSym.wrList, VG.Proof.Bignum.X86_64.AmmSym.word_wrList_other B l₂ _ (by omega) h]
    have := readW_writeW_inside m (VG.Proof.Bignum.X86_64.off B e) v (k := 8 * t) (n := 8) (by omega) (by decide)
    simp only [VG.Proof.Bignum.X86_64.word, VG.Proof.Bignum.X86_64.off] at this ⊢
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, this, show 8 * (8 * t) = 64 * t by omega]
  | cons x l₁ ih => exact ih _

/-! ## The stores -/

/-- 32-byte stores of registers at `b` plus offsets. -/
def storeCode (b : Reg) (l : List (Nat × XReg)) : List Instr :=
  l.map fun x => .vmovdquStore .l256 (VG.Impl.Rsa.X86_64.CrtIfma.at_ b x.1) x.2

theorem stores_gen {B : Addr} {b : Reg} :
    ∀ (l : List (Nat × XReg)) (s : State), s.gpr b = B →
      (∀ x ∈ l, InRegions s.wr (VG.Proof.Bignum.X86_64.off B x.1) 32) →
      WP isa (.block (VG.Proof.Bignum.X86_64.AmmSym.storeCode b l)) s fun s' => s' = { s with
                                                                mem := VG.Proof.Bignum.X86_64.AmmSym.wrList s.mem B (l.map fun x => (x.1, s.ymm x.2)) }
  | [], s, _, _ => WP.block_nil rfl
  | (e, r) :: rest, s, hB, hw => by
    rw [VG.Proof.Bignum.X86_64.AmmSym.storeCode, List.map_cons, WP.block_cons_iff]
    have ea : s.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ b e) = VG.Proof.Bignum.X86_64.off B e := by
      simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_, hB, VG.Proof.Bignum.X86_64.off]
      exact congrArg _ (BitVec.ofInt_natCast ..)
    refine ⟨{ s with mem := s.mem.writeW (VG.Proof.Bignum.X86_64.off B e) (s.ymm r) }, ?_, ?_⟩
    · simp only [exec, ea, State.store256, hw (e, r) (List.mem_cons_self ..), ite_true]
    · refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.stores_gen rest _ hB fun x hx => hw x (List.mem_cons_of_mem _ hx)) fun s' h => ?_
      rw [h]
      rfl

/-- The accumulators' stores of `ammCore`. -/
def accStores : List (Nat × XReg) :=
  (List.range 2).flatMap fun p => (List.range 5).map fun k => (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * k, VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0)

theorem accStores_code :
    ((List.range 2).flatMap fun p => (List.range 5).map fun k =>
      (Instr.vmovdquStore .l256 (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * k))
        (VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0))) = VG.Proof.Bignum.X86_64.AmmSym.storeCode .r11 VG.Proof.Bignum.X86_64.AmmSym.accStores := by
  decide

/-- The word at `e + 8 t` after writes of which only `(e, v)` touch it. -/
theorem word_wrList_unique (B : Addr) {e t : Nat} {v : BitVec 256} (ht : t < 4) (he : e + 32 ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (e, v) ∈ l →
      (∀ x ∈ l, x.1 + 32 ≤ 2 ^ 63 ∧ (x.1 = e ∨ e + 32 ≤ x.1 ∨ x.1 + 32 ≤ e)) → (∀ x ∈ l, x.1 = e → x.2 = v) →
      VG.Proof.Bignum.X86_64.word (VG.Proof.Bignum.X86_64.AmmSym.wrList m B l) B (e + 8 * t) = v.extractLsb' (64 * t) 64
  | [], _, h, _, _ => absurd h (List.not_mem_nil)
  | (e', v') :: rest, m, hm, hd, hv => by
    by_cases hr : (e, v) ∈ rest
    · rw [VG.Proof.Bignum.X86_64.AmmSym.wrList]
      exact VG.Proof.Bignum.X86_64.AmmSym.word_wrList_unique B ht he rest _ hr (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    · have h0 : (e, v) = (e', v') := by
        rcases List.mem_cons.1 hm with h | h
        · exact h
        · exact absurd h hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
      have := VG.Proof.Bignum.X86_64.AmmSym.word_wrList_hit B m [] rest (e := e) (t := t) v ht he (fun x hx => by
        refine ⟨(hd x (List.mem_cons_of_mem _ hx)).1, ?_⟩
        rcases (hd x (List.mem_cons_of_mem _ hx)).2 with h | h | h
        · exact absurd (by rw [← hv x (List.mem_cons_of_mem _ hx) h]; exact h ▸ hx) hr
        · omega
        · omega)
      simpa only [List.nil_append] using this

theorem acc_xr : ∀ p < 2, ∀ k < 5, VG.Impl.Rsa.X86_64.CrtIfma.acc p k 0 = xr (VG.Proof.Bignum.X86_64.AmmSym.regOf p k 0) := by decide

/-- The word of limb `k + 5 t` of prime `p` after the stores. -/
theorem read_stores (m : Mem) (B : Addr) (s : State) {p k t : Nat} (hp : p < 2) (hk : k < 5) (ht : t < 4) :
    VG.Proof.Bignum.X86_64.word (VG.Proof.Bignum.X86_64.AmmSym.wrList m B (accStores.map fun x => (x.1, s.ymm x.2))) B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * k + 8 * t) =
      qw s (xr (VG.Proof.Bignum.X86_64.AmmSym.regOf p k 0)) t := by
  rw [← qword256_ymm s _ ht, ← VG.Proof.Bignum.X86_64.AmmSym.acc_xr p hp k hk]
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  refine VG.Proof.Bignum.X86_64.AmmSym.word_wrList_unique B ht (by rw [hD]; omega) _ m ?_ (fun x hx => ?_) (fun x hx he => ?_)
  · simp only [VG.Proof.Bignum.X86_64.AmmSym.accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def]
    exact ⟨p, hp, k, hk, rfl⟩
  · simp only [VG.Proof.Bignum.X86_64.AmmSym.accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def] at hx
    obtain ⟨p', hp', k', hk', rfl⟩ := hx
    simp only [hD]
    omega
  · simp only [VG.Proof.Bignum.X86_64.AmmSym.accStores, List.map_flatMap, List.map_map, List.mem_flatMap, List.mem_range, List.mem_map,
      Function.comp_def] at hx
    obtain ⟨p', hp', k', hk', rfl⟩ := hx
    simp only [hD] at he ⊢
    have : p' = p ∧ k' = k := by omega
    obtain ⟨rfl, rfl⟩ := this
    rfl

/-! ## Frames of both regions -/

/-- `m'` agrees with `m` but on the bytes at offsets `[D p + o, D p + o + n)` of `B`, for `p < 2`. -/
def Out2 (B : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (∀ p < 2, VG.Proof.Bignum.X86_64.ofs B x < VG.Impl.Rsa.X86_64.CrtIfma.D * p + o ∨ VG.Impl.Rsa.X86_64.CrtIfma.D * p + o + n ≤ VG.Proof.Bignum.X86_64.ofs B x) → m' x = m x

theorem Out2.refl (B : Addr) (o n : Nat) (m : Mem) : VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m m := fun _ _ => rfl

theorem Out2.trans {B : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m₁ m₂) (h₂ : VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m₂ m₃) :
    VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Out2.of_outside {B : Addr} {o n p : Nat} {m m' : Mem} (hp : p < 2) (h : VG.Proof.Bignum.X86_64.Outside B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) n m m') :
    VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m m' := fun x hx => h x (hx p hp)

/-- Writes of 32 bytes within the windows. -/
theorem wrList_out2 (B : Addr) {o n : Nat} (hn : VG.Impl.Rsa.X86_64.CrtIfma.D + o + n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, ∃ p < 2, VG.Impl.Rsa.X86_64.CrtIfma.D * p + o ≤ x.1 ∧ x.1 + 32 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D * p + o + n) →
      VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m (VG.Proof.Bignum.X86_64.AmmSym.wrList m B l)
  | [], m, _ => Out2.refl B o n m
  | (e, v) :: rest, m, h => by
    obtain ⟨p, hp, h1, h2⟩ := h (e, v) (List.mem_cons_self ..)
    have hDp : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ VG.Impl.Rsa.X86_64.CrtIfma.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
    exact (Out2.of_outside hp ((VG.Proof.Bignum.X86_64.AmmSym.writeW256_outside m B v (by omega)).mono h1 (by omega))).trans
      (VG.Proof.Bignum.X86_64.AmmSym.wrList_out2 B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## The carries -/

open VG.Impl.Rsa.X86_64.CrtIfma (at_) in
/-- Limb `j` of both primes' carry chains. -/
def limbCode (j : Nat) : List Instr :=
  [.alu .add .rdx (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))), .mov .rax (.reg .rdx),
   .alu .and .rax (.reg .r12), .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j)) .rax, .shift .shr .rdx 52,
   .alu .add .rsi (.mem (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j))), .mov .rcx (.reg .rsi),
   .alu .and .rcx (.reg .r12), .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) .rcx,
   .shift .shr .rsi 52]

theorem carryOut_eq : carryOut = ([.mov32 .rdx (.imm 0), .mov32 .rsi (.imm 0)] : List Instr) ++ (List.range 20).flatMap VG.Proof.Bignum.X86_64.AmmSym.limbCode := rfl

theorem and_mask {y : Nat} (hy : y < 2 ^ 64) : BitVec.ofNat 64 y &&& mask52 = BitVec.ofNat 64 (y % 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show mask52.toNat = 2 ^ 52 - 1 from rfl]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hy, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show y % 2 ^ 52 < 2 ^ 64 by omega)]

theorem off_lt (j : Nat) (hj : j < 20) : VG.Impl.Rsa.X86_64.CrtIfma.off j + 8 ≤ 160 := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

theorem off_sep {j l : Nat} (hj : j < 20) (hl : l < 20) (h : l ≠ j) :
    VG.Impl.Rsa.X86_64.CrtIfma.off l + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.off j ∨
      VG.Impl.Rsa.X86_64.CrtIfma.off j + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.off l := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

/-- `s'` is `s` with `r := v`, and maybe other flags. -/
structure Upd (s s' : State) (r : Reg) (v : BitVec 64) : Prop where
  self : s'.gpr r = v
  other : ∀ r', r' ≠ r → s'.gpr r' = s.gpr r'
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr

theorem upd_setReg (t : State) (r : Reg) (v : BitVec 64) (s : State) (hg : t.gpr = s.gpr) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hx : t.mxcsr = s.mxcsr) : VG.Proof.Bignum.X86_64.AmmSym.Upd s (t.setReg r v) r v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun r' h => by rw [RegUpd.gpr_setReg_of_ne _ _ h, hg], hm, hrd, hwr, hx⟩

theorem ex_add_mem {s : State} {r : Reg} {m : MemOp} (hin : InRegions (s.rd ++ s.wr) (s.ea m) 8) :
    ∃ s', exec (.alu .add r (.mem m)) s = some s' ∧ VG.Proof.Bignum.X86_64.AmmSym.Upd s s' r (s.gpr r + s.mem.readW (s.ea m) 64) :=
  ⟨_, by simp only [exec, execAlu, readSrc, State.load64, hin, ite_true, Option.bind_some]; rfl,
    VG.Proof.Bignum.X86_64.AmmSym.upd_setReg (arithFlags s _ _ _) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_mov {s : State} {d r : Reg} : ∃ s', exec (.mov d (.reg r)) s = some s' ∧ VG.Proof.Bignum.X86_64.AmmSym.Upd s s' d (s.gpr r) :=
  ⟨_, rfl, VG.Proof.Bignum.X86_64.AmmSym.upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_and {s : State} {d r : Reg} :
    ∃ s', exec (.alu .and d (.reg r)) s = some s' ∧ VG.Proof.Bignum.X86_64.AmmSym.Upd s s' d (s.gpr d &&& s.gpr r) :=
  ⟨_, rfl, VG.Proof.Bignum.X86_64.AmmSym.upd_setReg _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_shr {s : State} {d : Reg} : ∃ s', exec (.shift .shr d 52) s = some s' ∧ VG.Proof.Bignum.X86_64.AmmSym.Upd s s' d (s.gpr d >>> 52) :=
  ⟨_, by simp only [exec, execShift, show (1 ≤ 52 ∧ 52 ≤ 63) by decide, and_self, ite_true],
    VG.Proof.Bignum.X86_64.AmmSym.upd_setReg (s.setFlags (some ((s.gpr d).getLsbD (52 - 1))) (if 52 = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> 52 == 0)) (some (s.gpr d >>> 52).msb)) _ _ _ rfl rfl rfl rfl rfl⟩

theorem ex_store {s : State} {m : MemOp} {r : Reg} (hin : InRegions s.wr (s.ea m) 8) :
    ∃ s', exec (.store m r) s = some s' ∧ s'.mem = s.mem.writeW (s.ea m) (s.gpr r) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  ⟨{ s with mem := s.mem.writeW (s.ea m) (s.gpr r) }, by simp only [exec, State.store64, hin, ite_true],
    rfl, rfl, rfl, rfl, rfl⟩

/-- After the carries of the limbs below `j`, from the stored limbs `L p`. -/
structure CarryInv (B : Addr) (L : Nat → Nat → Nat) (m₀ : Mem) (s : State) (j : Nat) : Prop where
  r11 : s.gpr .r11 = B
  r12 : s.gpr .r12 = mask52
  rdx : s.gpr .rdx = BitVec.ofNat 64 (carryIn (L 0) j)
  rsi : s.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j)
  words : ∀ p < 2, ∀ l < 20,
    VG.Proof.Bignum.X86_64.word s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) = BitVec.ofNat 64 (if l < j then carried (L p) l else L p l)
  frame : VG.Proof.Bignum.X86_64.AmmSym.Out2 B 0 160 m₀ s.mem

theorem ea_at {s : State} {B : Addr} (h : s.gpr .r11 = B) (d : Nat) :
    s.ea (VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 d) = VG.Proof.Bignum.X86_64.off B d := by
  simp only [State.ea, VG.Impl.Rsa.X86_64.CrtIfma.at_, h, VG.Proof.Bignum.X86_64.off]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem add_ofNat' {x y : Nat} (h : x + y < 2 ^ 64) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := VG.Proof.Bignum.X86_64.AmmSym.add_ofNat h

/-- One limb of both chains. -/
theorem limb_ok {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem} {s : State} {j : Nat} (hj : j < 20)
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61)
    (hw : ∀ d, d + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D + 160 → InRegions s.wr (VG.Proof.Bignum.X86_64.off B d) 8)
    (h : VG.Proof.Bignum.X86_64.AmmSym.CarryInv B L m₀ s j) :
    WP isa (.block (VG.Proof.Bignum.X86_64.AmmSym.limbCode j)) s fun s' => VG.Proof.Bignum.X86_64.AmmSym.CarryInv B L m₀ s' (j + 1) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have ho := VG.Proof.Bignum.X86_64.AmmSym.off_lt j hj
  have c0 := carryIn_lt (L := L 0) (n := j) fun l hl => hL 0 (by decide) l (by omega)
  have c1 := carryIn_lt (L := L 1) (n := j) fun l hl => hL 1 (by decide) l (by omega)
  have l0 := hL 0 (by decide) j hj
  have l1 := hL 1 (by decide) j hj
  have w0 : s.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 0 j) := by
    have := h.words 0 (by decide) j hj
    rw [Nat.mul_zero, Nat.zero_add, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have w1 : s.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    have := h.words 1 (by decide) j hj
    rw [Nat.mul_one, ite_eq_right_iff.2 (fun h => absurd h (by omega))] at this; exact this
  have rin : ∀ d, d + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D + 160 → InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B d) 8 := fun d hd => by
    obtain ⟨r, hr, hc⟩ := hw d hd; exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [VG.Proof.Bignum.X86_64.AmmSym.limbCode, WP.block_cons_iff]
  -- p = 0
  obtain ⟨s1, e1, u1⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_add_mem (s := s) (r := .rdx)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at h.r11]; exact rin (VG.Impl.Rsa.X86_64.CrtIfma.off j) (by omega))
  refine ⟨s1, e1, ?_⟩
  rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at h.r11, h.rdx, w0, VG.Proof.Bignum.X86_64.AmmSym.add_ofNat' (by omega)] at u1
  rw [WP.block_cons_iff]
  obtain ⟨s2, e2, u2⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_mov (s := s1) (d := .rax) (r := .rdx)
  refine ⟨s2, e2, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s3, e3, u3⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_and (s := s2) (d := .rax) (r := .r12)
  refine ⟨s3, e3, ?_⟩
  rw [u2.self, u2.other _ (by decide), u1.self, u1.other _ (by decide), h.r12, VG.Proof.Bignum.X86_64.AmmSym.and_mask (by omega)] at u3
  rw [WP.block_cons_iff]
  have r11₃ : s3.gpr .r11 = B := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r11]
  obtain ⟨s4, e4, m4, g4, rd4, wr4, x4⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_store (s := s3) (r := .rax)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₃, u3.wr, u2.wr, u1.wr]; exact hw _ (by omega))
  refine ⟨s4, e4, ?_⟩
  rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₃, u3.self] at m4
  rw [WP.block_cons_iff]
  obtain ⟨s5, e5, u5⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_shr (s := s4) (d := .rdx)
  refine ⟨s5, e5, ?_⟩
  rw [congrFun g4, u3.other _ (by decide), u2.other _ (by decide), u1.self, VG.Proof.Bignum.X86_64.AmmSym.shr_ofNat (by omega)] at u5
  -- p = 1
  have r11₅ : s5.gpr .r11 = B := by rw [u5.other _ (by decide), congrFun g4, r11₃]
  have mem₅ : s5.mem = (s.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Impl.Rsa.X86_64.CrtIfma.off j))
      (BitVec.ofNat 64 ((carryIn (L 0) j + L 0 j) % 2 ^ 52))) := by
    rw [u5.mem, m4, u3.mem, u2.mem, u1.mem]
  have w1' : s5.mem.readW (VG.Proof.Bignum.X86_64.off B (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j)) 64 = BitVec.ofNat 64 (L 1 j) := by
    rw [mem₅]
    exact ((VG.Proof.Bignum.X86_64.writeW_outside s.mem B _ (by omega)).word (by omega) (by omega)).trans w1
  have wr₅ : s5.wr = s.wr := by rw [u5.wr, wr4, u3.wr, u2.wr, u1.wr]
  have rd₅ : s5.rd = s.rd := by rw [u5.rd, rd4, u3.rd, u2.rd, u1.rd]
  rw [WP.block_cons_iff]
  obtain ⟨s6, e6, u6⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_add_mem (s := s5) (r := .rsi)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₅, rd₅, wr₅]; exact rin _ (by omega))
  refine ⟨s6, e6, ?_⟩
  have rsi₅ : s5.gpr .rsi = BitVec.ofNat 64 (carryIn (L 1) j) := by
    rw [u5.other _ (by decide), congrFun g4, u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), h.rsi]
  rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₅, rsi₅, w1', VG.Proof.Bignum.X86_64.AmmSym.add_ofNat' (by omega)] at u6
  rw [WP.block_cons_iff]
  obtain ⟨s7, e7, u7⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_mov (s := s6) (d := .rcx) (r := .rsi)
  refine ⟨s7, e7, ?_⟩
  rw [WP.block_cons_iff]
  obtain ⟨s8, e8, u8⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_and (s := s7) (d := .rcx) (r := .r12)
  refine ⟨s8, e8, ?_⟩
  have r12₇ : s7.gpr .r12 = mask52 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), congrFun g4,
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r12]
  rw [u7.self, u6.self, r12₇, VG.Proof.Bignum.X86_64.AmmSym.and_mask (by omega)] at u8
  have r11₈ : s8.gpr .r11 = B := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), r11₅]
  rw [WP.block_cons_iff]
  obtain ⟨s9, e9, m9, g9, rd9, wr9, x9⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_store (s := s8) (r := .rcx)
    (m := VG.Impl.Rsa.X86_64.CrtIfma.at_ .r11 (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
    (by rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₈, u8.wr, u7.wr, u6.wr, wr₅]; exact hw _ (by omega))
  refine ⟨s9, e9, ?_⟩
  rw [VG.Proof.Bignum.X86_64.AmmSym.ea_at r11₈, u8.self] at m9
  rw [WP.block_cons_iff]
  obtain ⟨s10, e10, u10⟩ := VG.Proof.Bignum.X86_64.AmmSym.ex_shr (s := s9) (d := .rsi)
  refine ⟨s10, e10, ?_⟩
  rw [congrFun g9, u8.other _ (by decide), u7.other _ (by decide), u6.self, VG.Proof.Bignum.X86_64.AmmSym.shr_ofNat (by omega)] at u10
  refine WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [u10.other _ (by decide), congrFun g9, r11₈]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), r12₇]
  · rw [u10.other _ (by decide), congrFun g9, u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.self]
    simp only [carryIn]; rw [Nat.add_comm]
  · rw [u10.self]; simp only [carryIn]; rw [Nat.add_comm]
  · have mem₁₀ : s10.mem = (s5.mem.writeW (VG.Proof.Bignum.X86_64.off B (VG.Impl.Rsa.X86_64.CrtIfma.D + VG.Impl.Rsa.X86_64.CrtIfma.off j))
        (BitVec.ofNat 64 ((carryIn (L 1) j + L 1 j) % 2 ^ 52))) := by
      rw [u10.mem, m9, u8.mem, u7.mem, u6.mem]
    intro p hp l hl
    have hol := VG.Proof.Bignum.X86_64.AmmSym.off_lt l hl
    rw [mem₁₀, mem₅]
    rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl
    · rw [Nat.mul_zero, Nat.zero_add, (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
      by_cases hlj : l = j
      · subst hlj
        rw [VG.Proof.Bignum.X86_64.word_writeW_self]
        simp only [carried, show l < l + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := VG.Proof.Bignum.X86_64.AmmSym.off_sep hj hl hlj
        rw [(VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 0 (by decide) l hl
        rw [Nat.mul_zero, Nat.zero_add] at this
        rw [this]
        by_cases hlt : l < j
        · simp only [hlt, show l < j + 1 by omega, ite_true]
        · simp only [hlt, show ¬ l < j + 1 by omega, ite_false]
    · rw [Nat.mul_one]
      by_cases hlj : l = j
      · subst hlj
        rw [VG.Proof.Bignum.X86_64.word_writeW_self]
        simp only [carried, show l < l + 1 by omega, ite_true]; rw [Nat.add_comm]
      · have hs := VG.Proof.Bignum.X86_64.AmmSym.off_sep hj hl hlj
        rw [(VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by omega) (by omega),
          (VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
        have := h.words 1 (by decide) l hl
        rw [Nat.mul_one] at this
        rw [this]
        by_cases hlt : l < j
        · simp only [hlt, show l < j + 1 by omega, ite_true]
        · simp only [hlt, show ¬ l < j + 1 by omega, ite_false]
  · rw [u10.mem, m9, u8.mem, u7.mem, u6.mem, mem₅]
    exact (h.frame.trans (Out2.of_outside (p := 0) (by decide)
      ((VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))).trans
      (Out2.of_outside (p := 1) (by decide) ((VG.Proof.Bignum.X86_64.writeW_outside _ B _ (by omega)).mono (by omega) (by omega)))
  · intro r h1 h2 h3 h4
    rw [u10.other _ h4, congrFun g9, u8.other _ h2, u7.other _ h2, u6.other _ h4, u5.other _ h3, congrFun g4,
      u3.other _ h1, u2.other _ h1, u1.other _ h3]
  · rw [u10.rd, rd9, u8.rd, u7.rd, u6.rd, rd₅]
  · rw [u10.wr, wr9, u8.wr, u7.wr, u6.wr, wr₅]
  · rw [u10.mxcsr, x9, u8.mxcsr, u7.mxcsr, u6.mxcsr, u5.mxcsr, x4, u3.mxcsr, u2.mxcsr, u1.mxcsr]


/-- The limbs from `j` on. -/
theorem limbs_ok {B : Addr} {L : Nat → Nat → Nat} {m₀ : Mem}
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61) :
    ∀ n j (s : State), j + n = 20 → (∀ d, d + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D + 160 → InRegions s.wr (VG.Proof.Bignum.X86_64.off B d) 8) →
      VG.Proof.Bignum.X86_64.AmmSym.CarryInv B L m₀ s j →
      WP isa (.block ((List.range' j n).flatMap VG.Proof.Bignum.X86_64.AmmSym.limbCode)) s fun s' => VG.Proof.Bignum.X86_64.AmmSym.CarryInv B L m₀ s' 20 ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr
  | 0, j, s, hn, _, h => WP.block_nil ⟨by rw [← hn]; exact h, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, j, s, hn, hw, h => by
    rw [List.range'_succ, List.flatMap_cons]
    refine WP.block_append (WP.mono (VG.Proof.Bignum.X86_64.AmmSym.limb_ok (by omega) hL hw h) fun s₁ ⟨h₁, g₁, rd₁, wr₁, x₁⟩ =>
      WP.mono (VG.Proof.Bignum.X86_64.AmmSym.limbs_ok hL n (j + 1) s₁ (by omega) (fun d hd => wr₁ ▸ hw d hd) h₁)
        fun s₂ ⟨h₂, g₂, rd₂, wr₂, x₂⟩ => ⟨h₂, fun r a b c d => (g₂ r a b c d).trans (g₁ r a b c d),
          rd₂.trans rd₁, wr₂.trans wr₁, x₂.trans x₁⟩)

/-- The carry pass, from the limbs `L p` stored. -/
theorem carryOut_ok {B : Addr} {L : Nat → Nat → Nat} {s : State}
    (hL : ∀ p < 2, ∀ l < 20, L p l < 2 ^ 61) (hw : ∀ d, d + 8 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D + 160 → InRegions s.wr (VG.Proof.Bignum.X86_64.off B d) 8)
    (hr11 : s.gpr .r11 = B) (hr12 : s.gpr .r12 = mask52)
    (hwords : ∀ p < 2, ∀ l < 20, VG.Proof.Bignum.X86_64.word s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) = BitVec.ofNat 64 (L p l)) :
    WP isa (.block carryOut) s fun s' => VG.Proof.Bignum.X86_64.AmmSym.CarryInv B L s.mem s' 20 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have g2 : ∀ r, r ≠ .rdx → r ≠ .rsi → ((s.setReg .rdx 0).setReg .rsi 0).gpr r = s.gpr r :=
    fun r a b => by rw [RegUpd.gpr_setReg_of_ne _ _ b, RegUpd.gpr_setReg_of_ne _ _ a]
  rw [VG.Proof.Bignum.X86_64.AmmSym.carryOut_eq, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .rdx 0, rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨(s.setReg .rdx 0).setReg .rsi 0, rfl, ?_⟩
  rw [List.nil_append, List.range_eq_range']
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.limbs_ok hL 20 0 _ rfl hw ⟨by rw [g2 _ (by decide) (by decide), hr11],
    by rw [g2 _ (by decide) (by decide), hr12], ?_, by rw [RegUpd.gpr_setReg_self]; rfl,
    fun p hp l hl => hwords p hp l hl, fun _ _ => rfl⟩) fun s' ⟨h, g, rd, wr, x⟩ =>
    ⟨h, fun r a b c d => (g r a b c d).trans (g2 r c d), rd, wr, x⟩
  rfl


/-! ## The whole multiplication -/

/-- Writes of 32 bytes below `n` leave the rest. -/
theorem wrList_outside (B : Addr) {n : Nat} (hn : n ≤ 2 ^ 63) :
    ∀ (l : List (Nat × BitVec 256)) (m : Mem), (∀ x ∈ l, x.1 + 32 ≤ n) → VG.Proof.Bignum.X86_64.Outside B 0 n m (VG.Proof.Bignum.X86_64.AmmSym.wrList m B l)
  | [], m, _ => Outside.refl B 0 n m
  | (e, v) :: rest, m, h => by
    have he := h (e, v) (List.mem_cons_self ..)
    exact ((VG.Proof.Bignum.X86_64.AmmSym.writeW256_outside m B v (by omega)).mono (by omega) (by omega)).trans
      (VG.Proof.Bignum.X86_64.AmmSym.wrList_outside B hn rest _ fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem accStores_win : ∀ x ∈ VG.Proof.Bignum.X86_64.AmmSym.accStores, ∃ p < 2, VG.Impl.Rsa.X86_64.CrtIfma.D * p + 0 ≤ x.1 ∧ x.1 + 32 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D * p + 0 + 160 := by decide

theorem accStores_lt : ∀ x ∈ VG.Proof.Bignum.X86_64.AmmSym.accStores, x.1 + 32 ≤ VG.Impl.Rsa.X86_64.CrtIfma.D + 160 := by decide

/-- `ammCore` from the operands `a` (at `r8`), `b` (at `r9`) and the modulus `m`
with `k` (at `rbx`), into limbs at `r11 = B`: each prime's limbs carried, and
its carry out. -/
theorem ammCore_ok {s : State} {B : Addr} {a m : Nat → Nat → Nat} {k : Nat → Nat} {bl : Nat → Nat → Nat}
    (e : VG.Proof.Bignum.X86_64.AmmSym.Env (s.setReg .r10 (s.gpr .rbx)) a m k bl) (hB : s.gpr .r11 = B) (hs : VG.Proof.Bignum.X86_64.Scr s B (VG.Impl.Rsa.X86_64.CrtIfma.D + 160)) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.ammCore s fun s' =>
      (∀ p < 2, ∀ l < 20, VG.Proof.Bignum.X86_64.word s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l) =
        BitVec.ofNat 64 (carried (VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl p 20) l)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (carryIn (VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl 0 20) 20) ∧
      s'.gpr .rsi = BitVec.ofNat 64 (carryIn (VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl 1 20) 20) ∧
      VG.Proof.Bignum.X86_64.AmmSym.Out2 B 0 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  refine WP.seq ?_
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg .r10 (s.gpr .rbx), rfl, ?_⟩
  rw [List.cons_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.zeros_ok (s := (s.setReg .r10 (s.gpr .rbx)).setReg32 .rcx 4)) fun s₁ ⟨hz, k₁⟩ => ?_
  have g₁ : ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = (s.setReg .r10 (s.gpr .rbx)).gpr r := fun r a c => by
    rw [k₁.gpr r a]; exact RegUpd.gpr_setReg_of_ne _ _ c
  have i₁ : VG.Proof.Bignum.X86_64.AmmSym.InBlk (s.setReg .r10 (s.gpr .rbx)) s₁ a m k bl 0 0 :=
    ⟨fun p hp kk hk t ht => by
      rw [hz _ (by unfold VG.Proof.Bignum.X86_64.AmmSym.regOf; omega) t ht]; rfl,
     fun t ht => hz 14 (by decide) t ht, g₁ _ (by decide) (by decide),
     by rw [g₁ _ (by decide) (by decide), Nat.mul_zero, BitVec.add_zero], g₁ _ (by decide) (by decide),
     k₁.mem, k₁.rd, k₁.wr⟩
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86_64.AmmSym.loop_ok e 4 s₁ (by decide) (by decide) i₁ (by rw [k₁.gpr _ (by decide)]; rfl))
    fun s₂ ⟨i₂, g₂, x₂⟩ => ?_)
  have hB₂ : s₂.gpr .r11 = B := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    exact (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans hB
  have wr₂ : s₂.wr = s.wr := by rw [i₂.wr]; rfl
  rw [VG.Proof.Bignum.X86_64.AmmSym.accStores_code, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.stores_gen VG.Proof.Bignum.X86_64.AmmSym.accStores s₂ hB₂ fun x hx =>
    wr₂ ▸ (let ⟨_, h, c⟩ := hs.region (VG.Proof.Bignum.X86_64.AmmSym.accStores_lt x hx) (by decide); ⟨_, h, c⟩)) fun s₃ h₃ => ?_
  subst h₃
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  have m₂ : s₂.mem = s.mem := i₂.mem
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.carryOut_ok (B := B) (L := fun p => VG.Proof.Bignum.X86_64.AmmSym.lm a m k bl p 20) (fun p _ l hl => VG.Proof.Bignum.X86_64.AmmSym.lm_lt (by decide) hl)
    (fun d hd => by rw [RegUpd.wr_setReg, wr₂]; exact hs.st hd) (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₂)
    (RegUpd.gpr_setReg_self _ _ _) fun p hp l hl => ?_) fun s' ⟨h, g, rd, wr, x⟩ => ?_
  · have := VG.Proof.Bignum.X86_64.AmmSym.read_stores s₂.mem B s₂ hp (k := l % 5) (t := l / 5) (Nat.mod_lt _ (by decide)) (by omega)
    rw [i₂.lanes p hp _ (Nat.mod_lt _ (by decide)) _ (by omega), Nat.mod_add_div] at this
    rw [RegUpd.mem_setReg, show VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off l = VG.Impl.Rsa.X86_64.CrtIfma.D * p + 32 * (l % 5) + 8 * (l / 5) by
      unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega]
    exact this
  refine ⟨fun p hp l hl => by rw [h.words p hp l hl]; simp only [hl, ite_true], h.rdx, h.rsi, ?_, fun r r1 r2 r3 r4 r5 r6 r7 => ?_,
    by rw [rd, RegUpd.rd_setReg, i₂.rd]; rfl, by rw [wr, RegUpd.wr_setReg, wr₂],
    by rw [x, RegUpd.mxcsr_setReg, x₂, k₁.mxcsr]; rfl⟩
  · have o := VG.Proof.Bignum.X86_64.AmmSym.wrList_out2 B (o := 0) (n := 160) (by omega) (accStores.map fun x => (x.1, s₂.ymm x.2)) s₂.mem
      fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact VG.Proof.Bignum.X86_64.AmmSym.accStores_win y hy
    have hf : VG.Proof.Bignum.X86_64.AmmSym.Out2 B 0 160 (VG.Proof.Bignum.X86_64.AmmSym.wrList s₂.mem B (accStores.map fun x => (x.1, s₂.ymm x.2))) s'.mem := h.frame
    have o' : VG.Proof.Bignum.X86_64.AmmSym.Out2 B 0 160 s.mem (VG.Proof.Bignum.X86_64.AmmSym.wrList s₂.mem B (accStores.map fun x => (x.1, s₂.ymm x.2))) :=
      fun x hx => (o x hx).trans (congrFun m₂ x)
    exact o'.trans hf
  · rw [g r r1 r2 r3 r4, RegUpd.gpr_setReg_of_ne _ _ r7, g₂ r r1 r2 r5, g₁ r r1 r2, RegUpd.gpr_setReg_of_ne _ _ r6]

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.AmmSpec`. -/
section

/-!
# RSA with AVX512_IFMA on x86-64: the multiplication

`amm o a b` (`amm_ok`): for each prime `p`, with its region at `B + D p`
(`B` in `rbx`), the numbers of twenty limbs of 52 bits at offsets `a` and
`b` multiplied and divided by `2¹⁰⁴⁰` modulo the modulus at `oM`, into
offset `o`: below twice the modulus when both operands are, and congruent
to their product over `2¹⁰⁴⁰`.

The numbers are in the vector layout: limb `j` at `off j`
(`CrtIfma.off`), read by `limb`; `val52` is their value.
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 mask52)

/-- Limb `j` of the number at `B + d`. -/
abbrev limb (m : Mem) (B : Addr) (d j : Nat) : Nat := (VG.Proof.Bignum.X86_64.word m B (d + VG.Impl.Rsa.X86_64.CrtIfma.off j)).toNat

/-- The number at `B + d`. -/
def val52 (m : Mem) (B : Addr) (d : Nat) : Nat := lval (VG.Proof.Bignum.X86_64.AmmSym.limb m B d) 20

theorem se_ofNat {c : Nat} (h : c < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; simp; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem off_add (B : Addr) (a d : Nat) : VG.Proof.Bignum.X86_64.off B a + BitVec.ofNat 64 d = VG.Proof.Bignum.X86_64.off B (a + d) := VG.Proof.Bignum.X86_64.off_off B a d

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `r := rbx + c`. -/
theorem setOff {s : State} {r : Reg} {c : Nat} {rest : List Instr} {Q : State → Prop} (hc : c < 2 ^ 31)
    (h : ∀ s', VG.Proof.Bignum.X86_64.AmmSym.Upd s s' r (VG.Proof.Bignum.X86_64.off (s.gpr .rbx) c) → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov r (.reg .rbx) :: .alu .add r (.imm (BitVec.ofNat 32 c)) :: rest)) s Q := by
  rw [WP.block_cons_iff]
  refine ⟨s.setReg r (s.gpr .rbx), rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, h _ ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, VG.Proof.Bignum.X86_64.AmmSym.se_ofNat hc]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr', RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr']

theorem off_lim (j : Nat) : VG.Impl.Rsa.X86_64.CrtIfma.off j = 32 * (j % 5) + 8 * (j / 5) := by
  unfold VG.Impl.Rsa.X86_64.CrtIfma.off; omega

theorem ofs_rebase' (B x : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (o ≤ VG.Proof.Bignum.X86_64.ofs B x ∧ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) x = VG.Proof.Bignum.X86_64.ofs B x - o) ∨ (VG.Proof.Bignum.X86_64.ofs B x < o ∧ 2 ^ 64 - o ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.Bignum.X86_64.off B o) x) := by
  simp only [VG.Proof.Bignum.X86_64.ofs, VG.Proof.Bignum.X86_64.off]
  rw [Offset.toNat_sub_add x B ho]
  have := (x - B).isLt
  by_cases h : o ≤ (x - B).toNat
  · left
    refine ⟨h, ?_⟩
    rw [show 2 ^ 64 - o + (x - B).toNat = (x - B).toNat - o + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- A frame at `B + o` as one at `B`. -/
theorem Out2.rebase {B : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.Bignum.X86_64.AmmSym.Out2 (VG.Proof.Bignum.X86_64.off B o) 0 n m m') (hn : o + VG.Impl.Rsa.X86_64.CrtIfma.D + n ≤ 2 ^ 64) :
    VG.Proof.Bignum.X86_64.AmmSym.Out2 B o n m m' := fun x hx => h x fun p hp => by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  have hDp : VG.Impl.Rsa.X86_64.CrtIfma.D * p ≤ VG.Impl.Rsa.X86_64.CrtIfma.D := by rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> simp
  rcases VG.Proof.Bignum.X86_64.AmmSym.ofs_rebase' B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hx p hp with h3 | h3 <;> omega
  · omega

/-- `ammCore` with `r8`, `r9`, `r11` at offsets `a`, `b`, `o` of `B = rbx`. -/
theorem ammCoreSpec_ok {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (r8₃ : s.gpr .r8 = VG.Proof.Bignum.X86_64.off B a) (r9₃ : s.gpr .r9 = VG.Proof.Bignum.X86_64.off B b) (r11₃ : s.gpr .r11 = VG.Proof.Bignum.X86_64.off B o)
    (hs : VG.Proof.Bignum.X86_64.Scr s B (2 * VG.Impl.Rsa.X86_64.CrtIfma.D))
    (ho : o + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D) (ha : a + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D) (hb : b + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D)
    (hlt : ∀ p < 2, ∀ j < 20, VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) j < 2 ^ 52 ∧ VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) j < 2 ^ 52 ∧
      VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < 2, ∀ t < 4, VG.Proof.Bignum.X86_64.word s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < 2, k p < 2 ^ 52) (hk0 : ∀ p < 2, (VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < 2, VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM))
    (hBv : ∀ p < 2, VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM))
    (hM : ∀ p < 2, 4 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) ≤ 2 ^ (52 * 20)) :
    WP isa VG.Impl.Rsa.X86_64.CrtIfma.ammCore s fun s' => (∀ p < 2,
      (∀ j < 20, VG.Proof.Bignum.X86_64.AmmSym.limb s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) j < 2 ^ 52) ∧
      VG.Proof.Bignum.X86_64.AmmSym.val52 s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) ∧
      VG.Proof.Bignum.X86_64.AmmSym.val52 s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) * 2 ^ (52 * 20) % VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) =
        VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) % VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM)) ∧
      VG.Proof.Bignum.X86_64.AmmSym.Out2 B o 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  -- the operands, as functions of the limb index
  let A : Nat → Nat → Nat := fun p => VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a)
  let Bl : Nat → Nat → Nat := fun p => VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b)
  let M : Nat → Nat → Nat := fun p => VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM)
  have rdS : ∀ d n, 0 < n → d + n ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D → InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off B d) n := fun d n hn hd =>
    let ⟨_, h, c⟩ := hs.region hd hn; ⟨_, List.mem_append_right _ h, c⟩
  have e : VG.Proof.Bignum.X86_64.AmmSym.Env (s.setReg .r10 (s.gpr .rbx)) A M k Bl := by
    refine ⟨fun p hp kk hk t ht => ?_, fun p hp kk hk t ht => ?_, fun p hp t ht => ?_, fun p hp l hl => ?_,
      fun p hp j hj => (hlt p hp j hj).1, fun p hp j hj => (hlt p hp j hj).2.2, hklt,
      fun p hp l hl => (hlt p hp l hl).2.1, fun d n hn hd => ?_, fun d n hn hd => ?_, fun d n hn hd => ?_⟩
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, VG.Proof.Bignum.X86_64.AmmSym.off_add]
      show _ = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) (kk + 5 * t))
      rw [VG.Proof.Bignum.X86_64.AmmSym.ofNat_toNat64, VG.Proof.Bignum.X86_64.AmmSym.off_lim _]
      exact congrArg (fun d => s.mem.readW (VG.Proof.Bignum.X86_64.off B d) 64) (by omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      show _ = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) (kk + 5 * t))
      rw [VG.Proof.Bignum.X86_64.AmmSym.ofNat_toNat64, VG.Proof.Bignum.X86_64.AmmSym.off_lim _]
      exact congrArg (fun d => s.mem.readW (VG.Proof.Bignum.X86_64.off B d) 64) (by simp only [oM]; omega)
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hB]
      exact hk p hp t ht
    · rw [RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, VG.Proof.Bignum.X86_64.AmmSym.off_add]
      show _ = BitVec.ofNat 64 (VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) l)
      rw [VG.Proof.Bignum.X86_64.AmmSym.ofNat_toNat64]
      exact congrArg (fun d => s.mem.readW (VG.Proof.Bignum.X86_64.off B d) 64) (by omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r8₃, VG.Proof.Bignum.X86_64.AmmSym.off_add]
      exact rdS _ n hn (by rw [show VG.Proof.Bignum.X86_64.AmmSym.lim .r8 = VG.Impl.Rsa.X86_64.CrtIfma.D + 160 from rfl] at hd; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_of_ne _ _ (by decide), r9₃, VG.Proof.Bignum.X86_64.AmmSym.off_add]
      exact rdS _ n hn (by rw [show VG.Proof.Bignum.X86_64.AmmSym.lim .r9 = VG.Impl.Rsa.X86_64.CrtIfma.D + 136 from rfl] at hd; omega)
    · rw [RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self, hB]
      exact rdS _ n hn (by rw [show VG.Proof.Bignum.X86_64.AmmSym.lim .r10 = VG.Impl.Rsa.X86_64.CrtIfma.D + 192 from rfl] at hd; omega)
  have hs₃ : VG.Proof.Bignum.X86_64.Scr s (VG.Proof.Bignum.X86_64.off B o) (VG.Impl.Rsa.X86_64.CrtIfma.D + 160) := hs.sub (by omega) (by omega)
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.ammCore_ok e r11₃ hs₃) fun s' ⟨hw, hdx, hsi, hf, hg, hrd, hwr, hx⟩ => ?_
  refine ⟨fun p hp => ?_, hf.rebase (by omega), hg, hrd, hwr, hx⟩
  have hl : ∀ j < 20, VG.Proof.Bignum.X86_64.AmmSym.limb s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) j = carried (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) j := fun j hj => by
    have := hw p hp j hj
    simp only [VG.Proof.Bignum.X86_64.word, VG.Proof.Bignum.X86_64.off_off] at this
    show (s'.mem.readW (VG.Proof.Bignum.X86_64.off B _) 64).toNat = _
    rw [show VG.Impl.Rsa.X86_64.CrtIfma.D * p + o + VG.Impl.Rsa.X86_64.CrtIfma.off j = o + (VG.Impl.Rsa.X86_64.CrtIfma.D * p + VG.Impl.Rsa.X86_64.CrtIfma.off j) by
      omega, this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := carried_lt (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) j; omega)]
  have hv : VG.Proof.Bignum.X86_64.AmmSym.val52 s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) = lval (carried (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20)) 20 := by
    unfold VG.Proof.Bignum.X86_64.AmmSym.val52; exact lval_congr hl
  have ok : (VG.Proof.Bignum.X86_64.AmmSym.ops A M k p).Ok := ⟨fun j hj => (hlt p hp j hj).1, fun j hj => (hlt p hp j hj).2.2, hk0 p hp⟩
  obtain ⟨he, hU⟩ := amm_val ok (b := Bl p) fun i hi => (hlt p hp i hi).2.1
  have hcv := carried_val (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) 20
  have hA' := hA p hp
  have hB' := hBv p hp
  have hM' := hM p hp
  rw [hv]
  unfold VG.Proof.Bignum.X86_64.AmmSym.val52 at hA' hB' hM' ⊢
  change lval (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) 20 * _ = lval (A p) 20 * lval (Bl p) 20 + lval (M p) 20 * _ at he
  change lval (A p) 20 < 2 * lval (M p) 20 at hA'
  change lval (Bl p) 20 < 2 * lval (M p) 20 at hB'
  change 4 * lval (M p) 20 ≤ _ at hM'
  have hlt2 := amm_lt he hU hA' hB' hM'
  have hz : lval (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) 20 < 2 ^ (52 * 20) := by
    generalize 2 ^ (52 * 20) = R at hM' ⊢; omega
  rw [carryIn_zero hz] at hcv
  replace hcv : lval (carried (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20)) 20 = lval (VG.Proof.Bignum.X86_64.AmmSym.lm A M k Bl p 20) 20 := by
    generalize 2 ^ (52 * 20) = R at hcv; omega
  rw [hcv]
  refine ⟨fun j hj => (hl j hj) ▸ carried_lt _ j, hlt2, ?_⟩
  rw [he, Nat.add_mul_mod_self_left]

/-- `[o] := [a] [b] / 2¹⁰⁴⁰` for both primes. -/
theorem amm_ok {s : State} {B : Addr} {o a b : Nat} {k : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : VG.Proof.Bignum.X86_64.Scr s B (2 * VG.Impl.Rsa.X86_64.CrtIfma.D))
    (ho : o + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D) (ha : a + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D) (hb : b + VG.Impl.Rsa.X86_64.CrtIfma.D + 160 ≤ 2 * VG.Impl.Rsa.X86_64.CrtIfma.D)
    (hlt : ∀ p < 2, ∀ j < 20, VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) j < 2 ^ 52 ∧ VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) j < 2 ^ 52 ∧
      VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) j < 2 ^ 52)
    (hk : ∀ p < 2, ∀ t < 4, VG.Proof.Bignum.X86_64.word s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oK0 + 8 * t) = BitVec.ofNat 64 (k p))
    (hklt : ∀ p < 2, k p < 2 ^ 52) (hk0 : ∀ p < 2, (VG.Proof.Bignum.X86_64.AmmSym.limb s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) 0 * k p + 1) % 2 ^ 52 = 0)
    (hA : ∀ p < 2, VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM))
    (hBv : ∀ p < 2, VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM))
    (hM : ∀ p < 2, 4 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) ≤ 2 ^ (52 * 20)) :
    WP isa (VG.Impl.Rsa.X86_64.CrtIfma.amm o a b) s fun s' => (∀ p < 2,
      (∀ j < 20, VG.Proof.Bignum.X86_64.AmmSym.limb s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) j < 2 ^ 52) ∧
      VG.Proof.Bignum.X86_64.AmmSym.val52 s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) < 2 * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) ∧
      VG.Proof.Bignum.X86_64.AmmSym.val52 s'.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + o) * 2 ^ (52 * 20) % VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM) =
        VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + a) * VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + b) % VG.Proof.Bignum.X86_64.AmmSym.val52 s.mem B (VG.Impl.Rsa.X86_64.CrtIfma.D * p + oM)) ∧
      VG.Proof.Bignum.X86_64.AmmSym.Out2 B o 160 s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hD : VG.Impl.Rsa.X86_64.CrtIfma.D = 3712 := rfl
  refine WP.seq ?_
  refine VG.Proof.Bignum.X86_64.AmmSym.setOff (by omega) fun s₁ u₁ => VG.Proof.Bignum.X86_64.AmmSym.setOff (by omega) fun s₂ u₂ =>
    VG.Proof.Bignum.X86_64.AmmSym.setOff (by omega) fun s₃ u₃ => WP.block_nil ?_
  rw [u₁.other _ (by decide), hB] at u₂
  rw [u₂.other _ (by decide), u₁.other _ (by decide), hB] at u₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have r8₃ : s₃.gpr .r8 = VG.Proof.Bignum.X86_64.off B a := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.self, hB]
  have r9₃ : s₃.gpr .r9 = VG.Proof.Bignum.X86_64.off B b := by rw [u₃.other _ (by decide), u₂.self]
  have rbx₃ : s₃.gpr .rbx = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hB]
  have g₃ : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → s₃.gpr r = s.gpr r := fun r h8 h9 h11 => by
    rw [u₃.other _ h11, u₂.other _ h9, u₁.other _ h8]
  rw [← m₃] at hlt hk hk0 hA hBv hM ⊢
  refine WP.mono (VG.Proof.Bignum.X86_64.AmmSym.ammCoreSpec_ok rbx₃ r8₃ r9₃ u₃.self (hs.congr wr₃) ho ha hb hlt hk hklt hk0 hA hBv hM)
    fun s' ⟨hv, hf, hg, hrd, hwr, hx⟩ => ⟨hv, hf, fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_,
      hrd.trans rd₃, hwr.trans wr₃, by rw [hx, u₃.mxcsr, u₂.mxcsr, u₁.mxcsr]⟩
  rw [hg r h1 h2 h3 h4 h6 h7 h9, g₃ r h5 h6 h8]

end VG.Proof.Bignum.X86_64.AmmSym

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Cmp`. -/
section

/-!
# Multiword arithmetic on x86-64: comparison

`X - m` over `w` words, with the borrow kept in `rbp` as a mask and the
difference discarded: `rbp` ends as the mask of `X < m` (`cmpLoop_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The comparison loop's body. -/
abbrev cmpBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]

/-- After `j` words from `s₀`: the low `j` words `X_j` and `m_j` and the
borrow `c` of `X_j - m_j`. -/
structure CmpInv (s₀ : State) (B : Addr) (Z eX eN : Nat) (j : Nat) (t : State) : Prop where
  scr : VG.Proof.Bignum.X86_64.Scr t B Z
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : ∃ (c : Bool) (d : Nat), t.gpr .rbp = VG.Proof.Bignum.X86_64.mask c ∧ d < 2 ^ (64 * j) ∧
    d + VG.Proof.Bignum.X86_64.wv s₀.mem B eN j = VG.Proof.Bignum.X86_64.wv s₀.mem B eX j + 2 ^ (64 * j) * c.toNat

theorem cmpStep_ok {s₀ : State} {B : Addr} {Z w eX eN : Nat}
    (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s₀.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Bignum.X86_64.CmpInv s₀ B Z eX eN j t) :
    WP isa (.block (VG.Proof.Bignum.X86_64.cmpBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.CmpInv s₀ B Z eX eN (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, d, hbp, hd, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      ∃ c' : Bool, t₁.gpr .rbp = VG.Proof.Bignum.X86_64.mask c' ∧ ∃ r : BitVec 64,
        r.toNat + (VG.Proof.Bignum.X86_64.word t.mem B (eN + 8 * j)).toNat + c.toNat =
          (VG.Proof.Bignum.X86_64.word t.mem B (eX + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨hm, c', h₁, r, hr⟩, k₁⟩ => ?_
  · unfold VG.Proof.Bignum.X86_64.cmpBody cfFromRbp cfToRbp
    xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 tbx hI.r14, VG.Proof.Bignum.X86_64.addr0 t10 hI.r14, hbp, VG.Proof.Bignum.X86_64.cf_mask,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, VG.Proof.Bignum.X86_64.sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [hI.mem] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ⟨c', d + 2 ^ (64 * j) * r.toNat, (k'.gpr (by decide)).trans h₁, ?_, ?_⟩⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * j)) (show r.toNat + 1 ≤ 2 ^ 64 from r.isLt)
    rw [VG.Proof.Bignum.X86_64.pow64_succ]; rw [Nat.mul_add, Nat.mul_one] at this; omega
  · simp only [VG.Proof.Bignum.X86_64.wv]
    rw [VG.Proof.Bignum.X86_64.pow64_succ]
    grind

theorem lt_of_borrow {X N d P : Nat} {c : Bool} (hd : d < P)
    (h : d + N = X + P * c.toNat) : c = decide (X < N) := by
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at h <;>
    (symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]) <;> omega

/-- `rbp := 0`, then the loop: `rbp` the mask of `X < m` for the `w`-word
numbers at `rbx` and `r10`. -/
theorem cmpLoop_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : VG.Proof.Bignum.X86_64.Scr s B Z)
    (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off B eX) (h10 : s.gpr .r10 = VG.Proof.Bignum.X86_64.off B eN)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hbp : s.gpr .rbp = VG.Proof.Bignum.X86_64.mask false) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) :
    WP isa (wordLoop 0 VG.Proof.Bignum.X86_64.cmpBody) s fun t =>
      t.gpr .rbp = VG.Proof.Bignum.X86_64.mask (decide (VG.Proof.Bignum.X86_64.wv s.mem B eX w < VG.Proof.Bignum.X86_64.wv s.mem B eN w)) ∧ t.mem = s.mem ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Bignum.X86_64.CmpInv s B Z eX eN 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), hm, h14,
      ⟨false, 0, (k.gpr (by decide)).trans hbp, Nat.one_pos, rfl⟩⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.CmpInv s B Z eX eN) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.cmpStep_ok hbx h10 h12 (by omega) hX hN hj hI)) fun t hI => ?_
  obtain ⟨c, d, hc, hd, hval⟩ := hI.val
  exact ⟨by rw [hc, VG.Proof.Bignum.X86_64.lt_of_borrow hd hval], hI.mem, hI.keep⟩

end VG.Proof.Bignum.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Bignum.X86_64.Copy`. -/
section

/-!
# Multiword arithmetic on x86-64: copying words

`copyWords` copies `w` words from `rsi` to `rbx` (`copyWords_ok`), between
the working space and a buffer outside it, either way.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-- Numbers at two places with the same words. -/
theorem wv_congr2 {m m' : Mem} {p p' : Addr} {d d' n : Nat}
    (h : ∀ i < n, VG.Proof.Bignum.X86_64.word m' p' (d' + 8 * i) = VG.Proof.Bignum.X86_64.word m p (d + 8 * i)) : VG.Proof.Bignum.X86_64.wv m' p' d' n = VG.Proof.Bignum.X86_64.wv m p d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [VG.Proof.Bignum.X86_64.wv]
    rw [ih fun i hi => h i (by omega), h n (by omega)]

/-- After copying `j` words from `S + eS` to `D + eD`. -/
structure CopyInv (s₀ : State) (S D : Addr) (eS eD : Nat) (j : Nat) (t : State) : Prop where
  keep : VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  done : ∀ i < j, VG.Proof.Bignum.X86_64.word t.mem D (eD + 8 * i) = VG.Proof.Bignum.X86_64.word s₀.mem S (eS + 8 * i)
  frame : VG.Proof.Bignum.X86_64.Outside D eD (8 * j) s₀.mem t.mem

theorem copyStep_ok {s₀ : State} {S D : Addr} {eS eD w : Nat}
    (hsi : s₀.gpr .rsi = VG.Proof.Bignum.X86_64.off S eS) (hbx : s₀.gpr .rbx = VG.Proof.Bignum.X86_64.off D eD) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Bignum.X86_64.off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s₀.wr (VG.Proof.Bignum.X86_64.off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, VG.Proof.Bignum.X86_64.ofs D (VG.Proof.Bignum.X86_64.off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ VG.Proof.Bignum.X86_64.ofs D (VG.Proof.Bignum.X86_64.off S (eS + 8 * j) + BitVec.ofNat 64 b))
    {j : Nat} (hj : j < w) {t : State} (hI : VG.Proof.Bignum.X86_64.CopyInv s₀ S D eS eD j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ VG.Proof.Bignum.X86_64.CopyInv s₀ S D eS eD (j + 1) t' := by
  have tsi : t.gpr .rsi = VG.Proof.Bignum.X86_64.off S eS := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = VG.Proof.Bignum.X86_64.off D eD := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have hld : InRegions (t.rd ++ t.wr) (VG.Proof.Bignum.X86_64.off S (eS + 8 * j)) 8 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd j hj
  have hst : InRegions t.wr (VG.Proof.Bignum.X86_64.off D (eD + 8 * j)) 8 := by rw [hI.keep.2.2]; exact hwr j hj
  have hv : VG.Proof.Bignum.X86_64.word t.mem S (eS + 8 * j) = VG.Proof.Bignum.X86_64.word s₀.mem S (eS + 8 * j) :=
    Mem.readW_congr fun b hb => hI.frame _ (by have := hsep j hj b hb; omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off D (eD + 8 * j)) (VG.Proof.Bignum.X86_64.word s₀.mem S (eS + 8 * j))) ?_ rfl)
    fun t₁ ⟨hm, k₁⟩ => ?_
  · xrun [State.ea, ix, VG.Proof.Bignum.X86_64.addr0 tsi hI.r14, VG.Proof.Bignum.X86_64.addr0 tbx hI.r14, hld, hst, hv]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (VG.Proof.Bignum.X86_64.count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), h14, fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(VG.Proof.Bignum.X86_64.writeW_outside t.mem D _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside t.mem D _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- `copyWords`: the `w` words at `S + eS` to `D + eD`, which they do not
overlap, changing only those. -/
theorem copyWords_ok {s : State} {S D : Addr} {eS eD w : Nat}
    (hsi : s.gpr .rsi = VG.Proof.Bignum.X86_64.off S eS) (hbx : s.gpr .rbx = VG.Proof.Bignum.X86_64.off D eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hD : eD + 8 * w ≤ 2 ^ 64)
    (hrd : ∀ j < w, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.X86_64.off S (eS + 8 * j)) 8)
    (hwr : ∀ j < w, InRegions s.wr (VG.Proof.Bignum.X86_64.off D (eD + 8 * j)) 8)
    (hsep : ∀ j < w, ∀ b < 8, VG.Proof.Bignum.X86_64.ofs D (VG.Proof.Bignum.X86_64.off S (eS + 8 * j) + BitVec.ofNat 64 b) < eD ∨
      eD + 8 * w ≤ VG.Proof.Bignum.X86_64.ofs D (VG.Proof.Bignum.X86_64.off S (eS + 8 * j) + BitVec.ofNat 64 b)) :
    WP isa copyWords s fun t =>
      VG.Proof.Bignum.X86_64.wv t.mem D eD w = VG.Proof.Bignum.X86_64.wv s.mem S eS w ∧ (∀ i < w, VG.Proof.Bignum.X86_64.word t.mem D (eD + 8 * i) = VG.Proof.Bignum.X86_64.word s.mem S (eS + 8 * i)) ∧
      VG.Proof.Bignum.X86_64.Outside D eD (8 * w) s.mem t.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → VG.Proof.MlKem.X86_64.Keep [.r14] s t → t.cf = s.cf →
      VG.Proof.Bignum.X86_64.CopyInv s S D eS eD 0 t := fun t h14 hm k _ =>
    ⟨k.mono (by decide), h14, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [hm]; exact Outside.refl _ _ _ _⟩
  refine WP.mono (VG.Proof.Bignum.X86_64.wordLoop_ok (start := 0) (N := w) (by omega) hw' (VG.Proof.Bignum.X86_64.CopyInv s S D eS eD) h0
    (fun j _ hj t hI => VG.Proof.Bignum.X86_64.copyStep_ok hsi hbx h12 (by omega) hD hrd hwr hsep hj hI)) fun t hI => ?_
  exact ⟨VG.Proof.Bignum.X86_64.wv_congr2 hI.done, hI.done, hI.frame, hI.keep⟩

end VG.Proof.Bignum.X86_64

end
