module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: working spaces within the scratch

The primes' working spaces are parts of the scratch: `Scr.sub`, what
separates two parts (`sep_sub`), offsets from a part (`ofs_sub`), frames of a
part as frames of the scratch (`out_sub`, `outs_sub`), and copying words
between two parts (`copySub_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum.PPC64LE

theorem toNat_off_le (B : Addr) (d : Nat) : (off B d).toNat ≤ B.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) (by have := Nat.mod_le d (2 ^ 64); omega)

/-- A part of a working space is one. -/
theorem _root_.VG.Proof.Bignum.PPC64LE.Scr.sub {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {d n : Nat} (h : d + n ≤ Z) :
    Scr s (off B d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, hn⟩ := hs
  exact ⟨⟨B₀, o + d, L, hm, by rw [hb, off_off], by omega, hL'⟩, by have := toNat_off_le B d; omega⟩

/-- The offset from `B` of an address within `n` bytes of `off B o`. -/
theorem ofs_sub {B x : Addr} {o n : Nat} (h : ofs (off B o) x < n) (hn : o + n ≤ 2 ^ 64) :
    ofs B x = o + ofs (off B o) x := by
  rcases ofs_rebase B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨_, h2⟩ <;> omega

/-- Two separate parts of `2⁶⁴` bytes from `B`. -/
theorem sep_sub (B : Addr) {a n b m : Nat} (ha : a + n ≤ 2 ^ 64) (hb : b + m ≤ 2 ^ 64)
    (hd : a + n ≤ b ∨ b + m ≤ a) (hm : 0 < m) : ∀ x, ofs (off B a) x < n → m ≤ ofs (off B b) x := by
  intro x hx
  have e := ofs_sub hx ha
  rcases ofs_rebase B x (o := b) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- Frames of a part are frames of the whole. -/
theorem outs_sub {B : Addr} {o S : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Mont.Outs (off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ S) (hS : o + S ≤ 2 ^ 64) (hS0 : 0 < S) : Outside B o S m m' := by
  intro x hx
  refine h x fun r hr' => ?_
  change ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x
  have := hr r hr'
  rcases ofs_rebase B x (o := o) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

theorem out_sub {B : Addr} {o d n S : Nat} {m m' : Mem} (h : Outside (off B o) d n m m')
    (hS : d + n ≤ S) (hS' : o + S ≤ 2 ^ 64) (hS0 : 0 < S) : Outside B o S m m' :=
  outs_sub (rs := [(d, n)]) (fun x hx => h x (hx _ (List.mem_singleton.mpr rfl)))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hS) hS' hS0

/-- Frames of the whole are frames of a part. -/
theorem out_super {B : Addr} {o d n : Nat} {m m' : Mem} (h : Outside B (o + d) n m m') (ho : o < 2 ^ 64) :
    Outside (off B o) d n m m' := by
  intro x hx
  refine h x ?_
  rcases ofs_rebase B x ho with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-- `copyWords`, `w` words from `a` to `b` of the working space (`r15`,
`r14`), apart, with `2 w` in `r11`. -/
theorem copySub_ok {s : State} {B : Addr} {Z a b w : Nat} (hs : Scr s B Z)
    (h15 : s.gpr .r15 = off B a) (h14 : s.gpr .r14 = off B b) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (ha : a + 8 * w ≤ Z) (hb : b + 8 * w ≤ Z)
    (hd : a + 8 * w ≤ b ∨ b + 8 * w ≤ a) :
    WP isa Precompute.copyWords s fun t =>
      ((∀ i < w, word t.mem B (b + 8 * i) = word s.mem B (a + 8 * i)) ∧
        Outside B b (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r15, .r17] s t := by
  have hn := hs.nowrap
  have z : ∀ c, off (off B c) 0 = off B c := fun c => by rw [off_off, Nat.add_zero]
  refine WP.mono (Pub.copyIn_ok (B := off B b) (Z := 8 * w) (P := off B a) (Zp := 8 * w) (dS := 0) (dD := 0)
    (hs.sub hb) (by have := toNat_off_le B a; omega)
    (fun i hi => by rw [off_off]; exact hs.ld (by omega) (by decide))
    (by rw [z]; exact h15) (by rw [z]; exact h14) h11 hw hw' (by omega) (by omega)
    (sep_sub B (by omega) (by omega) hd (by omega))) fun t ⟨⟨_, _, hw, ho⟩, k⟩ =>
      ⟨⟨fun i hi => by have := hw i hi; rwa [word_off, word_off, Nat.zero_add] at this,
        out_sub ho (by omega) (by omega) (by omega)⟩, k⟩

end VG.Proof.Bignum.PPC64LE.Crt
