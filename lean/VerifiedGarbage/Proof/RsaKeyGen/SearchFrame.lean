module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The prime search's public data and its frame, for any 64-bit target

`SearchPublic` is everything two constant-time runs of `vg_rsa_prime_search`
share: the arguments but the octets of `p` and of the tape, `e`, and the
counted candidates the search starts with. The search keeps its working
state in a frame of 20 words at `sp - 160` (`SearchPublic.F`), whose words
while it goes on are `SearchPublic.headers`; `writeFrame` stores words to it.
-/

-- separate module: it names no ISA, for every 64-bit target's prime search

@[expose] public section

namespace VG.Proof.RsaKeyGen.SearchFrame

open VG VG.Proof.Bignum
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

structure SearchPublic where
  op : Addr
  up : Addr
  ep : Addr
  pp : Addr
  rp : Addr
  B : Addr
  stp : Addr
  sp : Addr
  len : Nat
  elen : Nat
  plen : Nat
  randLen : Nat
  Z : Nat
  remaining : Nat
  eB : List Byte

/-- The frame's base. -/
abbrev SearchPublic.F (p : SearchPublic) : Addr := p.sp - BitVec.ofNat 64 160

/-- The frame's region. -/
abbrev SearchPublic.frame (p : SearchPublic) : Region := ⟨p.F, 160⟩

/-- The search from octet `used` of `rand`, with `remaining` counted
candidates left. -/
abbrev SearchPublic.tail (p : SearchPublic) (pB rand : List Byte) (used remaining : Nat) :
    PrimeSearchResult :=
  primeSearch p.len p.eB pB remaining (rand.drop used)

/-- The frame's words while the search goes on (but the request and the
status, which only a finished search has). -/
def SearchPublic.headers (p : SearchPublic) (used remaining : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 remaining), (1, BitVec.ofNat 64 p.len),
    (2, BitVec.ofNat 64 (primeEntropy p.len)),
    (5, p.op), (6, BitVec.ofNat 64 p.len), (7, p.up), (8, p.ep), (9, BitVec.ofNat 64 p.elen),
    (10, p.pp), (11, BitVec.ofNat 64 p.plen), (12, p.rp + BitVec.ofNat 64 used),
    (13, BitVec.ofNat 64 (p.randLen - used)), (14, p.B), (15, BitVec.ofNat 64 (p.Z / 8)),
    (16, BitVec.ofNat 64 used), (18, p.stp)]

theorem SearchPublic.headers_bound (p : SearchPublic) (used remaining : Nat) :
    ∀ e ∈ p.headers used remaining, e.1 < 20 := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

theorem SearchPublic.headers_four (p : SearchPublic) (used remaining : Nat) :
    ∀ e ∈ p.headers used remaining, 4 ≠ e.1 := by
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    dsimp only <;> decide

/-! ## The frame's words -/

/-- Words of the frame with given values. -/
def Slots (m : Mem) (B : Addr) (L : List (Nat × BitVec 64)) : Prop := ∀ p ∈ L, word m B (8 * p.1) = p.2

/-- Stores of words to the frame. -/
def writeFrame (m : Mem) (B : Addr) (values : List (Nat × BitVec 64)) : Mem :=
  values.foldl (fun m e => m.writeW (off B (8 * e.1)) e.2) m

/-- The frame's word `j` after stores of `values`. -/
def frameValue (values : List (Nat × BitVec 64)) (j : Nat) (initial : BitVec 64) : BitVec 64 :=
  values.foldl (fun value e => if j = e.1 then e.2 else value) initial

theorem frameValue_unchanged (values : List (Nat × BitVec 64)) (j : Nat) (initial : BitVec 64)
    (hnot : ∀ e ∈ values, j ≠ e.1) : frameValue values j initial = initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons e values ih =>
    change frameValue values j (if j = e.1 then e.2 else initial) = initial
    rw [ite_eq_right (hnot e (List.mem_cons_self ..))]
    exact ih initial (fun x hx => hnot x (List.mem_cons_of_mem _ hx))

theorem writeFrame_append (m : Mem) (B : Addr) (xs ys : List (Nat × BitVec 64)) :
    writeFrame m B (xs ++ ys) = writeFrame (writeFrame m B xs) B ys := List.foldl_append

theorem frame_store_word (m : Mem) (B : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 20) (hj : j < 20) :
    word (m.writeW (off B (8 * i)) v) B (8 * j) = if j = i then v else word m B (8 * j) := by
  by_cases he : j = i
  · subst he
    rw [ite_eq_left rfl]
    exact word_writeW_self _ _ _ _
  · rw [ite_eq_right he]
    exact hdrStore_hdr _ _ _ (by omega) (by omega) (Ne.symm he)

theorem writeFrame_word (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 20) (j : Nat) (hj : j < 20) :
    word (writeFrame m B values) B (8 * j) = frameValue values j (word m B (8 * j)) := by
  induction values generalizing m with
  | nil => rfl
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    change word (writeFrame (m.writeW (off B (8 * e.1)) e.2) B values) B (8 * j) = _
    rw [ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)), frame_store_word _ _ _ he hj]
    rfl

theorem writeFrame_frame (m : Mem) (B : Addr) (values : List (Nat × BitVec 64))
    (hvalues : ∀ e ∈ values, e.1 < 20) :
    Frame [⟨B, 160⟩] m (writeFrame m B values) := by
  induction values generalizing m with
  | nil => exact Frame.refl _ _
  | cons e values ih =>
    have he := hvalues e (List.mem_cons_self ..)
    have hstore : Frame [⟨B, 160⟩] m (m.writeW (off B (8 * e.1)) e.2) :=
      Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    exact hstore.trans (ih _ (fun x hx => hvalues x (List.mem_cons_of_mem _ hx)))

/-- A read above a store of the frame sees what was there. -/
theorem read_above_store (m : Mem) (B : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 d) v).readW (B + BitVec.ofNat 64 e) 64 = m.readW (B + BitVec.ofNat 64 e) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := e) (n := 8) (e := d) (k := 8) (Or.inr h) he (by omega))
    (by decide)

end VG.Proof.RsaKeyGen.SearchFrame
