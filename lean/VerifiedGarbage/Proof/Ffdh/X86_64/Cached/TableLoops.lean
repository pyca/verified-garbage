module

import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Ffdh.X86_64.Pow
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Ffdh.X86_64.Cached.Table`, which this module and modules that import it used -/

section

/-! # FFDH's context on x86-64: the comb's table

In the inner workspace for `p`, with `R² mod p` in `aR2`: entry 0
(Montgomery one) and entry 1 (`g R mod p`), then for each tooth `d = 2^j` its
entry, `rows` squares of the last, and the entries `d + i` for `0 < i < d`,
products of entry `i` and entry `d` (`table_ok`). Every entry is written to
its row of the context, and read back from there. -/

@[expose] public section

/-! # FFDH's context on x86-64: its rows, to and from the inner workspace

The context is `3 + 34 w` words outside the working space: three public
words, then 34 rows of `w` words (`p`, `R² mod p` and the 32 entries). A
row is copied to or from an array of the inner workspace by `copyWords`,
which changes only the row or the array. -/

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Memory that changes only outside the working space. -/
def OutScr (B : Addr) (Z : Nat) (m m' : Mem) : Prop := ∀ x, ofs B x < Z → m' x = m x

theorem OutScr.word_eq {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {d : Nat} (hd : d + 8 ≤ Z)
    (hn : B.toNat + Z ≤ 2 ^ 64) : Bignum.word m' B d = Bignum.word m B d :=
  Mem.readW_congr fun i hi => h _ (by rw [ofs_off B (d := d) (i := i) (by omega_using [hd, hn, hi])]; omega_using [hd, hi])

/-- The working space at an offset `o`: its words are unchanged too. -/
theorem OutScr.wordAt {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {o d : Nat}
    (hd : o + d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : Bignum.word m' (off B o) d = Bignum.word m (off B o) d := by
  have e : ∀ m : Mem, Bignum.word m (off B o) d = Bignum.word m B (o + d) := fun m => by
    simp only [Bignum.word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e, e]
  exact OutScr.word_eq h (by omega_using [hd]) hn

theorem OutScr.wvAt {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {o d n : Nat}
    (hd : o + d + 8 * n ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : wv m' (off B o) d n = wv m (off B o) d n :=
  wv_congr fun i hi => OutScr.wordAt h (by omega_using [hd, hi]) hn

/-- The working space is as it was, so is the inner workspace's context. -/
theorem SubCtx.of_outScr {s t : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64}
    (h : SubCtx s B Z o w wx mi) (hm : OutScr B Z s.mem t.mem) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx mi := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hlo := h.lo
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have h8w := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hT : 0 ≤ tabBytes wx := Nat.zero_le _
  have hw : ∀ i < 32, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    OutScr.wordAt hm (by have := hdr_lt_slot wx 8 hi'; omega_using [hi, this]) hn
  have hw0 : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    OutScr.word_eq hm (by have := hdr_lt_slot w 8 hi'; omega_using [hi, h8, hi']) hn
  refine ⟨⟨?_, h.scr.nowrap⟩, by rw [hdi]; exact h.rdi, ⟨?_, ?_, fun j hj => ?_⟩, ?_, ?_, fun j hj => ?_,
    h.lo, h.hi⟩
  · rw [hwr]; exact h.scr.wr
  · rw [hw _ (by decide)]; exact h.hdr.hw
  · rw [hw _ (by decide)]; exact h.hdr.hminv
  · rw [hw _ (by unfold sArr; omega_using [hj])]; exact h.hdr.harr j hj
  · rw [hw _ (by decide)]; exact h.link
  · rw [hw0 _ (by decide)]; exact h.nw
  · rw [hw0 _ (by unfold sArr; omega_using [hj])]; exact h.narr j hj

/-- The context's `n` words at `cp`: writable, outside the working space. -/
structure CtxRegion (s : State) (B : Addr) (Z : Nat) (cp : Addr) (n : Nat) : Prop where
  wr : ∀ i < n, InRegions s.wr (off cp (8 * i)) 8
  rd : ∀ i < n, InRegions (s.rd ++ s.wr) (off cp (8 * i)) 8
  sep : ∀ i < 8 * n, Z ≤ ofs B (cp + BitVec.ofNat 64 i)
  nowrap : cp.toNat + 8 * n ≤ 2 ^ 64

theorem CtxRegion.congr {s t : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRegion s B Z cp n)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxRegion t B Z cp n :=
  ⟨fun i hi => by rw [hwr]; exact h.wr i hi, fun i hi => by rw [hrd, hwr]; exact h.rd i hi, h.sep, h.nowrap⟩

/-- A byte of the working space is past the context's `8 n` bytes. -/
theorem CtxRegion.apart {s : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRegion s B Z cp n)
    {x : Addr} (hx : ofs B x < Z) : 8 * n ≤ ofs cp x :=
  le_ofs_of_sep h.sep hx

/-- A byte of the context is past the working space. -/
theorem CtxRegion.out {s : State} {B : Addr} {Z : Nat} {cp : Addr} {n : Nat} (h : CtxRegion s B Z cp n)
    {d : Nat} (hd : d < 8 * n) : Z ≤ ofs B (off cp d) := by
  have := h.sep d hd
  simpa [off] using this

/-- The words of row `j`. -/
def row (m : Mem) (cp : Addr) (w j : Nat) : List (BitVec 64) :=
  (List.range w).map fun i => word m cp (24 + 8 * w * j + 8 * i)

theorem row_congr {m m' : Mem} {cp : Addr} {w j : Nat}
    (h : ∀ i < w, word m' cp (24 + 8 * w * j + 8 * i) = word m cp (24 + 8 * w * j + 8 * i)) :
    row m' cp w j = row m cp w j := by
  unfold row
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A row outside the bytes that changed. -/
theorem row_outside {m m' : Mem} {cp : Addr} {w j o n : Nat} (h : Outside cp o n m m')
    (hj : 24 + 8 * w * j + 8 * w ≤ o ∨ o + n ≤ 24 + 8 * w * j) (hn : 24 + 8 * w * (j + 1) ≤ 2 ^ 64) :
    row m' cp w j = row m cp w j :=
  row_congr fun i hi => h.word (by rw [Nat.mul_add] at hn; omega_using [hj, hi]) (by rw [Nat.mul_add] at hn; omega_using [hn, hi])

/-- A row copied from `w` words of value `V`. -/
theorem row_of_words {m m' : Mem} {cp S : Addr} {w j e : Nat}
    (h : ∀ i < w, word m' cp (24 + 8 * w * j + 8 * i) = word m S (e + 8 * i)) :
    row m' cp w j = Spec.Rsa.toWords (wv m S e w) w := by
  unfold row Spec.Rsa.toWords
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]
  exact word_eq_ofNat m S e w (List.mem_range.mp hi)

/-- The value of a row that holds `toWords V w`, for `V < 2^(64 w)`. -/
theorem row_word {m : Mem} {cp : Addr} {w j V : Nat} (h : row m cp w j = Spec.Rsa.toWords V w)
    {i : Nat} (hi : i < w) : word m cp (24 + 8 * w * j + 8 * i) = BitVec.ofNat 64 (V / 2 ^ (64 * i)) := by
  have := congrArg (fun l => l[i]?) h
  simp only [row, Spec.Rsa.toWords, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at this
  exact this

theorem rowAddr (cp : Addr) (j wx : Nat) :
    (BitVec.ofNat 64 j * BitVec.ofNat 64 wx) <<< 3 + cp + BitVec.signExtend 64 (24 : BitVec 32) =
      off cp (24 + 8 * wx * j) := by
  have e : BitVec.signExtend 64 (24 : BitVec 32) = BitVec.ofNat 64 24 := by decide
  rw [e, BitVec.shiftLeft_eq_mul_twoPow]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow]
  simp only [Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
  congr 1
  ring_nf

theorem imul_low (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

/-- `rbx := ` row `j`'s first word, `r12 := w`. -/
theorem rowPtr_ok {s : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {cp : Addr} {j : Nat}
    (hc : SubCtx s B Z o w wx mi) (hctx : word s.mem (off B o) (8 * iCtx) = cp)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block rowPtr) s fun t => t.gpr .rbx = off cp (24 + 8 * wx * j) ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.mem = s.mem ∧ Keep [.rbx, .r12] s t := by
  have hg := hc.good
  have hW := hdr_lt_slot wx 8 (show sW < 32 by decide)
  have hC := hdr_lt_slot wx 8 (show iCtx < 32 by decide)
  refine WP.mono (WP.keep [.rbx, .r12] (Q := fun t => t.gpr .rbx = off cp (24 + 8 * wx * j) ∧
      t.gpr .r12 = BitVec.ofNat 64 wx ∧ t.mem = s.mem) (by
    unfold rowPtr
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sW) (by omega_using [hW]),
      hg.scr.ld (d := 8 * iCtx) (by omega_using [hC]), hg.hdr.hw, hctx, hax, execImul, imul_low]
    exact rowAddr cp j wx) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩

/-- The value of a row that holds `toWords V w`, for `V < 2^(64 w)`. -/
theorem wv_of_row {m : Mem} {cp : Addr} {w j V : Nat} (h : row m cp w j = Spec.Rsa.toWords V w)
    (hV : V < 2 ^ (64 * w)) : wv m cp (24 + 8 * w * j) w = V := by
  rw [← Nat.mod_eq_of_lt hV]
  refine wv_of_words fun i hi => ?_
  rw [row_word h hi, BitVec.toNat_ofNat]

/-- The address of word `i` of row `j`, as a word of the context. -/
theorem rowOff {w j i : Nat} : 24 + 8 * w * j + 8 * i = 8 * (3 + w * j + i) := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc]

/-- Array `a`'s `w` words to row `j`, changing only the row. -/
theorem storeRow_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {n j a : Nat}
    (hc : SubCtx s B Z o w w mi) (hctx : word s.mem (off B o) (8 * iCtx) = cp)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (ha : a < 8) (hR : CtxRegion s B Z cp n)
    (hj : 3 + w * (j + 1) ≤ n) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) :
    WP isa (storeRow a) s fun t =>
      row t.mem cp w j = Spec.Rsa.toWords (wv s.mem (off B o) (slot w a) w) w ∧
      Outside cp (24 + 8 * w * j) (8 * w) s.mem t.mem ∧ OutScr B Z s.mem t.mem ∧
      Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hg := hc.good
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hA := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega_using [ha])
  have hsa := slot_le (w := w) ha
  have hcn := hR.nowrap
  have e8 : 8 * w * j = 8 * (w * j) := Nat.mul_assoc _ _ _
  unfold storeRow
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok hc hctx hax) fun s₁ ⟨hbx, h12, hm₁, k₁⟩ => ?_
  have hg₁ : Good s₁ (off B o) (slot w 8) w mi :=
    ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off (off B o) (slot w a) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * sArr a) (by omega_using [hA]), hg₁.hdr.harr a ha]) rfl)
    fun s₂ ⟨⟨hsi, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (copyWords_ok hsi ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h12) hw
    (by omega_using [hw']) (by rw [Nat.mul_add] at hj; omega_using [hj, hcn, e8])
    (fun i hi' => by rw [k12.2.1, k12.2.2]; exact hg.scr.ld (by omega_using [hsa, hi']))
    (fun i hi' => by rw [k12.2.2, rowOff]; exact hR.wr _ (by rw [Nat.mul_add] at hj; omega_using [hj, hi']))
    (fun i hi' b hb => Or.inr (by
      have hx : ofs B (off (off B o) (slot w a + 8 * i) + BitVec.ofNat 64 b) < Z := by
        rw [show off (off B o) (slot w a + 8 * i) = off B (o + (slot w a + 8 * i)) by
          simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat], ofs_off B (by omega_using [hn, hi, hsa, hi', hb])]
        omega_using [hi, hsa, hi', hb]
      have := hR.apart hx
      rw [Nat.mul_add] at hj
      omega_using [hj, e8, this])))
    fun t ⟨_, hd, ho, k₃⟩ => ?_
  rw [hm₂, hm₁] at hd ho
  have hsep : ∀ x, ofs B x < Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hR.apart hx; rw [Nat.mul_add] at hj; omega_using [hj, e8, this]))
  exact ⟨row_of_words hd, ho, hsep, (k12.trans k₃).mono (by decide)⟩

/-- Row `j`, of value `V`, to array `a`'s `w` words, changing only those. -/
theorem loadRow_ok {s : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {cp : Addr} {n j a V : Nat}
    (hc : SubCtx s B Z o w w mi) (hctx : word s.mem (off B o) (8 * iCtx) = cp)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (ha : a < 8) (hR : CtxRegion s B Z cp n)
    (hj : 3 + w * (j + 1) ≤ n) (hw : 1 ≤ w) (hw' : w < 2 ^ 28)
    (hrow : row s.mem cp w j = Spec.Rsa.toWords V w) (hV : V < 2 ^ (64 * w)) :
    WP isa (loadRow a) s fun t =>
      wv t.mem (off B o) (slot w a) w = V ∧ Outside (off B o) (slot w a) (8 * w) s.mem t.mem ∧
      Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hg := hc.good
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have hA := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega_using [ha])
  have hsa := slot_le (w := w) ha
  have hcn := hR.nowrap
  have e8 : 8 * w * j = 8 * (w * j) := Nat.mul_assoc _ _ _
  unfold loadRow
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok hc hctx hax) fun s₁ ⟨hbx, h12, hm₁, k₁⟩ => ?_
  have hg₁ : Good s₁ (off B o) (slot w 8) w mi :=
    ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = off cp (24 + 8 * w * j) ∧
      t.gpr .rbx = off (off B o) (slot w a) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hbx, hg₁.scr.ld (d := 8 * sArr a) (by omega_using [hA]),
      hg₁.hdr.harr a ha]) rfl)
    fun s₂ ⟨⟨hsi, hbx₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (copyWords_ok hsi hbx₂ ((k₂.gpr (by decide)).trans h12) hw
    (by omega_using [hw']) (by omega_using [hn, hi, hsa])
    (fun i hi' => by rw [k12.2.1, k12.2.2, rowOff]; exact hR.rd _ (by rw [Nat.mul_add] at hj; omega_using [hj, hi']))
    (fun i hi' => by rw [k12.2.2]; exact hg.scr.st (by omega_using [hsa, hi']))
    (fun i hi' b hb => Or.inr (by
      have hx : 8 * n ≤ 24 + 8 * w * j + 8 * i + b → False := fun h => by
        rw [Nat.mul_add] at hj; omega_using [hctx, hax, ha, hj, hw, hw', hV, hn, hi, hA, hsa, hcn, e8, hbx, h12, hsi, hbx₂, hi', hb, h]
      have hb' : 24 + 8 * w * j + 8 * i + b < 8 * n := by rw [Nat.mul_add] at hj; omega_using [hj, e8, hi', hb]
      have := hR.out (d := 24 + 8 * w * j + 8 * i + b) hb'
      rw [show off cp (24 + 8 * w * j + 8 * i + b) =
          off cp (24 + 8 * w * j + 8 * i) + BitVec.ofNat 64 b by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
      rcases ofs_rebase B (off cp (24 + 8 * w * j + 8 * i) + BitVec.ofNat 64 b) (o := o) (by omega_using [hn, hi, hA])
        with ⟨_, e⟩ | ⟨h, _⟩
      · rw [e]; omega_using [hi, hsa, this]
      · omega_arith
)))
    fun t ⟨hv, _, ho, k₃⟩ => ?_
  rw [hm₂, hm₁] at hv ho
  refine ⟨hv.trans (wv_of_row hrow hV), ho, (k12.trans k₃).mono (by decide)⟩

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp), flatMap_congr' (fun x hx => h x (by simp [hx]))]

theorem range_mul_map {α : Type} (g : Nat → α) (w : Nat) : ∀ n,
    (List.range (w * n)).map g = (List.range n).flatMap fun j => (List.range w).map fun i => g (w * j + i)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.mul_succ, List.range_add, List.map_append, range_mul_map g w n, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.map_map]
    rfl

/-- The context's words: its three public words, then its 34 rows. -/
theorem wordsAt_rows (m : Mem) (cp : Addr) (w : Nat) :
    Spec.Rsa.wordsAt m cp (3 + 34 * w) =
      [word m cp 0, word m cp 8, word m cp 16] ++ (List.range 34).flatMap (row m cp w) := by
  unfold Spec.Rsa.wordsAt
  rw [List.range_add, List.map_append, show 34 * w = w * 34 from Nat.mul_comm _ _, List.map_map,
    range_mul_map _ w 34]
  have h3 : (List.range 3).map (fun i => m.readW (cp + BitVec.ofNat 64 (8 * i)) 64) =
      [word m cp 0, word m cp 8, word m cp 16] := rfl
  rw [h3]
  refine congrArg (_ ++ ·) (flatMap_congr' fun j _ => List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, Bignum.word, off]
  rw [rowOff, show 3 + (w * j + i) = 3 + w * j + i by omega_using []]

/-- The context's words from its parts. -/
theorem ctx_words {m : Mem} {cp : Addr} {w : Nat} {h₀ h₁ h₂ : BitVec 64} {r₀ r₁ : List (BitVec 64)}
    {ent : Nat → List (BitVec 64)} (e₀ : word m cp 0 = h₀) (e₁ : word m cp 8 = h₁) (e₂ : word m cp 16 = h₂)
    (f₀ : row m cp w 0 = r₀) (f₁ : row m cp w 1 = r₁) (fe : ∀ a < 32, row m cp w (2 + a) = ent a) :
    Spec.Rsa.wordsAt m cp (3 + 34 * w) = [h₀, h₁, h₂] ++ r₀ ++ r₁ ++ (List.range 32).flatMap ent := by
  rw [wordsAt_rows, e₀, e₁, e₂, show 34 = 2 + 32 from rfl, List.range_add, List.flatMap_append,
    show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, f₀, f₁,
    List.flatMap_map]
  simp only [List.append_nil, List.append_assoc]
  congr 3
  apply flatMap_congr'
  intro a ha
  exact fe a (List.mem_range.mp ha)

end VG.Proof.Ffdh.X86_64.Cached

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

/-- The table stage's public data: the working space, the inner
workspace's offset, the context and the comb's parameters. -/
structure TabP where
  B : Addr
  Z : Nat
  o : Nat
  w : Nat
  mi : BitVec 64
  cp : Addr
  P : Nat
  G : Nat
  bits : Nat

abbrev TabP.R (T : TabP) : Nat := 2 ^ (64 * T.w)
abbrev TabP.rows (T : TabP) : Nat := Spec.Rsa.FixedBaseComb.rows T.bits
abbrev TabP.n (T : TabP) : Nat := 3 + 34 * T.w

/-- `g^E R mod p`, in Montgomery form. -/
def TabP.M (T : TabP) (E : Nat) : Nat := Spec.Rsa.powMod T.G E T.P * T.R % T.P

/-- Entry `a`. -/
def TabP.entry (T : TabP) (a : Nat) : Nat := T.M (Spec.Rsa.FixedBaseComb.exponent T.bits a)

/-- What every step keeps: the inner workspace for `p`, the context's
pointer and row count in its header, and the context. -/
structure Env (T : TabP) (s : State) : Prop where
  mc : ModCtx s T.B T.Z T.o T.w T.mi T.P
  ctx : word s.mem (off T.B T.o) (8 * iCtx) = T.cp
  rows : word s.mem (off T.B T.o) (8 * iRows) = BitVec.ofNat 64 T.rows
  reg : CtxRegion s T.B T.Z T.cp T.n

/-- Memory outside the working space and the context is unchanged. -/
def Only (T : TabP) (m m' : Mem) : Prop := ∀ x, T.Z ≤ ofs T.B x → 8 * T.n ≤ ofs T.cp x → m' x = m x

theorem Only.refl (T : TabP) (m : Mem) : Only T m m := fun _ _ _ => rfl

theorem Only.trans {T : TabP} {m₁ m₂ m₃ : Mem} (h₁ : Only T m₁ m₂) (h₂ : Only T m₂ m₃) : Only T m₁ m₃ :=
  fun x hx hc => (h₂ x hx hc).trans (h₁ x hx hc)

/-- The ranges a step may change in the inner workspace: the counters and the
arrays but `aN`, `aR2` and `aOne`. -/
def innerR (w : Nat) : List (Nat × Nat) :=
  [(8 * 17, 8 * 15), (slot w aX, 3 * (8 * (w + 2))), (slot w aXm, 2 * (8 * (w + 2)))]

theorem innerR_ok (w : Nat) : ∀ r ∈ innerR w, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot w 8 ∧
    (r.1 + r.2 ≤ slot w aN ∨ slot w aN + 8 * (w + 2) ≤ r.1) ∧
    (r.1 + r.2 ≤ slot w aOne ∨ slot w aOne + 8 * (w + 2) ≤ r.1) ∧
    (r.1 + r.2 ≤ slot w aR2 ∨ slot w aR2 + 8 * (w + 2) ≤ r.1) := by
  intro r hr
  simp only [innerR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only [slot, hdrBytes, aX, aXm, aN, aOne, aR2] <;> omega_using []

/-- `ModCtx` after a change of only `innerR`. -/
theorem _root_.VG.Proof.Ffdh.X86_64.ModCtx.of_inner {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (h : ModCtx s B Z o w mi X) (hf : Frm (off B o) (innerR w) s.mem t.mem) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : ModCtx t B Z o w mi X := by
  have hGn := h.sub.good.scr.nowrap
  have sR := slot_le (w := w) (show aR2 < 8 by decide)
  have eR : wv t.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    hf.wv_eq (fun r hr => by have := (innerR_ok w r hr).2.2.2.2; omega_using [this]) (by omega_using [hGn, sR])
  exact ⟨h.sub.of_frm hf (fun r hr => ⟨(innerR_ok w r hr).1, (innerR_ok w r hr).2.1⟩) hwr hdi,
    h.xv.of_frmA hGn (by have := h.w2; omega_using [this]) hf (fun r hr => ⟨(innerR_ok w r hr).2.2.1, (innerR_ok w r hr).2.2.2.1⟩),
    by rw [eR]; exact h.r2l, by rw [eR]; exact h.r2, h.odd, h.x1, h.wide, h.w2, h.w28⟩

/-- A frame of fewer bytes. -/
theorem Frm.cover {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := fun x hx =>
  h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hc r hr
    have := hx r' hr'
    omega_using [h1, h2, this]

/-- `ModCtx` when the working space is unchanged. -/
theorem _root_.VG.Proof.Ffdh.X86_64.ModCtx.of_outScr {s t : State} {B : Addr} {Z o w : Nat} {mi : BitVec 64} {X : Nat}
    (h : ModCtx s B Z o w mi X) (hm : OutScr B Z s.mem t.mem) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : ModCtx t B Z o w mi X := by
  have hn := h.sub.scr.nowrap
  have hi := h.sub.hi
  have sN := slot_le (w := w) (show aN < 8 by decide)
  have sO := slot_le (w := w) (show aOne < 8 by decide)
  have sR := slot_le (w := w) (show aR2 < 8 by decide)
  have eR : wv t.mem (off B o) (slot w aR2) w = wv s.mem (off B o) (slot w aR2) w :=
    OutScr.wvAt hm (by omega_using [hi, sR]) hn
  refine ⟨SubCtx.of_outScr h.sub hm hwr hdi, ⟨?_, ?_, ?_⟩, by rw [eR]; exact h.r2l, by rw [eR]; exact h.r2, h.odd, h.x1,
    h.wide, h.w2, h.w28⟩
  · rw [OutScr.wvAt hm (by omega_using [hi, sN]) hn]; exact h.xv.n
  · rw [OutScr.wordAt hm (by have := h.w2; omega_using [hi, sN]) hn]; exact h.xv.inv
  · rw [OutScr.wvAt hm (by omega_using [hi, sO]) hn]; exact h.xv.one

theorem Env.of_outScr {T : TabP} {s t : State} (h : Env T s) (hm : OutScr T.B T.Z s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) : Env T t := by
  have hn := h.mc.sub.scr.nowrap
  have hi := h.mc.sub.hi
  have h8 := hdr_lt_slot T.w 8 (show 31 < 32 by decide)
  exact ⟨h.mc.of_outScr hm hwr hdi, by rw [OutScr.wordAt hm (by unfold iCtx sFn; omega_using [hi, h8]) hn]; exact h.ctx,
    by rw [OutScr.wordAt hm (by unfold iRows sFn; omega_using [hi, h8]) hn]; exact h.rows, h.reg.congr hrd hwr⟩

/-- A change of only `innerR`, inside the working space. -/
theorem Env.of_inner {T : TabP} {s t : State} (h : Env T s) (hf : Frm (off T.B T.o) (innerR T.w) s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi)
    (hc : word t.mem (off T.B T.o) (8 * iCtx) = word s.mem (off T.B T.o) (8 * iCtx))
    (hr : word t.mem (off T.B T.o) (8 * iRows) = word s.mem (off T.B T.o) (8 * iRows)) : Env T t :=
  ⟨h.mc.of_inner hf hwr hdi, by rw [hc]; exact h.ctx, by rw [hr]; exact h.rows, h.reg.congr hrd hwr⟩

/-- A change of the inner workspace (below `slot w 8`) is inside the working space. -/
theorem inScr_of_inner {T : TabP} {s t : State} (h : Env T s) {rs : List (Nat × Nat)}
    (hf : Frm (off T.B T.o) rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ slot T.w 8) :
    InScr T.B T.Z s.mem t.mem ∧ (∀ i < 32, word t.mem T.B (8 * i) = word s.mem T.B (8 * i)) := by
  obtain ⟨h1, h2⟩ := VG.Proof.Ffdh.X86_64.child_frm h.mc.sub h.mc.wide hf
    (fun r hr' => by have := hr r hr'; unfold tabBytes; omega_using [this])
  exact ⟨h2, h1⟩

/-- A row is unchanged by a change inside the working space. -/
theorem row_of_inScr {T : TabP} {s t : State} (h : Env T s) (hm : InScr T.B T.Z s.mem t.mem) {j : Nat}
    (hj : 3 + T.w * (j + 1) ≤ T.n) : row t.mem T.cp T.w j = row s.mem T.cp T.w j :=
  row_congr fun i hi => Mem.readW_congr fun b hb => hm _ (by
    have e : off T.cp (24 + 8 * T.w * j + 8 * i) + BitVec.ofNat 64 b = off T.cp (24 + 8 * T.w * j + 8 * i + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    have e8 : 8 * T.w * j = 8 * (T.w * j) := Nat.mul_assoc _ _ _
    exact h.reg.out (by rw [Nat.mul_add] at hj; omega_using [hj, hi, hb, e8]))

/-- A word of the context is unchanged by a change inside the working space. -/
theorem ctxWord_of_inScr {T : TabP} {s t : State} (h : Env T s) (hm : InScr T.B T.Z s.mem t.mem) {i : Nat}
    (hi : i < T.n) : word t.mem T.cp (8 * i) = word s.mem T.cp (8 * i) :=
  Mem.readW_congr fun b hb => hm _ (by
    have e : off T.cp (8 * i) + BitVec.ofNat 64 b = off T.cp (8 * i + b) := by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [e]
    exact h.reg.out (by omega_using [hi, hb]))

theorem Only.of_inScr {T : TabP} {m m' : Mem} (h : InScr T.B T.Z m m') : Only T m m' :=
  fun x hx _ => h x hx

theorem Only.of_outScr_outside {T : TabP} {s : State} {m' : Mem} {o n : Nat}
    (h : Outside T.cp o n s.mem m') (hn : o + n ≤ 8 * T.n) : Only T s.mem m' :=
  fun x _ hc => h x (Or.inr (by omega_using [hn, hc]))

/-- The ranges of `mm`'s writes are in `innerR`. -/
theorem mm_cover (w : Nat) {out : Nat} (ho : out = aX ∨ out = aXm ∨ out = aY) :
    ∀ r ∈ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w out, 8 * (w + 2))],
      ∃ r' ∈ innerR w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aX, aAcc]; omega_using [],
      by simp only [slot, aX, aAcc]; omega_using []⟩
  · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aX, aTmp]; omega_using [],
      by simp only [slot, aX, aTmp]; omega_using []⟩
  · rcases ho with rfl | rfl | rfl
    · exact ⟨(slot w aX, 3 * (8 * (w + 2))), by simp [innerR], by simp only [slot]; omega_using [],
        by simp only [slot]; omega_using []⟩
    · exact ⟨(slot w aXm, 2 * (8 * (w + 2))), by simp [innerR], by simp only [slot]; omega_using [],
        by simp only [slot]; omega_using []⟩
    · exact ⟨(slot w aXm, 2 * (8 * (w + 2))), by simp [innerR], by simp only [slot, aXm, aY]; omega_using [],
        by simp only [slot, aXm, aY]; omega_using []⟩

/-- What a step keeps outside the inner workspace and the context. -/
structure Kept (T : TabP) (s t : State) : Prop where
  only : Only T s.mem t.mem
  outer : ∀ i < 32, word t.mem T.B (8 * i) = word s.mem T.B (8 * i)
  hdr : ∀ i < 3, word t.mem T.cp (8 * i) = word s.mem T.cp (8 * i)

theorem Kept.refl (T : TabP) (s : State) : Kept T s s :=
  ⟨Only.refl _ _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Kept.trans {T : TabP} {s t u : State} (h₁ : Kept T s t) (h₂ : Kept T t u) : Kept T s u :=
  ⟨h₁.only.trans h₂.only, fun i hi => (h₂.outer i hi).trans (h₁.outer i hi),
    fun i hi => (h₂.hdr i hi).trans (h₁.hdr i hi)⟩

/-- Montgomery multiplication in the table's environment. -/
theorem mm_env (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {out a b : Nat}
    (ho : out = aX ∨ out = aXm ∨ out = aY) (ha : a < 8) (hb : b < 8) (ha₁ : a ≠ aAcc) (ha₂ : a ≠ aTmp)
    (hb₁ : b ≠ aAcc) (hb₂ : b ≠ aTmp)
    (hbl : wv s.mem (off T.B T.o) (slot T.w b) T.w < T.P) :
    WP isa (Mo.mm out a b) s fun t => Env T t ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w < T.P ∧
      wv t.mem (off T.B T.o) (slot T.w out) T.w * T.R % T.P =
        wv s.mem (off T.B T.o) (slot T.w a) T.w * wv s.mem (off T.B T.o) (slot T.w b) T.w % T.P ∧
      Arrays (off T.B T.o) T.w [aAcc, aTmp, out] s.mem t.mem ∧
      (∀ j, 3 + T.w * (j + 1) ≤ T.n → row t.mem T.cp T.w j = row s.mem T.cp T.w j) ∧
      (∀ i, 17 ≤ i → i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)) ∧
      Kept T s t ∧ Keep mmRegs s t := by
  have hc := he.mc
  have hw2 := hc.w2
  have hw28 := hc.w28
  have hGn := hc.sub.good.scr.nowrap
  have hout : out < 8 := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₁ : out ≠ aAcc := by rcases ho with rfl | rfl | rfl <;> decide
  have ho₂ : out ≠ aTmp := by rcases ho with rfl | rfl | rfl <;> decide
  refine WP.mono (Mo.mm_ok hc.sub.good (Nat.le_refl _) (by omega_using [hw2]) (by omega_using [hw28]) hout ha hb ho₁ ho₂ ha₁ hb₁
    hc.xv.inv (by rw [hc.xv.n]; exact hbl) ha₂ hb₂) fun t ⟨_, hl, hv, ha', k⟩ => ?_
  rw [hc.xv.n] at hl hv
  have hf : Frm (off T.B T.o) [(slot T.w aAcc, 8 * (T.w + 2)), (slot T.w aTmp, 8 * (T.w + 2)),
      (slot T.w out, 8 * (T.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  have hrng : ∀ r ∈ [(slot T.w aAcc, 8 * (T.w + 2)), (slot T.w aTmp, 8 * (T.w + 2)),
      (slot T.w out, 8 * (T.w + 2))], r.1 + r.2 ≤ slot T.w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact slot_le hout
  obtain ⟨hin, hout'⟩ := inScr_of_inner he hf hrng
  have hd : ∀ i, 17 ≤ i → i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i) :=
    fun i _ h2 => hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl (hdr_lt_slot T.w aAcc h2)
      · exact Or.inl (hdr_lt_slot T.w aTmp h2)
      · exact Or.inl (hdr_lt_slot T.w out h2))
      (by have := hdr_lt_slot T.w 8 (show i < 32 from h2); omega_using [h2])
  refine ⟨he.of_inner (Frm.cover hf (mm_cover T.w ho)) k.2.1 k.2.2 (k.gpr (by decide))
      (hd _ (by decide) (by decide)) (hd _ (by decide) (by decide)), hl, hv, ha',
    fun j hj => row_of_inScr he hin hj, hd, ⟨Only.of_inScr hin, hout', fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega_using [hi])⟩,
    k⟩

/-- A row of the context in its environment. -/
abbrev RowFits (T : TabP) (j : Nat) : Prop := 3 + T.w * (j + 1) ≤ T.n

/-- Array `a` to row `j` in the table's environment. -/
theorem store_env {T : TabP} {s : State} (he : Env T s) {j a : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (ha : a < 8) (hj : j < 34) :
    WP isa (storeRow a) s fun t => Env T t ∧
      row t.mem T.cp T.w j = Spec.Rsa.toWords (wv s.mem (off T.B T.o) (slot T.w a) T.w) T.w ∧
      (∀ j', j' ≠ j → RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      OutScr T.B T.Z s.mem t.mem ∧ Kept T s t ∧ Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hc := he.mc
  have hn := hc.sub.scr.nowrap
  have hcn := he.reg.nowrap
  have hfit : 3 + T.w * (j + 1) ≤ T.n := by
    unfold TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega_using [hj]); omega_using [this]
  refine WP.mono (storeRow_ok hc.sub he.ctx hax ha he.reg hfit (by have := hc.w2; omega_using [this]) hc.w28)
    fun t ⟨hrow, ho, hos, k⟩ => ?_
  have e8 : 8 * T.w * j = 8 * (T.w * j) := Nat.mul_assoc _ _ _
  refine ⟨he.of_outScr hos k.2.1 k.2.2 (k.gpr (by decide)), hrow, fun j' hne hj' => ?_, hos,
    ⟨Only.of_outScr_outside ho (by unfold TabP.n at hfit ⊢; rw [Nat.mul_add] at hfit; omega_using [hfit, e8]),
      fun i hi => OutScr.word_eq hos (by have := hdr_lt_slot T.w 8 hi; have := hc.sub.lo; have := hc.sub.hi; omega_arith) hn,
      fun i hi => ho.word (by omega_using [hi]) (by omega_using [hi])⟩, k⟩
  have e8' : 8 * T.w * j' = 8 * (T.w * j') := Nat.mul_assoc _ _ _
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : T.w * (j' + 1) ≤ T.w * j := Nat.mul_le_mul_left _ (by omega_using [h])
    exact row_outside ho (Or.inl (by rw [Nat.mul_add] at this; omega_using [e8, e8', this])) (by unfold RowFits TabP.n at hj'; unfold TabP.n at hcn; have : 8 * T.w * (j' + 1) = 8 * (T.w * (j' + 1)) := Nat.mul_assoc _ _ _; omega_using [hcn, hj', this])
  · have : T.w * (j + 1) ≤ T.w * j' := Nat.mul_le_mul_left _ (by omega_using [h])
    exact row_outside ho (Or.inr (by rw [Nat.mul_add] at this; omega_using [e8, e8', this])) (by unfold RowFits TabP.n at hj'; unfold TabP.n at hcn; have : 8 * T.w * (j' + 1) = 8 * (T.w * (j' + 1)) := Nat.mul_assoc _ _ _; omega_using [hcn, hj', this])

/-- Row `j`, of value `V`, to array `a` in the table's environment. -/
theorem load_env {T : TabP} {s : State} (he : Env T s) {j a V : Nat} (hax : s.gpr .rax = BitVec.ofNat 64 j)
    (ha : a = aX ∨ a = aXm ∨ a = aY) (hj : j < 34) (hrow : row s.mem T.cp T.w j = Spec.Rsa.toWords V T.w)
    (hV : V < 2 ^ (64 * T.w)) :
    WP isa (loadRow a) s fun t => Env T t ∧ wv t.mem (off T.B T.o) (slot T.w a) T.w = V ∧
      (∀ b < 8, b ≠ a → wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      (∀ i, i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)) ∧
      Kept T s t ∧ Keep [.rax, .r14, .rbx, .r12, .rsi] s t := by
  have hc := he.mc
  have hn := hc.sub.scr.nowrap
  have hGn := hc.sub.good.scr.nowrap
  have ha8 : a < 8 := by rcases ha with rfl | rfl | rfl <;> decide
  have hsa := slot_le (w := T.w) ha8
  have hfit : 3 + T.w * (j + 1) ≤ T.n := by
    unfold TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega_using [hj]); omega_using [this]
  refine WP.mono (loadRow_ok hc.sub he.ctx hax ha8 he.reg hfit (by have := hc.w2; omega_using [this]) hc.w28 hrow hV)
    fun t ⟨hv, ho, k⟩ => ?_
  have hf : Frm (off T.B T.o) [(slot T.w a, 8 * (T.w + 2))] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot T.w a) (n' := 8 * (T.w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  obtain ⟨hin, hout⟩ := inScr_of_inner he hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsa)
  have hd : ∀ i, i < 32 → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i) :=
    fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot T.w a hi))
      (by have := hdr_lt_slot T.w 8 hi; omega_using [hi])
  have hcov : ∀ r ∈ [(slot T.w a, 8 * (T.w + 2))], ∃ r' ∈ innerR T.w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
    intro r hr
    rw [List.mem_singleton.mp hr]
    rcases ha with rfl | rfl | rfl
    · exact ⟨(slot T.w aX, 3 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot]; omega_using [],
        by simp only [slot]; omega_using []⟩
    · exact ⟨(slot T.w aXm, 2 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot]; omega_using [],
        by simp only [slot]; omega_using []⟩
    · exact ⟨(slot T.w aXm, 2 * (8 * (T.w + 2))), by simp [innerR], by simp only [slot, aXm, aY]; omega_using [],
        by simp only [slot, aXm, aY]; omega_using []⟩
  refine ⟨he.of_inner (Frm.cover hf hcov) k.2.1 k.2.2 (k.gpr (by decide)) (hd _ (by decide)) (hd _ (by decide)),
    hv, fun b hb hne => hf.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := slot_sep (w := T.w) hne; simp only; omega_using [this])
      (by have := slot_le (w := T.w) hb; omega_using [hGn, this]),
    fun j' hj' => row_of_inScr he hin hj', hd,
    ⟨Only.of_inScr hin, hout, fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega_using [hi])⟩, k⟩

/-- A store to an inner counter slot (not the context's pointer or row count). -/
theorem slot_env {T : TabP} {s : State} (he : Env T s) {i : Nat} (hi : 19 ≤ i) (hi' : i < 32) {t : State}
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) v) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = s.gpr .rdi) :
    Env T t ∧ word t.mem (off T.B T.o) (8 * i) = v ∧
      (∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i')) ∧
      (∀ b < 8, wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t := by
  have hc := he.mc
  have hGn := hc.sub.good.scr.nowrap
  have ho := writeW_outside s.mem (off T.B T.o) (d := 8 * i) v (by omega_using [hi'])
  rw [← hm] at ho
  have hf : Frm (off T.B T.o) [(8 * i, 8)] s.mem t.mem := Frm.of_outside ho (by simp)
  obtain ⟨hin, hout⟩ := inScr_of_inner he hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := hdr_lt_slot T.w 0 hi'; simp only [slot] at this ⊢; omega_using [this])
  have hcov : ∀ r ∈ [(8 * i, 8)], ∃ r' ∈ innerR T.w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := by
    intro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨(8 * 17, 8 * 15), by simp [innerR], by simp only; omega_using [hi], by simp only; omega_using [hi']⟩
  have hd : ∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i') :=
    fun i' h1 h2 => ho.word (by omega_using [h2]) (by have := hdr_lt_slot T.w 8 h1; omega_using [h1])
  refine ⟨he.of_inner (Frm.cover hf hcov) hrd hwr hdi (hd _ (by decide) (by unfold iCtx sFn; omega_using [hi]))
      (hd _ (by decide) (by unfold iRows sFn; omega_using [hi])), by rw [hm]; exact word_writeW_self _ _ _ _, hd,
    fun b hb => hf.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := hdr_lt_slot T.w b hi'; simp only; omega_using [this])
      (by have := slot_le (w := T.w) hb; omega_using [hGn, this]),
    fun j' hj' => row_of_inScr he hin hj',
    ⟨Only.of_inScr hin, hout, fun i hi => ctxWord_of_inScr he hin (by unfold TabP.n; omega_using [hi])⟩⟩

/-! ## The table's values -/

theorem TabP.M_lt (T : TabP) (hP : 0 < T.P) (E : Nat) : T.M E < T.P := Nat.mod_lt _ hP

theorem TabP.M_lt_R (T : TabP) (hP : 0 < T.P) (hPR : T.P ≤ T.R) (E : Nat) : T.M E < 2 ^ (64 * T.w) :=
  Nat.lt_of_lt_of_le (T.M_lt hP E) hPR

/-- A Montgomery product of two entries. -/
theorem TabP.M_mul (T : TabP) (hodd : T.P % 2 = 1) {E F c : Nat} (hc : c < T.P)
    (h : c * T.R % T.P = T.M E * T.M F % T.P) : c = T.M (E + F) :=
  VG.Proof.Rsa.FixedBaseComb.mont_product_encoded (coprime_pow2 hodd _) hc rfl rfl h

theorem TabP.entry_zero (T : TabP) (h1 : 1 < T.P) : T.entry 0 = T.R % T.P := by
  unfold TabP.entry TabP.M
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_zero, powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt h1, Nat.one_mul]

theorem TabP.entry_one (T : TabP) : T.entry 1 = T.G * T.R % T.P := by
  unfold TabP.entry TabP.M
  have := VG.Proof.Rsa.FixedBaseComb.exponent_tooth T.bits 0 (by decide)
  simp only [Nat.pow_zero, Nat.zero_mul] at this
  rw [this, powMod_eq, Nat.pow_one, Nat.mod_mul_mod]

/-- The tooth `2^(j+1)`'s entry, `rows` squares of the tooth `2^j`'s. -/
theorem TabP.entry_tooth (T : TabP) {j : Nat} (hj : j < 4) :
    T.entry (2 ^ (j + 1)) = T.M (Spec.Rsa.FixedBaseComb.exponent T.bits (2 ^ j) * 2 ^ T.rows) := by
  unfold TabP.entry
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega_using [hj]),
    VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega_using [hj]), ← Nat.pow_add, Nat.succ_mul]

theorem TabP.entry_add (T : TabP) {j i : Nat} (hj : j < 5) (hi : i < 2 ^ j) :
    T.entry (2 ^ j + i) = T.M (Spec.Rsa.FixedBaseComb.exponent T.bits i + Spec.Rsa.FixedBaseComb.exponent T.bits (2 ^ j)) := by
  unfold TabP.entry
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth _ _ _ hj hi, VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ hj]

end VG.Proof.Ffdh.X86_64.Cached

end

end

/-! # FFDH's context on x86-64: the table's loops -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx)

theorem ofNat_succ_sub_one (k : Nat) :
    BitVec.ofNat 64 (k + 1) - 1 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_using []

theorem ofNat_beq_zero {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · rintro rfl; rfl

/-- `[i] := [i] - 1`, and whether it is now zero. -/
theorem dec_ok {T : TabP} {s : State} (he : Env T s) {i k : Nat} (hi' : i < 32)
    (hv : word s.mem (off T.B T.o) (8 * i) = BitVec.ofNat 64 (k + 1)) (hk : k + 1 < 2 ^ 64) :
    WP isa (.block [.mov .rax (.mem (hdr i)), .alu .sub .rax (.imm 1), .store (hdr i) .rax]) s fun t =>
      t.zf = some (decide (k = 0)) ∧ t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) (BitVec.ofNat 64 k) ∧
      Keep [.rax] s t := by
  have hg := he.mc.sub.good
  obtain hl := hdr_lt_slot T.w 8 hi'
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (k = 0)) ∧
      t.mem = s.mem.writeW (off (off T.B T.o) (8 * i)) (BitVec.ofNat 64 k)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * i) (by omega_using [hl]), hg.scr.st (d := 8 * i) (by omega_using [hl]), hv,
      ofNat_succ_sub_one k, ofNat_beq_zero (show k < 2 ^ 64 by omega_using [hk])])  rfl) fun t ⟨h, k'⟩ => ⟨h.1, h.2, k'⟩

/-- What a stage keeps: the arrays not in `as`, the inner slots not in `hs`,
and what `Kept` keeps. -/
structure Same (T : TabP) (as hs : List Nat) (s t : State) : Prop where
  arr : ∀ b < 8, b ∉ as → wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w
  hdr : ∀ i, 17 ≤ i → i < 32 → i ∉ hs → word t.mem (off T.B T.o) (8 * i) = word s.mem (off T.B T.o) (8 * i)
  kept : Kept T s t

theorem Kept.of_eq {T : TabP} {s t : State} (h : t.mem = s.mem) : Kept T s t :=
  ⟨fun x _ _ => by rw [h], fun i _ => by rw [h], fun i _ => by rw [h]⟩

theorem Same.refl (T : TabP) (as hs : List Nat) (s : State) : Same T as hs s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, Kept.refl _ _⟩

theorem Same.trans {T : TabP} {as hs : List Nat} {s t u : State} (h₁ : Same T as hs s t) (h₂ : Same T as hs t u) :
    Same T as hs s u :=
  ⟨fun b hb hn => (h₂.arr b hb hn).trans (h₁.arr b hb hn), fun i h1 h2 hn => (h₂.hdr i h1 h2 hn).trans (h₁.hdr i h1 h2 hn),
    h₁.kept.trans h₂.kept⟩

theorem Same.mono {T : TabP} {as hs as' hs' : List Nat} {s t : State} (h : Same T as hs s t)
    (ha : ∀ b ∈ as, b ∈ as') (hh : ∀ i ∈ hs, i ∈ hs') : Same T as' hs' s t :=
  ⟨fun b hb hn => h.arr b hb (fun hm => hn (ha b hm)), fun i h1 h2 hn => h.hdr i h1 h2 (fun hm => hn (hh i hm)), h.kept⟩

theorem Same.of_eq {T : TabP} {as hs : List Nat} {s t : State} (h : t.mem = s.mem) : Same T as hs s t :=
  ⟨fun _ _ _ => by rw [h], fun _ _ _ _ => by rw [h], Kept.of_eq h⟩

theorem Same.of_outScr {T : TabP} {as hs : List Nat} {s t : State} (he : Env T s)
    (h : OutScr T.B T.Z s.mem t.mem) (hk : Kept T s t) : Same T as hs s t := by
  have hn := he.mc.sub.scr.nowrap
  refine ⟨fun b hb _ => OutScr.wvAt h (by have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega_arith) hn,
    fun i _ h2 _ => OutScr.wordAt h (by
      have := hdr_lt_slot T.w 8 h2; have := he.mc.sub.lo; have := he.mc.sub.hi; omega_arith) hn, hk⟩

theorem Same.of_slot {T : TabP} {as hs : List Nat} {s t : State} {i : Nat} (hi : i ∈ hs)
    (hh : ∀ i', i' < 32 → i' ≠ i → word t.mem (off T.B T.o) (8 * i') = word s.mem (off T.B T.o) (8 * i'))
    (ha : ∀ b < 8, wv t.mem (off T.B T.o) (slot T.w b) T.w = wv s.mem (off T.B T.o) (slot T.w b) T.w)
    (hk : Kept T s t) : Same T as hs s t :=
  ⟨fun b hb _ => ha b hb, fun i' _ h2 hn => hh i' h2 (fun e => hn (e ▸ hi)), hk⟩

/-- After `j` of the squares from `s`. -/
def SqInv (T : TabP) (s : State) (E j : Nat) (t : State) : Prop := Env T t ∧
  word t.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - j) ∧
  wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.M (E * 2 ^ j) ∧
  (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
  Same T [aAcc, aTmp, aY] [iI] s t ∧ Keep mmRegs s t

/-- The squares' loop body. -/
abbrev sqBody (Mo : Mont) : Prog isa := .seq (Mo.mm aY aY aY)
  (.block [.mov .rax (.mem (hdr iI)), .alu .sub .rax (.imm 1), .store (hdr iI) .rax])

theorem squares_step (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {E j : Nat} (hj : j < T.rows)
    (hr' : T.rows < 2 ^ 63) {t : State} (hI : SqInv T s E j t) :
    WP isa (sqBody Mo) t fun u => u.zf = some (decide (j + 1 = T.rows)) ∧ SqInv T s E (j + 1) u := by
  obtain ⟨het, hIt, hxt, hrt, st, kt⟩ := hI
  obtain hP : 0 < T.P := by have := he.mc.x1; omega_using [this]
  refine WP.seq (WP.mono (mm_env Mo het (Or.inr (Or.inr rfl)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hxt]; exact T.M_lt hP _)) fun u ⟨heu, hlu, hvu, hau, hru, hhu, kpu, ku⟩ => ?_)
  rw [hxt] at hvu
  obtain hxu := T.M_mul he.mc.odd hlu hvu
  obtain hIu : word u.mem (off T.B T.o) (8 * iI) = BitVec.ofNat 64 (T.rows - (j + 1) + 1) := by
    rw [hhu _ (by decide) (by decide), hIt]; congr 1; omega_using [hj]
  refine WP.mono (dec_ok heu (by decide) hIu (by omega_using [hr'])) fun v ⟨hz, hmv, kv⟩ => ?_
  obtain ⟨hev, hIv, hhv, hav, hrv, kpv⟩ := slot_env heu (i := iI) (by decide) (by decide) hmv kv.2.1 kv.2.2
    (kv.gpr (by decide))
  refine ⟨by rw [hz]; congr 1; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; omega_using [hj],
    hev, hIv, by rw [hav _ (by decide), hxu]; congr 1; rw [Nat.pow_succ]; ring, fun j' hj' => (hrv j' hj').trans
      ((hru j' hj').trans (hrt j' hj')), st.trans ⟨fun b hb hn => (hav b hb).trans (hau.wv_of_not_mem hb hn
        he.mc.sub.good.scr.nowrap), fun i h1 h2 hn => (hhv i h2 (fun e => hn (by simp [e]))).trans (hhu i h1 h2),
        kpu.trans kpv⟩, (kt.trans (ku.trans kv)).mono (by decide)⟩

/-- The squares' setup: `iI := rows`. -/
theorem squares_start {T : TabP} {s : State} (he : Env T s) {E : Nat}
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.M E) :
    WP isa (.block [.mov .rax (.mem (hdr iRows)), .store (hdr iI) .rax]) s (SqInv T s E 0) := by
  have hg := he.mc.sub.good
  obtain hl := hdr_lt_slot T.w 8 (show iI < 32 by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off (off T.B T.o) (8 * iI)) (BitVec.ofNat 64 T.rows)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iRows) (by have := hdr_lt_slot T.w 8 (show iRows < 32 by decide); omega_using [this]),
      hg.scr.st (d := 8 * iI) (by omega_using [hl]), he.rows]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  obtain ⟨he₁, hI₁, hh₁, ha₁, hr₁, kp₁⟩ := slot_env he (i := iI) (by decide) (by decide) hm₁ k₁.2.1 k₁.2.2
    (k₁.gpr (by decide))
  exact ⟨he₁, by rw [hI₁]; simp, by rw [ha₁ _ (by decide), hx, Nat.pow_zero, Nat.mul_one],
      fun j' hj' => hr₁ j' hj',
      ⟨fun b hb _ => ha₁ b hb, fun i _ h2 hn => hh₁ i h2 (fun e => hn (by simp [e])), kp₁⟩, k₁.mono (by decide)⟩

/-- `aY := aY^(2^rows)`: the next tooth's entry from the last. -/
theorem squares_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {E : Nat}
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.M E) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63) :
    WP isa (Precompute.squares Mo.mm) s fun t => Env T t ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.M (E * 2 ^ T.rows) ∧
      (∀ j', RowFits T j' → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aY] [iI] s t ∧ Keep mmRegs s t := by
  unfold Precompute.squares
  refine WP.seq (WP.mono (squares_start he hx) fun s₁ h₁ =>
    wp_upto (a := 0) (N := T.rows) (by omega_using [hr]) (SqInv T s E) (fun j _ hj t hI => squares_step Mo he hj hr' hI)
      (fun t h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) h₁)

/-- The entries `a < n` are in their rows. -/
def Entries (T : TabP) (n : Nat) (m : Mem) : Prop :=
  ∀ a < n, row m T.cp T.w (2 + a) = Spec.Rsa.toWords (T.entry a) T.w

theorem Env.P_lt {T : TabP} {s : State} (he : Env T s) : T.P < 2 ^ (64 * T.w) := by
  rw [← he.mc.xv.n]; exact wv_lt _ _ _ _

theorem rowFits_of {T : TabP} {j : Nat} (hj : j < 34) : RowFits T j := by
  unfold RowFits TabP.n; have := Nat.mul_le_mul_left T.w (show j + 1 ≤ 34 by omega_using [hj]); omega_using [this]

/-- Entry `d + J := ` entry `J` times entry `d`, for `0 < J < d = 2^jt`. -/
theorem product_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {jt J : Nat} (hjt : jt < 5) (hJ : 0 < J)
    (hJd : J < 2 ^ jt) (hjtp : 0 < jt)
    (hJs : word s.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J)
    (hDs : word s.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt))
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt))
    (hE : Entries T (2 ^ jt + J) s.mem) :
    WP isa (Precompute.product Mo.mm) s fun t => Env T t ∧
      t.zf = some (decide (J + 1 = 2 ^ jt)) ∧
      word t.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 (J + 1) ∧
      word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt) ∧
      Entries T (2 ^ jt + (J + 1)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aX, aY] [iJ] s t ∧ Keep mmRegs s t := by
  have hg := he.mc.sub.good
  obtain hP : 0 < T.P := by have := he.mc.x1; omega
  obtain hlJ := hdr_lt_slot T.w 8 (show iJ < 32 by decide)
  obtain hlD := hdr_lt_slot T.w 8 (show iD < 32 by decide)
  obtain h32 : 2 ^ jt ≤ 16 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show jt ≤ 4 by omega); simpa using this
  unfold Precompute.product
  simp only [seqs]
  -- `rax := J + 2`.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (J + 2) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * iJ) (by omega), hJs]
    apply BitVec.eq_of_toNat_eq; simp) rfl)
    fun s₁ ⟨⟨hax₁, hm₁⟩, k₁⟩ => ?_)
  obtain he₁ : Env T s₁ := he.of_outScr (by intro x _; rw [hm₁]) k₁.2.1 k₁.2.2 (k₁.gpr (by decide))
  obtain hrJ : row s₁.mem T.cp T.w (J + 2) = Spec.Rsa.toWords (T.entry J) T.w := by
    rw [hm₁, show J + 2 = 2 + J by omega]; exact hE J (by omega)
  refine WP.seq (WP.mono (load_env he₁ hax₁ (Or.inl rfl) (by omega) hrJ
    (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _))
    fun s₂ ⟨he₂, hL₂, ha₂, hr₂, hh₂, kp₂, k₂⟩ => ?_)
  obtain hX₂ : wv s₂.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ jt) := by
    rw [ha₂ _ (by decide) (by decide), hm₁, hx]
  refine WP.seq (WP.mono (mm_env Mo he₂ (Or.inl rfl) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [hX₂]; exact T.M_lt hP _))
    fun s₃ ⟨he₃, hl₃, hv₃, ha₃, hr₃, hh₃, kp₃, k₃⟩ => ?_)
  rw [hL₂, hX₂] at hv₃
  obtain hv₃' : wv s₃.mem (off T.B T.o) (slot T.w aX) T.w = T.entry (2 ^ jt + J) := by
    rw [T.entry_add hjt hJd]; exact T.M_mul he.mc.odd hl₃ hv₃
  obtain hJ₃ : word s₃.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J := by
    rw [hh₃ _ (by decide) (by decide), hh₂ _ (by decide), hm₁, hJs]
  obtain hD₃ : word s₃.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) := by
    rw [hh₃ _ (by decide) (by decide), hh₂ _ (by decide), hm₁, hDs]
  have hg₃ := he₃.mc.sub.good
  -- `rax := J + d + 2`.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + (2 ^ jt + J)) ∧
      t.mem = s₃.mem) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.ld (d := 8 * iJ) (by omega), hg₃.scr.ld (d := 8 * iD) (by omega),
      hJ₃, hD₃]
    apply BitVec.eq_of_toNat_eq; simp; omega) rfl)
    fun s₄ ⟨⟨hax₄, hm₄⟩, k₄⟩ => ?_)
  obtain he₄ : Env T s₄ := he₃.of_outScr (by intro x _; rw [hm₄]) k₄.2.1 k₄.2.2 (k₄.gpr (by decide))
  refine WP.seq (WP.mono (store_env he₄ hax₄ (by decide) (by omega))
    fun s₅ ⟨he₅, hrow₅, hr₅, hos₅, kp₅, k₅⟩ => ?_)
  rw [hm₄, hv₃'] at hrow₅
  have hg₅ := he₅.mc.sub.good
  obtain hJ₅ : word s₅.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J := by
    rw [OutScr.wordAt hos₅ (by have := he.mc.sub.hi; have := he.mc.sub.lo; omega) he.mc.sub.scr.nowrap, hm₄, hJ₃]
  obtain hD₅ : word s₅.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ jt) := by
    rw [OutScr.wordAt hos₅ (by have := he.mc.sub.hi; have := he.mc.sub.lo; omega) he.mc.sub.scr.nowrap, hm₄, hD₃]
  obtain hD₅' : (s₅.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 (J + 1))).readW
      (off (off T.B T.o) (8 * iD)) 64 = BitVec.ofNat 64 (2 ^ jt) := by
    change Bignum.word _ (off T.B T.o) (8 * iD) = _
    rw [(writeW_outside s₅.mem (off T.B T.o) (d := 8 * iJ) _ (by decide)).word (d := 8 * iD) (by decide)
      (by decide)]; exact hD₅
  -- `J := J + 1`, and whether it reached `d`.
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (J + 1 = 2 ^ jt)) ∧
      t.mem = s₅.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 (J + 1))) (by
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hg₅.scr.ld (d := 8 * iJ) (by omega), hg₅.scr.st (d := 8 * iJ) (by omega),
      hg₅.scr.ld (d := 8 * iD) (by omega), hJ₅, ofNat_add_one, hD₅', ofNat_sub_beq (show J + 1 < 2 ^ 64 by omega)
      (show 2 ^ jt < 2 ^ 64 by omega)]) rfl)
    fun t ⟨⟨hz, hmt⟩, kt⟩ => ?_
  obtain ⟨het, hJt, hht, hat, hrt, kpt⟩ := slot_env he₅ (i := iJ) (by decide) (by decide) hmt kt.2.1 kt.2.2
    (kt.gpr (by decide))
  have hn := he.mc.sub.scr.nowrap
  obtain hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega
  obtain hwo : ∀ b < 8, T.o + slot T.w b + 8 * T.w ≤ T.Z := fun b hb => by
    have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega
  refine ⟨het, by rw [hz], hJt, ?_, ?_, fun a ha => ?_, fun j' hj' => ?_, ⟨fun b hb hnb => ?_,
    fun i h1 h2 hni => ?_, ((((Kept.of_eq hm₁).trans kp₂).trans kp₃).trans
      ((Kept.of_eq hm₄).trans kp₅)).trans kpt⟩, ((((k₁.trans k₂).trans k₃).trans k₄).trans (k₅.trans kt)).mono
      (by decide)⟩
  · rw [hht _ (by decide) (by decide)]; exact hD₅
  · rw [hat _ (by decide), OutScr.wvAt hos₅ (hwo _ (by decide)) hn, hm₄,
      ha₃.wv_of_not_mem (by decide) (by decide) he.mc.sub.good.scr.nowrap, hX₂]
  · rw [hrt _ (rowFits_of (by omega))]
    by_cases hlast : a = 2 ^ jt + J
    · rw [hlast]; exact hrow₅
    · rw [hr₅ _ (by omega) (rowFits_of (by omega)), hm₄, hr₃ _ (rowFits_of (by omega)), hr₂ _ (rowFits_of (by omega)),
        hm₁]
      exact hE a (by omega)
  · rw [hrt _ (rowFits_of (by omega)), hr₅ _ (by omega) (rowFits_of (by omega)), hm₄, hr₃ _ (rowFits_of (by omega)),
      hr₂ _ (rowFits_of (by omega)), hm₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnb
    rw [hat _ hb, OutScr.wvAt hos₅ (hwo _ hb) hn, hm₄,
      ha₃.wv_of_not_mem hb (by simp [hnb.1, hnb.2.1, hnb.2.2.1]) he.mc.sub.good.scr.nowrap,
      ha₂ _ hb hnb.2.2.1, hm₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hni
    rw [hht _ h2 hni, OutScr.wordAt hos₅ (hio _ h2) hn, hm₄, hh₃ _ h1 h2, hh₂ _ h2, hm₁]

/-- The tooth `d = 2^(c+1)`: its entry and the entries `d + J` for `0 < J < d`. -/
theorem column_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) {c : Nat} (hc : c < 4)
    (hDs : word s.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)))
    (hx : wv s.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ c))
    (hE : Entries T (2 ^ (c + 1)) s.mem) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63) :
    WP isa (Precompute.column Mo.mm) s fun t => Env T t ∧
      t.zf = some (decide (c + 1 = 4)) ∧
      word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 2)) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) ∧
      Entries T (2 ^ (c + 2)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧
      Same T [aAcc, aTmp, aX, aXm, aY] [iI, iJ, iD] s t ∧ Keep mmRegs s t := by
  have hn := he.mc.sub.scr.nowrap
  obtain hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega_arith
  obtain hwo : ∀ b < 8, T.o + slot T.w b + 8 * T.w ≤ T.Z := fun b hb => by
    have := slot_le (w := T.w) hb; have := he.mc.sub.hi; omega_arith
  obtain hlD := hdr_lt_slot T.w 8 (show iD < 32 by decide)
  obtain hlJ := hdr_lt_slot T.w 8 (show iJ < 32 by decide)
  obtain hd16 : 2 ^ (c + 1) ≤ 16 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show c + 1 ≤ 4 by omega_using [hc]); simpa using this
  obtain hd2 : 2 ≤ 2 ^ (c + 1) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ c + 1 by omega_using []); simpa using this
  unfold Precompute.column
  simp only [seqs]
  refine WP.seq (WP.mono (squares_ok Mo he hx hr hr') fun s₁ ⟨he₁, hx₁, hr₁, st₁, k₁⟩ => ?_)
  rw [← T.entry_tooth hc] at hx₁
  obtain hD₁ : word s₁.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) := by
    rw [st₁.hdr _ (by decide) (by decide) (by decide)]; exact hDs
  have hg₁ := he₁.mc.sub.good
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (2 + 2 ^ (c + 1)) ∧
      t.mem = s₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * iD) (by omega_using [hlD]), hD₁]
    apply BitVec.eq_of_toNat_eq; simp; omega_using []) rfl)
    fun s₂ ⟨⟨hax₂, hm₂⟩, k₂⟩ => ?_)
  obtain he₂ : Env T s₂ := he₁.of_outScr (by intro x _; rw [hm₂]) k₂.2.1 k₂.2.2 (k₂.gpr (by decide))
  refine WP.seq (WP.mono (store_env he₂ hax₂ (by decide) (by omega_using [hd16]))
    fun s₃ ⟨he₃, hrow₃, hr₃, hos₃, kp₃, k₃⟩ => ?_)
  rw [hm₂, hx₁] at hrow₃
  have hg₃ := he₃.mc.sub.good
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s₃.mem.writeW (off (off T.B T.o) (8 * iJ)) (BitVec.ofNat 64 1)) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hg₃.scr.st (d := 8 * iJ) (by omega_using [hlJ]),
      show BitVec.setWidth 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl]) rfl)
    fun s₄ ⟨hm₄, k₄⟩ => ?_)
  obtain ⟨he₄, hJ₄, hh₄, ha₄, hr₄, kp₄⟩ := slot_env he₃ (i := iJ) (by decide) (by decide) hm₄ k₄.2.1 k₄.2.2
    (k₄.gpr (by decide))
  obtain hD₄ : word s₄.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) := by
    rw [hh₄ _ (by decide) (by decide), OutScr.wordAt hos₃ (hio _ (by decide)) hn, hm₂, hD₁]
  obtain hx₄ : wv s₄.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) := by
    rw [ha₄ _ (by decide), OutScr.wvAt hos₃ (hwo _ (by decide)) hn, hm₂, hx₁]
  obtain hE₄ : Entries T (2 ^ (c + 1) + 1) s₄.mem := fun a ha => by
    rw [hr₄ _ (rowFits_of (by omega_using [hd16, ha]))]
    by_cases hlast : a = 2 ^ (c + 1)
    · rw [hlast]; exact hrow₃
    · rw [hr₃ _ (by omega_using [hlast]) (rowFits_of (by omega_using [hd16, ha])), hm₂, hr₁ _ (rowFits_of (by omega_using [hd16, ha]))]
      exact hE a (by omega_using [ha, hlast])
  let Inv : Nat → State → Prop := fun J t => Env T t ∧
    word t.mem (off T.B T.o) (8 * iJ) = BitVec.ofNat 64 J ∧
    word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) ∧
    wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ (c + 1)) ∧
    Entries T (2 ^ (c + 1) + J) t.mem ∧
    (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s₄.mem T.cp T.w j') ∧
    Same T [aAcc, aTmp, aX, aY] [iJ] s₄ t ∧ Keep mmRegs s₄ t
  refine WP.seq (WP.mono (wp_upto (a := 1) (N := 2 ^ (c + 1)) (by omega_using [hd2]) Inv
    (fun J hJ1 hJN t ⟨het, hJt, hDt, hxt, hEt, hpt, stt, kt⟩ => WP.mono
      (product_ok Mo het (jt := c + 1) (by omega_using [hc]) (by omega_using [hJ1]) hJN (by omega_using []) hJt hDt hxt hEt)
      fun u ⟨heu, hz, hJu, hDu, hxu, hEu, hpu, stu, ku⟩ =>
        ⟨hz, heu, hJu, hDu, hxu, hEu, fun j' hj' => (hpu j' hj').trans (hpt j' hj'), stt.trans stu,
          (kt.trans ku).mono (by decide)⟩)
    (fun t h => h) ⟨he₄, hJ₄, hD₄, hx₄, hE₄, fun _ _ => rfl, Same.refl _ _ _ _, Keep.refl _ _⟩)
    fun s₅ ⟨he₅, _, hD₅, hx₅, hE₅, hp₅, st₅, k₅⟩ => ?_)
  have hg₅ := he₅.mc.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (c + 1 = 4)) ∧
      t.mem = s₅.mem.writeW (off (off T.B T.o) (8 * iD)) (BitVec.ofNat 64 (2 ^ (c + 2)))) (by
    obtain e : BitVec.ofNat 64 (2 ^ (c + 1)) + BitVec.ofNat 64 (2 ^ (c + 1)) = BitVec.ofNat 64 (2 ^ (c + 2)) := by
      rw [BitVec.ofNat_add_ofNat, Nat.pow_succ 2 (c + 1)]; congr 1; omega_using []
    obtain hb : (BitVec.ofNat 64 (2 ^ (c + 2)) - 32 == 0) = decide (c + 1 = 4) := by
      obtain hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega_using [hc]
      rcases hc4 with rfl | rfl | rfl | rfl <;> decide
    xrun [State.ea, hdr, hg₅.rdi, hdrOff, hg₅.scr.ld (d := 8 * iD) (by omega_using [hlD]), hg₅.scr.st (d := 8 * iD) (by omega_using [hlD]),
      hD₅, e, hb]) rfl)
    fun t ⟨⟨hz, hmt⟩, kt⟩ => ?_
  obtain ⟨het, hDt, hht, hat, hrt, kpt⟩ := slot_env he₅ (i := iD) (by decide) (by decide) hmt kt.2.1 kt.2.2
    (kt.gpr (by decide))
  refine ⟨het, hz, hDt, by rw [hat _ (by decide)]; exact hx₅,
    fun a ha => by rw [hrt _ (rowFits_of (by rw [Nat.pow_succ 2 (c + 1)] at ha; omega))]
                   exact hE₅ a (by rw [Nat.pow_succ 2 (c + 1)] at ha; omega_using [ha]),
    fun j' hj' => by
      rw [hrt _ (rowFits_of (by omega_using [hj'])), hp₅ j' hj', hr₄ _ (rowFits_of (by omega_using [hj'])), hr₃ _ (by omega_using [hd2, hj'])
        (rowFits_of (by omega_using [hj'])), hm₂, hr₁ _ (rowFits_of (by omega_using [hj']))],
    ?_, ?_⟩
  · exact ((((((st₁.mono (by decide) (by decide)).trans (Same.of_eq hm₂)).trans (Same.of_outScr he₂ hos₃ kp₃)).trans
      (Same.of_slot (i := iJ) (by decide) hh₄ ha₄ kp₄)).trans (st₅.mono (by decide) (by decide))).trans
      (Same.of_slot (i := iD) (by decide) hht hat kpt))
  · exact ((k₁.trans k₂).trans ((k₃.trans k₄).trans (k₅.trans kt))).mono (by decide)

/-- Bytes outside the working space and the context keep their values. -/
theorem Src.of_only {T : TabP} {s t : State} {p : Addr} {bs : List Byte} (h : Src s T.B T.Z p bs)
    (hm : Only T s.mem t.mem) (hsep : ∀ i < bs.length, 8 * T.n ≤ ofs T.cp (p + BitVec.ofNat 64 i))
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Src t T.B T.Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi,
    fun i hi => by rw [hm _ (h.out i hi) (hsep i hi)]; exact h.val i hi, h.out⟩

/-- Entries 0 and 1, and the first tooth `d := 2`. -/
theorem initial_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s)
    {gp : Addr} {gb : List Byte} (hG : Spec.Rsa.os2ip gb = T.G)
    (hsG : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sG) = gp)
    (hsK : word s.mem T.B (8 * sK) = BitVec.ofNat 64 gb.length)
    (hsrc : Src s T.B T.Z gp gb) (hgsep : ∀ i < gb.length, 8 * T.n ≤ ofs T.cp (gp + BitVec.ofNat 64 i))
    (hgl : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ T.w) :
    WP isa (seqs (Precompute.initial Mo.mm ++ ([.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]] : List (Prog isa)))) s fun t =>
      Env T t ∧ word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (0 + 1)) ∧
      wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ 0) ∧ Entries T (2 ^ (0 + 1)) t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t := by
  have hn := he.mc.sub.scr.nowrap
  obtain hP : 0 < T.P := by have := he.mc.x1; omega_using [this]
  obtain hR : Nat.Coprime T.R T.P := VG.Proof.Bignum.coprime_pow2 he.mc.odd _
  obtain hio : ∀ i < 32, T.o + 8 * i + 8 ≤ T.Z := fun i hi => by
    have := hdr_lt_slot T.w 8 hi; have := he.mc.sub.lo; have := he.mc.sub.hi; omega_arith
  unfold Precompute.initial
  simp only [List.cons_append, List.append_assoc]
  -- Entry 0.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (mm_env Mo he (Or.inr (Or.inr rfl)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [he.mc.xv.one]; exact he.mc.x1))
    fun s₁ ⟨he₁, hl₁, hv₁, ha₁, hr₁, hh₁, kp₁, k₁⟩ => ?_)
  obtain hY₁ : wv s₁.mem (off T.B T.o) (slot T.w aY) T.w = T.entry 0 := by
    rw [T.entry_zero he.mc.x1]
    have := mont_cancel hR (o := wv s₁.mem (off T.B T.o) (slot T.w aY) T.w) (c := T.R) (by
      rw [hv₁, he.mc.xv.one, Nat.mul_one, ← he.mc.r2])
    rw [Nat.mod_eq_of_lt hl₁] at this
    exact this
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 2 ∧
      t.mem = s₁.mem) (by xrun [show BitVec.setWidth 64 (2 : BitVec 32) = BitVec.ofNat 64 2 from rfl]) rfl)
    fun s₂ ⟨⟨hax₂, hm₂⟩, k₂⟩ => ?_)
  obtain he₂ : Env T s₂ := he₁.of_outScr (by intro x _; rw [hm₂]) k₂.2.1 k₂.2.2 (k₂.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp [Crt.loadArr]) (WP.mono (store_env he₂ hax₂ (by decide) (by decide))
    fun s₃ ⟨he₃, hrow₃, hr₃, hos₃, kp₃, k₃⟩ => ?_)
  rw [hm₂, hY₁] at hrow₃
  -- `aX := g`.
  obtain kp₃' : Kept T s s₃ := (kp₁.trans (Kept.of_eq hm₂)).trans kp₃
  obtain hsrc₃ : Src s₃ T.B T.Z gp gb := Src.of_only hsrc kp₃'.only hgsep
    (by rw [k₃.2.1, k₂.2.1, k₁.2.1]) (by rw [k₃.2.2, k₂.2.2, k₁.2.2])
  refine wp_seqs_append (a := Crt.loadArr aX VG.Impl.Ffdh.X86_64.Domain.sG sK) (by simp [Crt.loadArr]) (by simp) (WP.mono (primeLoad_ok he₃.mc.sub he.mc.w2 (Nat.le_refl _)
    (by have := he.mc.w28; omega_using [this]) (show aX < 8 by decide) (show VG.Impl.Ffdh.X86_64.Domain.sG < 32 by decide)
    (show sK < 32 by decide) (by rw [kp₃'.outer _ (by decide)]; exact hsG)
    (by rw [kp₃'.outer _ (by decide)]; exact hsK) hsrc₃ hgl (by have := he.mc.w28; omega_using [hgw, this]) hgw)
    fun s₄ ⟨_, hX₄, ho₄, k₄⟩ => ?_)
  obtain hf₄ : Frm (off T.B T.o) [(slot T.w aX, 8 * (T.w + 2))] s₃.mem s₄.mem := Frm.of_outside ho₄ (by simp)
  obtain ⟨hin₄, hout₄⟩ := inScr_of_inner he₃ hf₄ (fun r hr => by rw [List.mem_singleton.mp hr]; exact slot_le (by decide))
  obtain hd₄ : ∀ i, i < 32 → word s₄.mem (off T.B T.o) (8 * i) = word s₃.mem (off T.B T.o) (8 * i) :=
    fun i hi => hf₄.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (hdr_lt_slot T.w aX hi))
      (by have := hdr_lt_slot T.w 8 hi; omega_using [hi])
  obtain he₄ : Env T s₄ := he₃.of_inner (Frm.cover hf₄ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨(slot T.w aX, 3 * (8 * (T.w + 2))), by simp [innerR], by simp only; omega_using [], by simp only; omega_using []⟩))
    k₄.2.1 k₄.2.2 (k₄.gpr (by decide)) (hd₄ _ (by decide)) (hd₄ _ (by decide))
  obtain kp₄ : Kept T s₃ s₄ := ⟨Only.of_inScr hin₄, hout₄, fun i hi => ctxWord_of_inScr he₃ hin₄ (by unfold TabP.n; omega_using [hi])⟩
  obtain hR2₄ : wv s₄.mem (off T.B T.o) (slot T.w aR2) T.w = wv s.mem (off T.B T.o) (slot T.w aR2) T.w := by
    rw [hf₄.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [slot, aX, aR2]; omega_using [])
      (by have := slot_le (w := T.w) (show aR2 < 8 by decide); have := he.mc.w28; unfold slot hdrBytes at *; omega_arith),
      OutScr.wvAt hos₃ (by have := slot_le (w := T.w) (show aR2 < 8 by decide); have := he.mc.sub.hi; omega_arith) hn,
      hm₂, ha₁.wv_of_not_mem (by decide) (by decide) he.mc.sub.good.scr.nowrap]
  -- Entry 1.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (mm_env Mo he₄ (Or.inr (Or.inl rfl)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hR2₄]; exact he.mc.r2l))
    fun s₅ ⟨he₅, hl₅, hv₅, ha₅, hr₅, hh₅, kp₅, k₅⟩ => ?_)
  obtain hXm₅ : wv s₅.mem (off T.B T.o) (slot T.w aXm) T.w = T.entry 1 := by
    rw [T.entry_one]
    have := mont_cancel hR (o := wv s₅.mem (off T.B T.o) (slot T.w aXm) T.w) (c := T.G * T.R) (by
      rw [hv₅, hX₄, hG, hR2₄, Nat.mul_mod, he.mc.r2, ← Nat.mul_mod, Nat.mul_assoc])
    rw [Nat.mod_eq_of_lt hl₅] at this
    exact this
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 3 ∧
      t.mem = s₅.mem) (by xrun [show BitVec.setWidth 64 (3 : BitVec 32) = BitVec.ofNat 64 3 from rfl]) rfl)
    fun s₆ ⟨⟨hax₆, hm₆⟩, k₆⟩ => ?_)
  obtain he₆ : Env T s₆ := he₅.of_outScr (by intro x _; rw [hm₆]) k₆.2.1 k₆.2.2 (k₆.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (store_env he₆ hax₆ (by decide) (by decide))
    fun s₇ ⟨he₇, hrow₇, hr₇, hos₇, kp₇, k₇⟩ => ?_)
  rw [hm₆, hXm₅] at hrow₇
  -- `aY :=` entry 1.
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 3 ∧
      t.mem = s₇.mem) (by xrun [show BitVec.setWidth 64 (3 : BitVec 32) = BitVec.ofNat 64 3 from rfl]) rfl)
    fun s₉ ⟨⟨hax₉, hm₉⟩, k₉⟩ => ?_)
  obtain he₉ : Env T s₉ := he₇.of_outScr (by intro x _; rw [hm₉]) k₉.2.1 k₉.2.2 (k₉.gpr (by decide))
  refine VG.Proof.Ffdh.X86_64.wp_seqs_cons (by simp) (WP.mono (load_env he₉ hax₉ (V := T.entry 1) (Or.inr (Or.inr rfl)) (by decide)
    (by rw [hm₉]; exact hrow₇) (T.M_lt_R hP (Nat.le_of_lt he.P_lt) _))
    fun s₁₀ ⟨he₁₀, hY₁₀, _, hr₁₀, _, kp₁₀, k₁₀⟩ => ?_)
  have hg₇ := he₁₀.mc.sub.good
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s₁₀.mem.writeW (off (off T.B T.o) (8 * iD)) (BitVec.ofNat 64 2)) (by
    xrun [State.ea, hdr, hg₇.rdi, hdrOff, hg₇.scr.st (d := 8 * iD) (by have := hdr_lt_slot T.w 8 (show iD < 32 by decide); omega_using [this]),
      show BitVec.setWidth 64 (2 : BitVec 32) = BitVec.ofNat 64 2 from rfl]) rfl)
    fun s₈ ⟨hm₈, k₈⟩ => ?_
  obtain ⟨he₈, hD₈, _, ha₈, hr₈, kp₈⟩ := slot_env he₁₀ (i := iD) (by decide) (by decide) hm₈ k₈.2.1 k₈.2.2
    (k₈.gpr (by decide))
  obtain hXm₈ : wv s₈.mem (off T.B T.o) (slot T.w aY) T.w = T.entry 1 := by
    rw [ha₈ _ (by decide)]; exact hY₁₀
  obtain hE₈ : Entries T 2 s₈.mem := fun a ha => by
    rw [hr₈ _ (rowFits_of (by omega_using [ha])), hr₁₀ _ (rowFits_of (by omega_using [ha])), hm₉]
    rcases (show a = 0 ∨ a = 1 by omega_using [ha]) with rfl | rfl
    · rw [hr₇ _ (by decide) (rowFits_of (by decide)), hm₆, hr₅ _ (rowFits_of (by decide)),
        row_of_inScr he₃ hin₄ (rowFits_of (by decide))]
      exact hrow₃
    · exact hrow₇
  obtain hp₈ : ∀ j', j' < 2 → row s₈.mem T.cp T.w j' = row s.mem T.cp T.w j' := fun j' hj' => by
    rw [hr₈ _ (rowFits_of (by omega_using [hj'])), hr₁₀ _ (rowFits_of (by omega_using [hj'])), hm₉,
      hr₇ _ (by omega_using [hj']) (rowFits_of (by omega_using [hj'])), hm₆, hr₅ _ (rowFits_of (by omega_using [hj'])),
      row_of_inScr he₃ hin₄ (rowFits_of (by omega_using [hj'])), hr₃ _ (by omega_using [hj']) (rowFits_of (by omega_using [hj'])), hm₂,
      hr₁ _ (rowFits_of (by omega_using [hj']))]
  obtain kp₈' : Kept T s s₈ := (((((kp₃'.trans kp₄).trans kp₅).trans (Kept.of_eq hm₆)).trans kp₇).trans
    ((Kept.of_eq hm₉).trans kp₁₀)).trans kp₈
  obtain k₈' : Keep mmRegs s s₈ := ((((k₁.trans k₂).trans (k₃.trans k₄)).trans (k₅.trans k₆)).trans
    ((k₇.trans (k₉.trans k₁₀)).trans k₈)).mono (by decide)
  exact ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩

/-- The table: entries 0 and 1, then the four teeth's columns. -/
theorem table_ok (Mo : Mont) {T : TabP} {s : State} (he : Env T s) (hr : 1 ≤ T.rows) (hr' : T.rows < 2 ^ 63)
    {gp : Addr} {gb : List Byte} (hG : Spec.Rsa.os2ip gb = T.G)
    (hsG : word s.mem T.B (8 * VG.Impl.Ffdh.X86_64.Domain.sG) = gp)
    (hsK : word s.mem T.B (8 * sK) = BitVec.ofNat 64 gb.length)
    (hsrc : Src s T.B T.Z gp gb) (hgsep : ∀ i < gb.length, 8 * T.n ≤ ofs T.cp (gp + BitVec.ofNat 64 i))
    (hgl : 1 ≤ gb.length) (hgw : (gb.length + 7) / 8 ≤ T.w) :
    WP isa (seqs (Precompute.table Mo.mm)) s fun t => Env T t ∧ Entries T 32 t.mem ∧
      (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t := by
  unfold Precompute.table
  rw [show Precompute.initial Mo.mm ++ [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax],
      .loop (Precompute.column Mo.mm) .ne] = (Precompute.initial Mo.mm ++
      [.block [.mov32 .rax (.imm 2), .store (hdr iD) .rax]]) ++ [.loop (Precompute.column Mo.mm) .ne] by simp]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (initial_ok Mo he hG hsG hsK hsrc hgsep hgl hgw)
    fun s₈ ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩ => ?_)
  -- The four teeth.
  let Inv : Nat → State → Prop := fun c t => Env T t ∧
    word t.mem (off T.B T.o) (8 * iD) = BitVec.ofNat 64 (2 ^ (c + 1)) ∧
    wv t.mem (off T.B T.o) (slot T.w aY) T.w = T.entry (2 ^ c) ∧ Entries T (2 ^ (c + 1)) t.mem ∧
    (∀ j', j' < 2 → row t.mem T.cp T.w j' = row s.mem T.cp T.w j') ∧ Kept T s t ∧ Keep mmRegs s t
  exact wp_upto (a := 0) (N := 4) (by decide) Inv
    (fun c _ hc t ⟨het, hDt, hxt, hEt, hpt, kpt, kt⟩ => WP.mono (column_ok Mo het hc hDt hxt hEt hr hr')
      fun u ⟨heu, hz, hDu, hxu, hEu, hpu, stu, ku⟩ =>
        ⟨hz, heu, hDu, by rw [hxu], hEu, fun j' hj' => (hpu j' hj').trans (hpt j' hj'), kpt.trans stu.kept,
          (kt.trans ku).mono (by decide)⟩)
    (fun t ⟨het, _, _, hEt, hpt, kpt, kt⟩ => ⟨het, hEt, hpt, kpt, kt⟩)
    ⟨he₈, hD₈, hXm₈, hE₈, hp₈, kp₈', k₈'⟩

end VG.Proof.Ffdh.X86_64.Cached
