module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Cached
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Ring

/-! # FFDH's context on x86-64: its rows, to and from the inner workspace

The context is `3 + 34 w` words outside the working space: three public
words, then 34 rows of `w` words (`p`, `R² mod p` and the 32 entries). A
row is copied to or from an array of the inner workspace by `copyWords`,
which changes only the row or the array. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Memory that changes only outside the working space. -/
def OutScr (B : Addr) (Z : Nat) (m m' : Mem) : Prop := ∀ x, ofs B x < Z → m' x = m x

theorem OutScr.refl (B : Addr) (Z : Nat) (m : Mem) : OutScr B Z m m := fun _ _ => rfl

theorem OutScr.trans {B : Addr} {Z : Nat} {m₁ m₂ m₃ : Mem} (h₁ : OutScr B Z m₁ m₂)
    (h₂ : OutScr B Z m₂ m₃) : OutScr B Z m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem OutScr.word_eq {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {d : Nat} (hd : d + 8 ≤ Z)
    (hn : B.toNat + Z ≤ 2 ^ 64) : Bignum.word m' B d = Bignum.word m B d :=
  Mem.readW_congr fun i hi => h _ (by rw [ofs_off B (d := d) (i := i) (by omega)]; omega)

/-- The working space at an offset `o`: its words are unchanged too. -/
theorem OutScr.wordAt {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {o d : Nat}
    (hd : o + d + 8 ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : Bignum.word m' (off B o) d = Bignum.word m (off B o) d := by
  have e : ∀ m : Mem, Bignum.word m (off B o) d = Bignum.word m B (o + d) := fun m => by
    simp only [Bignum.word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [e, e]
  exact OutScr.word_eq h (by omega) hn

theorem OutScr.wvAt {B : Addr} {Z : Nat} {m m' : Mem} (h : OutScr B Z m m') {o d n : Nat}
    (hd : o + d + 8 * n ≤ Z) (hn : B.toNat + Z ≤ 2 ^ 64) : wv m' (off B o) d n = wv m (off B o) d n :=
  wv_congr fun i hi => OutScr.wordAt h (by omega) hn

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
    OutScr.wordAt hm (by have := hdr_lt_slot wx 8 hi'; omega) hn
  have hw0 : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    OutScr.word_eq hm (by have := hdr_lt_slot w 8 hi'; omega) hn
  refine ⟨⟨?_, h.scr.nowrap⟩, by rw [hdi]; exact h.rdi, ⟨?_, ?_, fun j hj => ?_⟩, ?_, ?_, fun j hj => ?_,
    h.lo, h.hi⟩
  · rw [hwr]; exact h.scr.wr
  · rw [hw _ (by decide)]; exact h.hdr.hw
  · rw [hw _ (by decide)]; exact h.hdr.hminv
  · rw [hw _ (by unfold sArr; omega)]; exact h.hdr.harr j hj
  · rw [hw _ (by decide)]; exact h.link
  · rw [hw0 _ (by decide)]; exact h.nw
  · rw [hw0 _ (by unfold sArr; omega)]; exact h.narr j hj

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
  row_congr fun i hi => h.word (by rw [Nat.mul_add] at hn; omega) (by rw [Nat.mul_add] at hn; omega)

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
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sW) (by omega),
      hg.scr.ld (d := 8 * iCtx) (by omega), hg.hdr.hw, hctx, hax, execImul, imul_low]
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
  have hA := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega)
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
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hg₁.scr.ld (d := 8 * sArr a) (by omega), hg₁.hdr.harr a ha]) rfl)
    fun s₂ ⟨⟨hsi, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (copyWords_ok hsi ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h12) hw
    (by omega) (by rw [Nat.mul_add] at hj; omega)
    (fun i hi' => by rw [k12.2.1, k12.2.2]; exact hg.scr.ld (by omega))
    (fun i hi' => by rw [k12.2.2, rowOff]; exact hR.wr _ (by rw [Nat.mul_add] at hj; omega))
    (fun i hi' b hb => Or.inr (by
      have hx : ofs B (off (off B o) (slot w a + 8 * i) + BitVec.ofNat 64 b) < Z := by
        rw [show off (off B o) (slot w a + 8 * i) = off B (o + (slot w a + 8 * i)) by
          simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat], ofs_off B (by omega)]
        omega
      have := hR.apart hx
      rw [Nat.mul_add] at hj
      omega)))
    fun t ⟨_, hd, ho, k₃⟩ => ?_
  rw [hm₂, hm₁] at hd ho
  have hsep : ∀ x, ofs B x < Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hR.apart hx; rw [Nat.mul_add] at hj; omega))
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
  have hA := hdr_lt_slot w 8 (show sArr a < 32 by unfold sArr; omega)
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
    (by xrun [State.ea, hdr, hg₁.rdi, hdrOff, hbx, hg₁.scr.ld (d := 8 * sArr a) (by omega),
      hg₁.hdr.harr a ha]) rfl)
    fun s₂ ⟨⟨hsi, hbx₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  refine WP.mono (copyWords_ok hsi hbx₂ ((k₂.gpr (by decide)).trans h12) hw
    (by omega) (by omega)
    (fun i hi' => by rw [k12.2.1, k12.2.2, rowOff]; exact hR.rd _ (by rw [Nat.mul_add] at hj; omega))
    (fun i hi' => by rw [k12.2.2]; exact hg.scr.st (by omega))
    (fun i hi' b hb => Or.inr (by
      have hx : 8 * n ≤ 24 + 8 * w * j + 8 * i + b → False := fun h => by
        rw [Nat.mul_add] at hj; omega
      have hb' : 24 + 8 * w * j + 8 * i + b < 8 * n := by rw [Nat.mul_add] at hj; omega
      have := hR.out (d := 24 + 8 * w * j + 8 * i + b) hb'
      rw [show off cp (24 + 8 * w * j + 8 * i + b) =
          off cp (24 + 8 * w * j + 8 * i) + BitVec.ofNat 64 b by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]] at this
      rcases ofs_rebase B (off cp (24 + 8 * w * j + 8 * i) + BitVec.ofNat 64 b) (o := o) (by omega)
        with ⟨_, e⟩ | ⟨h, _⟩
      · rw [e]; omega
      · omega
)))
    fun t ⟨hv, _, ho, k₃⟩ => ?_
  rw [hm₂, hm₁] at hv ho
  refine ⟨hv.trans (wv_of_row hrow hV), ho, (k12.trans k₃).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Cached
