module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: the layout of `scratch`

A call's `scratch` (`Lay`): `Z` bytes at `S`, holding the P space (at `S`,
`w = p_len / 8`, 28 arrays), the Q space (at `S + qOff`, `w = 4`, 28 arrays,
1600 bytes) and the buffer (at `S + bOff`, `2 p_len` bytes).

* `InP`, `InQ`: the registers are those of the P space or the Q space
  (`Env`), with `S` in `r21` and the space in `r23`;
* `Body`: memory changed only past the P space's header, within `scratch`,
  to which the frames of the working spaces' code convert (`Outside.shift`,
  `Outs.within`);
* `Hdr`: the values the header keeps, read by `enterP_ok` and `enterQ_ok`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- A call's `scratch`: `Z` bytes at `S`, for `p_len` and `q_len`. -/
structure Lay where
  S : Addr
  Z : Nat
  pl : Nat
  ql : Nat

namespace Lay

/-- The P space's words. -/
abbrev wp (L : Lay) : Nat := L.pl / 8

/-- The Q space's offset. -/
abbrev qOff (L : Lay) : Nat := slot L.wp 28

/-- The buffer's offset. -/
abbrev bOff (L : Lay) : Nat := L.qOff + 1600

/-- The Q space. -/
abbrev Q (L : Lay) : Addr := off L.S L.qOff

/-- The buffer. -/
abbrev Buf (L : Lay) : Addr := off L.S L.bOff

/-- The widths are supported and `scratch` has room for the layout. -/
structure Ok (L : Lay) : Prop where
  pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384
  ql : 20 ≤ L.ql ∧ L.ql ≤ 32
  room : 128 * L.pl ≤ L.Z
  nowrap : L.S.toNat + L.Z ≤ 2 ^ 64

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

theorem Ok.qOff_eq {L : Lay} (h : L.Ok) : L.qOff = 704 + 28 * L.pl := by
  rcases h.pl with e | e | e <;> simp [slot_eq, Lay.wp, e]

theorem Ok.wp_eq {L : Lay} (h : L.Ok) : 8 * L.wp = L.pl := by
  rcases h.pl with e | e | e <;> simp [Lay.wp, e]

theorem Ok.wp_ge {L : Lay} (h : L.Ok) : 16 ≤ L.wp ∧ L.wp ≤ 48 := by
  rcases h.pl with e | e | e <;> simp [Lay.wp, e]

/-- The buffer ends within `scratch`. -/
theorem Ok.buf_end {L : Lay} (h : L.Ok) : L.bOff + 2 * L.pl ≤ L.Z := by
  have := h.qOff_eq; have := h.room; rcases h.pl with e | e | e <;> simp only [bOff] <;> omega

end Lay

/-! ## The working spaces -/

/-- The first `n` bytes of a working space are one. -/
theorem scr_prefix {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) (h : n ≤ size) :
    Scr s base n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega, hL'⟩, by have := hs.nowrap; omega⟩

/-- Part of a working space is one. -/
theorem scr_sub {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o n : Nat}
    (h : o + n ≤ size) (hn0 : 0 < n) : Scr s (off base o) n := by
  obtain ⟨⟨B₀, o₀, L, hm, hb, hL, hL'⟩, hn⟩ := hs
  refine ⟨⟨B₀, o₀ + o, L, hm, ?_, by omega, hL'⟩, ?_⟩
  · subst hb; simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [show (off base o).toNat = base.toNat + o by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]]
    omega

/-- In the P space. -/
structure InP (s : State) (L : Lay) : Prop where
  env : Env s L.S L.qOff L.wp
  h21 : s.gpr .r21 = L.S
  h23 : s.gpr .r23 = L.S

/-- In the Q space. -/
structure InQ (s : State) (L : Lay) : Prop where
  env : Env s L.Q 1600 4
  h21 : s.gpr .r21 = L.S
  h23 : s.gpr .r23 = L.Q

/-- The registers `InP` and `InQ` read. -/
def inRegs : List Reg := [.r10, .r11, .r21, .r23, .r29, .r31]

theorem InP.keep {s t : State} {L : Lay} {rs : List Reg} (h : InP s L) (k : Keep rs s t)
    (hr : ∀ r ∈ inRegs, r ∉ rs) : InP t L :=
  ⟨h.env.keep k fun r hm => hr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide),
    (k.gpr _ (hr _ (by decide))).trans h.h21, (k.gpr _ (hr _ (by decide))).trans h.h23⟩

theorem InQ.keep {s t : State} {L : Lay} {rs : List Reg} (h : InQ s L) (k : Keep rs s t)
    (hr : ∀ r ∈ inRegs, r ∉ rs) : InQ t L :=
  ⟨h.env.keep k fun r hm => hr r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide),
    (k.gpr _ (hr _ (by decide))).trans h.h21, (k.gpr _ (hr _ (by decide))).trans h.h23⟩

/-! ## Frames -/

/-- Memory changed only past the P space's header, within `scratch`. -/
abbrev Body (L : Lay) (m m' : Mem) : Prop := Outside L.S 256 (L.Z - 256) m m'

theorem Body.refl (L : Lay) (m : Mem) : Body L m m := Outside.refl _ _ _ _

theorem Body.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : Body L m₁ m₂) (h₂ : Body L m₂ m₃) : Body L m₁ m₃ :=
  Outside.trans h₁ h₂

/-- A frame relative to `B + a` is one relative to `B`. -/
theorem outside_shift {B : Addr} {a o n : Nat} {m m' : Mem} (h : Outside (off B a) o n m m')
    (ha : a + o + n ≤ 2 ^ 64) (ha' : a < 2 ^ 64) : Outside B (a + o) n m m' := by
  intro x hx
  apply h
  have hlt := (x - B).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x B (by omega)]
  by_cases hd : a ≤ (x - B).toNat
  · rw [show 2 ^ 64 - a + (x - B).toNat = (x - B).toNat - a + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- A frame of several ranges within `[lo, hi)` is one of `[lo, hi)`. -/
theorem outs_within {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {lo hi : Nat}
    (hw : ∀ r ∈ rs, lo ≤ r.1 ∧ r.1 + r.2 ≤ hi) : Outside B lo (hi - lo) m m' :=
  fun x hx => h x fun r hr => by have := hw r hr; omega

/-- A change in the P space's arrays is within the body. -/
theorem Body.ofP {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.S o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ L.qOff) : Body L m m' :=
  h.mono ho (by have := hL.buf_end; simp only [Lay.bOff] at this; omega)

/-- A change in the Q space's arrays is within the body. -/
theorem Body.ofQ {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.Q o n m m')
    (hn : o + n ≤ 1600) : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  simp only [Lay.bOff] at hb
  exact (outside_shift h (by omega) (by omega)).mono (by simp only [Lay.qOff, Lay.slot_eq]; omega) (by omega)

/-- A change in the buffer is within the body. -/
theorem Body.ofBuf {L : Lay} (hL : L.Ok) {n : Nat} {m m' : Mem} (h : Outside L.Buf 0 n m m')
    (hn : n ≤ 2 * L.pl) : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have eb : L.bOff = 256 + 28 * (8 * (L.wp + 2)) + 1600 := rfl
  have := hL.wp_eq
  simp only [Lay.bOff, Lay.qOff, Lay.slot_eq] at hb
  exact (outside_shift h (by omega) (by omega)).mono (by omega) (by omega)

/-! ## The header -/

/-- The values the header keeps from the entry. -/
structure Hdr (m : Mem) (L : Lay) (key sig dig : Addr) : Prop where
  key : word m L.S hKey = key
  pl : word m L.S hP = BitVec.ofNat 64 L.pl
  ql : word m L.S hQ = BitVec.ofNat 64 L.ql
  qws : word m L.S hQws = L.Q
  buf : word m L.S hBuf = L.Buf
  sig : word m L.S hSig = sig
  dig : word m L.S hDig = dig

/-- A header word, unchanged by a change in the body. -/
theorem Body.word {L : Lay} {m m' : Mem} (h : Body L m m') (hZ : 256 ≤ L.Z) {d : Nat} (hd : d + 8 ≤ 256)
    (hw : L.S.toNat + L.Z ≤ 2 ^ 64) : word m' L.S d = word m L.S d :=
  Outside.word h (Or.inl hd) (by have := hZ; have := hw; omega)

theorem Hdr.body {L : Lay} {m m' : Mem} {key sig dig : Addr} (h : Hdr m L key sig dig) (hb : Body L m m')
    (hL : L.Ok) : Hdr m' L key sig dig := by
  have hZ : 256 ≤ L.Z := by have := hL.room; rcases hL.pl with e | e | e <;> omega
  have w := fun {d : Nat} (hd : d + 8 ≤ 256) => hb.word hZ hd hL.nowrap
  exact ⟨(w (by decide)).trans h.key, (w (by decide)).trans h.pl, (w (by decide)).trans h.ql,
    (w (by decide)).trans h.qws, (w (by decide)).trans h.buf, (w (by decide)).trans h.sig,
    (w (by decide)).trans h.dig⟩

/-- `scratch` is a working space. -/
abbrev ScrL (s : State) (L : Lay) : Prop := Scr s L.S L.Z

theorem ScrL.p {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.S L.qOff :=
  scr_prefix h (by have := hL.buf_end; simp only [Lay.bOff] at this; omega)

theorem ScrL.q {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.Q 1600 :=
  scr_sub h (by have := hL.buf_end; simp only [Lay.bOff] at this; omega) (by decide)

theorem ScrL.buf {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.Buf (2 * L.pl) :=
  scr_sub h hL.buf_end (by rcases hL.pl with e | e | e <;> omega)

/-- The registers `enterP` writes. -/
def enterRegs : List Reg := [.r10, .r11, .r23, .r29, .r31]

/-- `enterP`: into the P space. -/
theorem enterP_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block enterP) s fun t => (InP t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  refine WP.keep _ ?_ (by decide)
  unfold enterP
  have hld : InRegions (s.rd ++ s.wr) (L.S + BitVec.ofNat 64 8) 8 := hs.ld (show 8 + 8 ≤ L.Z by
    have := hL.room; rcases hL.pl with e | e | e <;> omega)
  have hr : s.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := hh.pl
  prun [h21, hld, hr, BitVec.add_zero, hdrBytes, hP]
  have e3 : BitVec.ofNat 64 L.pl >>> 3 = BitVec.ofNat 64 L.wp := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rcases hL.pl with e | e | e <;> simp [e, Lay.wp]
  have e16 : BitVec.ofNat 64 (8 * L.wp) + 16#64 = BitVec.ofNat 64 (8 * (L.wp + 2)) := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]; congr 1
  rw [e3, Pub.ofNat_shl3, Pub.ofNat_shl1, e16]
  refine ⟨⟨Scr.congr (hs.p hL) rfl, ?_, ?_, ?_, ?_, by omega, by omega, Nat.le_refl _⟩, ?_, ?_⟩ <;>
    simp only [gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp [off, Lay.slot_eq]
  · exact h21

/-- `enterQ`: into the Q space. -/
theorem enterQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) :
    WP isa (.block enterQ) s fun t => (InQ t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  refine WP.keep _ ?_ (by decide)
  unfold enterQ
  have hld : InRegions (s.rd ++ s.wr) (L.S + BitVec.ofNat 64 24) 8 := hs.ld (show 24 + 8 ≤ L.Z by
    have := hL.room; rcases hL.pl with e | e | e <;> omega)
  have hr : s.mem.readW (L.S + BitVec.ofNat 64 24) 64 = L.Q := hh.qws
  prun [h21, hld, hr, BitVec.add_zero, hdrBytes, hQws]
  refine ⟨⟨Scr.congr (hs.q hL) rfl, ?_, ?_, ?_, ?_, by decide, by decide, by decide⟩, ?_, ?_⟩ <;>
    simp only [gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [Lay.Q, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  · exact h21

/-! ## Buffers apart from `scratch` -/

/-- `n` bytes at `D`, readable and apart from `scratch`. -/
structure Src (s : State) (L : Lay) (D : Addr) (n : Nat) : Prop where
  rd : ∀ i < n, InRegions (s.rd ++ s.wr) (off D i) 1
  sep : ∀ i < n, ∀ x, ofs L.S x < L.Z → off D i ≠ x

theorem Src.keep {s t : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Src t L D n :=
  ⟨by rw [hrd, hwr]; exact h.rd, h.sep⟩

/-- Part of a buffer is one. -/
theorem Src.sub {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {o k : Nat} (hk : o + k ≤ n) :
    Src s L (off D o) k :=
  ⟨fun i hi => by rw [off, off, Offset.add_add]; exact h.rd (o + i) (by omega),
    fun i hi x hx => by rw [off, off, Offset.add_add]; exact h.sep (o + i) (by omega) x hx⟩

/-- A buffer's bytes are apart from a working space within `scratch`. -/
theorem Src.sepIn {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {a Z : Nat}
    (ha : a + Z ≤ L.Z) (hw : L.S.toNat + L.Z ≤ 2 ^ 64) :
    ∀ i < n, ∀ x, ofs (off L.S a) x < Z → off D i ≠ x := by
  intro i hi x hx
  refine h.sep i hi x ?_
  have hlt := (x - L.S).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega)] at hx
  by_cases hd : a ≤ (x - L.S).toNat
  · rw [show 2 ^ 64 - a + (x - L.S).toNat = (x - L.S).toNat - a + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hx
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hx; omega

/-- A buffer's bytes, unchanged by a change in the body. -/
theorem Src.bytes {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {m m' : Mem} (hb : Body L m m')
    (hZ : 256 ≤ L.Z) :
    Spec.Rsa.bytesAt m' D n = Spec.Rsa.bytesAt m D n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hb _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

/-! ## The arrays of the two spaces -/

/-- Array `j` of the P space. -/
abbrev arrP (m : Mem) (L : Lay) (j : Nat) : Nat := arr m L.S L.wp j

/-- Array `j` of the Q space. -/
abbrev arrQ (m : Mem) (L : Lay) (j : Nat) : Nat := arr m L.Q 4 j

/-! ## The key -/

/-- p, q, g and y, from the key at `key`. -/
def pOf (m : Mem) (L : Lay) (key : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m key L.pl)
def qOf (m : Mem) (L : Lay) (key : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key L.pl) L.ql)
def gOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (L.pl + L.ql)) L.pl)
def yOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (2 * L.pl + L.ql)) L.pl)

end VG.Proof.Dsa.PPC64LE
