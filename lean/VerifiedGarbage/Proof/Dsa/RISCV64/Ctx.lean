module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Common
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on RISC-V: the layout of `scratch`

As on PPC64LE (`Proof/Dsa/PPC64LE/Ctx.lean`), a call's `scratch` (`Lay`):
`Z` bytes at `S`, holding the P space (at `S`, `w = p_len / 8`, 28 arrays),
the Q space (at `S + qOff`, `w = ⌈q_len / 8⌉`, 28 arrays within 1600 bytes)
and the buffer (at `S + bOff`, `2 p_len` bytes).

* `Env`: the registers of a working space, `a7` its array 0, `s5` an
  array's size, `t0` its words; `InP`, `InQ` for the two spaces, with `S` in
  `s6`;
* `Body`: memory changed only past the P space's header, within `scratch`,
  which keeps the header's words (`Body.word`): the lengths (`hLens`), the
  digest's address and the saved registers;
* `Regs`: `S`, the key and the signature in `s6`, `s11` and `ra`, and the
  lengths in the header, which `getP_ok`, … read.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
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

/-- The Q space's words. -/
abbrev wq (L : Lay) : Nat := (L.ql + 7) / 8

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
  ql : L.ql = 20 ∨ L.ql = 28 ∨ L.ql = 32
  room : 128 * L.pl ≤ L.Z
  nowrap : L.S.toNat + L.Z ≤ 2 ^ 64

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

theorem Ok.qOff_eq {L : Lay} (h : L.Ok) : L.qOff = 704 + 28 * L.pl := by
  rcases h.pl with e | e | e <;> simp [slot_eq, Lay.wp, e]

theorem Ok.wp_eq {L : Lay} (h : L.Ok) : 8 * L.wp = L.pl := by
  rcases h.pl with e | e | e <;> simp [Lay.wp, e]

theorem Ok.wp_ge {L : Lay} (h : L.Ok) : 16 ≤ L.wp ∧ L.wp ≤ 48 := by
  rcases h.pl with e | e | e <;> simp [Lay.wp, e]

theorem Ok.wq_ge {L : Lay} (h : L.Ok) : 3 ≤ L.wq ∧ L.wq ≤ 4 ∧ L.ql ≤ 8 * L.wq := by
  rcases h.ql with e | e | e <;> simp [Lay.wq, e]

theorem Ok.qslot {L : Lay} (h : L.Ok) : slot L.wq 28 ≤ 1600 := by
  rcases h.ql with e | e | e <;> simp [slot_eq, Lay.wq, e]

theorem Ok.z256 {L : Lay} (h : L.Ok) : 256 ≤ L.Z := by
  have := h.room; rcases h.pl with e | e | e <;> omega_arith

/-- The buffer ends within `scratch`. -/
theorem Ok.buf_end {L : Lay} (h : L.Ok) : L.bOff + 2 * L.pl ≤ L.Z := by
  have := h.qOff_eq; have := h.room; rcases h.pl with e | e | e <;> simp only [bOff] <;> omega_arith

end Lay

/-! ## The working spaces -/

/-- The first `n` bytes of a working space are one. -/
theorem scr_prefix {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) (h : n ≤ size) :
    Scr s base n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩,
    by have := hs.nowrap; omega_arith, hs.al⟩

/-- Part of a working space, at a multiple of 8, is one. -/
theorem scr_sub {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o n : Nat}
    (h : o + n ≤ size) (h8 : o % 8 = 0) (hn0 : 0 < n) : Scr s (off base o) n := by
  obtain ⟨⟨B₀, o₀, L, hm, hb, hL, hL'⟩, hn, ha⟩ := hs
  have e : (off base o).toNat = base.toNat + o := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  refine ⟨⟨B₀, o₀ + o, L, hm, ?_, by omega_arith, hL'⟩, by rw [e]; omega_arith, by rw [e]; omega_arith⟩
  subst hb; simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- What the code of a working space keeps: `a7` its array 0, `s5` an
array's size, `t0` its words. -/
structure Env (s : State) (B : Addr) (Z w : Nat) : Prop where
  hs : Scr s B Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  w2 : 2 ≤ w
  w48 : w ≤ 48
  hZ : slot w 28 ≤ Z

/-- The registers `Env` reads. -/
def envRegs : List Reg := [.a7, .s5, .t0]

theorem Env.keep {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : Env s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : Env t B Z w :=
  ⟨h.hs.congr k.2.2, (k.gpr (hr _ (by decide))).trans h.a7, (k.gpr (hr _ (by decide))).trans h.s5,
    (k.gpr (hr _ (by decide))).trans h.t0, h.w2, h.w48, h.hZ⟩

theorem slot_lt {w j k : Nat} (h : j < k) : slot w j + 8 * (w + 2) ≤ slot w k := by
  unfold slot
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show j + 1 ≤ k by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem Env.arr {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {j : Nat} (hj : j < 28) :
    slot w j + 8 * (w + 2) ≤ Z :=
  Nat.le_trans (slot_lt hj) h.hZ

/-- In the P space. -/
structure InP (s : State) (L : Lay) : Prop where
  env : Env s L.S L.qOff L.wp
  s6 : s.gpr .s6 = L.S

/-- In the Q space. -/
structure InQ (s : State) (L : Lay) : Prop where
  env : Env s L.Q 1600 L.wq
  s6 : s.gpr .s6 = L.S

/-- The registers `InP` and `InQ` read. -/
def inRegs : List Reg := [.a7, .s5, .t0, .s6]

theorem InP.keep {s t : State} {L : Lay} {rs : List Reg} (h : InP s L) (k : Keep rs s t)
    (hr : ∀ r ∈ inRegs, r ∉ rs := by decide) : InP t L :=
  ⟨h.env.keep k fun r hm => hr r ((by decide : ∀ r ∈ envRegs, r ∈ inRegs) r hm),
    (k.gpr (hr _ (by decide))).trans h.s6⟩

theorem InQ.keep {s t : State} {L : Lay} {rs : List Reg} (h : InQ s L) (k : Keep rs s t)
    (hr : ∀ r ∈ inRegs, r ∉ rs := by decide) : InQ t L :=
  ⟨h.env.keep k fun r hm => hr r ((by decide : ∀ r ∈ envRegs, r ∈ inRegs) r hm),
    (k.gpr (hr _ (by decide))).trans h.s6⟩

/-! ## Frames -/

/-- Memory changed only past the P space's header, within `scratch`. -/
abbrev Body (L : Lay) (m m' : Mem) : Prop := Outside L.S 256 (L.Z - 256) m m'

theorem Body.refl (L : Lay) (m : Mem) : Body L m m := Outside.refl _ _ _ _

theorem Body.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : Body L m₁ m₂) (h₂ : Body L m₂ m₃) : Body L m₁ m₃ :=
  Outside.trans h₁ h₂

/-- A header's word is kept by a change in the body. -/
theorem Body.word {L : Lay} {m m' : Mem} (h : Body L m m') {d : Nat} (hd : d + 8 ≤ 256) :
    word m' L.S d = word m L.S d :=
  Outside.word h (Or.inl (by omega)) (by omega)

/-- A frame relative to `B + a` is one relative to `B`. -/
theorem outside_shift {B : Addr} {a o n : Nat} {m m' : Mem} (h : Outside (off B a) o n m m')
    (ha : a + o + n ≤ 2 ^ 64) (ha' : a < 2 ^ 64) : Outside B (a + o) n m m' := by
  intro x hx
  apply h
  have hlt := (x - B).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x B (by omega_arith)]
  by_cases hd : a ≤ (x - B).toNat
  · rw [show 2 ^ 64 - a + (x - B).toNat = (x - B).toNat - a + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- A change in the P space's arrays is within the body. -/
theorem Body.ofP {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.S o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ L.qOff) : Body L m m' :=
  h.mono ho (by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith)

/-- A change in the Q space is within the body. -/
theorem Body.ofQ {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.Q o n m m')
    (hn : o + n ≤ 1600) : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have e : L.bOff = L.qOff + 1600 := rfl
  have := hL.qOff_eq
  exact (outside_shift h (by omega_arith) (by omega_arith)).mono (by omega_arith) (by omega_arith)

/-- A change in the buffer is within the body. -/
theorem Body.ofBuf {L : Lay} (hL : L.Ok) {n : Nat} {m m' : Mem} (h : Outside L.Buf 0 n m m')
    (hn : n ≤ 2 * L.pl) : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have e : L.bOff = L.qOff + 1600 := rfl
  have := hL.qOff_eq
  exact (outside_shift h (by omega_arith) (by omega_arith)).mono (by omega_arith) (by omega_arith)

/-- Memory changed only in the P space's arrays. -/
abbrev PBody (L : Lay) (m m' : Mem) : Prop := Outside L.S 256 (L.qOff - 256) m m'

/-- Memory changed only in the Q space's arrays. -/
abbrev QBody (L : Lay) (m m' : Mem) : Prop := Outside L.Q 256 1344 m m'

theorem PBody.refl (L : Lay) (m : Mem) : PBody L m m := Outside.refl _ _ _ _

theorem PBody.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : PBody L m₁ m₂) (h₂ : PBody L m₂ m₃) : PBody L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem QBody.refl (L : Lay) (m : Mem) : QBody L m m := Outside.refl _ _ _ _

theorem QBody.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : QBody L m₁ m₂) (h₂ : QBody L m₂ m₃) : QBody L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem PBody.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') : Body L m m' :=
  Body.ofP hL h (Nat.le_refl _) (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith)

theorem QBody.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBody L m m') : Body L m m' :=
  Body.ofQ hL h (by decide)

/-- A change in the P space's arrays keeps the Q space and the buffer. -/
theorem PBody.q {L : Lay} {m m' : Mem} (h : PBody L m m') : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x :=
  fun x hx => h x (Or.inr (by simp only [Lay.qOff, Lay.slot_eq] at hx ⊢; omega_arith))

/-- A change in arrays `j < 28` of the P space. -/
theorem PBody.of {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.S o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ L.qOff) : PBody L m m' :=
  h.mono ho (by simp only [Lay.qOff, Lay.slot_eq] at hn ⊢; omega_arith)

/-- A change in arrays `j < 28` of the Q space. -/
theorem QBody.of {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.Q o n m m') (ho : 256 ≤ o)
    (hn : o + n ≤ slot L.wq 28) : QBody L m m' :=
  h.mono ho (by have := hL.qslot; simp only [Lay.slot_eq] at this hn; omega_arith)

/-! ## The values kept -/

/-- The packed lengths: `p_len`, `q_len`, q's significant octets and the
digest's length, 16 bits each. -/
def pack (pl ql qb d : Nat) : BitVec 64 := BitVec.ofNat 64 (pl + 2 ^ 16 * ql + 2 ^ 32 * qb + 2 ^ 48 * d)

theorem pack_toNat {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : (pack pl ql qb d).toNat = pl + 2 ^ 16 * ql + 2 ^ 32 * qb + 2 ^ 48 * d := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Nat.reducePow] at *
  omega_arith

/-- `sizes` adds q's significant octets. -/
theorem pack_add {pl ql qb d : Nat} (h3 : qb < 2 ^ 16) :
    pack pl ql 0 d + BitVec.ofNat 64 qb <<< 32 = pack pl ql qb d := by
  apply BitVec.eq_of_toNat_eq
  rw [pack, pack, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := qb) (by simp only [Nat.reducePow] at *; omega_arith)]
  simp only [Nat.reducePow] at *
  omega_arith

/-- The values kept: `S`, the key and the signature (or the nonce) in
`s6`, `s11` and `ra`; `p_len` and `q_len` in the header's word `hLens`. -/
structure Regs (s : State) (L : Lay) (key sig : Addr) : Prop where
  s6 : s.gpr .s6 = L.S
  s11 : s.gpr .s11 = key
  ra : s.gpr .ra = sig
  pl : (word s.mem L.S hLens).toNat % 2 ^ 16 = L.pl
  ql : (word s.mem L.S hLens).toNat / 2 ^ 16 % 2 ^ 16 = L.ql

/-- The registers `Regs` reads. -/
def regsRegs : List Reg := [.s6, .s11, .ra]

/-- `Regs` through code that keeps its registers and changes memory only in
the body. -/
theorem Regs.keep {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : Regs s L key sig)
    (k : Keep rs s t) (hb : Body L s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) :
    Regs t L key sig :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra, by rw [hb.word (by decide)]; exact h.pl,
    by rw [hb.word (by decide)]; exact h.ql⟩

/-- `Regs` through a block that keeps memory. -/
theorem Regs.keepM {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : Regs s L key sig)
    (k : Keep rs s t) (hm : t.mem = s.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  h.keep k (by rw [hm]; exact Body.refl _ _) hr

theorem shl_shr_ofNat (x : BitVec 64) (a : Nat) (ha : a = 16 ∨ a = 32 ∨ a = 48) :
    x <<< a >>> 48 = BitVec.ofNat 64 (x.toNat % 2 ^ (64 - a) / 2 ^ (48 - a)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  rcases ha with rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub] <;> omega_arith

/-- `scratch` is a working space. -/
abbrev ScrL (s : State) (L : Lay) : Prop := Scr s L.S L.Z

theorem ScrL.p {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.S L.qOff :=
  scr_prefix h (by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith)

theorem ScrL.q {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.Q 1600 :=
  scr_sub h (by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith) (slot_al _ _) (by decide)

theorem ScrL.buf {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) : Scr s L.Buf (2 * L.pl) :=
  scr_sub h hL.buf_end (by simp only [Lay.bOff, Lay.qOff, Lay.slot_eq]; omega)
    (by rcases hL.pl with e | e | e <;> omega)

/-- The header's word `d`, loaded. -/
theorem ScrL.hdr {s : State} {L : Lay} (hs : ScrL s L) (hL : L.Ok) {d : Nat} (hd : d + 8 ≤ 256)
    (h8 : d % 8 = 0) :
    InRegions (s.rd ++ s.wr) (off L.S d) 8 ∧ (off L.S d).toNat % 8 = 0 :=
  ⟨hs.ld (by have := hL.z256; omega), hs.al8 (by have := hL.z256; omega) h8⟩

/-- `li` of a numeral below 2048, as an `Int` literal. -/
theorem exec_li_lit {s : State} {d : Reg} {m : Nat} (h : m < 2048) :
    exec (.li d (OfNat.ofNat m : Int)) s = some (s.write d (BitVec.ofNat 64 m)) :=
  exec_li_nat h

/-- `li` of 0. -/
theorem exec_li_zero {s : State} {d : Reg} : exec (.li d 0) s = some (s.write d 0) := by
  rw [exec_li (by decide)]; rfl

/-- `rd :=` a field of the header's lengths: `ld`, then `sll a`, `srl 48`. -/
theorem getField_ok {s : State} {L : Lay} (hs : ScrL s L) (hL : L.Ok) (h6 : s.gpr .s6 = L.S) (rd : Reg)
    (a : Nat) (ha : a = 16 ∨ a = 32 ∨ a = 48) :
    WP isa (.block [.load .d rd .s6 hLens, .shift .sll .d rd rd a, .shift .srl .d rd rd 48]) s fun t =>
      (t.gpr rd = BitVec.ofNat 64 ((word s.mem L.S hLens).toNat % 2 ^ (64 - a) / 2 ^ (48 - a)) ∧
        t.mem = s.mem) ∧ Keep [rd] s t := by
  obtain ⟨hin, hal⟩ := hs.hdr hL (d := 16) (by decide) (by decide)
  have e := shl_shr_ofNat (word s.mem L.S hLens) a ha
  rcases ha with rfl | rfl | rfl
  all_goals
    refine WP.keep _ ?_ (by cases rd <;> decide) (by rfl)
    brun [hLens, h6, hin, hal, exec_shift_d (show 16 < 64 by decide), exec_shift_d (show 32 < 64 by decide),
      exec_shift_d (show 48 < 64 by decide)]
    exact e

/-- `getP rd`: `rd := p_len`. -/
theorem getP_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (h : Regs s L key sig)
    (rd : Reg) :
    WP isa (.block (getP rd)) s fun t => (t.gpr rd = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [rd] s t :=
  WP.mono (getField_ok hs hL h.s6 rd 48 (by decide)) fun t ⟨⟨a, m⟩, k⟩ =>
    ⟨⟨by rw [a, ← h.pl]; simp only [Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one], m⟩, k⟩

/-- `getQ rd`: `rd := q_len`. -/
theorem getQ_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (h : Regs s L key sig)
    (rd : Reg) :
    WP isa (.block (getQ rd)) s fun t => (t.gpr rd = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [rd] s t :=
  WP.mono (getField_ok hs hL h.s6 rd 32 (by decide)) fun t ⟨⟨a, m⟩, k⟩ =>
    ⟨⟨by rw [a, ← h.ql]; congr 1; omega_arith, m⟩, k⟩

/-- `getQb rd`: `rd :=` the 16 bits of the lengths from bit 32. -/
theorem getQb_ok {s : State} {L : Lay} (hs : ScrL s L) (hL : L.Ok) (h6 : s.gpr .s6 = L.S) (rd : Reg) :
    WP isa (.block (getQb rd)) s fun t =>
      (t.gpr rd = BitVec.ofNat 64 ((word s.mem L.S hLens).toNat / 2 ^ 32 % 2 ^ 16) ∧ t.mem = s.mem) ∧
        Keep [rd] s t :=
  WP.mono (getField_ok hs hL h6 rd 16 (by decide)) fun t ⟨⟨a, m⟩, k⟩ =>
    ⟨⟨by rw [a]; congr 1; omega_arith, m⟩, k⟩

/-- `getD rd`: `rd :=` the lengths' top 16 bits. -/
theorem getD_ok {s : State} {L : Lay} (hs : ScrL s L) (hL : L.Ok) (h6 : s.gpr .s6 = L.S) (rd : Reg) :
    WP isa (.block (getD rd)) s fun t =>
      (t.gpr rd = BitVec.ofNat 64 ((word s.mem L.S hLens).toNat / 2 ^ 48) ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  obtain ⟨hin, hal⟩ := hs.hdr hL (d := 16) (by decide) (by decide)
  refine WP.keep _ ?_ (by cases rd <;> decide) (by rfl)
  unfold getD
  brun [hLens, h6, hin, hal, exec_shift_d (show 48 < 64 by decide)]
  apply BitVec.eq_of_toNat_eq
  have := (word s.mem L.S 16).isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

/-! ## Entering the spaces -/

theorem mem_pair {rd t r : Reg} (h : r ∈ [rd, t] ++ [rd]) : r ∈ [rd, t] := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h <;> simp [h]

theorem mem_pair' {rd t r : Reg} (h : r ∈ [rd] ++ [rd, t]) : r ∈ [rd, t] := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h <;> simp [h]

/-- The registers `enterP` and `enterQ` write. -/
def enterRegs : List Reg := [.a7, .t0, .t2, .s5]

theorem q_addr {L : Lay} (hL : L.Ok) :
    BitVec.ofNat 64 L.pl * BitVec.ofNat 64 28 + BitVec.ofNat 64 704 + L.S = L.Q := by
  rw [Lay.Q, off, hL.qOff_eq, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.add_comm]
  congr 2
  omega_arith

/-- `qBase rd t`: `rd :=` the Q space. -/
theorem qBase_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig)
    {rd t : Reg} (hrd : rd ≠ .s6) (ht : t ≠ .s6) (hrt : rd ≠ t) :
    WP isa (.block (qBase rd t)) s fun u => (u.gpr rd = L.Q ∧ u.mem = s.mem) ∧ Keep [rd, t] s u := by
  unfold qBase
  rw [WP.block_append_iff]
  refine WP.mono (getP_ok hs hL hr rd) fun v ⟨⟨a, mv⟩, kv⟩ => ?_
  have h6 : v.gpr .s6 = L.S := (kv.gpr (by simpa using hrd.symm)).trans hr.s6
  have hq := q_addr hL
  refine WP.mono (WP.keep [rd, t] (Q := fun u => u.gpr rd = L.Q ∧ u.mem = v.mem) ?_
    (by cases rd <;> cases t <;> simp_all <;> decide) (by rfl)) fun u ⟨⟨b, mu⟩, ku⟩ =>
      ⟨⟨b, by rw [mu, mv]⟩, (kv.trans ku).mono fun _ h => mem_pair' h⟩
  brun [a, h6, exec_li_lit (show 28 < 2048 by decide), hrd.symm, ht.symm, hrt.symm, hrt, gpr_write_self, gpr_write_of_ne _ _ hrt.symm,
    gpr_write_of_ne _ _ hrd]
  rw [hq]

/-- `enterP`: into the P space. -/
theorem enterP_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig) :
    WP isa (.block enterP) s fun t => (InP t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  unfold enterP
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.a7] (Q := fun u => u.gpr .a7 = off L.S (slot L.wp 0) ∧ u.mem = s.mem)
      (by brun [hr.s6, hdrBytes]; simp [Lay.slot_eq]) (by decide) (by rfl)) fun u ⟨⟨a7, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t0) fun v ⟨⟨b0, mv⟩, kv⟩ => ?_
  refine WP.mono (WP.keep [.t0, .s5] (Q := fun t => t.gpr .t0 = BitVec.ofNat 64 L.wp ∧
      t.gpr .s5 = BitVec.ofNat 64 (8 * (L.wp + 2)) ∧ t.mem = v.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨c0, c5, mt⟩, kt⟩ => ?_
  · have e3 : BitVec.ofNat 64 L.pl >>> 3 = BitVec.ofNat 64 L.wp := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rcases hL.pl with e | e | e <;> simp [e, Lay.wp]
    have e5 : BitVec.ofNat 64 L.wp <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (L.wp + 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      omega_arith
    brun [b0, e3, exec_shift_d (show 3 < 64 by decide), e5]
  · have k := (ku.trans kv).trans kt
    refine ⟨⟨⟨⟨Scr.congr (hs.p hL) k.2.2, ?_, c5, c0, by omega, by omega, Nat.le_refl _⟩,
      (k.gpr (by decide)).trans hr.s6⟩, by rw [mt, mv, mu]⟩, k.mono (by decide)⟩
    rw [kt.gpr (by decide), kv.gpr (by decide), a7]

/-- `enterQ`: into the Q space. -/
theorem enterQ_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig) :
    WP isa (.block enterQ) s fun t => (InQ t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  have hw := hL.wq_ge
  unfold enterQ
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (qBase_ok hs hL hr (rd := .a7) (t := .t2) (by decide) (by decide) (by decide))
    fun u ⟨⟨a7, mu⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.a7] (Q := fun v => v.gpr .a7 = off L.Q (slot L.wq 0) ∧ v.mem = u.mem)
      (by brun [a7, hdrBytes]; simp [Lay.slot_eq, off]) (by decide) (by rfl)) fun v ⟨⟨b7, mv⟩, kv⟩ => ?_
  have hr' : Regs v L key sig := hr.keepM (ku.trans kv) (by rw [mv, mu])
  refine WP.mono (getQ_ok (hs.congr (ku.trans kv).2.2) hL hr' .t0) fun x ⟨⟨c0, mx⟩, kx⟩ => ?_
  refine WP.mono (WP.keep [.t0, .s5] (Q := fun t => t.gpr .t0 = BitVec.ofNat 64 L.wq ∧
      t.gpr .s5 = BitVec.ofNat 64 (8 * (L.wq + 2)) ∧ t.mem = x.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨d0, d5, mt⟩, kt⟩ => ?_
  · have e3 : (BitVec.ofNat 64 L.ql + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 L.wq := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rcases hL.ql with e | e | e <;> simp [e, Lay.wq]
    have e5 : BitVec.ofNat 64 L.wq <<< 3 + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (L.wq + 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      omega_arith
    brun [c0, e3, exec_shift_d (show 3 < 64 by decide), e5]
  · have k := ((ku.trans kv).trans kx).trans kt
    refine ⟨⟨⟨⟨Scr.congr (hs.q hL) k.2.2, ?_, d5, d0, by omega, by omega, hL.qslot⟩,
      (k.gpr (by decide)).trans hr.s6⟩, by rw [mt, mx, mv, mu]⟩, k.mono (by decide)⟩
    rw [kt.gpr (by decide), kx.gpr (by decide), b7]

/-- `bufBase rd t`: `rd :=` the buffer. -/
theorem bufBase_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig)
    {rd t : Reg} (hrd : rd ≠ .s6) (ht : t ≠ .s6) (hrt : rd ≠ t) :
    WP isa (.block (bufBase rd t)) s fun u => (u.gpr rd = L.Buf ∧ u.mem = s.mem) ∧ Keep [rd, t] s u := by
  unfold bufBase
  rw [WP.block_append_iff]
  refine WP.mono (qBase_ok hs hL hr hrd ht hrt) fun v ⟨⟨a, mv⟩, kv⟩ => ?_
  refine WP.mono (WP.keep [rd] (Q := fun u => u.gpr rd = L.Buf ∧ u.mem = v.mem) ?_ (by cases rd <;> decide)
    (by rfl)) fun u ⟨⟨b, mu⟩, ku⟩ => ⟨⟨b, by rw [mu, mv]⟩, (kv.trans ku).mono fun _ h => mem_pair h⟩
  brun [a, gpr_write_self]

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
  ⟨fun i hi => by rw [off, off, Offset.add_add]; exact h.rd (o + i) (by omega_arith),
    fun i hi x hx => by rw [off, off, Offset.add_add]; exact h.sep (o + i) (by omega_arith) x hx⟩

/-- A buffer's bytes are apart from a working space within `scratch`. -/
theorem Src.sepIn {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {a Z : Nat}
    (ha : a + Z ≤ L.Z) (hw : L.S.toNat + L.Z ≤ 2 ^ 64) :
    ∀ i < n, ∀ x, ofs (off L.S a) x < Z → off D i ≠ x := by
  intro i hi x hx
  refine h.sep i hi x ?_
  have hlt := (x - L.S).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega_arith)] at hx
  by_cases hd : a ≤ (x - L.S).toNat
  · rw [show 2 ^ 64 - a + (x - L.S).toNat = (x - L.S).toNat - a + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)] at hx
    omega_arith
  · rw [Nat.mod_eq_of_lt (by omega_arith)] at hx; omega_arith

/-- A buffer's bytes, unchanged by a change in `scratch`. -/
theorem Src.bytes {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {m m' : Mem} {o k : Nat}
    (hb : Outside L.S o k m m') (hk : o + k ≤ L.Z) :
    Spec.Rsa.bytesAt m' D n = Spec.Rsa.bytesAt m D n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hb _ ?_
  have hi := List.mem_range.mp hi
  by_contra hc
  exact h.sep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

/-! ## The key -/

/-- p, q, g and y, from the key at `key`. -/
def pOf (m : Mem) (L : Lay) (key : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m key L.pl)
def qOf (m : Mem) (L : Lay) (key : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key L.pl) L.ql)
def gOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (L.pl + L.ql)) L.pl)
def yOf (m : Mem) (L : Lay) (key : Addr) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off key (2 * L.pl + L.ql)) L.pl)

end VG.Proof.Dsa.RISCV64
