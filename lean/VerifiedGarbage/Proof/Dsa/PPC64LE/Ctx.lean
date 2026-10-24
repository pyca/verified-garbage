module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
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

theorem Ok.z256 {L : Lay} (h : L.Ok) : 256 ≤ L.Z := by
  have := h.room; rcases h.pl with e | e | e <;> omega

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

/-- A change in the P space's arrays is one in the body. -/
theorem PBody.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') : Body L m m' :=
  Body.ofP hL h (Nat.le_refl _) (by simp only [Lay.qOff, Lay.slot_eq]; omega)

/-- A change in the Q space's arrays is one in the body. -/
theorem QBody.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBody L m m') : Body L m m' :=
  Body.ofQ hL h (by decide)

/-- A change in the P space's arrays keeps the Q space and the buffer. -/
theorem PBody.outQ {L : Lay} {m m' : Mem} (h : PBody L m m') :
    Outside L.S 0 L.qOff m m' :=
  h.mono (Nat.zero_le _) (by simp only [Lay.qOff, Lay.slot_eq]; omega)

/-- A change in the P space's arrays, seen from the Q space: none at its own offsets. -/
theorem PBody.q {L : Lay} {m m' : Mem} (h : PBody L m m') : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x :=
  fun x hx => h x (Or.inr (by simp only [Lay.qOff, Lay.slot_eq] at hx ⊢; omega))

/-- Memory changed only in the P space's arrays from array 1 on. -/
abbrev PArr (L : Lay) (m m' : Mem) : Prop := Outside L.S (slot L.wp 1) (L.qOff - slot L.wp 1) m m'

/-- Memory changed only in the Q space's arrays from array 1 on. -/
abbrev QArr (L : Lay) (m m' : Mem) : Prop := Outside L.Q (slot 4 1) (1600 - slot 4 1) m m'

theorem PArr.refl (L : Lay) (m : Mem) : PArr L m m := Outside.refl _ _ _ _

theorem PArr.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : PArr L m₁ m₂) (h₂ : PArr L m₂ m₃) : PArr L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem QArr.refl (L : Lay) (m : Mem) : QArr L m m := Outside.refl _ _ _ _

theorem QArr.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : QArr L m₁ m₂) (h₂ : QArr L m₂ m₃) : QArr L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem PArr.pbody {L : Lay} {m m' : Mem} (h : PArr L m m') : PBody L m m' :=
  h.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.qOff, Lay.slot_eq]; omega)

theorem QArr.qbody {L : Lay} {m m' : Mem} (h : QArr L m m') : QBody L m m' :=
  h.mono (by simp only [Lay.slot_eq]; omega) (by simp only [Lay.slot_eq]; omega)

/-- A change in arrays `1 ≤ j < 28` of the P space. -/
theorem PArr.of {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.S o n m m') (ho : slot L.wp 1 ≤ o)
    (hn : o + n ≤ L.qOff) : PArr L m m' :=
  h.mono ho (by omega)

/-- A change in arrays `1 ≤ j < 28` of the Q space. -/
theorem QArr.of {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.Q o n m m') (ho : slot 4 1 ≤ o)
    (hn : o + n ≤ 1600) : QArr L m m' :=
  h.mono ho (by omega)

/-! ## The values kept in registers -/

/-- The values kept in registers: `S`, the key, the signature (or the
nonce), the digest, and `p_len` and `q_len` in `r2`'s low 32 bits. -/
structure Regs (s : State) (L : Lay) (key sig dig : Addr) : Prop where
  r21 : s.gpr .r21 = L.S
  r27 : s.gpr .r27 = key
  r28 : s.gpr .r28 = sig
  r26 : s.gpr .r26 = dig
  pl : (s.gpr .r2).toNat % 2 ^ 16 = L.pl
  ql : (s.gpr .r2).toNat / 2 ^ 16 % 2 ^ 16 = L.ql

/-- `r2`'s fields: `p_len`, `q_len`, q's significant octets and the digest's
length, 16 bits each. -/
def pack (pl ql qb d : Nat) : BitVec 64 := BitVec.ofNat 64 (pl + 2 ^ 16 * ql + 2 ^ 32 * qb + 2 ^ 48 * d)

theorem pack_toNat {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : (pack pl ql qb d).toNat = pl + 2 ^ 16 * ql + 2 ^ 32 * qb + 2 ^ 48 * d := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simp only [Nat.reducePow] at *
  omega

theorem pack_pl {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : (pack pl ql qb d).toNat % 2 ^ 16 = pl := by
  rw [pack_toNat h1 h2 h3 h4]; simp only [Nat.reducePow] at *; omega

theorem pack_ql {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : (pack pl ql qb d).toNat / 2 ^ 16 % 2 ^ 16 = ql := by
  rw [pack_toNat h1 h2 h3 h4]; simp only [Nat.reducePow] at *; omega

theorem pack_qb {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : (pack pl ql qb d).toNat / 2 ^ 32 % 2 ^ 16 = qb := by
  rw [pack_toNat h1 h2 h3 h4]; simp only [Nat.reducePow] at *; omega

theorem pack_d {pl ql qb d : Nat} (h1 : pl < 2 ^ 16) (h2 : ql < 2 ^ 16) (h3 : qb < 2 ^ 16)
    (h4 : d < 2 ^ 16) : pack pl ql qb d >>> 48 = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, pack_toNat h1 h2 h3 h4, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *; omega

/-- `sizes` adds q's significant octets. -/
theorem pack_add {pl ql qb d : Nat} (h3 : qb < 2 ^ 16) :
    pack pl ql 0 d + BitVec.ofNat 64 qb <<< 32 = pack pl ql qb d := by
  apply BitVec.eq_of_toNat_eq
  rw [pack, pack, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := qb) (by simp only [Nat.reducePow] at *; omega)]
  simp only [Nat.reducePow] at *
  omega

/-- `Regs` for `r2` holding `pack`. -/
theorem Regs.of_pack {s : State} {L : Lay} {key sig dig : Addr} {qb d : Nat} (hL : L.Ok)
    (h21 : s.gpr .r21 = L.S) (h27 : s.gpr .r27 = key) (h28 : s.gpr .r28 = sig) (h26 : s.gpr .r26 = dig)
    (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (h3 : qb < 2 ^ 16) (h4 : d < 2 ^ 16) : Regs s L key sig dig := by
  have hp : L.pl < 2 ^ 16 := by rcases hL.pl with e | e | e <;> omega
  have hq : L.ql < 2 ^ 16 := by have := hL.ql; omega
  exact ⟨h21, h27, h28, h26, by rw [h2]; exact pack_pl hp hq h3 h4, by rw [h2]; exact pack_ql hp hq h3 h4⟩

/-- The registers `Regs` reads. -/
def regsRegs : List Reg := [.r2, .r21, .r26, .r27, .r28]

theorem Regs.keep {s t : State} {L : Lay} {key sig dig : Addr} {rs : List Reg} (h : Regs s L key sig dig)
    (k : Keep rs s t) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig dig :=
  ⟨(k.gpr _ (hr _ (by decide))).trans h.r21, (k.gpr _ (hr _ (by decide))).trans h.r27,
    (k.gpr _ (hr _ (by decide))).trans h.r28, (k.gpr _ (hr _ (by decide))).trans h.r26,
    by rw [k.gpr _ (hr _ (by decide))]; exact h.pl, by rw [k.gpr _ (hr _ (by decide))]; exact h.ql⟩

theorem shl_shr_ofNat (x : BitVec 64) (a : Nat) (ha : a = 16 ∨ a = 32 ∨ a = 48) :
    x <<< a >>> 48 = BitVec.ofNat 64 (x.toNat % 2 ^ (64 - a) / 2 ^ (48 - a)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  rcases ha with rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub] <;> omega

/-- `getP rd`: `rd := p_len`. -/
theorem getP_ok {s : State} {L : Lay} {key sig dig : Addr} (h : Regs s L key sig dig) (rd : Reg) :
    WP isa (.block (getP rd)) s fun t => (t.gpr rd = BitVec.ofNat 64 L.pl ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  refine WP.keep _ ?_ (by cases rd <;> decide)
  unfold getP
  prun [shl_shr_ofNat _ 48 (by decide)]
  rw [← h.pl]
  simp only [Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one]

theorem Regs.p_eq {s : State} {L : Lay} {key sig dig : Addr} (h : Regs s L key sig dig) :
    s.gpr .r2 <<< 48 >>> 48 = BitVec.ofNat 64 L.pl := by
  rw [shl_shr_ofNat _ 48 (by decide), ← h.pl]
  simp only [Nat.reduceSub, Nat.reducePow, Nat.pow_zero, Nat.div_one]

theorem Regs.q_eq {s : State} {L : Lay} {key sig dig : Addr} (h : Regs s L key sig dig) :
    s.gpr .r2 <<< 32 >>> 48 = BitVec.ofNat 64 L.ql := by
  rw [shl_shr_ofNat _ 32 (by decide), ← h.ql]
  congr 1
  omega

/-- `getQ rd`: `rd := q_len`. -/
theorem getQ_ok {s : State} {L : Lay} {key sig dig : Addr} (h : Regs s L key sig dig) (rd : Reg) :
    WP isa (.block (getQ rd)) s fun t => (t.gpr rd = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  refine WP.keep _ ?_ (by cases rd <;> decide)
  unfold getQ
  prun [shl_shr_ofNat _ 32 (by decide)]
  rw [← h.ql]
  congr 1
  omega

/-- `getQb rd`: `rd :=` the 16 bits of `r2` from bit 32. -/
theorem getQb_ok (s : State) (rd : Reg) :
    WP isa (.block (getQb rd)) s fun t =>
      (t.gpr rd = BitVec.ofNat 64 ((s.gpr .r2).toNat / 2 ^ 32 % 2 ^ 16) ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  refine WP.keep _ ?_ (by cases rd <;> decide)
  unfold getQb
  prun [shl_shr_ofNat _ 16 (by decide)]
  congr 1
  omega

/-- `getD rd`: `rd :=` `r2`'s top 16 bits. -/
theorem getD_ok (s : State) (rd : Reg) :
    WP isa (.block (getD rd)) s fun t =>
      (t.gpr rd = BitVec.ofNat 64 ((s.gpr .r2).toNat / 2 ^ 48) ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  refine WP.keep _ ?_ (by cases rd <;> decide)
  unfold getD
  prun
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := (s.gpr .r2).isLt
  omega

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
    (hr : Regs s L key sig dig) :
    WP isa (.block enterP) s fun t => (InP t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  unfold enterP
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r23, .r31, .r10] (Q := fun u => u.gpr .r23 = L.S ∧ u.gpr .r31 = L.S ∧
      u.gpr .r10 = L.S + BitVec.ofNat 64 256 ∧ u.mem = s.mem) (by prun [hr.r21, BitVec.add_zero, hdrBytes])
      (by decide)) fun u ⟨⟨a23, a31, a10, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hr.keep ku) .r11) fun v ⟨⟨b11, mv⟩, kv⟩ => ?_
  refine WP.mono (WP.keep [.r11, .r29] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (2 * L.wp) ∧
      t.gpr .r29 = BitVec.ofNat 64 (8 * (L.wp + 2)) ∧ t.mem = v.mem) ?_ (by decide))
    fun t ⟨⟨c11, c29, mt⟩, kt⟩ => ?_
  · have e3 : BitVec.ofNat 64 L.pl >>> 3 = BitVec.ofNat 64 L.wp := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rcases hL.pl with e | e | e <;> simp [e, Lay.wp]
    have e16 : BitVec.ofNat 64 (8 * L.wp) + 16#64 = BitVec.ofNat 64 (8 * (L.wp + 2)) := by
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]; congr 1
    prun [b11, e3, Pub.ofNat_shl3, Pub.ofNat_shl1, e16]
  · have k := (ku.trans kv).trans kt
    refine ⟨⟨⟨⟨Scr.congr (hs.p hL) k.wr, ?_, c29, c11, ?_, by omega, by omega, Nat.le_refl _⟩,
      (k.gpr .r21 (by decide)).trans hr.r21, ?_⟩, by rw [mt, mv, mu]⟩, k.mono (by decide)⟩
    · rw [kt.gpr .r10 (by decide), kv.gpr .r10 (by decide), a10]; simp [off, Lay.slot_eq]
    · rw [kt.gpr .r31 (by decide), kv.gpr .r31 (by decide), a31]
    · rw [kt.gpr .r23 (by decide), kv.gpr .r23 (by decide), a23]

theorem q_addr {L : Lay} (hL : L.Ok) :
    BitVec.ofNat 64 L.pl * BitVec.ofNat 64 28 + BitVec.ofNat 64 704 + L.S = L.Q := by
  rw [Lay.Q, off, hL.qOff_eq, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.add_comm]
  congr 2
  omega

/-- The registers `qBase` is used with. -/
def qPairs : List (Reg × Reg) := [(.r23, .r11), (.r24, .r0), (.r30, .r0), (.r12, .r0)]

/-- `qBase rd t`: `rd :=` the Q space. -/
theorem qBase_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) {rd t : Reg}
    (hp : (rd, t) ∈ qPairs) :
    WP isa (.block (qBase rd t)) s fun u => (u.gpr rd = L.Q ∧ u.mem = s.mem) ∧ Keep [rd, t] s u := by
  unfold qBase
  rw [WP.block_append_iff]
  refine WP.mono (getP_ok hr rd) fun v ⟨⟨a, mv⟩, kv⟩ => ?_
  have h21 : v.gpr .r21 = L.S := (kv.gpr .r21 (by simp [qPairs] at hp; rcases hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)).trans hr.r21
  have hq := q_addr hL
  refine WP.mono (WP.keep [rd, t] (Q := fun u => u.gpr rd = L.Q ∧ u.mem = v.mem) ?_ ?_)
    fun u ⟨⟨b, mu⟩, ku⟩ => ⟨⟨b, by rw [mu, mv]⟩, (kv.trans ku).mono (by
      intro r hr; simp at hr ⊢; omega)⟩
  all_goals simp only [qPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
  all_goals rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first | decide | prun [a, h21, exec_mul, hq]

/-- `enterQ`: into the Q space. -/
theorem enterQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) :
    WP isa (.block enterQ) s fun t => (InQ t L ∧ t.mem = s.mem) ∧ Keep enterRegs s t := by
  unfold enterQ
  rw [WP.block_append_iff]
  refine WP.mono (qBase_ok hL hr (by decide)) fun v ⟨⟨a, mv⟩, kv⟩ => ?_
  have h21 : v.gpr .r21 = L.S := (kv.gpr .r21 (by decide)).trans hr.r21
  refine WP.mono (WP.keep [.r31, .r10, .r11, .r29] (Q := fun t => t.gpr .r31 = L.Q ∧
      t.gpr .r10 = L.Q + BitVec.ofNat 64 256 ∧ t.gpr .r11 = BitVec.ofNat 64 8 ∧
      t.gpr .r29 = BitVec.ofNat 64 48 ∧ t.mem = v.mem) (by prun [a, BitVec.add_zero, hdrBytes]) (by decide))
    fun t ⟨⟨c31, c10, c11, c29, mt⟩, kt⟩ => ?_
  have k := kv.trans kt
  refine ⟨⟨⟨⟨Scr.congr (hs.q hL) k.wr, ?_, c29, c11, c31, by decide, by decide, by decide⟩,
    (k.gpr .r21 (by decide)).trans hr.r21, (kt.gpr .r23 (by decide)).trans a⟩, by rw [mt, mv]⟩,
    k.mono (by decide)⟩
  rw [c10]; simp [off, Lay.slot_eq]

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

/-- The first octets of a buffer apart from `scratch`. -/
theorem Src.take {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {k : Nat} (hk : k ≤ n) :
    Src s L D k :=
  ⟨fun i hi => h.rd i (by omega), fun i hi => h.sep i (by omega)⟩

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
