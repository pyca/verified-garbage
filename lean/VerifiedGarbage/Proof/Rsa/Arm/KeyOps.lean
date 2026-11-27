module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.CopyWords
public import VerifiedGarbage.Proof.Bignum.Arm.SelectState
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Bignum.Arm.CopyWords`, which this module and modules that import it used -/

section

/-! # Termination and exact value of runtime-length word copying -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CopyWord.lean`, which only this module imported.
section

/-! A word copy writes the source once, without evaluating a selection mask. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem copyWord_ok (s : State) (o a : Addr)
    (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = a)
    (wo : InRegions s.wr o 4) (ra : InRegions (s.rd ++ s.wr) a 4) :
    WP isa copyWord s fun t =>
      t.mem = s.mem.writeW o (s.mem.readW a 32) ∧ Rest selectClobbers s t := by
  unfold copyWord
  refine wp_ldr (a := a) (by decide) ha ra fun u load => ?_
  refine wp_str (a := o) (by decide) (by rw [load.other .r0 (by decide)]; exact ho)
    (by rw [load.wr]; exact wo) fun t store => WP.block_nil ?_
  refine ⟨?_, (load.rest (by simp [selectClobbers])).trans (store.rest _)⟩
  rw [store.mem,load.mem,load.gpr]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CopyWordBody.lean`, which only this module imported.
section

/-! # A word copy preserves the selection invariant with identical sources -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem copyWordBody_ok {s0 s : State} {base : BitVec 32} {size o a n i : Nat}
    (ctx : SubCtx s0 base size o a a n) (inv : SelectInv s0 base o a a n i s) (hi : i < n) :
    WP isa copyWordBody s fun t => SelectInv s0 base o a a n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have ha := ctx.aFits
  have hb := ctx.bFits
  have addr {r : Reg} {d : Nat} (hp : s.gpr r = base + BitVec.ofNat 32 d) (hd : d < size) :
      State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr base) d := by
    rw [hp, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have writable (d : Nat) (hd : d + 4 ≤ size) : InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega)⟩
  have readable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable d hd
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [copyWordBody, WP.seq_iff]
  refine WP.mono (copyWord_ok s _ _ (addr inv.outPtr (by omega)) (addr inv.aPtr (by omega))
    (writable _ (by omega)) (readable _ (by omega))) ?_
  rintro u ⟨mem, keep⟩
  have selected : u.mem = s.mem.writeW (off (State.addr base) (o + 4 * i))
      (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr base) (a + 4 * i)) 32
        else s.mem.readW (off (State.addr base) (a + 4 * i)) 32) := by
    simpa only [ite_self] using mem
  obtain ⟨outside, prefixValue⟩ := select_value_step ctx inv hi selected
  refine WP.mono (subAdvance_ok u) ?_
  rintro t ⟨p0, p10, p12, count, zero, mem2, keep2⟩
  have uc : u.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (keep.gpr .lr (by simp [selectClobbers])).trans inv.count
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, keep.gpr .r0 (by simp [selectClobbers]), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p10, keep.gpr .r10 (by simp [selectClobbers]), inv.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, keep.gpr .r12 (by simp [selectClobbers]), inv.bPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, uc]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [mem2]; exact outside
  · rw [mem2]; exact prefixValue
  · rw [keep2.gpr .r4 (by simp), keep.gpr .r4 (by simp [selectClobbers]),
      keep2.gpr .r11 (by simp), keep.gpr .r11 (by simp [selectClobbers])]
    exact inv.mask
  · refine inv.rest.trans ((keep.mono ?_).trans (keep2.mono ?_))
    all_goals decide
  · rw [zero, uc]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem copyWords_ok (s : State) {base : BitVec 32} {size o a n : Nat}
    (ctx : SubCtx s base size o a a n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 a)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa copyWords s (SelectInv s base o a a n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectInv s base o a a n i t
  rw [copyWords, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (copyWordBody_ok ctx hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, he], hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    refine ⟨by omega_using [], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r0 (by simp)).trans hp0
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r10 (by simp)).trans hp10
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm

end

end

/-! # The operations on the arrays of the working space: subtraction and selection -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The registers the operations may change: all but `r6`–`r9`. -/
abbrev opRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r10, .r11, .r12, .lr]

/-- The pointers of three arrays into `r0`, `r10` and `r12`. -/
theorem ptr3_ok {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < 256) (ha : a < 256) (hb : b < 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = B + BitVec.ofNat 32 (arr w o) → t.gpr .r10 = B + BitVec.ofNat 32 (arr w a) →
      t.gpr .r12 = B + BitVec.ofNat 32 (arr w b) → Rest [.r0, .r10, .r12] s t → t.mem = s.mem →
      Ws t B Z w N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ rest)) s Q := by
  simp only [List.append_assoc]
  refine ptr_ok h (by decide) ho fun s1 p1 r1 m1 h1 => ?_
  refine ptr_ok h1 (by decide) ha fun s2 p2 r2 m2 h2 => ?_
  refine ptr_ok h2 (by decide) hb fun t p3 r3 m3 h3 => ?_
  refine k t ?_ ?_ p3 ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp))))
    (m3.trans (m2.trans m1)) h3
  · rw [r3.gpr _ (by decide), r2.gpr _ (by decide), p1]
  · rw [r3.gpr _ (by decide), p2]

theorem Ws.subCtxN {s : State} {B : BitVec 32} {Z w N o a b n : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) (hn : n ≤ w) :
    SubCtx s B Z (arr w o) (arr w a) (arr w b) n := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have da := arr_disj (w := w) hoa
  have db := arr_disj (w := w) hob
  have hS : S w = 4 * (w + 2) := rfl
  refine ⟨h.nowrap, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, h.writable⟩

theorem Ws.subCtx {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) :
    SubCtx s B Z (arr w o) (arr w a) (arr w b) w :=
  h.subCtxN ho ha hb hoa hob (Nat.le_refl _)

/-- `lrPre lrw`: `lr = n`, set to `w` for `lrw`, or already `n`. -/
theorem lrPre_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) {lrw : Bool} {n : Nat}
    (hlr : lrw = true ∧ n = w ∨ lrw = false ∧ s.gpr .lr = BitVec.ofNat 32 n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Ws u B Z w N → u.gpr .lr = BitVec.ofNat 32 n → Rest [.lr] s u → u.mem = s.mem →
      WP isa (.block rest) u Q) :
    WP isa (.block (lrPre lrw ++ rest)) s Q := by
  rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, hl⟩
  · simp only [lrPre, List.cons_append, List.nil_append]
    exact wp_mov (op2_reg _ _) fun u u1 => k u (h.of_upd u1 (by decide) (by decide) (by decide))
      (by rw [u1.gpr, h.r9]) (u1.rest (by simp)) u1.mem
  · simp only [lrPre, List.nil_append]
    exact k s h hl (Rest.refl _ _) rfl

/-- `subN o a b lrw`: `[o] = [a] - [b]` over the `n` low words (`lr`), the borrow in `r11`. -/
theorem subN_ok {s : State} {B : BitVec 32} {Z w N o a b n : Nat} {lrw : Bool} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hn : 0 < n) (hnw : n ≤ w) (hlr : lrw = true ∧ n = w ∨ lrw = false ∧ s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (subN o a b lrw) s fun t => Ws t B Z w N ∧ Outside (State.addr B) (arr w o) (4 * n) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr w o) n + val32 s.mem (State.addr B) (arr w b) n =
        val32 s.mem (State.addr B) (arr w a) n + 2 ^ (32 * n) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest opRegs s t := by
  rw [subN, WP.seq_iff, List.append_assoc]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine lrPre_ok h3 (hlr.imp id fun ⟨e, l⟩ => ⟨e, by rw [r3.gpr _ (by decide)]; exact l⟩)
    fun s4 h4 l4 r4 m4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (m4.trans m3)
  have restU : Rest opRegs s u := (r3.mono (by simp)).trans ((r4.mono (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (subRow_ok u (hu.subCtxN ho ha hb hoa hob hnw) hn
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p0])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p10])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p12])
    (by rw [u5.other _ (by decide), l4])
    (by rw [u5.gpr]; decide)) ?_
  intro t inv
  have v := inv.value
  rw [u5.gpr, mu] at v
  refine ⟨hu.rest inv.rest, by simpa only [mu] using inv.outside, ?_, inv.borrow,
    restU.trans (inv.rest.mono (by simp))⟩
  simpa using v

/-- `sub3 o a b`: `[o] = [a] - [b]` with the borrow in `r11`. -/
theorem sub3_ok {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (32 * w) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest opRegs s t := by
  rw [sub3]
  refine WP.mono (subN_ok h ho ha hb hN hoa hob h.wpos (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩))
    fun t ⟨ht, O, v, c, R⟩ => ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
      (by simp only [S]; omega_arith) (by simp), v, c, R⟩

/-- `selN o a b sl lrw`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0, over the `n` low words. -/
theorem selN_ok {s : State} {B : BitVec 32} {Z w N o a b sl n : Nat} {lrw : Bool} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 4 ≤ hdr) (bit : slot s.mem B sl ≤ 1)
    (hn : 0 < n) (hnw : n ≤ w) (hlr : lrw = true ∧ n = w ∨ lrw = false ∧ s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (selN o a b sl lrw) s fun t => Ws t B Z w N ∧ Outside (State.addr B) (arr w o) (4 * n) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr w o) n = (if slot s.mem B sl = 0 then
        val32 s.mem (State.addr B) (arr w a) n else val32 s.mem (State.addr B) (arr w b) n) ∧
      Rest opRegs s t := by
  rw [selN, WP.seq_iff, List.append_assoc]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine lrPre_ok h3 (hlr.imp id fun ⟨e, l⟩ => ⟨e, by rw [r3.gpr _ (by decide)]; exact l⟩)
    fun s4 h4 l4 r4 m4 => ?_
  refine wp_ldrSlot h4 hsl fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (m4.trans m3)
  have restU : Rest opRegs s u := (r3.mono (by simp)).trans ((r4.mono (by simp)).trans (u5.rest (by simp)))
  have bitU : (u.gpr .r11).toNat = slot s.mem B sl := by rw [u5.gpr, m4, m3]
  refine WP.mono (selectRow_ok u (hu.subCtxN ho ha hb hoa hob hnw) hn
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p0])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p10])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p12])
    (by rw [u5.other _ (by decide), l4])
    (by rw [bitU]; exact bit)) ?_
  intro t inv
  have v := inv.value
  rw [bitU, mu] at v
  exact ⟨hu.rest inv.rest, by simpa only [mu] using inv.outside, v, restU.trans (inv.rest.mono (by simp))⟩

/-- `sel o a b sl`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_ok {s : State} {B : BitVec 32} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 4 ≤ hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Rest opRegs s t := by
  rw [sel]
  refine WP.mono (selN_ok h ho ha hb hN hoa hob hsl bit h.wpos (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩))
    fun t ⟨ht, O, v, R⟩ => ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
      (by simp only [S]; omega_arith) (by simp), v, R⟩

/-- `copyN o a lrw`: `[o] = [a]` over the `n` low words. -/
theorem copyN_ok {s : State} {B : BitVec 32} {Z w N o a n : Nat} {lrw : Bool} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a)
    (hn : 0 < n) (hnw : n ≤ w) (hlr : lrw = true ∧ n = w ∨ lrw = false ∧ s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (copyN o a lrw) s fun t => Ws t B Z w N ∧ Outside (State.addr B) (arr w o) (4 * n) s.mem t.mem ∧
      val32 t.mem (State.addr B) (arr w o) n = val32 s.mem (State.addr B) (arr w a) n ∧ Rest opRegs s t := by
  rw [copyN, WP.seq_iff, List.append_assoc]
  refine ptr3_ok h (by omega_arith) (by omega_arith) (by omega_arith) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine lrPre_ok h3 (hlr.imp id fun ⟨e, l⟩ => ⟨e, by rw [r3.gpr _ (by decide)]; exact l⟩)
    fun s4 h4 l4 r4 m4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (m4.trans m3)
  have restU : Rest opRegs s u := (r3.mono (by simp)).trans ((r4.mono (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (copyWords_ok u (hu.subCtxN ho ha ha hoa hoa hnw) hn
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p0])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p10])
    (by rw [u5.other _ (by decide), r4.gpr _ (by decide), p12])
    (by rw [u5.other _ (by decide), l4])) ?_
  intro t inv
  have v := inv.value
  rw [mu] at v
  refine ⟨hu.rest inv.rest, by simpa only [mu] using inv.outside, ?_, restU.trans (inv.rest.mono (by simp))⟩
  rw [v]; split <;> rfl

/-- `copy o a`: `[o] = [a]`. -/
theorem copy_ok {s : State} {B : BitVec 32} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Rest opRegs s t ∧
      w32 t.mem (State.addr B) (arr w o + 4 * w) = w32 s.mem (State.addr B) (arr w o + 4 * w) := by
  rw [copy]
  have fo := h.fit64 ho
  refine WP.mono (copyN_ok h ho ha hN hoa h.wpos (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩))
    fun t ⟨ht, O, v, R⟩ => ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
      (by simp only [S]; omega_arith) (by simp), v, R, ?_⟩
  exact O.w32 (by omega_arith) (by simp only [S] at fo; omega_arith)

end VG.Proof.Rsa.Arm.Keys
