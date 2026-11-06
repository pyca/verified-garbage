module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Base
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Bignum.RISCV64.Run

/-!
# RSA paddings on RISC-V: MGF1

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/MgfArith.lean`, `MgfSteps.lean`, `Mgf.lean`):
a comparison of values below `2⁶³` as the top bit of their difference
(`ltBit`, `msgBit`), the selection of `min(a, b)` from it (`minSel`), the
bytes of the counter (`i2osp_four`) and of an exclusive-or (`byte_xor`); the
blocks of MGF1's round between the calls: the counter written big-endian to
`S + oCtr` (`ctr_ok`, as `ctrV`) and the exclusive-or of digest bytes into
`dst` (`xorLoop_ok`); where `src` and `dst` lie (`MFit`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_xor wp_mov wp_srl
  wp_sb wp_lbu wp_nil eval_nonzero ofNat_succ')
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaPkcs1Sig (bytesAt_length writeBytes_out)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-! ## Arithmetic -/

theorem ltBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = if x < y then 1 else 0 := by
  have e : ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63).toNat = if x < y then 1 else 0 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    split <;> omega
  apply BitVec.eq_of_toNat_eq; rw [e]; split <;> rfl

theorem ne_zero_ltBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 != 0) = decide (x < y) := by
  rw [ltBit hx hy]; split <;> simp_all

/-- The test of `chkMsg`: the top bit of `y`, or of `x - y`, for `x < 2⁶³`. -/
theorem msgBit {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 64) :
    ((BitVec.ofNat 64 y >>> 63 ||| (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63) != 0) = decide (x < y) := by
  by_cases h : y < 2 ^ 63
  · rw [ltBit hx h]
    have e : BitVec.ofNat 64 y >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
    rw [e]; split <;> rename_i hxy <;> simp only [hxy, decide_true, decide_false] <;> decide
  · have e : BitVec.ofNat 64 y >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [Nat.mod_eq_of_lt hy]; simp; omega
    rw [e, decide_eq_true (by omega), bne_iff_ne]
    intro h0
    have := congrArg (fun v : BitVec 64 => v.getLsbD 0) h0
    simp at this

/-- `b + ((a - b) ∧ -(a < b))`: `min(a, b)`. -/
theorem minSel {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 b + ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63)) = BitVec.ofNat 64 (min b a) := by
  rw [ltBit ha hb]
  by_cases h : a < b
  · rw [ite_eq_left h, show BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      Nat.min_eq_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right h, show BitVec.ofNat 64 0 - 0 = 0#64 by decide, BitVec.and_zero, BitVec.add_zero,
      Nat.min_eq_left (by omega)]

theorem trunc8 (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem shr8 {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 8 = BitVec.ofNat 64 (x / 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- `I2OSP(c, 4)`, byte by byte. -/
theorem i2osp_four (c : Nat) :
    Spec.Rsa.i2osp c 4 = [BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8), BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8),
      BitVec.ofNat 8 (c / 2 ^ 8), BitVec.ofNat 8 c] := by
  simp only [Spec.Rsa.i2osp, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul, Nat.reduceSub,
    Nat.pow_zero, Nat.div_one]

theorem byte_xor (x y : Byte) : BitVec.setWidth 8 (x.setWidth 64 ^^^ y.setWidth 64) = x ^^^ y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  have := x.isLt
  have := y.isLt
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
  have : x.toNat ^^^ y.toNat < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  omega


/-! ## The blocks between the calls -/

/-- Our part of the working space with `I2OSP(c, 4)` at `oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (o : Nat) : Byte :=
  if oCtr ≤ o ∧ o < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (o - oCtr) 0 else V o

theorem off_add (S : Addr) (d j : Nat) : off S d + BitVec.ofNat 64 j = off S (d + j) := off_off S d j

theorem view_w8' (m : Mem) {S : Addr} {d j o : Nat} (b : Byte) (hd : d + j < oRsa) (ho : o < oRsa) :
    view (m.writeW (off S d + BitVec.ofNat 64 j) b) S o = if o = d + j then b else view m S o := by
  rw [off_add]; exact view_w8 m b hd ho

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

/-- The counter, big-endian, to `S + oCtr`; then `update`'s arguments for it. -/
theorem ctr_ok {t : State} (h : Base S vf s t) {c : Nat} (h10 : t.gpr .s10 = BitVec.ofNat 64 c) (hc : c < 2 ^ 32) :
    WP isa (.block updCtrArgs) t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      (∀ o < oRsa, view t'.mem (S s) o = ctrV (view t.mem (S s)) c o) ∧
      t'.gpr .a0 = off (S s) oSt ∧ t'.gpr .a1 = t.gpr .s7 ∧ t'.gpr .a2 = off (S s) oCtr ∧
      t'.gpr .a3 = BitVec.ofNat 64 4 := by
  obtain ⟨_, _, _, _, _⟩ := offs
  have hw : ∀ {u : State}, u.wr = t.wr → ∀ j < 4, InRegions u.wr (off (S s) oCtr + BitVec.ofNat 64 j) 1 :=
    fun hu j hj => by rw [hu, h.wr, off_add]; exact sc_inW P (by omega)
  simp only [updCtrArgs]
  refine wp_addi (imm := oCtr) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => ?_
  have a₂ : u₂.gpr .a2 = off (S s) oCtr := by rw [o₂.get .a2, e₁, h.s0]
  have k₂ : Only [.a2, .t1] t u₂ := (o₁.trans o₂).mono
  refine wp_sb (a := off (S s) oCtr + BitVec.ofNat 64 3) (by rw [a₂]) (hw k₂.wr 3 (by omega)) fun u₃ m₃ => ?_
  refine wp_srl fun u₄ o₄ e₄ => ?_
  refine wp_sb (a := off (S s) oCtr + BitVec.ofNat 64 2) (by rw [o₄.get .a2, m₃.gpr, a₂])
    (hw (by rw [o₄.wr, m₃.wr, k₂.wr]) 2 (by omega)) fun u₅ m₅ => ?_
  refine wp_srl fun u₆ o₆ e₆ => ?_
  refine wp_sb (a := off (S s) oCtr + BitVec.ofNat 64 1) (by rw [o₆.get .a2, m₅.gpr, o₄.get .a2, m₃.gpr, a₂])
    (hw (by rw [o₆.wr, m₅.wr, o₄.wr, m₃.wr, k₂.wr]) 1 (by omega)) fun u₇ m₇ => ?_
  refine wp_srl fun u₈ o₈ e₈ => ?_
  refine wp_sb (a := off (S s) oCtr + BitVec.ofNat 64 0)
    (by rw [o₈.get .a2, m₇.gpr, o₆.get .a2, m₅.gpr, o₄.get .a2, m₃.gpr, a₂])
    (hw (by rw [o₈.wr, m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, k₂.wr]) 0 (by omega)) fun u₉ m₉ => ?_
  refine wp_addi (imm := oSt) fun u₁₀ o₁₀ e₁₀ => wp_mov fun u₁₁ o₁₁ e₁₁ =>
    wp_li (imm := 4) (by decide) fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  -- The bytes.
  have r1₂ : u₂.gpr .t1 = BitVec.ofNat 64 c := by rw [e₂, o₁.get .s10, h10]
  have r1₄ : u₄.gpr .t1 = BitVec.ofNat 64 (c / 2 ^ 8) := by rw [e₄, m₃.gpr, r1₂, shr8 (by omega)]
  have r1₆ : u₆.gpr .t1 = BitVec.ofNat 64 (c / 2 ^ 8 / 2 ^ 8) := by
    rw [e₆, m₅.gpr, r1₄, shr8 (by omega)]
  have r1₈ : u₈.gpr .t1 = BitVec.ofNat 64 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8) := by
    rw [e₈, m₇.gpr, r1₆, shr8 (by omega)]
  have k₁₂ : Only [.a0, .a1, .a3] u₉ u₁₂ := (o₁₀.trans (o₁₁.trans o₁₂)).mono
  have hm : u₁₂.mem = (((t.mem.writeW (off (S s) oCtr + BitVec.ofNat 64 3) (BitVec.ofNat 8 c)).writeW
      (off (S s) oCtr + BitVec.ofNat 64 2) (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off (S s) oCtr + BitVec.ofNat 64 1)
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW (off (S s) oCtr + BitVec.ofNat 64 0)
      (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)) := by
    rw [k₁₂.mem, m₉.mem, r1₈, trunc8, o₈.mem, m₇.mem, r1₆, trunc8, o₆.mem, m₅.mem, r1₄, trunc8, o₄.mem, m₃.mem,
      r1₂, trunc8, k₂.mem]
  have hK : Kept [.a0, .a1, .a2, .a3, .t1] t u₁₂ :=
    (k₂.keep.trans (m₃.keep.trans (o₄.keep.trans (m₅.keep.trans (o₆.keep.trans (m₇.keep.trans
      (o₈.keep.trans (m₉.keep.trans k₁₂.keep)))))))).mono
  have hf : Frame [⟨off (S s) oCtr, 4⟩] t.mem u₁₂.mem := by
    rw [hm]
    have c : ∀ j < 4, Region.Contains ⟨off (S s) oCtr, 4⟩ (off (S s) oCtr + BitVec.ofNat 64 j) (8 / 8) :=
      fun j hj => Offset.contains_base _ (by omega) (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 2 (by omega)) |>.writeW (List.mem_singleton_self _) _ (c 1 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 0 (by omega))
  refine ⟨h.keep P hK hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))),
    fun r hr => hK.gpr r (by revert r; decide), fun o ho => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, view_w8' _ _ (by omega) ho, view_w8' _ _ (by omega) ho, view_w8' _ _ (by omega) ho,
      view_w8' _ _ (by omega) ho, ctrV, i2osp_four]
    rcases (show o = oCtr ∨ o = oCtr + 1 ∨ o = oCtr + 2 ∨ o = oCtr + 3 ∨ ¬(oCtr ≤ o ∧ o < oCtr + 4) by omega) with
      h' | h' | h' | h' | h'
    · subst h'; simp
    · subst h'; simp
    · subst h'; simp
    · subst h'; simp
    · rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega), ifn h']
  · rw [o₁₂.get .a0, o₁₁.get .a0, e₁₀, m₉.gpr, o₈.get .s0, m₇.gpr, o₆.get .s0, m₅.gpr,
      o₄.get .s0, m₃.gpr, k₂.get .s0, h.s0]
  · rw [o₁₂.get .a1, e₁₁, o₁₀.get .s7, m₉.gpr, o₈.get .s7, m₇.gpr, o₆.get .s7, m₅.gpr,
      o₄.get .s7, m₃.gpr, k₂.get .s7]
  · rw [k₁₂.get .a2, m₉.gpr, o₈.get .a2, m₇.gpr, o₆.get .a2, m₅.gpr, o₄.get .a2, m₃.gpr, a₂]
  · rw [e₁₂]

end

/-- The `n` bytes at `p` XORed with those at `q`. -/
def xorAt (m : Mem) (p q : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i)

theorem xorAt_length (m : Mem) (p q : Addr) (n : Nat) : (xorAt m p q n).length = n := by simp [xorAt]

theorem xorAt_take_succ (m : Mem) (p q : Addr) {n i : Nat} (hi : i < n) :
    (xorAt m p q n).take (i + 1) =
      (xorAt m p q n).take i ++ [m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i)] := by
  simp only [xorAt]
  rw [← List.map_take, ← List.map_take, List.take_range, List.take_range, Nat.min_eq_left (by omega),
    Nat.min_eq_left (by omega), List.range_succ, List.map_append]
  rfl

/-- `xorBody`'s loop XORs the `n` bytes at `a4 = q` into those at
`a5 = p`, counted down in `a6`. -/
theorem xorLoop_ok {t : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : t.gpr .a4 = q) (h5 : t.gpr .a5 = p) (h6 : t.gpr .a6 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions t.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i)
    (hp : ∀ i < n, ∀ j < n, i ≠ j → p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j) :
    WP isa (Impl.Bignum.RISCV64.countLoop .a6 xorBody) t fun t' => Kept [.t1, .t2, .a4, .a5, .a6] t t' ∧
      t'.mem = writeBytes t.mem p (xorAt t.mem p q n) := by
  refine WP.mono (wp_countdown (cnt := .a6) hn' hn
    (fun i u => Kept [.t1, .t2, .a4, .a5, .a6] t u ∧
      u.mem = writeBytes t.mem p ((xorAt t.mem p q n).take i) ∧
      u.gpr .a5 = p + BitVec.ofNat 64 i ∧ u.gpr .a4 = q + BitVec.ofNat 64 i) ?_
    ⟨Kept.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun u h => ⟨h.1, ?_⟩
  · intro i hi u ⟨hK, hm, h5', h4'⟩ _
    simp only [xorBody, List.cons_append, List.nil_append]
    have hR : InRegions (u.rd ++ u.wr) (u.gpr .a4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hvq : u.mem (q + BitVec.ofNat 64 i) = t.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, xorAt_length]; omega)]
    have hvp : u.mem (p + BitVec.ofNat 64 i) = t.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun i' hi' => hp i hi i' (by omega) (by omega))
        (by simp only [List.length_take, xorAt_length]; omega)]
    refine wp_lbu rfl hR fun u₁ o₁ e₁ => ?_
    have hR' : InRegions (u₁.rd ++ u₁.wr) (u₁.gpr .a5 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.get .a5, h5', o₁.rd, o₁.wr, hK.rd, hK.wr, BitVec.add_zero]
      obtain ⟨r, hr', hc⟩ := hw i hi
      exact ⟨r, List.mem_append_right _ hr', hc⟩
    refine wp_lbu rfl hR' fun u₂ o₂ e₂ => wp_xor fun u₃ o₃ e₃ => ?_
    have hA : InRegions u₃.wr (u₃.gpr .a5 + BitVec.ofNat 64 0) 1 := by
      rw [o₃.wr, o₂.wr, o₁.wr, o₃.get .a5, o₂.get .a5, o₁.get .a5, h5', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_sb rfl hA fun u₄ m₄ => wp_addi (imm := 1) fun u₅ o₅ e₅ => wp_addi (imm := 1) fun u₆ o₆ e₆ =>
      wp_subi (imm := 1) fun u₇ o₇ e₇ => wp_nil ?_
    have hK' : Kept [.t1, .t2, .a4, .a5, .a6] u u₇ :=
      (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (m₄.keep.trans (o₅.keep.trans (o₆.keep.trans
        o₇.keep)))))).mono
    have hlt : ((xorAt t.mem p q n).take i).length = i := by simp [xorAt_length]; omega
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₇.mem, o₆.mem, o₅.mem, m₄.mem, e₃, e₂, o₂.get .t1, e₁, o₃.mem, o₂.mem, o₁.mem, o₃.get .a5,
        o₂.get .a5, o₁.get .a5, h5', h4']
      simp only [BitVec.add_zero]
      rw [hvp, hvq, byte_xor, hm, xorAt_take_succ _ _ _ hi, writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₇.get .a5, e₆, o₅.get .a5, m₄.gpr, o₃.get .a5, o₂.get .a5, o₁.get .a5, h5', ofNat_succ']
    · rw [o₇.get .a4, o₆.get .a4, e₅, m₄.gpr, o₃.get .a4, o₂.get .a4, o₁.get .a4, h4', ofNat_succ']
    · rw [e₇, o₆.get .a6, o₅.get .a6, m₄.gpr, o₃.get .a6, o₂.get .a6, o₁.get .a6]
  · rw [List.take_of_length_le (by simp [xorAt_length])] at h
    exact h.2.1

/-! ## The rounds -/

/-- The offsets of our part of the working space that MGF1 changes only in
`dst`: all but those of the streaming state, the digest and the counter. -/
abbrev Kp (o : Nat) : Prop := o < oRsa ∧ (o < oSt ∨ oCtr + 4 ≤ o)

/-- `src`, `srcLen`, `dst` and `dstLen`: in `EM`'s place, and apart. -/
structure MFit (src srcLen dst dstLen : Nat) : Prop where
  fs : src + srcLen ≤ 1024
  fd : dst + dstLen ≤ 1024
  sep : src + srcLen ≤ dst ∨ dst + dstLen ≤ src
  pos : 0 < dstLen

theorem xorAt_getD (m : Mem) (p q : Addr) {n i : Nat} (hi : i < n) :
    (xorAt m p q n).getD i 0 = m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i) := by
  simp [xorAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- The bytes of `src`, from the view. -/
theorem bytesAt_view (m : Mem) (S : Addr) (src n : Nat) :
    Spec.Rsa.bytesAt m (off S src) n = srcB (view m S) src n := by
  simp only [Spec.Rsa.bytesAt, srcB, view]
  exact List.map_congr_left fun i _ => by rw [off_add]

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

end

end VG.Proof.RsaOaep.RISCV64
