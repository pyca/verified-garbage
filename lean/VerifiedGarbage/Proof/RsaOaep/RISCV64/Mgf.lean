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
`S + oCtr` (`ctr_ok`, as `ctrV`), how many digest bytes go into `dst`
(`xorHead_ok`), their exclusive-or into it (`xorLoop_ok`), and the next
counter (`nextCtr_ok`); `round_ok`, a round of `mgfXor` XORs the next block
of the mask into `dst` (`MgfI`, the invariant: after `c` rounds, the first
`min(c hLen, dstLen)` bytes of the mask are XORed in); `mgfXor_ok`,
`dst ⊕= MGF1(src, dstLen)` in `EM`'s place (`mixV`).
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

theorem byte64 (b : Byte) : ((b.setWidth 64)).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq; simp

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

/-- How many bytes of the digest go into `dst`: `min(hLen, dstLen - done)`. -/
theorem xorHead_ok {G : Hash} {t : State} {S : Addr} {dst dstLen done : Nat}
    (hD : G.D < 2048) (h0 : t.gpr .s0 = S) (h8 : t.gpr .s8 = off S dst) (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 done) (hlt : done < dstLen) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (xorHead G)) t fun t' => Only [.a4, .a5, .a6, .t1, .t2, .t3, .t4] t t' ∧
      t'.gpr .a4 = off S oDig ∧ t'.gpr .a5 = off S (dst + done) ∧
      t'.gpr .a6 = BitVec.ofNat 64 (min G.D (dstLen - done)) := by
  simp only [xorHead]
  refine wp_addi (imm := oDig) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_li (imm := G.D) hD fun u₄ o₄ e₄ => wp_sub fun u₅ o₅ e₅ => wp_srl fun u₆ o₆ e₆ =>
    wp_li (imm := 0) (by decide) fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ =>
    wp_and fun u₉ o₉ e₉ => wp_add fun u₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k : Only [.a4, .a5, .a6, .t1, .t2, .t3, .t4] t u₁₀ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have r1 : u₃.gpr .t1 = BitVec.ofNat 64 (dstLen - done) := by
    rw [e₃, o₂.get .s9, o₂.get .s11, o₁.get .s9, o₁.get .s11, h9, h11, Offset.ofNat_sub_ofNat (by omega)]
  have r2 : u₅.gpr .t2 = BitVec.ofNat 64 (dstLen - done) - BitVec.ofNat 64 G.D := by
    rw [e₅, o₄.get .t1, r1, e₄]
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [o₁₀.get .a4, o₉.get .a4, o₈.get .a4, o₇.get .a4, o₆.get .a4, o₅.get .a4, o₄.get .a4, o₃.get .a4,
      o₂.get .a4, e₁, h0]
  · rw [o₁₀.get .a5, o₉.get .a5, o₈.get .a5, o₇.get .a5, o₆.get .a5, o₅.get .a5, o₄.get .a5, o₃.get .a5, e₂,
      o₁.get .s8, o₁.get .s11, h8, h11, off_add]
  · rw [e₁₀, o₉.get .a6, o₈.get .a6, o₇.get .a6, o₆.get .a6, o₅.get .a6, e₄, e₉, o₈.get .t2, o₇.get .t2,
      o₆.get .t2, r2, e₈, e₇, o₇.get .t3, e₆, r2]
    exact minSel (by omega) (by omega)

/-- `nextCtr`: the next counter and `done`, and in `t1` whether `done` is
still below `dstLen`. -/
theorem nextCtr_ok {G : Hash} {t : State} {c done dstLen : Nat}
    (h10 : t.gpr .s10 = BitVec.ofNat 64 c) (h11 : t.gpr .s11 = BitVec.ofNat 64 done)
    (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen) (hD : G.D < 2048) (hd : done + G.D < 2 ^ 63) (hdl : dstLen < 2 ^ 63) :
    WP isa (.block (nextCtr G)) t fun t' => Only [.s10, .s11, .t1] t t' ∧
      t'.gpr .s10 = BitVec.ofNat 64 (c + 1) ∧ t'.gpr .s11 = BitVec.ofNat 64 (done + G.D) ∧
      (t'.gpr .t1 != 0) = decide (done + G.D < dstLen) := by
  simp only [nextCtr]
  refine wp_addi (imm := 1) fun u₁ o₁ e₁ => wp_addi (imm := G.D) (h := hD) fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ =>
    wp_srl fun u₄ o₄ e₄ => wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_, ?_⟩
  · rw [o₄.get .s10, o₃.get .s10, o₂.get .s10, e₁, h10, BitVec.ofNat_add]
  · rw [o₄.get .s11, o₃.get .s11, e₂, o₁.get .s11, h11, BitVec.ofNat_add]
  · rw [e₄, e₃, o₂.get .s9, e₂, o₁.get .s11, o₁.get .s9, h11, h9, ← BitVec.ofNat_add]
    exact ne_zero_ltBit hd hdl

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

/-- After `c` rounds: `Base`, MGF1's registers, and the first
`min(c D, dstLen)` bytes of the mask `mk` XORed into `dst` in `EM`'s place,
whose view was `V`. -/
structure MgfI (S : State → Addr) (vf : State → Reg → BitVec 64) (s : State) (V : Nat → Byte) (mk : List Byte)
    (src srcLen dst dstLen D c : Nat) (v : State) : Prop where
  base : Base S vf s v
  s6 : v.gpr .s6 = off (S s) src
  s7 : v.gpr .s7 = BitVec.ofNat 64 srcLen
  s8 : v.gpr .s8 = off (S s) dst
  s9 : v.gpr .s9 = BitVec.ofNat 64 dstLen
  s10 : v.gpr .s10 = BitVec.ofNat 64 c
  s11 : v.gpr .s11 = BitVec.ofNat 64 (c * D)
  em : ∀ o, Kp o → view v.mem (S s) o = mixV V mk dst (min (c * D) dstLen) o

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

theorem round_ok {G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs) {V : Nat → Byte}
    {src srcLen dst dstLen c : Nat} (hf : MFit src srcLen dst dstLen) {v : State}
    (I : MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D c v)
    (hc : c * G.D < dstLen) :
    WP isa (round G) v fun v' => (v'.gpr .t1 != 0) = decide ((c + 1) * G.D < dstLen) ∧
      MgfI S vf s V (Spec.Mgf1.mgf1 Gs (srcB V src srcLen) dstLen) src srcLen dst dstLen G.D (c + 1) v' := by
  have F := hfits hG
  obtain ⟨_, hSt, hDg, hCt, hRs⟩ := offs
  have hD0 := hG.hD0
  have hD64 := hG.hD64
  have hfs := hf.fs
  have hfd := hf.fd
  have hsep := hf.sep
  have hcD : c ≤ c * G.D := Nat.le_mul_of_pos_right c hD0
  -- The registers MGF1 keeps.
  let mg : List Reg := [.s6, .s7, .s8, .s9, .s10, .s11]
  have pm : ∀ r ∈ mg, r ∈ preserved := by decide
  -- `init`.
  refine WP.seq (wp_addi (imm := oSt) fun t₁ o₁ e₁ => wp_nil ?_)
  have b₁ := I.base.only P o₁
  refine WP.seq (WP.mono (init_ok P hG hF b₁ (by rw [e₁, I.base.s0])) fun t₂ ⟨b₂, g₂, s₂, r₂⟩ => ?_)
  have m₂ : ∀ r ∈ mg, t₂.gpr r = v.gpr r := fun r hr => by
    rw [g₂ r (pm r hr), o₁.gpr r (by revert r; decide)]
  -- `update` with `src`.
  refine WP.seq (wp_addi (imm := oSt) fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ =>
    wp_mov fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil ?_)
  have k₆ : Only [.a0, .a1, .a2, .a3] t₂ t₆ := (o₃.trans (o₄.trans (o₅.trans o₆))).mono
  have b₆ := b₂.only P k₆
  refine WP.seq (WP.mono (upd_ok P hG hF b₆ (dat := off (S s) src) (len := srcLen)
    (by rw [o₆.get .a0, o₅.get .a0, o₄.get .a0, e₃, b₂.s0])
    (by rw [o₆.get .a2, e₅, o₄.get .s6, o₃.get .s6, m₂ _ (by decide), I.s6])
    (by rw [e₆, o₅.get .s7, o₄.get .s7, o₃.get .s7, m₂ _ (by decide), I.s7, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)])
    (Covers.right (by rw [b₆.wr]; exact sc_cov P (by omega))) (sdis (.inl (by omega)) (by omega) (by omega))
    (cR_dis P (by omega))) fun t₇ ⟨b₇, g₇, s₇, r₇⟩ => ?_)
  have m₇ : ∀ r ∈ mg, t₇.gpr r = v.gpr r := fun r hr => by
    rw [g₇ r (pm r hr), k₆.gpr r (by revert r; decide), m₂ r hr]
  have hsrc : Spec.Rsa.bytesAt t₆.mem (off (S s) src) srcLen = srcB V src srcLen := by
    rw [bytesAt_view]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [k₆.mem, s₂ _ (by omega) (by simp; omega), o₁.mem, I.em _ ⟨by omega, .inl (by omega)⟩, mixV, ifn (by omega)]
  have hR7 : hG.SH.Repr t₇.mem (off (S s) oSt) (srcB V src srcLen) := by
    have := r₇ [] (by rw [k₆.mem]; exact r₂) (by rw [o₆.get .a1, o₅.get .a1, e₄]; rfl)
    rw [List.nil_append] at this
    exact hsrc ▸ this
  -- The counter, and `update` with it.
  refine WP.seq (WP.mono (ctr_ok P b₇ (c := c) (by rw [m₇ _ (by decide), I.s10]) (by omega))
    fun t₈ ⟨b₈, g₈, v₈, x0, x1, x2, x3⟩ => ?_)
  have m₈ : ∀ r ∈ mg, t₈.gpr r = v.gpr r := fun r hr => by rw [g₈ r (pm r hr), m₇ r hr]
  have hR8 : hG.SH.Repr t₈.mem (off (S s) oSt) (srcB V src srcLen) :=
    hG.congr t₇.mem t₈.mem (off (S s) oSt) _ (fun i hi => by
      have e := v₈ (oSt + i) (by omega)
      simp only [view, ctrV] at e
      rw [ifn (by omega)] at e
      rw [off_add]; exact e) hR7
  refine WP.seq (WP.mono (upd_ok P hG hF b₈ (dat := off (S s) oCtr) (len := 4) x0 x2 (by rw [x3]; rfl)
    (Covers.right (by rw [b₈.wr]; exact sc_cov P (by omega))) (sdis (.inr (by omega)) (by omega) (by omega))
    (cR_dis P (by omega))) fun t₉ ⟨b₉, g₉, s₉, r₉⟩ => ?_)
  have m₉ : ∀ r ∈ mg, t₉.gpr r = v.gpr r := fun r hr => by rw [g₉ r (pm r hr), m₈ r hr]
  have hctr : Spec.Rsa.bytesAt t₈.mem (off (S s) oCtr) 4 = Spec.Rsa.i2osp c 4 := by
    rw [bytesAt_view]
    refine (List.map_congr_left fun i hi => ?_).trans ((RsaOaep.range_map_getD (n := 4)
      (xs := Spec.Rsa.i2osp c 4) (by rw [Proof.Mgf1.i2osp_length])).trans
      (List.take_of_length_le (by rw [Proof.Mgf1.i2osp_length])))
    have := List.mem_range.mp hi
    rw [v₈ _ (by omega), ctrV, ifp (by omega), Nat.add_sub_cancel_left]
  have hml : (srcB V src srcLen).length = srcLen := by simp [srcB]
  have hR9 : hG.SH.Repr t₉.mem (off (S s) oSt) (srcB V src srcLen ++ Spec.Rsa.i2osp c 4) := by
    have := r₉ _ hR8 (by rw [x1, m₇ _ (by decide), I.s7, hml])
    exact hctr ▸ this
  -- `finalize`.
  refine WP.seq (wp_addi (imm := oSt) fun t₁₀ o₁₀ e₁₀ => wp_addi (imm := 4) fun t₁₁ o₁₁ e₁₁ =>
    wp_addi (imm := oDig) fun t₁₂ o₁₂ e₁₂ => wp_nil ?_)
  have k₁₂ : Only [.a0, .a1, .a2] t₉ t₁₂ := (o₁₀.trans (o₁₁.trans o₁₂)).mono
  have b₁₂ := b₉.only P k₁₂
  have hl4 : (srcB V src srcLen ++ Spec.Rsa.i2osp c 4).length = srcLen + 4 := by
    rw [List.length_append, hml, Proof.Mgf1.i2osp_length]
  refine WP.seq (WP.mono (fin_ok P hG hF b₁₂ (by rw [o₁₂.get .a0, o₁₁.get .a0, e₁₀, b₉.s0])
    (by rw [e₁₂, o₁₁.get .s0, o₁₀.get .s0, b₉.s0])) fun t₁₃ ⟨b₁₃, g₁₃, s₁₃, r₁₃⟩ => ?_)
  have m₁₃ : ∀ r ∈ mg, t₁₃.gpr r = v.gpr r := fun r hr => by
    rw [g₁₃ r (pm r hr), k₁₂.gpr r (by revert r; decide), m₉ r hr]
  have hfh := r₁₃ _ (by rw [k₁₂.mem]; exact hR9) (by rw [hl4]; omega)
    (by rw [o₁₂.get .a1, e₁₁, o₁₀.get .s7, m₉ _ (by decide), I.s7, hl4, BitVec.ofNat_add])
  have hdig : ∀ j < G.D, view t₁₃.mem (S s) (oDig + j) =
      (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD j 0 := fun j hj => by
    rw [hGh, ← hfh, view, ← off_add]
    simp only [Spec.Sha256.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  -- Into `dst`.
  have hdc := Nat.min_le_left G.D (dstLen - c * G.D)
  have hn0 : 0 < min G.D (dstLen - c * G.D) := by omega
  refine WP.seq (WP.seq (WP.mono (xorHead_ok (G := G) (S := S s) (dst := dst) (dstLen := dstLen)
    (done := c * G.D) (by omega) b₁₃.s0 (by rw [m₁₃ _ (by decide), I.s8]) (by rw [m₁₃ _ (by decide), I.s9])
    (by rw [m₁₃ _ (by decide), I.s11]) hc (by omega)) fun t₁₄ ⟨k₁₄, x4, x5, x6⟩ => ?_))
  have b₁₄ := b₁₃.only P k₁₄
  refine WP.mono (xorLoop_ok (p := off (S s) (dst + c * G.D)) (q := off (S s) oDig) hn0 (by omega) x4 x5 x6
    (fun j hj => by
      rw [off_add, k₁₄.rd, k₁₄.wr, b₁₃.wr, b₁₃.rd]; exact sc_inR P (by omega) _)
    (sc_w P (by rw [k₁₄.wr, b₁₃.wr]) (by omega))
    (fun j hj i hi => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))
    (fun i hi j hj hij => by
      rw [off_add, off_add]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)))
    fun t₁₅ ⟨k₁₅, x₁₅⟩ => ?_
  have b₁₅ : Base S vf s t₁₅ := b₁₄.wb P k₁₅ (by rw [xorAt_length]; omega) x₁₅
  have m₁₅ : ∀ r ∈ mg, t₁₅.gpr r = v.gpr r := fun r hr => by
    rw [k₁₅.gpr r (by revert r; decide), k₁₄.gpr r (by revert r; decide), m₁₃ r hr]
  -- The next counter.
  refine WP.mono (nextCtr_ok (G := G) (c := c) (done := c * G.D) (dstLen := dstLen)
    (by rw [m₁₅ _ (by decide), I.s10]) (by rw [m₁₅ _ (by decide), I.s11]) (by rw [m₁₅ _ (by decide), I.s9])
    (by omega) (by omega) (by omega)) fun t₁₆ ⟨k₁₆, x10, x11, xt⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  refine ⟨by rw [xt, hs1], b₁₅.only P k₁₆, by rw [k₁₆.get .s6, m₁₅ _ (by decide), I.s6],
    by rw [k₁₆.get .s7, m₁₅ _ (by decide), I.s7], by rw [k₁₆.get .s8, m₁₅ _ (by decide), I.s8],
    by rw [k₁₆.get .s9, m₁₅ _ (by decide), I.s9], x10, by rw [x11, hs1], fun o ⟨ho, ho'⟩ => ?_⟩
  -- `EM`'s place.
  have hold : view t₁₃.mem (S s) o = view v.mem (S s) o := by
    have e₁₃ := s₁₃ o (by omega) (by simp; omega)
    have e₉ := s₉ o (by omega) (by simp; omega)
    have e₈ := v₈ o (by omega)
    have e₇ := s₇ o (by omega) (by simp; omega)
    have e₂ := s₂ o (by omega) (by simp; omega)
    simp only [ctrV] at e₈
    rw [ifn (by omega)] at e₈
    simp only [view] at *
    rw [e₁₃, k₁₂.mem, e₉, e₈, e₇, k₆.mem, e₂, o₁.mem]
  have hv : view t₁₆.mem (S s) o = if dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D) then
      view v.mem (S s) o ^^^ (Gs.hash (srcB V src srcLen ++ Spec.Rsa.i2osp c 4)).getD (o - (dst + c * G.D)) 0
      else view v.mem (S s) o := by
    rw [k₁₆.mem, x₁₅, k₁₄.mem, view_wb _ _ (by rw [xorAt_length]; omega) (by omega), xorAt_length]
    split
    · rename_i hx
      rw [xorAt_getD _ _ _ (by omega), off_add, off_add,
        show dst + c * G.D + (o - (dst + c * G.D)) = o by omega, ← hold]
      simp only [view]
      rw [← hdig _ (by omega)]
      simp only [view]
    · exact hold
  rw [hv]
  by_cases hx : dst + c * G.D ≤ o ∧ o < dst + c * G.D + min G.D (dstLen - c * G.D)
  · have hs2 : G.D * (c + 1) = c * G.D + G.D := by rw [Nat.mul_comm]; exact hs1
    have hs3 : G.D * c = c * G.D := Nat.mul_comm _ _
    have hq : (o - dst) / G.D = c := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hr : (o - dst) % G.D = o - (dst + c * G.D) := by
      rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]; omega
    rw [ifp hx, I.em o ⟨ho, ho'⟩, mixV, mixV, ifn (by omega), ifp (by rw [hs1]; omega),
      Proof.Mgf1.mgf1_getD hGv _ (show o - dst < dstLen by omega), hGl, hq, hr]
  · rw [ifn hx, I.em o ⟨ho, ho'⟩, mixV, mixV]
    by_cases hy : dst ≤ o ∧ o < dst + min (c * G.D) dstLen
    · rw [ifp hy, ifp (by rw [hs1]; omega)]
    · rw [ifn hy, ifn (by rw [hs1]; omega)]

/-- `dst ⊕= MGF1(src, dstLen)` in `EM`'s place, from `src`, `srcLen`, `dst`
and `dstLen` in `s6`–`s9`. -/
theorem mgfXor_ok {G : Hash} (hG : HashOK G) (hF : G.F ≤ 208) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D) (hGv : Proof.Mgf1.Valid Gs)
    {src srcLen dst dstLen : Nat} (hf : MFit src srcLen dst dstLen) {t : State} (h : Base S vf s t)
    (h6 : t.gpr .s6 = off (S s) src) (h7 : t.gpr .s7 = BitVec.ofNat 64 srcLen) (h8 : t.gpr .s8 = off (S s) dst)
    (h9 : t.gpr .s9 = BitVec.ofNat 64 dstLen) :
    WP isa (mgfXor G) t fun t' => Base S vf s t' ∧ ∀ o, Kp o → view t'.mem (S s) o =
      mixV (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) dst dstLen o := by
  have hpos := hf.pos
  have hD : 0 < G.D := hG.hD0
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₁ o₁ e₁ => wp_li (imm := 0) (by decide) fun t₂ o₂ e₂ =>
    wp_nil ?_)
  have k₂ : Only [.s10, .s11] t t₂ := (o₁.trans o₂).mono
  have I0 : MgfI S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src
      srcLen dst dstLen G.D 0 t₂ :=
    ⟨h.only P k₂, by rw [k₂.get .s6, h6], by rw [k₂.get .s7, h7], by rw [k₂.get .s8, h8],
      by rw [k₂.get .s9, h9], by rw [o₂.get .s10, e₁], by rw [e₂, Nat.zero_mul],
      fun o _ => by rw [mixV, ifn (by omega), k₂.mem]⟩
  refine WP.loop (M := isa) (fun n w => ∃ c, n = dstLen - c * G.D ∧ c * G.D < dstLen ∧
      MgfI S vf s (view t.mem (S s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (S s)) src srcLen) dstLen) src srcLen dst
        dstLen G.D c w)
    ?_ (dstLen - 0 * G.D) t₂ ⟨0, rfl, by omega, I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  refine WP.mono (round_ok P hG hF hGh hGl hGv hf I hc) fun w' ⟨hcf, I'⟩ => ?_
  have hs1 : (c + 1) * G.D = c * G.D + G.D := Nat.succ_mul _ _
  by_cases h' : (c + 1) * G.D < dstLen
  · exact .inr ⟨by rw [eval_nonzero, hcf, decide_eq_true h'], _, by omega, c + 1, rfl, h', I'⟩
  · exact .inl ⟨by rw [eval_nonzero, hcf, decide_eq_false h'], I'.base,
      fun o ho => by rw [I'.em o ho, Nat.min_eq_right (by omega)]⟩

end

end VG.Proof.RsaOaep.RISCV64
