module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Front
public import VerifiedGarbage.Proof.Ffdh.ScalarWidth
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: the scalar

`scalarC_ok`: x is `rand`'s `p_len` octets cut to the context's width (the
header's words 5 and 6): `GenerateKey`'s cut at the index `p_len − bytes`,
with the mask of the first octet's bits, `255 >> (8 bytes − bits)`, so that
x is `rand mod 2^bits` (`scalarC_value`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (XR cut_ok cutRegs scRegs outX_scr)
open VG.Proof.Ffdh.RISCV64.Derive (AR)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.Ffdh.ScalarWidth (width headBits mask cut_value)
open VG.Proof.Bignum (slot)

/-- With at least a bit, the scalar's octets are `⌈bits / 8⌉`. -/
theorem width_of_pos {bits : Nat} (h : 1 ≤ bits) : width bits = (bits + 7) / 8 := by
  unfold width; omega_using [h]

/-- x's value: `rand`'s mod `2^bits`. -/
theorem scalarC_value {rb : List Byte} {k bits : Nat} (hl : rb.length = k) (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * k) :
    Spec.Rsa.os2ip (cut rb (k - (bits + 7) / 8) (mask bits)) = Spec.Rsa.os2ip rb % 2 ^ bits := by
  subst hl
  rw [← width_of_pos hb1]
  exact cut_value (by omega_using [hb1, hbk]) hbk

theorem exec_srl_reg {s : State} {d n m : Reg} :
    exec (.shiftReg .srl .d d n m) s = some (s.write d (s.gpr n >>> ((s.gpr m).toNat % 64))) := rfl

/-- The mask of the first octet's bits. -/
theorem mask_shift {bits : Nat} (h : 1 ≤ bits) :
    BitVec.ofNat 64 255 >>> ((BitVec.ofNat 64 (8 * ((bits + 7) / 8) - bits)).toNat % 64) =
      (mask bits).setWidth 64 := by
  have key : ∀ d < 8, BitVec.ofNat 64 255 >>> ((BitVec.ofNat 64 d).toNat % 64) =
      (BitVec.ofNat 8 (2 ^ (8 - d) - 1)).setWidth 64 := by decide
  rw [key _ (by omega_arith), mask, headBits, width_of_pos h]
  rw [show 8 - (8 * ((bits + 7) / 8) - bits) = bits - 8 * ((bits + 7) / 8 - 1) by omega_arith]

/-- `scalarBlock`: the mask, the index, and the cut's start. -/
theorem sb_ok {s : State} {S X : Addr} {Z k bits : Nat} (hs : Scr s S Z) (hZ : 64 ≤ Z) (h6 : s.gpr .s6 = S)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 k) (h5 : s.gpr .a5 = X) (hb1 : 1 ≤ bits) (hk : (bits + 7) / 8 ≤ k)
    (hbw : word s.mem S 40 = BitVec.ofNat 64 bits) (hyw : word s.mem S 48 = BitVec.ofNat 64 ((bits + 7) / 8)) :
    WP isa (.block scalarBlock) s fun t =>
      (t.gpr .s2 = (mask bits).setWidth 64 ∧ t.gpr .s1 = BitVec.ofNat 64 (k - (bits + 7) / 8) ∧
        t.gpr .t5 = BitVec.ofNat 64 k ∧ t.gpr .t4 = BitVec.ofNat 64 0 ∧ t.gpr .a0 = off X 0 ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .s2, .s1, .t5, .t4, .a0] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have l40 := hs.ld (d := 40) (n := 8) (by omega_arith)
  have l48 := hs.ld (d := 48) (n := 8) (by omega_arith)
  have a40 := hs.al8 (d := 40) (by omega_arith) (by decide)
  have a48 := hs.al8 (d := 48) (by omega_arith) (by decide)
  have v40 : s.mem.readW (off S 40) 64 = BitVec.ofNat 64 bits := hbw
  have v48 : s.mem.readW (off S 48) 64 = BitVec.ofNat 64 ((bits + 7) / 8) := hyw
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold scalarBlock GenerateKey.cutSetup hBytes hBits
  brun [h6', h4, h5, l40, l48, a40, a48, v40, v48, exec_srl_reg, Proof.Dsa.RISCV64.exec_li_lit (show 255 < 2048 by decide),
    fin64_exec_li_zero, add_ofNat_zero,
    Pre.ofNat_shl3,
    Offset.ofNat_sub_ofNat (show bits ≤ 8 * ((bits + 7) / 8) by omega_arith),
    Offset.ofNat_sub_ofNat hk, mask_shift hb1]
  rfl

/-- `scalar`: x's octets the cut of `rand`'s at the context's width, and
`s0 := 0`. -/
theorem scalarC_core {x : XD} {R : Addr} {s : State} {bits : Nat} (hb : Base x s) (ha : AR x s) (hx : XR x R s)
    (h1 : s.gpr .t1 = R) (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * x.k)
    (hbw : word s.mem x.S 40 = BitVec.ofNat 64 bits) (hyw : word s.mem x.S 48 = BitVec.ofNat 64 ((bits + 7) / 8)) :
    WP isa scalar s fun t =>
      (Spec.Rsa.bytesAt t.mem x.X x.k = cut (Spec.Rsa.bytesAt s.mem R x.k) (x.k - (bits + 7) / 8) (mask bits) ∧
        Outside x.X 0 x.k s.mem t.mem ∧ t.gpr .s0 = 0) ∧ Keep scRegs s t := by
  have hc := hb.ctx
  have hk := hc.k64
  have hk' := hc.k1024
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  unfold scalar
  refine WP.seq (WP.mono (sb_ok (X := x.X) hc.scr (by omega_arith) hb.s6 ha.a4 ha.a5 hb1 (by omega_arith)
    hbw hyw) fun s₁ ⟨⟨a2, a1, a5, a4, a0, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (cut_ok (R := R) (X := x.X) (k := x.k) (ld := x.k - (bits + 7) / 8) (tb := mask bits)
    (by omega_arith) (by omega_arith) (by omega_arith) hx.nwX (by rw [k1.2.2]; exact hx.wX)
    (by rw [k1.2.1, k1.2.2]; exact hx.rdR) hx.sepRX (by rw [k1.gpr (by decide), h1]; simp [off]) a0 a4 a1 a2 a5)
    fun s₂ ⟨⟨b2, o2⟩, k2⟩ => ?_)
  refine WP.mono (WP.keep [.s0] (Q := fun u => u.gpr .s0 = 0 ∧ u.mem = s₂.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ⟨⟨?_, ?_, t0⟩, ((k1.trans k2).trans kt).mono (by decide)⟩
  · rw [mt, b2, m1]
  · rw [mt, ← m1]; exact o2

/-- `scalar` keeps `X4`, `AR` and `XR`. -/
theorem scalarC_ok {x : XD} {R : Addr} {s : State} {bits : Nat} (h : X4 x s) (hz : s.gpr .s0 = 0) (ha : AR x s)
    (hx : XR x R s) (h1 : s.gpr .t1 = R) (hb1 : 1 ≤ bits) (hbk : bits ≤ 8 * x.k)
    (hbw : word s.mem x.S 40 = BitVec.ofNat 64 bits) (hyw : word s.mem x.S 48 = BitVec.ofNat 64 ((bits + 7) / 8)) :
    WP isa scalar s fun t => X4 x t ∧ t.gpr .s0 = 0 ∧ AR x t ∧ XR x R t ∧
      Spec.Rsa.bytesAt t.mem x.X x.k = cut (Spec.Rsa.bytesAt s.mem R x.k) (x.k - (bits + 7) / 8) (mask bits) ∧
      Outside x.X 0 x.k s.mem t.mem := by
  have hv := h.2.2.mp hz
  have hb := h.1
  have hc := hb.ctx
  have hZ := hc.hZ
  have hn := hc.scr.nowrap
  unfold slot hdrBytes at hZ
  refine WP.mono (WP.rdwr (scalarC_core hb ha hx h1 hb1 hbk hbw hyw)) fun s₁ ⟨⟨⟨xb, xo, z0⟩, k1⟩, r1, w1, _⟩ => ?_
  have hc1 := GenerateKey.Ctx.ofX hc hx r1 w1 xo
  have os1 := outX_scr xo hx.sepSX
  have hb1 : Base x s₁ := ⟨hc1, (k1.gpr (by decide)).trans hb.s6, (k1.gpr (by decide)).trans hb.a7,
    (k1.gpr (by decide)).trans hb.s5, (k1.gpr (by decide)).trans hb.t0, (k1.gpr (by decide)).trans hb.s7,
    (k1.gpr (by decide)).trans hb.s8, (k1.gpr (by decide)).trans hb.s10, (k1.gpr (by decide)).trans hb.s11⟩
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  exact ⟨⟨hb1, by rw [Outside.wordsVal os1 (Or.inl (by omega_arith)) (by omega_arith)]; exact h.2.1,
    fun _ => hv, fun _ => z0⟩, z0, ha.keep k1, hx.keep r1 w1, xb, xo⟩

end VG.Proof.Ffdh.RISCV64.Cached
