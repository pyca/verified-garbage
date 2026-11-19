module

public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyComb
import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyProd
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignAdd
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.Double64

/-! ### `Dsa.RISCV64.SignBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.SignOutput`, which only this module used -/

section

/-!
# DSA signing on RISC-V: the output

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Output.lean`). `output_ok`: r (array
25) and s (array 6), selected with 0 by the mask of the header's `hMask` and
`s ≠ 0`, to `out` (the header's `Sign.hOut`); `a0 :=` the mask's low bit.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The registers `sel` writes. -/
def selRegs : List Reg := [.a2, .a5, .a6, .a0, .t3, .t4, .t5, .s2, .s3]

/-- `sel o a t`: `[o] := c ? [a] : [t]`, `c`'s mask in `s4`. -/
theorem sel_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {c : Bool} {o a t : Nat}
    (ho : o < 28) (ha : a < 28) (ht : t < 28) (hoa : o ≠ a) (hot : o ≠ t) (h4 : s.gpr .s4 = mask c) :
    WP isa (sel o a t) s fun u =>
      (wordsVal u.mem B (slot w o) w = (if c then wordsVal s.mem B (slot w a) w else wordsVal s.mem B (slot w t) w) ∧
        Outside B (slot w o) (8 * w) s.mem u.mem) ∧ Keep selRegs s u := by
  have hZ := h.hZ
  have hw2 := h.w2
  have hw48 := h.w48
  obtain al := slot_al8 w
  obtain hO := slot_lt (w := w) ho; have hA := slot_lt (w := w) ha; have hT := slot_lt (w := w) ht
  obtain sa := slot_sep' (w := w) hoa; have st := slot_sep' (w := w) hot
  unfold sel
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .a2) (by decide) o) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  obtain e1 := h.keep k1
  refine WP.mono (e1.base (rd := .a5) (by decide) a) fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  obtain e2 := e1.keep k2
  refine WP.mono (e2.base (rd := .a6) (by decide) t) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  obtain e3 := e2.keep k3
  obtain k13 := (k1.trans k2).trans k3
  obtain hm3 : t₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w a) (dT := slot w t) (dO := slot w o) (b := c) e3.hs
    ((k3.gpr (by decide)).trans a5) a6 ((k2.trans k3).gpr (by decide) |>.trans a2) e3.t0
    ((k13.gpr (by decide)).trans h4) (by omega_using [hw2]) (by have := e3.w48; omega_using [hw48]) (al a) (al t) (al o)
    (by omega_using [hZ, hA]) (by omega_using [hZ, hT]) (by omega_using [hZ, hO]) (by omega_using [sa]) (by omega_using [st])) fun u ⟨hv, ou, ku⟩ => ?_
  rw [hm3] at hv ou
  exact ⟨⟨hv, ou⟩, (k13.trans ku).mono (by decide)⟩

/-- A buffer apart from `scratch` is past the Q space. -/
theorem Src.pastQ {s : State} {L : Lay} {O : Addr} {n : Nat} (h : Src s L O n) (hL : L.Ok) :
    ∀ x, ofs O x < n → 1600 ≤ ofs L.Q x := fun x hx => by
  by_contra hc
  exact h.sepQ hL _ hx x (by omega_using [hc]) (off_ofs O x)

/-- A change in such a buffer leaves the Q space. -/
theorem outside_pastQ {L : Lay} {O : Addr} {k : Nat} {m m' : Mem} (h : Outside O 0 k m m')
    (hsep : ∀ x, ofs O x < k → 1600 ≤ ofs L.Q x) : Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  obtain hlt := (x - L.Q).isLt
  refine h x (Or.inr ?_)
  by_contra hc
  have := hsep x (by omega_using [hc])
  simp only [ofs] at hx this; omega_using [hx, this]

/-- A change in such a buffer keeps `scratch`'s header word `hLens`. -/
theorem out_hdr {s : State} {L : Lay} (hL : L.Ok) {O : Addr} {n k : Nat} (hos : Src s L O n) {m m' : Mem}
    (h : Outside O 0 k m m') (hk : k ≤ n) : word m' L.S hLens = word m L.S hLens := by
  have := hL.z256
  have := hL.nowrap
  refine (Mem.readW_congr fun i hi => (h _ (Or.inr ?_)).symm).symm
  by_contra hc
  exact hos.sep (ofs O (off L.S hLens + BitVec.ofNat 64 i)) (by simp only [ofs] at hc ⊢; omega_using [hk, hc]) _
    (by rw [ofs_off L.S (by simp only [hLens]; omega_using [hi])]; simp only [hLens]; omega_arith) (off_ofs _ _)

/-- The registers `output` writes. -/
def outputRegs : List Reg :=
  [.s0, .t3, .t5] ++ [.a4] ++ nonZeroRegs ++ [.s4] ++ selRegs ++ selRegs ++ [.s7, .s8] ++ storeRegs ++ [.s7] ++
    storeRegs ++ [.a0]

/-- `output`: r and s, selected with 0 by `b ∧ s ≠ 0`, to `out`; `a0 :=` 1 if
`b ∧ s ≠ 0`, else 0. Memory changes only in the Q space's arrays and in
`out`'s `2 q_len` octets. -/
theorem output_ok {s : State} {L : Lay} {key nonce out : Addr} {b : Bool} (hL : L.Ok)
    (h : QS s L key nonce) (hw : word s.mem L.S Sign.hOut = out) (hm : word s.mem L.S hMask = mask b)
    (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1) (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64)
    (hos : Src s L out (2 * L.ql))
    (h25 : arrQ s.mem L 25 < 2 ^ (8 * L.ql)) (h6 : arrQ s.mem L 6 < 2 ^ (8 * L.ql)) :
    WP isa output s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem out L.ql) =
          (if b && decide (arrQ s.mem L 6 ≠ 0) then arrQ s.mem L 25 else 0) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off out L.ql) L.ql) =
          (if b && decide (arrQ s.mem L 6 ≠ 0) then arrQ s.mem L 6 else 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (if b && decide (arrQ s.mem L 6 ≠ 0) then 1 else 0) ∧
        ∃ m, QArr L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ Keep outputRegs s t := by
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  have hZ := hL.z256
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
  obtain e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
  unfold output
  -- 0 into array 7.
  refine WP.seq (WP.mono (zeroArr_ok h.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
  obtain qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega_using [e1, e7]) (by omega_using [e7, e28])
  obtain Q1 := h.step k1 (qa1.body hL)
  -- The mask into `a4`.
  obtain ⟨hld, hal⟩ := ScrL.hdr Q1.scr hL (d := 0) (by decide) (by decide)
  obtain hw1 : word s₁.mem L.S hMask = mask b := by rw [(qa1.body hL).word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₁.mem)
    (by brun [hMask, Q1.regs.s6, hld, hal]; exact hw1) (by decide) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
  obtain Q2 := Q1.stepM k2 m2
  -- `a4 &=` the mask of `s ≠ 0`.
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a4)
    fun s₃ ⟨⟨b4, m3⟩, k3⟩ => ?_)
  obtain Q3 := Q2.stepM k3 m3
  obtain A6 : wordsVal s₂.mem L.Q (slot L.wq 6) L.wq = arrQ s.mem L 6 := by
    rw [m2]; exact o1.wordsVal (by omega_using [e6, e7]) (by omega_using [hwq, e6])
  obtain A25 : wordsVal s₁.mem L.Q (slot L.wq 25) L.wq = arrQ s.mem L 25 := o1.wordsVal (by omega_using [e7, e25]) (by omega_using [hwq, e25])
  rw [A6] at b4
  generalize (b && decide (arrQ s.mem L 6 ≠ 0)) = c at b4 ⊢
  refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = mask c ∧ u.mem = s₃.mem)
    (by brun [b4, BitVec.add_zero]) (by decide) (by rfl)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
  obtain Q4 := Q3.stepM k4 m4
  obtain hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  -- The selections into arrays 1 and 2.
  refine WP.seq (WP.mono (sel_ok Q4.inq.env (c := c) (o := 1) (a := 25) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨v1, o5⟩, k5⟩ => ?_)
  obtain Q5 := Q4.step k5 (Body.ofQ hL o5 (by omega_using [hwq, e1]))
  refine WP.seq (WP.mono (sel_ok Q5.inq.env (c := c) (o := 2) (a := 6) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k5.gpr (by decide)).trans a20)) fun s₆ ⟨⟨v2, o6⟩, k6⟩ => ?_)
  obtain Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega_using [hwq, e2]))
  obtain z7' : wordsVal s₄.mem L.Q (slot L.wq 7) L.wq = 0 := by rw [hm4]; exact z7
  obtain V1 : wordsVal s₆.mem L.Q (slot L.wq 1) L.wq = if c then arrQ s.mem L 25 else 0 := by
    rw [o6.wordsVal (by omega_using [e1, e2]) (by omega_using [hwq, e1]), v1, z7', hm4, A25]
  obtain V2 : wordsVal s₆.mem L.Q (slot L.wq 2) L.wq = if c then arrQ s.mem L 6 else 0 := by
    rw [v2, o5.wordsVal (d := slot L.wq 7) (by omega_using [e1, e7]) (by omega_using [hwq, e7]), o5.wordsVal (d := slot L.wq 6) (by omega_using [e1, e6]) (by omega_using [hwq, e6]),
      z7', show wordsVal s₄.mem L.Q (slot L.wq 6) L.wq = arrQ s.mem L 6 by rw [m4, m3]; exact A6]
  obtain qa6 : QArr L s.mem s₆.mem := by
    refine qa1.trans ?_
    rw [← hm4]
    exact (QArr.of o5 (by omega_using []) (by omega_using [e1, e28])).trans (QArr.of o6 (by omega_using [e1, e2]) (by omega_using [e2, e28]))
  obtain K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  -- `out` into `s7`, `q_len` into `s8`.
  obtain ⟨hld', hal'⟩ := ScrL.hdr Q6.scr hL (d := 24) (by decide) (by decide)
  obtain hwo : word s₆.mem L.S Sign.hOut = out := by rw [(qa6.body hL).word (by decide)]; exact hw
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = out ∧ u.mem = s₆.mem)
    (by brun [Sign.hOut, Q6.regs.s6, hld', hal']; exact hwo) (by decide) (by rfl)) fun s₇ ⟨⟨a7, m7⟩, k7⟩ =>
    WP.mono (getQ_ok (Q6.scr.congr k7.2.2) hL (Q6.regs.keepM k7 m7) .s8) fun s₈ ⟨⟨a8, m8⟩, k8⟩ => ?_))
  obtain k78 := k7.trans k8
  obtain hm8 : s₈.mem = s₆.mem := m8.trans m7
  obtain Q8 := Q6.stepM k78 hm8
  obtain K8 := K6.trans k78
  -- r to `out`.
  obtain sep1 := hos.pastQ hL
  refine WP.seq (WP.mono (storeBE_ok (j := 1) (O := out) (k := L.ql) Q8.inq.env (by decide)
    (fun i hi => by rw [K8.2.2]; exact hout i (by omega_using [hi])) (by omega_using [hno]) ((k8.gpr (by decide)).trans a7) a8
    (by omega_using [hql]) (by omega_using [hwq]) (fun x hx => sep1 x (by omega_using [hx]))) fun s₉ ⟨⟨vt1, ot1⟩, k9⟩ => ?_)
  obtain kq1 := outside_pastQ (L := L) ot1 (fun x hx => sep1 x (by omega_using [hx]))
  obtain Q9 : QS s₉ L key nonce := ⟨Q8.inq.keep k9, Q8.scr.congr k9.2.2, Q8.regs.keepHdr k9
    (out_hdr hL hos ot1 (by omega_using []))⟩
  -- `out + q_len` into `s7`.
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = off out L.ql ∧ u.mem = s₉.mem)
    (by brun [(k9.gpr (r := .s7) (by decide)).trans ((k8.gpr (r := .s7) (by decide)).trans a7),
      (k9.gpr (r := .s8) (by decide)).trans a8]) (by decide) (by rfl)) fun s₁₀ ⟨⟨b7, m10⟩, k10⟩ => ?_)
  obtain Q10 := Q9.stepM k10 m10
  obtain K10 := (K8.trans k9).trans k10
  -- s to `out + q_len`.
  obtain hos2 := hos.sub (o := L.ql) (k := L.ql) (by omega_using [])
  obtain sep2 := hos2.pastQ hL
  obtain hoa : (off out L.ql).toNat = out.toNat + L.ql := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L.ql < 2 ^ 64 by omega_using [hno])]; exact Nat.mod_eq_of_lt (by omega_using [hno])
  refine WP.seq (WP.mono (storeBE_ok (j := 2) (O := off out L.ql) (k := L.ql) Q10.inq.env (by decide)
    (fun i hi => by rw [K10.2.2, off_off]; exact hout _ (by omega_using [hi])) (by omega_using [hno, hoa]) b7
    ((k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans a8)) (by omega_using [hql]) (by omega_using [hwq]) sep2)
    fun s₁₁ ⟨⟨vt2, ot2⟩, k11⟩ => ?_)
  -- `a0 :=` the mask's low bit.
  obtain c4 : s₁₁.gpr .a4 = mask c :=
    ((((((k5.trans k6).trans k78).trans k9).trans k10).trans k11).gpr (by decide)).trans
      ((k4.gpr (by decide)).trans b4)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₁₁.mem) (by brun [c4, mask_low]) (by decide) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  obtain kall := (K10.trans k11).trans kt
  obtain ot2' : Outside out L.ql L.ql s₁₀.mem s₁₁.mem := by
    have := outside_shift (B := out) (a := L.ql) ot2 (by omega_using [hno]) (by omega_using [hno])
    rwa [Nat.add_zero] at this
  refine ⟨⟨?_, ?_, t0, ⟨s₆.mem, qa6, ?_⟩⟩, ?_⟩
  · have hb : Spec.Rsa.bytesAt t.mem out L.ql = Spec.Rsa.bytesAt s₉.mem out L.ql := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      rw [mt, ot2' _ (Or.inl (by rw [show out + BitVec.ofNat 64 i = off out i from rfl, ofs_off0 out (by omega_using [hno, hi])]; omega_using [hi])),
        m10]
    rw [hb, vt1, hm8, read_low (w := L.wq) _ _ (by omega_using [hwq]) (by rw [V1]; split <;> omega_using [h25]), V1]
  · have e2' : wordsVal s₉.mem L.Q (slot L.wq 2) L.wq = if c then arrQ s.mem L 6 else 0 := by
      rw [kq1.wordsVal (Or.inl (by omega_using [hwq, e2])) (by omega_using [hwq, e2]), hm8, V2]
    rw [mt, vt2, m10, read_low (w := L.wq) _ _ (by omega_using [hwq]) (by rw [e2']; split <;> omega_arith), e2']
  · rw [mt, ← hm8]
    obtain o9 : Outside out 0 (2 * L.ql) s₈.mem s₉.mem := ot1.mono (Nat.le_refl _) (by omega_using [])
    obtain o11 : Outside out 0 (2 * L.ql) s₁₀.mem s₁₁.mem := ot2'.mono (by omega_using []) (by omega_using [])
    rw [m10] at o11
    exact o9.trans o11
  · simp only [outputRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.SignS`, which only this module used -/

section

/-!
# DSA signing on RISC-V: `s = w (z + x r) mod q`

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/S.lean`).

* `qmont28_ok`: verification's `qmont_ok` for any of the 28 arrays, as
  `sValue` multiplies by r in array 25;
* `sValue_ok`: in the Q space, with q in array 0, w in array 4, `R² mod q` in
  array 24 and r in array 25, `w (z + x r) mod q` into array 6 (z the digest's
  scalar, x the key's last `q_len` octets).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

/-- `montOp o a b` in the Q space, for `o` among 5 and 6 and any arrays `a`
and `b`, `[b] < q`. -/
theorem qmont28_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    {o a b : Nat} (ho : o = 5 ∨ o = 6) (ha : a < 28) (ha2 : a ≠ 2) (hb : b < 28) (hb2 : b ≠ 2)
    (hB : arrQ s.mem L b < arrQ s.mem L 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L o < arrQ s.mem L 0 ∧
        arrQ t.mem L o * 2 ^ (64 * L.wq) % arrQ s.mem L 0 = arrQ s.mem L a * arrQ s.mem L b % arrQ s.mem L 0 ∧
        (∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hn : L.Q.toNat + slot L.wq 28 ≤ 2 ^ 64 := by have := e.hs.nowrap; omega_using [hqs, this]
  refine WP.mono (Pub.montOpN_ok e.hs (n := 28) (by decide) (by omega_using [ho]) ha hb (by omega_using [ho]) (by omega_using [ho]) ha2 hb2 e.w2
    (by omega_using [hwq]) e.hZ e.a7 e.s5 e.t0 hi hB) fun t ⟨⟨lt, eq, ar⟩, k⟩ => ?_
  obtain qa : QArr L s.mem t.mem := arrays_qarr ar (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [ho, hk])
  refine ⟨⟨h.step k (qa.body hL), ?_, lt, eq, fun j hj h2 h3 ho' => arrays_val ar hj (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [h2, h3, ho', hk]) hn, qa⟩, k⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [arrays_word0 ar (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [ho, hk]) hn,
    k.gpr (by decide)]
  exact hi

/-! ## The arrays a step keeps -/

/-- The Q space's arrays but those in `ws` are kept. -/
def AKeep (L : Lay) (ws : List Nat) (m m' : Mem) : Prop :=
  ∀ j, j < 28 → j ∉ ws → arrQ m' L j = arrQ m L j

theorem AKeep.get {L : Lay} {ws : List Nat} {m m' : Mem} (h : AKeep L ws m m') (j : Nat)
    (hj : j < 28 := by decide) (hn : j ∉ ws := by decide) : arrQ m' L j = arrQ m L j :=
  h j hj hn

theorem AKeep.trans {L : Lay} {ws ws' : List Nat} {m₁ m₂ m₃ : Mem} (h₁ : AKeep L ws m₁ m₂)
    (h₂ : AKeep L ws' m₂ m₃) : AKeep L (ws ++ ws') m₁ m₃ := fun j hj hn =>
  (h₂ j hj fun h => hn (List.mem_append_right _ h)).trans (h₁ j hj fun h => hn (List.mem_append_left _ h))

theorem AKeep.one {L : Lay} (hL : L.Ok) {o n : Nat} {m m' : Mem} (h : Outside L.Q (slot L.wq o) n m m')
    (hn : n ≤ 8 * (L.wq + 2)) : AKeep L [o] m m' := fun j hj ho => by
  obtain hjo : j ≠ o := by simpa only [List.mem_singleton] using ho
  have := slot_sep' (w := L.wq) hjo
  have := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  exact h.wordsVal (by omega_arith) (by simp only [Lay.slot_eq] at *; omega_arith)

theorem AKeep.red {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.Q (slot L.wq 1) (24 * (L.wq + 2)) m m') :
    AKeep L [1, 2, 3] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain hl := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  obtain e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e4 := Lay.slot_eq L.wq 4
  obtain e28 := Lay.slot_eq L.wq 28
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact h.wordsVal (Or.inl (by omega_using [e0, e1])) (by omega_using [this, e0])
  · have := slot_mono (w := L.wq) (show 4 ≤ j by omega_using [hn, hj0])
    exact h.wordsVal (Or.inr (by omega_using [e1, e4, this])) (by omega_arith)

theorem AKeep.add {L : Lay} (hL : L.Ok) {o : Nat} {m m' : Mem} (h : AddFrame L.Q L.wq o m m')
    (hnw : L.Q.toNat + 1600 ≤ 2 ^ 64) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h.arr_eq (Z := 1600) hL.qslot hnw hj hn.1 hn.2.1 hn.2.2

theorem AKeep.mont {L : Lay} {o : Nat} {m m' : Mem}
    (h : ∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ m' L j = arrQ m L j) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h j hj hn.1 hn.2.1 hn.2.2

theorem AddFrame.qarr {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q L.wq o m m') (ho1 : 1 ≤ o)
    (ho : o < 28) : QArr L m m' := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  obtain h1 := slot_mono (w := L.wq) ho1
  obtain h2 := slot_lt (w := L.wq) ho
  exact (QArr.of h₁ (by simp only [Lay.slot_eq]; omega_using []) (by simp only [Lay.slot_eq]; omega_using [])).trans
    (QArr.of h₂ h1 (by omega_using [h2]))

theorem QArr.word0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') :
    word m' L.Q (slot L.wq 0) = word m L.Q (slot L.wq 0) := by
  have := hL.wq_ge
  exact h.word (Or.inl (by simp only [Lay.slot_eq]; omega_using [])) (by simp only [Lay.slot_eq]; omega_using [])

theorem QInv.keepW {s t : State} {L : Lay} (hi : QInv s L) (hw : word t.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0))
    (h1 : t.gpr .t1 = s.gpr .t1) : QInv t L := by
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [hw, h1]; exact hi

/-! ## s -/

/-- The registers `sValue` writes. -/
def sValueRegs : List Reg :=
  scalarRegs ++ [.s0, .t3, .t5] ++ addModRegs ++ ptrRegs ++ [.s9, .s10] ++
    (ModArith.redRegs ++ [.a2, .a5, .a6]) ++ copyRegs ++ copyRegs ++ Pub.montRegs ++ Pub.montRegs ++ addModRegs ++
    Pub.montRegs ++ Pub.montRegs

/-- `sValue`: in the Q space, `w (z + x r) mod q` into array 6. -/
theorem sValue_ok {s : State} {L : Lay} {key nonce dig : Addr} {qb d : Nat} (hL : L.Ok) (h : QS s L key nonce)
    (hi : QInv s L) (hdg8 : word s.mem L.S hDigest = dig) (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d)
    (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16) (hdg : Src s L dig (min d qb)) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hq3 : 3 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0)
    (h4 : arrQ s.mem L 4 < arrQ s.mem L 0) (h25 : arrQ s.mem L 25 < arrQ s.mem L 0)
    (hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) < 2 * arrQ s.mem L 0) :
    WP isa sValue s fun t =>
      (QS t L key nonce ∧ QInv t L ∧
        arrQ t.mem L 6 = arrQ s.mem L 4 * ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) %
          arrQ s.mem L 0 + xOf s.mem L key * arrQ s.mem L 25 % arrQ s.mem L 0) % arrQ s.mem L 0) %
            arrQ s.mem L 0 ∧
        arrQ t.mem L 25 = arrQ s.mem L 25 ∧ QArr L s.mem t.mem) ∧ Keep sValueRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hcop : Nat.Coprime (2 ^ (64 * L.wq)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  obtain hRR := pow_two_mul L.wq
  have hnw : L.Q.toNat + 1600 ≤ 2 ^ 64 := h.inq.env.hs.nowrap
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  obtain e8 := e 8; have e24 := e 24; have e25 := e 25; have e28 := e 28
  generalize hq : arrQ s.mem L 0 = q at hq3 hqo h24 h4 h25 hz hcop ⊢
  generalize (2 : Nat) ^ (128 * L.wq) = R2 at h24 hRR
  unfold sValue
  -- z into array 6, 0 into array 7, `z mod q` into array 6.
  refine WP.seq (WP.mono (scalar_ok hL h hdg8 hlen hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) = z at v6 hz ⊢
  obtain f1 : AKeep L [6] s.mem s₁.mem := AKeep.one hL o1 (by omega_using [])
  obtain qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega_using [e1, e6]) (by omega_using [e6, e28])
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  obtain Q2 := Q1.step k2 (Body.ofQ hL o2 (by omega_using [hwq, e7]))
  obtain f2 : AKeep L [7] s₁.mem s₂.mem := AKeep.one hL o2 (by omega_using [])
  obtain qa2 : QArr L s₁.mem s₂.mem := QArr.of o2 (by omega_using [e1, e7]) (by omega_using [e7, e28])
  obtain q2 : arrQ s₂.mem L 0 = q := by rw [(qa1.trans qa2).arr0 hL]; exact hq
  obtain z2 : arrQ s₂.mem L 6 = z := (f2.get 6).trans v6
  refine WP.seq (WP.mono (addMod_ok Q2.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show arrQ s₂.mem L 6 + arrQ s₂.mem L 7 < 2 * arrQ s₂.mem L 0; rw [z2, show arrQ s₂.mem L 7 = 0 from z7, q2]
        omega_using [hz])) fun s₃ ⟨⟨a6, fr3⟩, k3⟩ => ?_)
  obtain a6' : arrQ s₃.mem L 6 = z % q := by
    show wordsVal s₃.mem L.Q (slot L.wq 6) L.wq = _
    rw [a6, show wordsVal s₂.mem L.Q (slot L.wq 6) L.wq = arrQ s₂.mem L 6 from rfl, z2,
      show wordsVal s₂.mem L.Q (slot L.wq 7) L.wq = 0 from z7,
      show wordsVal s₂.mem L.Q (slot L.wq 0) L.wq = arrQ s₂.mem L 0 from rfl, q2, Nat.add_zero]
  obtain qa3' := fr3.qarr (by decide) (by decide)
  obtain Q3 := Q2.step k3 (qa3'.body hL)
  obtain f3 := AKeep.add hL fr3 hnw
  obtain qa13 : QArr L s.mem s₃.mem := (qa1.trans qa2).trans qa3'
  obtain q3 : arrQ s₃.mem L 0 = q := by rw [qa13.arr0 hL]; exact hq
  obtain k13 := (k1.trans k2).trans k3
  obtain I3 : QInv s₃ L := hi.keepW (qa13.word0 hL) (k13.gpr (by decide))
  -- x's octets, and `x mod q` into array 1.
  refine WP.seq (WP.block_append (WP.mono (ptrX_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
    WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off key (3 * L.pl + L.ql) ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₅ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_))
  obtain k35 := k4.trans k5
  obtain hm5 : s₅.mem = s₃.mem := by rw [m5, m4]
  obtain e3 := Q3.inq.env.keep k35
  obtain hx := (hk.keep (k13.trans k35).2.1 (k13.trans k35).2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := L.Q) (Z := 1600) (w := L.wq) (D := off key (3 * L.pl + L.ql))
    (L := L.ql) e3.hs (by omega_using [hwq]) (by omega_using [hwq]) (by omega_using [hwq, e4]) e3.a7 e3.s5 e3.t0
    (by rw [hm5]; show 0 < arrQ s₃.mem L 0; rw [q3]; omega_using [hq3])
    (by rw [c9]; exact (BitVec.add_zero _).symm) c10 (by omega_using [hql]) (by omega_using [hwq]) hx.rd (hx.sepQ hL))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  rw [hm5] at v1 o6
  obtain x6 : arrQ s₆.mem L 1 = xOf s.mem L key % q := by
    refine v1.trans ?_
    rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])).bytes (qa13.body hL) (by have := hL.z256; omega_using [this])]
    show _ % arrQ s₃.mem L 0 = _
    rw [q3]
    rfl
  obtain f6 := AKeep.red hL o6
  obtain qa6 : QArr L s₃.mem s₆.mem := QArr.of o6 (Nat.le_refl _) (by omega_using [e1, e28])
  obtain Q6 := Q3.step (k35.trans k6) (qa6.body hL)
  -- `x mod q` into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (copy_ok Q6.inq.env (o := 5) (a := 1) (by decide) (by decide) (by decide))
    fun s₇ ⟨⟨v5, o7⟩, k7⟩ => ?_)
  obtain Q7 := Q6.step k7 (Body.ofQ hL o7 (by omega_using [hwq, e5]))
  obtain f7 : AKeep L [5] s₆.mem s₇.mem := AKeep.one hL o7 (Nat.le_refl _)
  refine WP.seq (WP.mono (copy_ok Q7.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨v1', o8⟩, k8⟩ => ?_)
  obtain Q8 := Q7.step k8 (Body.ofQ hL o8 (by omega_using [hwq, e1]))
  obtain f8 : AKeep L [1] s₇.mem s₈.mem := AKeep.one hL o8 (Nat.le_refl _)
  obtain qa8 : QArr L s.mem s₈.mem :=
    ((qa13.trans qa6).trans (QArr.of o7 (by omega_using [e1, e5]) (by omega_using [e5, e28]))).trans (QArr.of o8 (by omega_using []) (by omega_using [e1, e28]))
  obtain k18 := ((k13.trans k35).trans k6).trans (k7.trans k8)
  obtain I8 : QInv s₈ L := hi.keepW (qa8.word0 hL) (k18.gpr (by decide))
  obtain F38 := (f6.trans f7).trans f8
  obtain F08 := ((f1.trans f2).trans f3).trans F38
  obtain A0 : arrQ s₈.mem L 0 = q := by rw [qa8.arr0 hL]; exact hq
  obtain A1 : arrQ s₈.mem L 1 = R2 % q := by
    rw [arrQ, wordsVal_congr (m := s₇.mem) (d := slot L.wq 24) fun i hi => v1' i (by omega_using [hi])]
    show arrQ s₇.mem L 24 = _
    rw [f7.get 24, f6.get 24, f3.get 24, f2.get 24, f1.get 24]; exact h24
  obtain A4 : arrQ s₈.mem L 4 = arrQ s.mem L 4 := F08.get 4
  obtain A5 : arrQ s₈.mem L 5 = xOf s.mem L key % q := by
    rw [f8.get 5, arrQ, wordsVal_congr (m := s₆.mem) (d := slot L.wq 1) fun i hi => v5 i (by omega_using [hi])]
    exact x6
  obtain A6 : arrQ s₈.mem L 6 = z % q := (F38.get 6).trans a6'
  obtain A25 : arrQ s₈.mem L 25 = arrQ s.mem L 25 := F08.get 25
  -- `x r mod q` into array 5.
  refine WP.seq (WP.mono (qmont28_ok hL Q8 I8 (o := 5) (a := 5) (b := 25) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A25, A0]; exact h25)) fun s₉ ⟨⟨Q9, I9, _, e9, k9a, qa9⟩, k9⟩ => ?_)
  rw [A0, A5, A25] at e9
  obtain f9 := AKeep.mont k9a
  obtain B0 : arrQ s₉.mem L 0 = q := (f9.get 0).trans A0
  obtain B1 : arrQ s₉.mem L 1 = R2 % q := (f9.get 1).trans A1
  refine WP.seq (WP.mono (qmont28_ok hL Q9 I9 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega_using [hq3])))
    fun s₁₀ ⟨⟨Q10, I10, l10, e10, k10a, qa10⟩, k10⟩ => ?_)
  rw [B0] at l10
  rw [B0, B1] at e10
  obtain X10 : arrQ s₁₀.mem L 5 = xOf s.mem L key % q * arrQ s.mem L 25 % q :=
    prod_mont_back hcop l10 e9 (by rw [e10, hRR])
  obtain f10 := AKeep.mont k10a
  obtain F910 := f9.trans f10
  obtain C0 : arrQ s₁₀.mem L 0 = q := (F910.get 0).trans A0
  obtain C6 : arrQ s₁₀.mem L 6 = z % q := (F910.get 6).trans A6
  -- `z + x r mod q` into array 6.
  obtain l1 := Nat.mod_lt z (show 0 < q by omega_using [hq3])
  obtain l2 := Nat.mod_lt (xOf s.mem L key % q * arrQ s.mem L 25) (show 0 < q by omega_using [hq3])
  refine WP.seq (WP.mono (addMod_ok Q10.inq.env (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show arrQ s₁₀.mem L 6 + arrQ s₁₀.mem L 5 < 2 * arrQ s₁₀.mem L 0; rw [C6, X10, C0]; omega_using [l1, l2]))
    fun s₁₁ ⟨⟨a11, fr11⟩, k11⟩ => ?_)
  obtain a11' : arrQ s₁₁.mem L 6 = (z % q + xOf s.mem L key * arrQ s.mem L 25 % q) % q := by
    show wordsVal s₁₁.mem L.Q (slot L.wq 6) L.wq = _
    rw [a11, show wordsVal s₁₀.mem L.Q (slot L.wq 6) L.wq = arrQ s₁₀.mem L 6 from rfl, C6,
      show wordsVal s₁₀.mem L.Q (slot L.wq 5) L.wq = arrQ s₁₀.mem L 5 from rfl, X10,
      show wordsVal s₁₀.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₀.mem L 0 from rfl, C0, Nat.mod_mul_mod]
  obtain qa11 := fr11.qarr (by decide) (by decide)
  obtain Q11 := Q10.step k11 (qa11.body hL)
  obtain I11 : QInv s₁₁ L := I10.keepW (qa11.word0 hL) (k11.gpr (by decide))
  obtain f11 := AKeep.add hL fr11 hnw
  obtain F911 := F910.trans f11
  obtain D0 : arrQ s₁₁.mem L 0 = q := (F911.get 0).trans A0
  obtain D1 : arrQ s₁₁.mem L 1 = R2 % q := (F911.get 1).trans A1
  obtain D4 : arrQ s₁₁.mem L 4 = arrQ s.mem L 4 := (F911.get 4).trans A4
  -- `w (z + x r) mod q` into array 6.
  refine WP.seq (WP.mono (qmont28_ok hL Q11 I11 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D4, D0]; exact h4)) fun s₁₂ ⟨⟨Q12, I12, _, e12, k12a, qa12⟩, k12⟩ => ?_)
  rw [D0, a11', D4] at e12
  obtain f12 := AKeep.mont k12a
  obtain E0 : arrQ s₁₂.mem L 0 = q := (f12.get 0).trans D0
  obtain E1 : arrQ s₁₂.mem L 1 = R2 % q := (f12.get 1).trans D1
  refine WP.mono (qmont28_ok hL Q12 I12 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E1, E0]; exact Nat.mod_lt _ (by omega_using [hq3])))
    fun t ⟨⟨Qt, It, lt, et, kta, qat⟩, kt⟩ => ?_
  rw [E0] at lt
  rw [E0, E1] at et
  obtain ft := AKeep.mont kta
  obtain Ft := (((F08.trans F910).trans f11).trans f12).trans ft
  obtain kall := (((((k18.trans k9).trans k10).trans k11).trans k12).trans kt)
  refine ⟨⟨Qt, It, ?_, Ft.get 25, (((((qa8.trans qa9).trans qa10).trans qa11).trans qa12).trans qat)⟩, ?_⟩
  · exact (prod_mont_back hcop lt e12 (by rw [et, hRR])).trans (by rw [Nat.mul_comm _ (arrQ s.mem L 4)])
  · simp only [sValueRegs, List.append_assoc] at kall ⊢
    exact kall

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.SignInverse`, which only this module used -/

section

/-!
# DSA signing on RISC-V: k's inverse

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Inverse.lean`). `inverseK_ok`:
verification's `inverse_ok` (`VerifyInv.lean`) with the base k, the nonce at
`ra`, in place of s.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
  VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

theorem inverseK_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    (hsg : Src s L sig L.ql) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) :
    WP isa inverseK s fun t =>
      (QS t L key sig ∧ QInv t L ∧
        arrQ t.mem L 4 = kOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        (∀ j < 28, 24 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep invRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  unfold inverseK
  refine WP.seq (WP.mono (ptrR_ok h.scr hL h.regs) fun s₁ ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
  obtain Q1 := h.stepM k1 m1
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide)
      (hsg.keep k1.2.1 k1.2.2) a7 a8 (by omega_using [hql]) (by omega_using [hwq]))
    fun s₂ ⟨⟨Q2, v4, _, o2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨c1, o3⟩, k3⟩ => ?_)
  obtain Q3 := Q2.step k3 (Body.ofQ hL o3 (by omega_using [hwq, e1]))
  obtain A0 : arrQ s₃.mem L 0 = arrQ s.mem L 0 := by
    rw [arrQ, o3.wordsVal (by omega_using [e0, e1]) (by omega_arith), o2.wordsVal (by omega_using [e0, e4]) (by omega_arith)]
  obtain W0 : word s₃.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) := by
    rw [o3.word (by omega_using [e0, e1]) (by omega_arith), o2.word (by omega_using [e0, e4]) (by omega_arith)]
  obtain A4 : arrQ s₃.mem L 4 = kOf s.mem L sig := by
    rw [arrQ, o3.wordsVal (by omega_using [e1, e4]) (by omega_arith)]; exact v4
  obtain A24 : ∀ j < 28, 24 ≤ j → arrQ s₃.mem L j = arrQ s.mem L j := fun j hj hj24 => by
    have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o3.wordsVal (by omega_using [e1, e24, this]) (by omega_arith), o2.wordsVal (by omega_using [e4, e24, this]) (by omega_arith)]
  obtain A1 : arrQ s₃.mem L 1 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 := by
    rw [arrQ, wordsVal_congr (m := s₂.mem) (d := slot L.wq 24) fun i hi => c1 i (by omega_using [hi])]
    rw [← h24, arrQ, o2.wordsVal (by omega_using [e4, e24]) (by omega_arith)]
  obtain hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql := by
    obtain qa : QArr L s.mem s₃.mem :=
      (QArr.of o2 (by omega_using [e1, e4]) (by omega_using [e4, e28])).trans (QArr.of o3 (by omega_using []) (by omega_using [e1, e28]))
    exact qa.bufBytes hL (by omega_using [hwq])
  -- The exponent's pointer and length.
  refine WP.seq (WP.block_append (WP.mono (ptrBuf_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
    WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off L.Buf 0 ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₅ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_))
  obtain k35 := k4.trans k5
  obtain m53 : s₅.mem = s₃.mem := by rw [m5, m4]
  obtain e5 := Q3.inq.env.keep k35
  obtain k15 := (((k1.trans k2).trans k3).trans k35)
  refine WP.mono (Win.powWin_ok (D := L.Buf) (L := L.ql) e5.hs (by omega_using [hwq]) (by omega_using [hwq])
    (by omega_using [hwq, e24]) e5.a7 e5.s5 e5.t0
    (by rw [m53, W0, k15.gpr (by decide)]; exact hi)
    (by rw [m53]; show 2 ≤ arrQ s₃.mem L 0; rw [A0]; exact hq2)
    (by rw [m53]; show arrQ s₃.mem L 0 % 2 = 1; rw [A0]; exact hqo)
    (by rw [m53]; show arrQ s₃.mem L 1 < arrQ s₃.mem L 0; rw [A1, A0]; exact Nat.mod_lt _ (by omega_using [hq2]))
    c9 c10 (by omega_using [hql]) (by omega_arith)
    (fun i hi => by
      rw [k35.2.1, k35.2.2]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by rcases hL.pl with e | e | e <;> omega_using [hwq, e])).ld
        (show i + 1 ≤ L.ql by omega_using [hi]))
    (buf_apartQ L (by omega_using [hwq]))) fun t ⟨⟨r4, o4'⟩, k6⟩ => ?_
  obtain o4 : Outside L.Q (slot L.wq 1) (23 * (8 * (L.wq + 2))) s₃.mem t.mem := by rw [← m53]; exact o4'
  rw [m53] at r4
  obtain r4 := r4 (by
    show arrQ s₃.mem L 1 = 2 ^ (64 * L.wq) * 2 ^ (64 * L.wq) % arrQ s₃.mem L 0
    rw [A1, A0, pow_two_mul])
  rw [hbuf] at r4
  obtain qa : QArr L s.mem t.mem :=
    ((QArr.of o2 (by omega_using [e1, e4]) (by omega_using [e4, e28])).trans (QArr.of o3 (by omega_using []) (by omega_using [e1, e28]))).trans
      (QArr.of o4 (by omega_using []) (by omega_using [e1, e28]))
  refine ⟨⟨Q3.step (k35.trans k6) (Body.ofQ hL o4 (by omega_using [hwq, e1])), ?_, ?_, fun j hj hj24 => ?_, qa⟩,
    (k15.trans k6).mono (by decide)⟩
  · show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega_using [e0, e1]) (by omega_arith), W0, (k15.trans k6).gpr (by decide)]; exact hi
  · show wordsVal t.mem L.Q (slot L.wq 4) L.wq = _
    rw [r4]
    show arrQ s₃.mem L 4 ^ _ % arrQ s₃.mem L 0 = _
    rw [A4, A0]
  · have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o4.wordsVal (by omega_using [e1, e24, this]) (by omega_arith)]; exact A24 j hj hj24

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.SignR`, which this module and modules that import it used -/

section

/-!
# DSA signing on RISC-V: r and the ranges

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Output.lean`). `rRanges_ok`: in the Q
space, `r = (g^k mod p) mod q` (`reduce64` of the buffer's `p_len` octets)
into array 25, and the header's word `hMask &=` the masks of `0 < k < q`,
`0 < x < q` and `r ≠ 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- An array of the Q space, kept by a change apart from it. -/
theorem qa_eq {L : Lay} (hL : L.Ok) {m m' : Mem} {o n j : Nat} (h : Outside L.Q o n m m') (hj : j < 28)
    (hd : slot L.wq j + 8 * L.wq ≤ o ∨ o + n ≤ slot L.wq j) : arrQ m' L j = arrQ m L j := by
  have := slot_lt (w := L.wq) hj
  have := hL.wq_ge
  exact h.wordsVal hd (by simp only [Lay.slot_eq] at *; omega_arith)

/-- The registers `rRanges` writes. -/
def rRangesRegs : List Reg :=
  enterRegs ++ [.s9, .t2] ++ [.s10] ++ (VG.Proof.Bignum.RISCV64.redRegs ++ [.a2, .a5, .a6]) ++ copyRegs ++
    [.s0, .t3, .t5] ++ [.s7, .s8] ++ loadRegs ++ ptrRegs ++ loadRegs ++ [.a4] ++ inRangeRegs ++ inRangeRegs ++
    nonZeroRegs

/-- `rRanges`: in the Q space, r into array 25, and `hMask &=` the masks of
`0 < k < q`, `0 < x < q` and `r ≠ 0`. Memory changes only in the Q space's
arrays 1–27 and in `hMask`. -/
theorem rRanges_ok {s : State} {L : Lay} {key nonce : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hq : 0 < arrQ s.mem L 0) (hm : word s.mem L.S hMask = mask b) :
    WP isa rRanges s fun t =>
      (QS t L key nonce ∧
        arrQ t.mem L 25 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ∧
        word t.mem L.S hMask = mask (b && decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < arrQ s.mem L 0) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < arrQ s.mem L 0) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 ≠ 0)) ∧
        (∃ m, QArr L s.mem m ∧ Outside L.S hMask 8 m t.mem)) ∧ Keep rRangesRegs s t := by
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega_using [e]
  have hZ := hL.z256
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  obtain e7 := e 7; have e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
  unfold rRanges
  -- r into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  refine WP.mono (bufBase_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1) (rd := .s9) (t := .t2) (by decide) (by decide)
    (by decide)) fun s₁' ⟨⟨a9, m1'⟩, k1'⟩ => ?_
  refine WP.mono (getP_ok (hs.congr (k1.trans k1').2.2) hL ((hr.keepM k1 m1).keepM k1' m1') .s10)
    fun s₂ ⟨⟨a10, m2⟩, k2'⟩ => ?_
  obtain k2 := k1'.trans k2'
  replace a9 : s₂.gpr .s9 = L.Buf := (k2'.gpr (by decide)).trans a9
  obtain m21 : s₂.mem = s.mem := by rw [m2, m1', m1]
  obtain k12 := k1.trans k2
  obtain e2 := q1.env.keep k2
  refine WP.seq (WP.mono (ModArith.reduce64_ok (B := L.Q) (Z := 1600) (w := L.wq) (D := L.Buf) (L := L.pl)
    e2.hs (by omega_using [hwq]) (by omega_using [hwq]) (by omega_using [hwq, e4]) e2.a7 e2.s5 e2.t0
    (by rw [m21]; exact hq) (by rw [a9]; exact (BitVec.add_zero _).symm) a10 (by omega_using [hpl]) (by omega_using [hpl])
    (by have := bufRd hL (hs.congr k12.2.2) (o := 0) (k := L.pl) (by omega_using [])
        simpa only [off, BitVec.add_zero] using this)
    (buf_apartQ L (n := L.pl) (by omega_using [hpl]))) fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  rw [m21] at v1 o3
  obtain k13 := k12.trans k3
  obtain Q3 : QS s₃ L key nonce := ⟨q1.keep (k2.trans k3), hs.congr k13.2.2,
    hr.keep k13 (Body.ofQ hL o3 (by omega_using [hwq, e1]))⟩
  -- r into array 25, 0 into array 7.
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 25) (a := 1) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨v25, o4⟩, k4⟩ => ?_)
  obtain Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega_using [hwq, e25]))
  refine WP.seq (WP.mono (zeroArr_ok Q4.inq.env (j := 7) (by decide)) fun s₅ ⟨⟨z7, o5⟩, k5⟩ => ?_)
  obtain Q5 := Q4.step k5 (Body.ofQ hL o5 (by omega_using [hwq, e7]))
  -- k into array 6, x into array 5.
  refine WP.seq (WP.mono (ptrR_ok Q5.scr hL Q5.regs) fun s₆ ⟨⟨b7, b8, m6⟩, k6⟩ => ?_)
  obtain Q6 := Q5.stepM k6 m6
  obtain k16 := ((k13.trans k4).trans k5).trans k6
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q6 hL (by decide) (hn.keep k16.2.1 k16.2.2) b7 b8
      (by omega_using [hql]) (by omega_using [hwq])) fun s₇ ⟨⟨Q7, v6, top6, o7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (ptrX_ok Q7.scr hL Q7.regs) fun s₈ ⟨⟨c7, c8, m8⟩, k8⟩ => ?_)
  obtain Q8 := Q7.stepM k8 m8
  obtain k18 := (k16.trans k7).trans k8
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q8 hL (by decide)
      ((hk.keep k18.2.1 k18.2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])) c7 c8
      (by omega_using [hql]) (by omega_using [hwq])) fun s₉ ⟨⟨Q9, v5, top5, o9⟩, k9⟩ => ?_)
  obtain k19 := k18.trans k9
  obtain qa : QArr L s.mem s₉.mem := by
    obtain q3 : QArr L s.mem s₃.mem := QArr.of o3 (by omega_using []) (by omega_using [e1, e28])
    obtain q4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega_using [e1, e25]) (by omega_using [e25, e28])
    obtain q5 : QArr L s₄.mem s₅.mem := QArr.of o5 (by omega_using [e1, e7]) (by omega_using [e7, e28])
    obtain q7 : QArr L s₆.mem s₇.mem := QArr.of o7 (by omega_using [e1, e6]) (by omega_using [e6, e28])
    obtain q9 : QArr L s₈.mem s₉.mem := QArr.of o9 (by omega_using [e1, e5]) (by omega_using [e5, e28])
    rw [m6] at q7; rw [m8] at q9
    exact (((q3.trans q4).trans q5).trans q7).trans q9
  -- `hMask` into `a4`.
  obtain ⟨hld, hal⟩ := ScrL.hdr Q9.scr hL (d := 0) (by decide) (by decide)
  obtain hw9 : word s₉.mem L.S hMask = mask b := by
    rw [(qa.body hL).word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₉.mem)
    (by brun [hMask, Q9.regs.s6, hld, hal]; exact hw9) (by decide) (by rfl)) fun s₁₀ ⟨⟨a4, m10⟩, k10⟩ => ?_)
  obtain Q10 := Q9.stepM k10 m10
  -- The values in arrays 0, 5, 6, 7 and 25.
  obtain A0 : arrQ s₁₀.mem L 0 = arrQ s.mem L 0 := by rw [m10]; exact qa.arr0 hL
  obtain b3 : Body L s.mem s₃.mem := Body.ofQ hL o3 (by omega_using [hwq, e1])
  obtain b5 : Body L s.mem s₅.mem := (b3.trans (Body.ofQ hL o4 (by omega_using [hwq, e25]))).trans (Body.ofQ hL o5 (by omega_using [hwq, e7]))
  obtain b7 : Body L s.mem s₇.mem := b5.trans (by rw [← m6]; exact Body.ofQ hL o7 (by omega_using [hwq, e6]))
  obtain A6 : arrQ s₁₀.mem L 6 = kOf s.mem L nonce := by
    rw [m10, qa_eq hL o9 (by decide) (by omega_using [e5, e6]), m8]
    refine v6.trans ?_
    rw [kOf, m6, hn.bytes b5 (by omega_using [hZ])]
  obtain A5 : arrQ s₁₀.mem L 5 = xOf s.mem L key := by
    rw [m10]
    refine v5.trans ?_
    rw [xOf, m8, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])).bytes b7 (by omega_using [hZ])]
  obtain A25 : arrQ s₁₀.mem L 25 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
    rw [m10, qa_eq hL o9 (by decide) (by omega_using [e5, e25]), m8, qa_eq hL o7 (by decide) (by omega_using [e6, e25]), m6,
      qa_eq hL o5 (by decide) (by omega_using [e7, e25])]
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot L.wq 1) fun i hi => v25 i (by omega_using [hi])]
    exact v1
  obtain z7' : arrQ s₁₀.mem L 7 = 0 := by
    rw [m10, qa_eq hL o9 (by decide) (by omega_using [e5, e7]), m8, qa_eq hL o7 (by decide) (by omega_using [e6, e7]), m6]
    exact z7
  obtain top6' : word s₁₀.mem L.Q (slot L.wq 6 + 8 * L.wq) = 0 := by
    rw [m10, o9.word (by omega_using [e5, e6]) (by omega_using [hwq, e6]), m8]; exact top6
  obtain top5' : word s₁₀.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by rw [m10]; exact top5
  -- The ranges and `r ≠ 0`.
  refine WP.seq (WP.mono (inRange_ok Q10.inq.env (a := 6) (b := b) (by decide) (by decide) (by decide) top6'
    z7' a4) fun s₁₁ ⟨⟨b4, o11⟩, k11⟩ => ?_)
  obtain Q11 := Q10.step k11 (Body.ofQ hL o11 (by omega_using [hwq, e3]))
  refine WP.seq (WP.mono (inRange_ok Q11.inq.env (a := 5) (b := _) (by decide) (by decide) (by decide)
    (by rw [o11.word (by omega_using [e3, e5]) (by omega_using [hwq, e5])]; exact top5')
    (by rw [show wordsVal s₁₁.mem L.Q (slot L.wq 7) L.wq = arrQ s₁₁.mem L 7 from rfl,
      qa_eq hL o11 (by decide) (by omega_using [e3, e7])]; exact z7') b4) fun s₁₂ ⟨⟨c4, o12⟩, k12'⟩ => ?_)
  obtain Q12 := Q11.step k12' (Body.ofQ hL o12 (by omega_using [hwq, e3]))
  refine WP.seq (WP.mono (nonZero_ok Q12.inq.env (a := 25) (c := 0) (by decide)
    (by rw [show wordsVal s₁₂.mem L.Q (slot L.wq 7) L.wq = arrQ s₁₂.mem L 7 from rfl,
      qa_eq hL o12 (by decide) (by omega_using [e3, e7]), qa_eq hL o11 (by decide) (by omega_using [e3, e7])]; exact z7')
    c4) fun s₁₃ ⟨⟨d4, m13⟩, k13'⟩ => ?_)
  obtain Q13 := Q12.stepM k13' m13
  -- The mask to `hMask`.
  obtain ⟨_, hal'⟩ := ScrL.hdr Q13.scr hL (d := 0) (by decide) (by decide)
  obtain hst : InRegions s₁₃.wr (off L.S 0) 8 := Q13.scr.st (by omega_using [hZ])
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s₁₃.mem.writeW (off L.S 0) (s₁₃.gpr .a4))
    (by brun [hMask, Q13.regs.s6, hst, hal']) (by decide) (by rfl)) fun t ⟨mt, kt⟩ => ?_
  obtain wo : Outside L.S hMask 8 s₁₃.mem t.mem := by
    rw [mt]; exact writeW_outside s₁₃.mem L.S _ (by simp only [hMask]; omega_using [])
  obtain kall := (((((k19.trans k10).trans k11).trans k12').trans k13').trans kt)
  obtain qa13 : QArr L s.mem s₁₃.mem := by
    rw [m13]
    exact (qa.trans (by rw [← m10]; exact QArr.of o11 (by omega_using [e1, e3]) (by omega_using [e3, e28]))).trans (QArr.of o12 (by omega_using [e1, e3]) (by omega_using [e3, e28]))
  refine ⟨⟨⟨Q13.inq.keep kt, Q13.scr.congr kt.2.2, Q13.regs.keepHdr kt
      (wo.word (Or.inr (by decide)) (by simp only [hLens]; omega_using []))⟩, ?_, ?_, ⟨s₁₃.mem, qa13, wo⟩⟩, ?_⟩
  · rw [qa_eq hL (mask_keepQ hL wo) (by decide) (Or.inl (by omega_using [hwq, e25])), m13, qa_eq hL o12 (by decide) (by omega_using [e3, e25]),
      qa_eq hL o11 (by decide) (by omega_using [e3, e25]), A25]
  · rw [mt, show off L.S 0 = off L.S hMask from rfl, word_writeW_self, d4, show wordsVal s₁₂.mem L.Q (slot L.wq 25) L.wq = arrQ s₁₂.mem L 25 from rfl,
      qa_eq hL o12 (by decide) (by omega_using [e3, e25]), qa_eq hL o11 (by decide) (by omega_using [e3, e25]),
      show wordsVal s₁₁.mem L.Q (slot L.wq 5) L.wq = arrQ s₁₁.mem L 5 from rfl,
      show wordsVal s₁₁.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₁.mem L 0 from rfl,
      qa_eq hL o11 (by decide) (by omega_using [e3, e5]), qa_eq hL o11 (by decide) (by omega_using [e0, e3]),
      show wordsVal s₁₀.mem L.Q (slot L.wq 6) L.wq = arrQ s₁₀.mem L 6 from rfl,
      show wordsVal s₁₀.mem L.Q (slot L.wq 0) L.wq = arrQ s₁₀.mem L 0 from rfl, A25, A6, A5, A0]
    simp only [Bool.and_assoc, Bool.decide_and]
  · simp only [rRangesRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.SignGk`, which only this module used -/

section

/-!
# DSA signing on RISC-V: `g^k mod p`

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Gk.lean`). `gk_ok`: in the P space
with p in array 0 and `R² mod p` in array 24, `g^k mod p` (k the `q_len`
octets at `ra`) to the buffer's first `p_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

/-- A word of the P space, kept by a change in the buffer's first `p_len` octets. -/
theorem buf_pword {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.Buf 0 L.pl m m') {d : Nat}
    (hd : d + 8 ≤ L.qOff) : word m' L.S d = word m L.S d := by
  have hw := hL.wp_ge
  have hq : L.qOff < 2 ^ 63 := by simp only [Lay.qOff, Lay.slot_eq]; omega_using [hw]
  refine (Mem.readW_congr fun i hi => (h _ (Or.inr ?_)).symm).symm
  by_contra hc
  have h1 := bufPastP hL (off L.S d + BitVec.ofNat 64 i) (by
    simp only [ofs] at hc ⊢; omega_using [hc])
  have h2 := ofs_off L.S (d := d) (i := i) (by omega_using [hd, hq, hi])
  simp only [ofs] at h1 h2
  omega_using [hd, hi, h1, h2]

/-- The registers `gk` writes. -/
def gkRegs : List Reg := [.s9] ++ ptrRegs ++ powPRegs ++ [.s7, .t2] ++ [.s8] ++ storeRegs

/-- `gk`: `g^k mod p` to the buffer's first `p_len` octets. Memory changes
only in the P space's arrays 1–23 and the buffer's first `p_len` octets. -/
theorem gk_ok {s : State} {L : Lay} {key nonce : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (2 * L.pl + L.ql))
    (hn : Src s L nonce L.ql) (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa gk s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L nonce % p ∧
        InP t L ∧ PInv t L ∧ ∃ m, PLow L s.mem m ∧ Outside L.Buf 0 L.pl m t.mem) ∧ Keep gkRegs s t := by
  have hw8 := hL.wp_eq
  have hpl := hL.pl
  unfold gk
  -- The pointers: the nonce into `s9`, g's octets into `s7`.
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = nonce ∧ u.mem = s.mem)
    (by brun [hr.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ =>
    WP.mono (ptrG_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨b7, _, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^k mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := nonce) (p := p) hL (hs.congr k12.2.2)
      (hr.keepM k12 hm2) (hin.keep k12) (by
        show ((word s₂.mem L.S (slot L.wp 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [hm2, k12.gpr (by decide)]; exact hi)
      ((hk.keep k12.2.1 k12.2.2).sub (o := L.pl + L.ql) (k := L.pl) (by omega_using [])) b7 (hn.keep k12.2.1 k12.2.2)
      ((k2.gpr (by decide)).trans a9) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, i3, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  have hr3 : Regs s₃ L key nonce := hr.keep k13 (PLow.body hL o3)
  -- To the buffer.
  refine WP.seq (WP.block_append (WP.mono (bufBase_ok (hs.congr k13.2.2) hL hr3 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k13.trans ku).2.2) hL (hr3.keepM ku mu) .s8) fun s₄ ⟨⟨f8, m4⟩, k4⟩ => ?_))
  have hm4 : s₄.mem = s₃.mem := by rw [m4, mu]
  have k14 := (k13.trans ku).trans k4
  have en4 := in3.env.keep (ku.trans k4)
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) en4 (by decide)
    (by have := ScrL.bufSt (hs.congr k14.2.2) hL (o := 0) (k := L.pl) (by omega_using [])
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega_using []) (by omega_using [hpl]); simpa only [off, BitVec.add_zero] using this)
    ((k4.gpr (by decide)).trans f7) f8 (by omega_using [hpl]) (by omega_using [hw8]) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm4] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega_using []]; exact wordsVal_lt _ _ _ _
  have kall := k14.trans kt
  have y3 : arrP s₃.mem L 4 = gOf s.mem L key ^ kOf s.mem L nonce % p := v4
  refine ⟨⟨?_, ⟨en4.keep kt, (kall.gpr (by decide)).trans hin.s6⟩, ?_, ⟨s₃.mem, o3, ot⟩⟩, ?_⟩
  · rw [vt, read_low _ _ (w := L.wp) (by rw [hw8]) (by
      show arrP s₃.mem L 4 < 2 ^ (8 * L.pl); rw [y3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp])) hplt)]
    exact y3
  · show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [buf_pword hL ot (by simp only [Lay.qOff, Lay.slot_eq]; omega_using []), ((ku.trans k4).trans kt).gpr (by decide)]
    exact i3
  · simp only [gkRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA signing on RISC-V: after the check of the key

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Body.lean`). `sbody_ok`: `Sign.body`
writes to `out` r's and s's `q_len` octets, most significant first, and
leaves 1 in `a0`, exactly when `0 < x < q`, `0 < k < q`, `g^x mod p = y`,
`r ≠ 0` and `s ≠ 0` (`SignOk`), for `r = (g^k mod p) mod q` (`sigR`) and
`s = k^(q − 2) (z + x r) mod q` (`sigS`), z the digest's first
`min(digest_len, bitLength q / 8)` octets; else zeros and 0. Memory changes
only in `scratch`'s `hMask` and past its header (`BKept`), and in `out`.
`sbodyWith_ok` states it of `kp` then `Sign.tail` for any first step `kp`
that does what `keyPair` does (`KPOk`): `vg_dsa_sign_prevalidated`'s
`setMask` is one, for a key with `g^x mod p = y`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- r, from the key and the nonce. -/
def sigR (p q g k : Nat) : Nat := g ^ k % p % q

/-- s, from x, the nonce, the digest's scalar and r. -/
def sigS (q x k z r : Nat) : Nat := k ^ (q - 2) % q * ((z % q + x * r % q) % q) % q

/-- The checks of signing past the public key's. -/
def SignOk (p q g y x k z : Nat) : Prop :=
  (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ sigR p q g k ≠ 0 ∧ sigS q x k z (sigR p q g k) ≠ 0

instance (p q g y x k z : Nat) : Decidable (SignOk p q g y x k z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `2^bitLength q ≤ 2 q`. -/
theorem pow_bitLength_le {q : Nat} (hq : q ≠ 0) : 2 ^ Spec.Dsa.bitLength q ≤ 2 * q := by
  simp only [Spec.Dsa.bitLength, hq, ite_false]
  rw [Nat.pow_succ]
  have := Nat.log2_self_le hq
  omega_using [this]

theorem encodeBE_zero (n : Nat) : Spec.Dsa.encodeBE n 0 = List.replicate n 0 := by
  rw [VG.Proof.Dsa.encodeBE_i2osp, VG.Proof.Bignum.i2osp_zero']

/-- Two values' octets, one after the other. -/
theorem out_bytes {m : Mem} {out : Addr} {ql a b : Nat} (ha : a < 256 ^ ql) (hb : b < 256 ^ ql)
    (h1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m out ql) = a)
    (h2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off out ql) ql) = b) :
    Spec.Rsa.bytesAt m out (2 * ql) = Spec.Dsa.encodeBE ql a ++ Spec.Dsa.encodeBE ql b := by
  obtain e1 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := 0) (len := ql) (by omega_using [])
  obtain e2 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := ql) (len := ql) (by omega_using [])
  simp only [List.drop_zero, BitVec.add_zero] at e1
  rw [List.take_of_length_le (by simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega_using [])] at e2
  rw [← List.take_append_drop ql (Spec.Rsa.bytesAt m out (2 * ql)), e1, e2,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) ha).mpr h1.symm,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) hb).mpr h2.symm]

/-- `Regs` through a change in `hMask` and past the header. -/
theorem Regs.ofBKept {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : Regs s L key sig)
    (k : Keep rs s t) (hb : BKept L s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  h.keepHdr k (hb.word (by decide) (by decide)) hr

theorem mask_keepQ' {L : Lay} (hL : L.Ok) {m m₁ m' : Mem} (h₁ : QArr L m m₁) (h₂ : Outside L.S hMask 8 m₁ m') :
    arrQ m' L 0 = arrQ m L 0 :=
  (keepQ_arr0 hL (mask_keepQ hL h₂)).trans (h₁.arr0 hL)

/-- `rrQ_ok`, and arrays 25–27 kept. -/
theorem rrQ25_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) :
    WP isa Verify.rrQ s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧
        (∀ j < 28, 25 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep rrQRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e25 := Lay.slot_eq L.wq 25
  obtain e28 := Lay.slot_eq L.wq 28
  unfold Verify.rrQ
  obtain hodd : (word s.mem L.Q (slot L.wq 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wq) (by omega_using [hwq])]; exact hqo
  refine WP.seq (WP.mono (minv_ok e.hs e.a7 (slot_al _ _) (by omega_using [e0]) hodd) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  obtain e1' := e.keep k1
  refine WP.mono (rr_ok e1' (by rw [m1]; exact hq)) fun t ⟨⟨_, r24, o⟩, kt⟩ => ?_
  rw [m1] at r24 o
  obtain qa : QArr L s.mem t.mem := QArr.of o (by omega_using []) (by omega_using [e1, e28])
  refine ⟨⟨h.step (k1.trans kt) (qa.body hL), ?_, r24, fun j hj hj25 => ?_, qa⟩, k1.trans kt⟩
  · show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega_using [e0, e1]) (by omega_using [e0]), kt.gpr (by decide)]
    exact i1
  · have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj25
    exact o.wordsVal (Or.inr (by omega_using [e1, e25, this])) (by omega_arith)

/-- What `keyPair` does from `s`, which signing's first step `kp` does too:
the mask of `g^x mod p = y` into `hMask`, memory changed only there and in
the P space's arrays 1–23. -/
def KPOk (kp : Prog isa) (s : State) (L : Lay) (key : Addr) : Prop :=
  ∀ p, arrP s.mem L 0 = p → 2 ≤ p → p % 2 = 1 → arrP s.mem L 24 = 2 ^ (128 * L.wp) % p →
    WP isa kp s fun t =>
      (word t.mem L.S hMask = mask (decide (gOf s.mem L key ^ xOf s.mem L key % p = yOf s.mem L key)) ∧
        InP t L ∧ PInv t L ∧ ∃ m, PLow L s.mem m ∧ Outside L.S hMask 8 m t.mem) ∧ Keep keyPairRegs s t

/-- `keyPair` is a first step of signing. -/
theorem keyPair_KPOk {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (3 * L.pl + 2 * L.ql)) :
    KPOk keyPair s L key :=
  fun _ p0 hp hpo p24 => keyPair_ok hL hs hr hin hi hk p0 hp hpo p24

/-- The registers of `Sign.body` up to `output`. -/
def sprefixRegs : List Reg :=
  keyPairRegs ++ gkRegs ++ rRangesRegs ++ rrQRegs ++ qm2Regs ++ invRegs ++ sValueRegs

/-- `Sign.body` up to `output` (here any `c`): `sValue` leaves r in the Q
space's array 25, s in its array 6, and in the header's word `hMask` the mask
of the checks but `s ≠ 0`. -/
theorem sprefix_ok {s₀ s : State} {L : Lay} {key nonce dig : Addr} {d : Nat} {kp c : Prog isa}
    {Q : State → Prop}
    (hL : L.Ok) (hK : ParamsOk s₀.mem L key) (hc : Checked s₀ s L key nonce d) (hfst : KPOk kp s L key)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig)
    (hcont : ∀ t, QS t L key nonce → BKept L s.mem t.mem →
      word t.mem L.S hMask = mask (decide (gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key =
          yOf s₀.mem L key) &&
        decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < qOf s₀.mem L key) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key) ∧
          sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) ≠ 0)) →
      arrQ t.mem L 25 = sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) →
      arrQ t.mem L 6 = sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
        (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)) →
      Keep sprefixRegs s t → WP isa c t Q) :
    WP isa (.seq kp (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
      (.seq sValue c))))))) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  obtain ⟨ip, scr, regs, p0, -, inv, p24, q0, -, lens⟩ := hc
  obtain hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega_using [])
  obtain hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega_using [])
  obtain ⟨-, eq, eg⟩ := params_kept hk2 hkp
  obtain ey := y_kept hk3 hkp
  obtain hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  unfold ParamsOk at hK
  generalize pOf s₀.mem L key = p at hK p0 p24 hcont
  generalize qOf s₀.mem L key = q at hK q0 lens hqlt hcont
  generalize gOf s₀.mem L key = g at hK eg hcont
  generalize yOf s₀.mem L key = y at ey hcont
  obtain B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  obtain hq8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
    have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega_using [this]
  obtain hnq : Spec.Dsa.bitLength q / 8 ≤ L.ql := q_bits (by omega_using [B]) hqlt
  generalize Spec.Dsa.bitLength q / 8 = n at lens hq8 hnq hcont
  -- The values read from outside `scratch`, kept.
  obtain hdgn : Src s L dig (min d n) := hdg.take (Nat.min_le_left _ _)
  obtain vals : ∀ {m : Mem}, BKept L s.mem m → xOf m L key = xOf s.mem L key ∧ kOf m L nonce = kOf s.mem L nonce ∧
      gOf m L key = g ∧ yOf m L key = y ∧ Spec.Rsa.bytesAt m dig (min d n) = Spec.Rsa.bytesAt s.mem dig (min d n) :=
    fun hm => ⟨by simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])).bytes hm.out (by omega_using [])],
      by simp only [kOf]; rw [hn.bytes hm.out (by omega_using [])],
      by simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega_using [])).bytes hm.out (by omega_using [])]; exact eg,
      by simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega_using [])).bytes hm.out (by omega_using [])]; exact ey,
      hdgn.bytes hm.out (by omega_using [])⟩
  generalize hX : xOf s.mem L key = X at vals hcont
  generalize kOf s.mem L nonce = K at vals hcont
  -- The mask of `g^x mod p = y`.
  refine WP.seq (WP.mono (hfst p p0 (by omega_using [B]) hpo p24)
    fun s₁ ⟨⟨mx₁, ip₁, i₁, m₁, o₁, w₁⟩, k₁⟩ => ?_)
  rw [(vals (BKept.refl _ _)).2.2.1, (vals (BKept.refl _ _)).2.2.2.1, hX] at mx₁
  obtain K₁ : BKept L s.mem s₁.mem := (BKept.ofBody hL (PLow.body hL o₁)).trans (BKept.ofMask hL w₁)
  obtain q0₁ : arrQ s₁.mem L 0 = q := by
    rw [keepQ_arr0 hL (mask_keepQ hL w₁), keepQ_arr0 hL (PLow.keepQ hL o₁)]; exact q0
  obtain p0₁ : arrP s₁.mem L 0 = p := by rw [mask_arrP hL w₁ 0 (by decide), PLow.arr hL o₁ (by decide) (.inl rfl)]; exact p0
  obtain p24₁ : arrP s₁.mem L 24 = 2 ^ (128 * L.wp) % p := by
    rw [mask_arrP hL w₁ 24 (by decide), PLow.arr hL o₁ (by decide) (.inr (by decide))]; exact p24
  obtain hr₁ := regs.ofBKept k₁ K₁
  -- `g^k mod p` to the buffer.
  refine WP.seq (WP.mono (gk_ok (p := p) hL (scr.congr k₁.2.2) hr₁ ip₁ i₁ (hk2.keep k₁.2.1 k₁.2.2)
      (hn.keep k₁.2.1 k₁.2.2) p0₁ (by omega_using [B]) hpo p24₁)
    fun s₂ ⟨⟨gk₂, _, _, m₂, o₂, b₂⟩, k₂⟩ => ?_)
  rw [(vals K₁).2.2.1, (vals K₁).2.1] at gk₂
  obtain B₂ : Body L s₁.mem s₂.mem := (PLow.body hL o₂).trans (Body.ofBuf hL b₂ (by omega_using []))
  obtain K₂ := K₁.trans (BKept.ofBody hL B₂)
  obtain k₁₂ := k₁.trans k₂
  obtain q0₂ : arrQ s₂.mem L 0 = q := by
    rw [keepQ_arr0 hL (bufKeepQ b₂ (by omega_using [hpl])), keepQ_arr0 hL (PLow.keepQ hL o₂)]; exact q0₁
  obtain mx₂ : word s₂.mem L.S hMask = mask (decide (g ^ X % p = y)) := (B₂.word (by decide)).trans mx₁
  -- r, and the masks of the ranges.
  refine WP.seq (WP.mono (rRanges_ok hL (scr.congr k₁₂.2.2) (regs.ofBKept k₁₂ K₂) (hk.keep k₁₂.2.1 k₁₂.2.2)
      (hn.keep k₁₂.2.1 k₁₂.2.2) (by rw [q0₂]; omega_using [B]) mx₂)
    fun s₃ ⟨⟨Q₃, r25₃, m₃, mf, fa, fb⟩, k₃⟩ => ?_)
  rw [q0₂, gk₂] at r25₃
  rw [q0₂, gk₂, (vals K₂).1, (vals K₂).2.1] at m₃
  obtain K₃ := (K₂.trans (BKept.ofBody hL (fa.body hL))).trans (BKept.ofMask hL fb)
  obtain k₁₃ := k₁₂.trans k₃
  obtain q0₃ : arrQ s₃.mem L 0 = q := (mask_keepQ' hL fa fb).trans q0₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ25_ok hL Q₃ (by rw [q0₃]; omega_using [B]) (by rw [q0₃]; exact hqo))
    fun s₄ ⟨⟨Q₄, I₄, h24₄, a25₄, qa₄⟩, k₄⟩ => ?_)
  rw [q0₃] at h24₄
  obtain q0₄ : arrQ s₄.mem L 0 = q := (qa₄.arr0 hL).trans q0₃
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok hL Q₄ (by rw [q0₄]; omega_using [B]) (by rw [q0₄]; exact hqlt))
    fun s₅ ⟨⟨Q₅, bq₅, kj₅, w0₅, qb₅⟩, k₅⟩ => ?_)
  rw [q0₄] at bq₅
  obtain q0₅ : arrQ s₅.mem L 0 = q := (kj₅ 0 (by decide) (by decide)).trans q0₄
  obtain I₅ : QInv s₅ L := I₄.keepW w0₅ (k₅.gpr (by decide))
  obtain K₅ := K₃.trans (BKept.ofBody hL ((qa₄.body hL).trans (qb₅.body hL)))
  obtain k₁₅ := (k₁₃.trans k₄).trans k₅
  -- `w = k^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverseK_ok hL Q₅ I₅ (hn.keep k₁₅.2.1 k₁₅.2.2) (by rw [q0₅]; omega_using [B])
      (by rw [q0₅]; exact hqo) (by rw [q0₅, kj₅ 24 (by decide) (by decide)]; exact h24₄))
    fun s₆ ⟨⟨Q₆, I₆, w4₆, k24₆, qa₆⟩, k₆⟩ => ?_)
  rw [q0₅, bq₅, (vals K₅).2.1] at w4₆
  obtain q0₆ : arrQ s₆.mem L 0 = q := (qa₆.arr0 hL).trans q0₅
  obtain K₆ := K₅.trans (BKept.ofBody hL (qa₆.body hL))
  obtain k₁₆ := k₁₅.trans k₆
  obtain r25₆ : arrQ s₆.mem L 25 = g ^ K % p % q :=
    (k24₆ 25 (by decide) (by decide)).trans ((kj₅ 25 (by decide) (by decide)).trans
      ((a25₄ 25 (by decide) (by decide)).trans r25₃))
  -- s.
  obtain hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₆.mem dig (min d n)) < 2 * arrQ s₆.mem L 0 := by
    rw [(vals K₆).2.2.2.2, q0₆]
    refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
    rw [VG.Proof.Bignum.bytesAt_length]
    refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right d n)) ?_
    have := pow_bitLength_le (q := q) (by omega_using [B])
    rw [hq8, Nat.pow_mul] at this
    exact this
  refine WP.seq (WP.mono (sValue_ok hL Q₆ I₆ (by rw [K₆.word (by decide) (by decide)]; exact hdg8)
      (by rw [K₆.word (by decide) (by decide)]; exact lens) hnq hd
      (hdgn.keep k₁₆.2.1 k₁₆.2.2) (hk.keep k₁₆.2.1 k₁₆.2.2) (by rw [q0₆]; omega_using [B]) (by rw [q0₆]; exact hqo)
      (by rw [k24₆ 24 (by decide) (by decide), kj₅ 24 (by decide) (by decide), h24₄, q0₆])
      (by rw [w4₆, q0₆]; exact Nat.mod_lt _ (by omega_using [B]))
      (by rw [r25₆, q0₆]; exact Nat.mod_lt _ (by omega_using [B])) hz)
    fun s₇ ⟨⟨Q₇, _, s6₇, a25₇, qa₇⟩, k₇⟩ => ?_)
  rw [q0₆, w4₆, r25₆, (vals K₆).1, (vals K₆).2.2.2.2] at s6₇
  exact hcont s₇ Q₇ (K₆.trans (BKept.ofBody hL (qa₇.body hL))) (((qa₄.body hL).trans
    ((qb₅.body hL).trans ((qa₆.body hL).trans (qa₇.body hL)))).word (by decide) |>.trans m₃)
    (a25₇.trans r25₆) s6₇ (by
      have := k₁₆.trans k₇; simp only [sprefixRegs, List.append_assoc] at this ⊢; exact this)

/-- The registers `Sign.body` writes. -/
def sbodyRegs : List Reg := sprefixRegs ++ outputRegs

theorem sbodyWith_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat} {kp : Prog isa}
    (hL : L.Ok) (hK : ParamsOk s₀.mem L key) (hc : Checked s₀ s L key nonce d) (hfst : KPOk kp s L key)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64) (hos : Src s L out (2 * L.ql)) :
    WP isa (.seq kp Sign.tail) s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) =
          (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
              (xOf s.mem L key) (kOf s.mem L nonce)
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            then Spec.Dsa.encodeBE L.ql (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
                (kOf s.mem L nonce)) ++
              Spec.Dsa.encodeBE L.ql (sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
                (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
                (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)))
            else List.replicate (2 * L.ql) 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
            (yOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
          then 1 else 0) ∧
        (∃ m, BKept L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧
        Keep sbodyRegs s t := by
  have scr := hc.scr
  obtain hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    obtain eq := (params_kept (hk.take (k := 2 * L.pl + L.ql) (by omega_using [])) hkp).2.1
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  unfold Sign.tail
  refine sprefix_ok hL hK hc hfst hkp hk hn hd hdg hdg8 fun s₇ Q₇ K₇ m₇ r25₇ s6₇ k₁₇ => ?_
  unfold ParamsOk at hK
  generalize pOf s₀.mem L key = p at hK m₇ r25₇ s6₇ ⊢
  generalize qOf s₀.mem L key = q at hK hqlt m₇ r25₇ s6₇ ⊢
  generalize gOf s₀.mem L key = g at hK m₇ r25₇ s6₇ ⊢
  generalize yOf s₀.mem L key = y at m₇ ⊢
  generalize xOf s.mem L key = X at m₇ s6₇ ⊢
  generalize kOf s.mem L nonce = K at m₇ r25₇ s6₇ ⊢
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength q / 8))) = Z at s6₇ ⊢
  obtain B := VG.Proof.Dsa.supported_bounds hK.1.1
  -- The output.
  obtain hrq : sigR p q g K < q := Nat.mod_lt _ (by omega_using [B])
  obtain hsq : sigS q X K Z (sigR p q g K) < q := Nat.mod_lt _ (by omega_using [B])
  refine WP.mono (output_ok hL Q₇ (by rw [K₇.word (by decide) (by decide)]; exact hw) m₇
      (fun i hi => by rw [k₁₇.2.2]; exact hout i hi) hno (hos.keep k₁₇.2.1 k₁₇.2.2)
      (by rw [r25₇]; omega_using [hqlt, hrq]) (by rw [s6₇]; omega_using [hqlt, hsq]))
    fun t ⟨⟨o1, o2, t0, mo, qo, oo⟩, kt⟩ => ?_
  rw [r25₇, s6₇] at o1
  rw [s6₇] at o2 t0
  obtain hcb : (decide (g ^ X % p = y) && decide ((0 < K ∧ K < q) ∧ (0 < X ∧ X < q) ∧ sigR p q g K ≠ 0) &&
      decide (sigS q X K Z (sigR p q g K) ≠ 0)) = decide (SignOk p q g y X K Z) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold SignOk sigR
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨h3, h2, h1, h4, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h3, h2, h1, h4⟩, h5⟩
  rw [hcb] at o1 o2 t0
  obtain h256 : ∀ v, v < q → v < 256 ^ L.ql := fun v hv => by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; omega_using [hqlt, hv]
  obtain kall := k₁₇.trans kt
  refine ⟨⟨?_, ?_, ⟨mo, K₇.trans (BKept.ofBody hL (qo.body hL)), oo⟩,
    (kt.gpr (by decide)).trans Q₇.regs.s6, scr.congr kall.2.2⟩, ?_⟩
  · by_cases hc : SignOk p q g y X K Z
    · simp only [hc, decide_true, ite_true] at o1 o2 ⊢
      exact out_bytes (h256 _ hrq) (h256 _ hsq) o1 o2
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at o1 o2 ⊢
      rw [out_bytes (Nat.pow_pos (by decide : 0 < 256)) (Nat.pow_pos (by decide : 0 < 256)) o1 o2, encodeBE_zero,
        List.replicate_append_replicate, Nat.two_mul]
  · rw [t0]
    simp only [decide_eq_true_eq]
  · exact kall

theorem sbody_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : ParamsOk s₀.mem L key) (hc : Checked s₀ s L key nonce d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64) (hos : Src s L out (2 * L.ql)) :
    WP isa Sign.body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) =
          (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
              (xOf s.mem L key) (kOf s.mem L nonce)
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            then Spec.Dsa.encodeBE L.ql (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
                (kOf s.mem L nonce)) ++
              Spec.Dsa.encodeBE L.ql (sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
                (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
                (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)))
            else List.replicate (2 * L.ql) 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
            (yOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
          then 1 else 0) ∧
        (∃ m, BKept L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧
        Keep sbodyRegs s t :=
  sbodyWith_ok hL hK hc (keyPair_KPOk hL hc.scr hc.regs hc.inp hc.inv hk) hkp hk hn hd hdg hdg8 hw hout hno hos

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.SignFront`, which this module and modules that import it used -/

section

/-!
# DSA signing on RISC-V: the contract on the registers, and the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/PrevalidatedSign/Contract.lean`). `sContract`:
`vg_dsa_sign(out = a0, out_len = a1, key = a2, key_len = a3, p_len = a4,
nonce = a5, q_len = a6, digest = a7, digest_len, scratch, scratch_len)`, the
last three on the stack. `sfront_ok`: `entry` loads `scratch`'s address
from the stack, saves the callee-saved registers and `ra` in its header,
keeps the key and the nonce in `s11` and `ra` (`Regs`), and the digest's
address, `out` and the lengths in the header's `hDigest`, `Sign.hOut` and
`hLens`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- The arguments on the stack: `digest_len`, `scratch` and `scratch_len`. -/
abbrev sStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The signature `signBytes` gives, on entry. -/
def sRes (s : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- `vg_dsa_sign`, on the registers and the stack. -/
def sContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let key : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let nc : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let dg : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.rd = [key, nc, dg, sStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint key ∧ out.Disjoint nc ∧ out.Disjoint dg ∧ out.Disjoint scr ∧ out.Disjoint (sStackArgs s) ∧
      key.Disjoint scr ∧ nc.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (sStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a4).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat + 2 * (s.gpr .a6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 2).toNat ∧
      (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (sRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat = (sRes s).getD (List.replicate (s.gpr .a1).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a4).toNat (s₁.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat) ++ [Spec.Dsa.signStatus (sRes s₁)] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a4).toNat (s₂.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat) ++ [Spec.Dsa.signStatus (sRes s₂)]

/-- `vg_dsa_sign`'s contract on the registers, for a key that passes `valid`. -/
def sContractWith (valid : Nat → Nat → List Byte → Bool) : Contract isa where
  pre s := sContract.pre s ∧
    valid (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = true
  post := sContract.post
  pub := sContract.pub

/-- A call's layout. -/
def slayOf (s : State) : Lay := ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .a4).toNat, (s.gpr .a6).toNat⟩

theorem slayOf_ok {s : State} (h : sContract.pre s) : (slayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw, -, -⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, nw⟩

/-- The stack's arguments lie apart from the header's word at `d`. -/
theorem stack_sep {S B : Addr} {Z d : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hdZ : d + 8 ≤ Z)
    (hZ : Z ≤ 2 ^ 64) : Mem.Sep B 8 (off S d) 8 := by
  intro x h₁ h₂
  rw [off, Offset.lt_iff x S (by omega_using [hdZ, hZ])] at h₂
  exact hd x (by simp only [Region.Contains]; omega_using [hdZ, h₂]) (by simp only [Region.Contains]; omega_using [h₁])

/-- The stack's arguments are kept by a change in the header. -/
theorem stack_kept {S B : Addr} {Z : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hZ : 256 ≤ Z)
    {m m' : Mem} (ho : Outside S 0 256 m m') : m'.readW B 64 = m.readW B 64 := by
  refine Mem.readW_congr fun i hi => ho _ (Or.inr ?_)
  by_contra hc
  obtain hlt := (B + BitVec.ofNat 64 i - S).isLt
  exact hd (B + BitVec.ofNat 64 i) (by simp only [Region.Contains, ofs] at hc ⊢; omega_arith)
    (by simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

/-- The registers `Sign.entry` writes. -/
def sentryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3, .a7, .a1]

/-- What `Sign.entry` leaves. -/
structure SFront (s t : State) : Prop where
  regs : Regs t (slayOf s) (s.gpr .a2) (s.gpr .a5)
  scr : ScrL t (slayOf s)
  lens : word t.mem (stackArg s 1) hLens = pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64)
  dig : word t.mem (stackArg s 1) hDigest = s.gpr .a7
  outw : word t.mem (stackArg s 1) Sign.hOut = s.gpr .a0
  sav : ∀ i < 13, word t.mem (stackArg s 1) (saveOff i) = s.gpr (saved i)
  out : Outside (stackArg s 1) 0 256 s.mem t.mem

/-- `entry`: `scratch` (from the stack) into `s6`, the callee-saved
registers saved in its header, the key and the nonce into `s11` and `ra`,
the digest's address, `out` and the lengths into the header. Memory changes
only in the header. -/
theorem sfront_ok {s : State} (h : sContract.pre s) :
    WP isa (.block Sign.entry) s fun t => SFront s t ∧ Keep sentryRegs s t := by
  obtain hL := slayOf_ok h
  have hZ := hL.z256
  obtain hpl : (s.gpr .a4).toNat < 2 ^ 16 := by have := hL.pl; simp only [slayOf] at this; omega_arith
  obtain hql : (s.gpr .a6).toNat < 2 ^ 16 := by have := hL.ql; simp only [slayOf] at this; omega_arith
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dSS, -, -, -, -, nw, -, -, -, -, alS, sp16⟩ := h
  obtain hscr : ∀ t : State, t.wr = s.wr → ScrL t (slayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [slayOf]) nw alS
  obtain hZ' : (stackArg s 2).toNat * 8 ≤ 2 ^ 64 := by omega_using [nw]
  obtain hZS : 256 ≤ (stackArg s 2).toNat * 8 := by simp only [slayOf] at hZ; exact hZ
  unfold Sign.entry
  simp only [List.append_assoc]
  -- `scratch` into `t2`.
  obtain hld8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
      rw [show s.sp + BitVec.ofNat 64 8 - s.sp = BitVec.ofNat 64 8 by rw [BitVec.add_comm, BitVec.add_sub_cancel]]; decide⟩
  obtain hal8 : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [sp16]
  have hv8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  refine WP.block_append (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = stackArg s 1 ∧ u.mem = s.mem ∧
      u.sp = s.sp) (by brun [exec_addSp (show 8 < 2048 by decide), hld8, hal8, hv8]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a2, m1, sp1⟩, k1⟩ => ?_)
  obtain hs₁ := hscr s₁ k1.2.2
  obtain hin : ∀ i < 13, InRegions s₁.wr (off (savW (stackArg s 1)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.st (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
  obtain hal : ∀ i < 13, (off (savW (stackArg s 1)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.al8 (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega_using [])
  refine WP.block_append (WP.mono (saveT2_ok s₁ a2 hin hal) fun s₂ hS₂ => ?_)
  obtain k12 := k1.trans hS₂.keep
  obtain e : ∀ r, r ≠ .t2 → r ≠ .s6 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr fun hm => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact h1 hm
      · exact h1 hm
      · exact h2 hm
  obtain hs₂ := hscr s₂ k12.2.2
  obtain sp₂ : s₂.sp = s.sp := hS₂.sp.trans sp1
  obtain hst8 : InRegions s₂.wr (off (stackArg s 1) 8) 8 := hs₂.st (d := 8) (by simp only [slayOf] at hZ ⊢; omega_using [hZ])
  obtain hst16 : InRegions s₂.wr (off (stackArg s 1) 16) 8 := hs₂.st (d := 16) (by simp only [slayOf] at hZ ⊢; omega_using [hZ])
  obtain hst24 : InRegions s₂.wr (off (stackArg s 1) 24) 8 := hs₂.st (d := 24) (by simp only [slayOf] at hZ ⊢; omega_using [hZ])
  obtain hal8' : (off (stackArg s 1) 8).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 8) (by decide) (by decide)).2
  obtain hal16' : (off (stackArg s 1) 16).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 16) (by decide) (by decide)).2
  obtain hal24' : (off (stackArg s 1) 24).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 24) (by decide) (by decide)).2
  -- `digest_len`, from the stack.
  obtain f1 : Outside (stackArg s 1) 128 104 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (base := stackArg s 1) (d := 128) (len := 104) hS₂.frame (by omega_using [])
  have dSS' : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩ := dSS
  obtain hv0 : ((s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)).writeW (off (stackArg s 1) 24) (s.gpr .a0)).readW
      (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := by
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
        (show Mem.Sep (s.sp + BitVec.ofNat 64 0) 8 (off (stackArg s 1) 24) 8 from
          stack_sep (B := stackArgAddr s 0) dSS' (by omega_using [hZS]) hZ') (by decide),
      Mem.readW_writeW_sep (w := 64) (w' := 64)
        (show Mem.Sep (s.sp + BitVec.ofNat 64 0) 8 (off (stackArg s 1) 8) 8 from
          stack_sep (B := stackArgAddr s 0) dSS' (by omega_using [hZS]) hZ') (by decide),
      show s.sp + BitVec.ofNat 64 0 = stackArgAddr s 0 from rfl,
      stack_kept dSS' hZS (f1.mono (Nat.zero_le _) (by omega_using [])), m1]
    rfl
  obtain hld0 : InRegions (s₂.rd ++ s₂.wr) (s.sp + BitVec.ofNat 64 0) 8 := by
    rw [k12.2.1, k12.2.2]
    exact ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains, stackArgAddr, Nat.mul_zero]; rw [BitVec.sub_self]; decide⟩
  obtain hal0 : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; omega_using [sp16]
  obtain hv0' : ((s₂.mem.writeW (stackArg s 1 + BitVec.ofNat 64 8) (s.gpr .a7)).writeW
      (stackArg s 1 + BitVec.ofNat 64 24) (s.gpr .a0)).readW s.sp 64 = stackArg s 0 := by
    rw [← add_ofNat_zero s.sp]; exact hv0
  obtain hld0' : InRegions (s₂.rd ++ s₂.wr) s.sp 8 := by rw [← add_ofNat_zero s.sp]; exact hld0
  obtain hal0' : s.sp.toNat % 8 = 0 := by omega_using [sp16]
  -- The key, the nonce, the digest's address, `out` and `digest_len`.
  refine WP.block_append (WP.mono (WP.keep [.s11, .ra, .t3, .a7] (Q := fun t =>
      t.mem = (s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)).writeW (off (stackArg s 1) 24) (s.gpr .a0) ∧
      t.gpr .s11 = s.gpr .a2 ∧ t.gpr .ra = s.gpr .a5 ∧ t.gpr .a7 = stackArg s 0) (by
        brun [hS₂.s6, e .a2 (by decide) (by decide), e .a5 (by decide) (by decide), e .a7 (by decide) (by decide),
          e .a0 (by decide) (by decide), hDigest, Sign.hOut, hst8, hal8', hst24, hal24', BitVec.add_zero, sp₂,
          exec_addSp (show 0 < 2048 by decide), hld0', hal0', hv0'])
      (by decide) (by rfl)) fun s₃ ⟨⟨m3, t11, tra, ta7⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  obtain e3 : ∀ r, r ≠ .t2 → r ≠ .s6 → r ≠ .s11 → r ≠ .ra → r ≠ .t3 → r ≠ .a7 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => (k3.gpr (by simp [h3, h4, h5, h6])).trans (e r h1 h2)
  obtain hcap := cap_eq (stackArg s 0)
  obtain hpk := pack_entry (s.gpr .a4) (s.gpr .a6) hpl hql (show min (stackArg s 0).toNat 64 < 2 ^ 16 by omega_using [])
  refine WP.mono (WP.keep [.t3, .a1] (Q := fun t =>
      t.mem = s₃.mem.writeW (off (stackArg s 1) 16)
        (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 (min (stackArg s 0).toNat 64))) ?_ (by decide) (by rfl))
    fun t ⟨mt, kt⟩ => ?_
  · unfold Verify.capD
    brun [(k3.gpr (r := .s6) (by decide)).trans hS₂.s6, e3 .a4 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), e3 .a6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ta7, hLens, k3.2.2 ▸ hst16, hal16', hcap, hpk, exec_li_zero,
      exec_li_lit (show 64 < 2048 by decide), exec_shift_d (show 6 < 64 by decide),
      exec_shift_d (show 63 < 64 by decide), exec_shift_d (show 48 < 64 by decide),
      exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]
  · have k := k13.trans kt
    have hp16 : (slayOf s).pl < 2 ^ 16 := hpl
    have hq16 : (slayOf s).ql < 2 ^ 16 := hql
    obtain hd16 : min (stackArg s 0).toNat 64 < 2 ^ 16 := by omega_using []
    obtain hnw : (stackArg s 1).toNat + 256 ≤ 2 ^ 64 := by simp only [slayOf] at hZ; omega_using [hZ, nw]
    obtain w16 := writeW_outside s₃.mem (stackArg s 1) (d := 16)
      (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 (min (stackArg s 0).toNat 64)) (by omega_using [])
    obtain w24 := writeW_outside (s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)) (stackArg s 1) (d := 24)
      (s.gpr .a0) (by omega_using [])
    obtain w8 := writeW_outside s₂.mem (stackArg s 1) (d := 8) (s.gpr .a7) (by omega_using [])
    obtain hlen : word t.mem (stackArg s 1) hLens =
        pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64) := by
      rw [mt]; exact word_writeW_self _ _ _ _
    have hlen' : word t.mem (slayOf s).S hLens =
        pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64) := hlen
    refine ⟨⟨⟨(kt.gpr (by decide)).trans ((k3.gpr (by decide)).trans hS₂.s6), (kt.gpr (by decide)).trans t11,
      (kt.gpr (by decide)).trans tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) hd16,
      by rw [hlen']; exact pack_ql hp16 hq16 (by decide) hd16⟩, hscr t k.2.2, hlen, ?_, ?_, fun i hi => ?_, ?_⟩,
      k.mono (by decide)⟩
    · rw [mt, w16.word (by simp only [hDigest]; omega_using []) (by simp only [hDigest]; omega_using []), m3,
        w24.word (by simp only [hDigest]; omega_using []) (by simp only [hDigest]; omega_using [])]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [Sign.hOut]; omega_using []) (by simp only [Sign.hOut]; omega_using []), m3]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi]), m3,
        w24.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi]),
        w8.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])]
      show s₂.mem.readW (stackArg s 1 + BitVec.ofNat 64 (saveOff i)) 64 = _
      rw [saveOff_eq, hS₂.saved i hi]
      exact k1.gpr fun h => saved_ne_t2 i hi (List.mem_singleton.mp h)
    · have o3 : Outside (stackArg s 1) 0 256 s₁.mem s₃.mem := by
        rw [m3]
        exact ((f1.mono (Nat.zero_le _) (by omega_using [])).trans (w8.mono (Nat.zero_le _) (by omega_using []))).trans
          (w24.mono (Nat.zero_le _) (by omega_using []))
      rw [mt, ← m1]
      exact o3.trans (w16.mono (Nat.zero_le _) (by omega_using []))

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA signing on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Fn.lean`). `sign_correct`:
`vg_dsa_sign` meets `sContract`. After `entry` (`sfront_ok`), `checkSignKey`
(`checkSignKey_ok`: the domain's checks and `1 < y < p`) either runs `body`
(`sbody_ok`) or `zeroOut` (`szero_ok`), and `restore` gives back the
callee-saved registers (`sfinish_ok`); the result is the specification's by
`Proof/Dsa/Accepted.lean`'s `signBytes_compute`. The specification's
`y^q mod p = 1` needs no check of its own: with the domain's `g^q mod p = 1`
it follows from `g^x mod p = y`, which `body` checks (`signChecks_iff`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)

/-- `y^q mod p = 1` from `g^q mod p = 1` and `g^x mod p = y`. -/
theorem pow_order_of_gen {p q g x y : Nat} (hp : 1 < p) (hg : g ^ q % p = 1) (hy : g ^ x % p = y) :
    y ^ q % p = 1 := by
  subst hy
  rw [← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, hg, Nat.one_pow,
    Nat.mod_eq_of_lt hp]

/-- With the domain's checks and `1 < y < p`, the public key's checks hold
whenever signing's do: `y^q mod p = 1` follows from `g^x mod p = y`. -/
theorem signChecks_iff {p q g y x k z : Nat} (hg : 1 < g ∧ g < p) (hd : (p - 1) % q = 0)
    (hgq : g ^ q % p = 1) (hy : 1 < y ∧ y < p) :
    (VG.Proof.Dsa.publicChecks p q g y ∧ SignOk p q g y x k z) ↔ SignOk p q g y x k z :=
  ⟨fun h => h.2, fun h => ⟨⟨⟨hg, hy⟩, hd, hgq, pow_order_of_gen (by omega_using [hg]) hgq h.2.2.1⟩, h⟩⟩

/-- The domain passes its checks and `1 < y < p`: what `checkSignKey`
checks. -/
abbrev SignKeyOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  ParamsOk m L key ∧ (1 < yOf m L key ∧ yOf m L key < pOf m L key)

/-- `Sign.checkSignKey rest fail` runs `rest` exactly when the domain passes
the specification's checks and `1 < y < p` (`SignKeyOk`), leaving what
`checkKey` leaves (`Checked`); else `fail`. -/
theorem checkSignKey_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, SignKeyOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ SignKeyOk s.mem L key → Kept L s.mem t.mem → Regs t L key sig → ScrL t L →
      Keep ckRegs s t → WP isa fail t Q) :
    WP isa (Sign.checkSignKey rest fail) s Q := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hbuf := hL.buf_end
  obtain hqZ : L.qOff ≤ L.Z := by have := hbuf; simp only [Lay.bOff] at this; omega_using [this]
  obtain e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  obtain e0 := e 0; have e4 := e 4; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold Sign.checkSignKey
  refine checkParams_ok hL hs hr hlen hd (hk.take (by omega_using [])) (fun t hP hc hb kc => ?_)
    (fun t hn hb hrt hst kc => hfail t (fun hK => hn hK.1) hb hrt hst (keepPre (keepPre kc)))
  have hpo : pOf s.mem L key % 2 = 1 := hP.1.2.2
  obtain hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hP.1.1).1
  unfold andThen
  refine WP.seq (WP.seq (WP.mono (ptrY_ok hc.scr hL hc.regs) fun t₇ ⟨⟨b7, b8, m₇⟩, k₇⟩ => ?_))
  obtain k₀₇ := kc.trans k₇
  obtain hk₇ := hk.keep k₀₇.2.1 k₀₇.2.2
  obtain C₇ : Checked s t₇ L key sig d := hc.elem hL k₇ (by decide) (k₇.gpr (by decide)) (hc.inp.keep k₇)
    (by rw [m₇]; exact Outside.refl _ _ _ _)
  obtain he := hk₇.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega_using [])
  have en := C₇.inp.env
  refine WP.seq (WP.mono (loadArr_ok en (j := 4) (N := off key (2 * L.pl + L.ql)) (by decide)
      (by rw [b7]; exact (BitVec.add_zero _).symm) b8 (by omega_using [hw, hw8]) (by omega_using [hw8]) he.rd
      (fun i hi x hx => he.sep i hi x (Nat.lt_of_lt_of_le hx hqZ)))
    fun s₁ ⟨⟨v4, top4, o1, a7⟩, k1⟩ => ?_)
  obtain e1' : Env s₁ L.S L.qOff L.wp :=
    ⟨en.hs.congr k1.2.2, a7, (k1.gpr (by decide)).trans en.s5, (k1.gpr (by decide)).trans en.t0, en.w2, en.w48,
      en.hZ⟩
  obtain A0 : wordsVal s₁.mem L.S (slot L.wp 0) L.wp = pOf s.mem L key := by
    rw [o1.wordsVal (by omega_using [e0, e4]) (by omega_arith)]; exact C₇.p0
  refine WP.mono (elemRange_ok e1' top4) fun t₈ ⟨⟨r0, _, o2, e2⟩, k2⟩ => ?_
  obtain K₇ : Kept L s.mem t₇.mem := by rw [m₇]; exact hb
  obtain ey : Spec.Rsa.os2ip (Spec.Rsa.bytesAt t₇.mem (off key (2 * L.pl + L.ql)) L.pl) = yOf s.mem L key :=
    y_kept hk K₇
  rw [v4, A0, ey] at r0
  obtain o12 := p_elem2 o1 o2
  obtain k12 := k1.trans k2
  obtain ip₈ : InP t₈ L := ⟨e2, (k12.gpr (by decide)).trans C₇.inp.s6⟩
  obtain C₈ : Checked s t₈ L key sig d := C₇.elem hL k12 (by decide) (k12.gpr (by decide)) ip₈ o12
  obtain K₈ := K₇.trans (Kept.ofBody hL (p_arrays_body hL o12))
  obtain k₀₈ : Keep ckRegs s t₈ := (k₀₇.trans k12).mono fun r h => by
    simp only [ckRegs, elemRegs, List.mem_append] at h ⊢
    rcases h with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb₈ => ?_) (fun hb₈ => hfail t₈ (fun hK => by
      rw [r0.mpr hK.2] at hb₈
      exact absurd hb₈ (by decide)) K₈ C₈.regs C₈.scr k₀₈)
  exact hrest t₈ ⟨hP, r0.mp (beq_iff_eq.mp hb₈)⟩ C₈ K₈ k₀₈

/-- The registers `Sign.zeroOut` writes. -/
def szeroRegs : List Reg := [.t4, .t5, .s0] ++ zeroLoopRegs ++ [.a0]

/-- `zeroOut`: `out`'s `2 q_len` octets (`out` from the header's `Sign.hOut`)
:= 0, and `a0 := 0`. -/
theorem szero_ok {s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key x)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64) :
    WP isa Sign.zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) = List.replicate (2 * L.ql) 0 ∧
        Outside out 0 (2 * L.ql) s.mem t.mem ∧ t.gpr .a0 = 0) ∧ Keep szeroRegs s t := by
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain ⟨hin24, hal24⟩ := ScrL.hdr hs hL (d := 24) (by decide) (by decide)
  unfold Sign.zeroOut
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = out ∧ u.mem = s.mem)
    (by brun [Sign.hOut, hr.s6, hin24, hal24]; exact hw) (by decide) (by rfl)) fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun v ⟨⟨b5, mv⟩, kv⟩ => ?_
  refine WP.mono (WP.keep [.t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (2 * L.ql) ∧
      u.gpr .s0 = 0 ∧ u.mem = v.mem)
    (by
      brun [b5, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, a0, m1'⟩, k1'⟩ => ?_
  obtain k1 := (ku.trans kv).trans k1'
  obtain m1 : s₁.mem = s.mem := by rw [m1', mv, mu]
  obtain a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans k1') |>.gpr (by decide)]; exact a4
  refine WP.seq (WP.mono (zeroLoop_ok (N := 2 * L.ql) (by omega_using [hql]) (by omega_using [hql])
      (fun i hi => by rw [k1.2.2]; exact hout i hi) hno a0 a4₁ a5)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl))
    fun u ⟨⟨u0, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m1]; exact tout, u0⟩,
      ((k1.trans tk).trans ku).mono (by decide)⟩

theorem sign_correct (s : State) (h : sContract.pre s) :
    ∃ tr t, Exec isa Sign.sign s tr t ∧ abiPreserved s t ∧ sContract.post s t := by
  show WP isa Sign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  suffices main : WP isa Sign.sign s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ sContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  obtain hL := slayOf_ok h
  have hZ := hL.z256
  have hnwS := hL.nowrap
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -, -, -⟩ := h
  obtain mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hnw, hk, hi])⟩, fun i hi => Pub.ne_of_disjoint hd (by omega_using [hnw]) i (by omega_using [hk, hi])⟩
  have h1 : (s.gpr .a1).toNat = 2 * (slayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  obtain srcK := mkSrc (A := s.gpr .a2) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .a3).isLt (by omega_using [h3])
  obtain srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      Src t (slayOf s) (s.gpr .a2) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega_using [])
  obtain srcN := mkSrc (A := s.gpr .a5) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .a6).isLt (Nat.le_refl _)
  obtain srcD := mkSrc (A := s.gpr .a7) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  obtain srcO := mkSrc (A := s.gpr .a0) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .a1).isLt (by omega_using [h1])
  obtain hno : (s.gpr .a0).toNat + 2 * (slayOf s).ql ≤ 2 ^ 64 := by rw [← h1]; exact nwO
  obtain hout : ∀ t : State, t.wr = s.wr → ∀ i < 2 * (slayOf s).ql, InRegions t.wr (off (s.gpr .a0) i) 1 :=
    fun t ht i hi => ⟨_, by rw [ht, hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega_using [h1, hi]) (by omega_using [h1, hi])⟩
  -- A change in `out` keeps `scratch`'s header.
  obtain outSep : ∀ {m m' : Mem}, Outside (s.gpr .a0) 0 (2 * (slayOf s).ql) m m' →
      ∀ {d : Nat}, d + 8 ≤ 256 → word m' (slayOf s).S d = word m (slayOf s).S d := fun ho d hd =>
    in_word (out_in (o := 0) (N := 2 * (slayOf s).ql)
      (by simpa only [off, BitVec.add_zero] using ho) (by omega_using []) (by omega_using [h1]) (srcO s rfl rfl).sep)
      (by omega_using [hZ, hd]) (by omega_using [hnwS])
  -- The specification's values.
  obtain hkey : Spec.Dsa.privateKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .a2), qOf s.mem (slayOf s) (s.gpr .a2), gOf s.mem (slayOf s) (s.gpr .a2)⟩,
        yOf s.mem (slayOf s) (s.gpr .a2), some (xOf s.mem (slayOf s) (s.gpr .a2))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega_using [hkl]),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a2) (by simp only [slayOf] at h3; omega_using [hkl])]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
            (gOf s.mem (slayOf s) (s.gpr .a2)) (yOf s.mem (slayOf s) (s.gpr .a2))
            (xOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .a2))
              (qOf s.mem (slayOf s) (s.gpr .a2)) (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .a2)) (xOf s.mem (slayOf s) (s.gpr .a2))
              (kOf s.mem (slayOf s) (s.gpr .a5))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
                (gOf s.mem (slayOf s) (s.gpr .a2)) (kOf s.mem (slayOf s) (s.gpr .a5)))))
        else none := fun {n} hs hq8 => by
    obtain hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .a5))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h3) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  unfold Sign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  obtain hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 13, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
  obtain hal' : ∀ i < 13, (off (savW (stackArg s 1)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact F.scr.al8 (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega_using [])
  obtain hsav' : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (stackArg s 1) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega_using [], by simp only [saveOff]; omega_using [hi]⟩)).trans (F.sav i hi)
  obtain hwo : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S Sign.hOut = s.gpr .a0 :=
    fun u hu => (hu.word (Or.inr ⟨by simp only [Sign.hOut, hLens]; omega_using [], by simp only [Sign.hOut]; omega_using []⟩)).trans F.outw
  obtain hwd : ∀ u : State, Kept (slayOf s) s₁.mem u.mem → word u.mem (slayOf s).S hDigest = s.gpr .a7 :=
    fun u hu => (hu.word (Or.inl (by simp only [hDigest, hLens]; omega_using []))).trans F.dig
  obtain Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega_using [hZ])
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept (srcK3 s rfl rfl) Out₁
  obtain hKs : SignKeyOk s₁.mem (slayOf s) (s.gpr .a2) ↔ SignKeyOk s.mem (slayOf s) (s.gpr .a2) := by
    simp only [SignKeyOk, ParamsOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (checkSignKey_ok hL F.scr F.regs F.lens (by omega_using []) (srcK3 s₁ k₁.2.1 k₁.2.2)
    (fun t hK hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    obtain hKt := hKs.mp hK
    obtain Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
    obtain hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) =
        8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) := by
      have := hKt.1.1.1; unfold Spec.Dsa.supportedSizes at this; omega_using [this]
    refine WP.mono (sbody_ok hL hK.1 hc Kd (srcK t kt.2.1 kt.2.2) (srcN t kt.2.1 kt.2.2) (by omega_using [])
      ((srcD t kt.2.1 kt.2.2).take (Nat.min_le_left _ _)) (hwd t Kd) (hwo t Kd) (hout t kt.2.2) hno
      (srcO t kt.2.1 kt.2.2)) fun u ⟨⟨ob, r0u, ⟨m, Km, Om⟩, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h6u (hwr' u scru) hal'
      (fun i hi => (outSep Om (by simp only [saveOff]; omega_using [hi])).trans
        ((Km.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])).trans (hsav' t Kd i hi))))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    obtain ex : xOf t.mem (slayOf s) (s.gpr .a2) = xOf s.mem (slayOf s) (s.gpr .a2) := by
      simp only [xOf]
      rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega_using [])).bytes Ot
        (by omega_using [])]
    obtain ek : kOf t.mem (slayOf s) (s.gpr .a5) = kOf s.mem (slayOf s) (s.gpr .a5) := by
      simp only [kOf]; rw [(srcN s rfl rfl).bytes Ot (by omega_using [])]
    rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r0u
    obtain ed : Spec.Rsa.bytesAt t.mem (s.gpr .a7)
        (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) =
        Spec.Rsa.bytesAt s.mem (s.gpr .a7)
          (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8)) := by
      have := hKt.1.1.1; unfold Spec.Dsa.supportedSizes at this
      rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) =
        min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) by omega_using [this]]
      exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).bytes Ot (by omega_using [])
    rw [ed] at ob r0u
    obtain hres := hspec hKt.1.1 hq8
    simp only [signChecks_iff hKt.1.2.1 hKt.1.2.2.1 hKt.1.2.2.2 hKt.2] at hres
    refine ⟨?_, ?_⟩
    · rw [w0, r0u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h1, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    refine WP.mono (szero_ok hL scrt hrt (hwo t Kd) (hout t kt.2.2) hno) fun u ⟨⟨ub, uo, u0⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2)) hal'
      (fun i hi => (outSep uo (by simp only [saveOff]; omega_using [hi])).trans (hsav' t Kd i hi)))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    obtain hn' : ¬ SignKeyOk s.mem (slayOf s) (s.gpr .a2) := fun hx => hn (hKs.mpr hx)
    obtain hres : sRes s = none := by
      by_cases hs : VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .a2)) (qOf s.mem (slayOf s) (s.gpr .a2))
      · have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) =
            8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .a2)) / 8) := by
          have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega_using [this]
        rw [hspec hs hq8]
        split
        · rename_i hx
          exact absurd ⟨⟨hs, hx.1.1.1, hx.1.2.1, hx.1.2.2.1⟩, hx.1.1.2⟩ hn'
        · rfl
      · exact VG.Proof.Dsa.signBytes_invalid_shape (by rw [hkey]; exact hs)
    refine ⟨?_, ?_⟩
    · rw [w0, u0, hres]; rfl
    · rw [wm, h1, ub, hres]; rfl

end VG.Proof.Dsa.RISCV64
