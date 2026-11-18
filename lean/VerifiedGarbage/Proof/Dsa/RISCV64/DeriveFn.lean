module

public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower

/-! ### `Dsa.RISCV64.DeriveBody`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.DeriveOutput`, which this module and modules that import it used -/

section

/-!
# DSA key derivation on RISC-V: the output

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Output.lean`). `doutput_ok`: the
domain's `2 p_len + q_len` octets, the buffer's first `p_len` octets (y) and
x's `q_len` octets, each and'ed with the mask in `a4`, to `out` (the
header's `Sign.hOut`), and `a0 :=` the mask's low bit. Memory changes only
in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, off, BitVec.add_assoc, BitVec.ofNat_add]

/-- Octets apart from a changed range are kept. -/
theorem bytes_kept {m m' : Mem} {D O : Addr} {k n : Nat} (h : Outside O 0 n m m')
    (hsep : ∀ i < k, ∀ y, ofs O y < n → off D i ≠ y) :
    Spec.Rsa.bytesAt m' D k = Spec.Rsa.bytesAt m D k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  obtain hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

/-- A part of a range, unchanged by a change apart from it. -/
theorem part_kept {m m' : Mem} {O : Addr} {o n a k : Nat} (h : Outside O o n m m') (hd : a + k ≤ o ∨ o + n ≤ a)
    (hw : a + k < 2 ^ 64) : Spec.Rsa.bytesAt m' (off O a) k = Spec.Rsa.bytesAt m (off O a) k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  obtain hi := List.mem_range.mp hi
  rw [show off O a + BitVec.ofNat 64 i = off O (a + i) from off_off O a i, ofs_off0 _ (by omega_using [hw, hi])]
  omega_using [hd, hi]

/-- A separation from a whole range is one from a part of it. -/
theorem sep_part {D O : Addr} {k n a b : Nat} (hab : a + b ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ i < k, ∀ y, ofs O y < n → off D i ≠ y) : ∀ i < k, ∀ y, ofs (off O a) y < b → off D i ≠ y :=
  fun i hi y hy => h i hi y (by
    have := (Offset.lt_iff y O (d := a) (n := b) (by omega_using [hab, hn])).mp hy
    simp only [ofs]; omega_using [hab, this])

theorem off_toNat {O : Addr} {a : Nat} (h : O.toNat + a < 2 ^ 64) : (off O a).toNat = O.toNat + a := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_using [h])]
  exact Nat.mod_eq_of_lt h

/-- A change in a part of `out`, apart from `scratch`, keeps `scratch`. -/
theorem out_in {m m' : Mem} {out S : Addr} {o n N Z : Nat} (h : Outside (off out o) 0 n m m') (hon : o + n ≤ N)
    (hN : N < 2 ^ 64) (hsep : ∀ i < N, ∀ x, ofs S x < Z → off out i ≠ x) :
    ∀ x, ofs S x < Z → m' x = m x := by
  intro x hx
  refine h x (Or.inr ?_)
  by_contra hc
  have := (Offset.lt_iff x out (d := o) (n := n) (by omega_using [hon, hN])).mp (by simp only [ofs, off] at hc ⊢; omega_using [hc])
  exact hsep (ofs out x) (by simp only [ofs] at this ⊢; omega_using [hon, this]) x hx (off_ofs _ _)

theorem in_word {m m' : Mem} {S : Addr} {Z d : Nat} (h : ∀ x, ofs S x < Z → m' x = m x) (hd : d + 8 ≤ Z)
    (hZ : Z ≤ 2 ^ 64) : word m' S d = word m S d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off S (by omega_using [hd, hZ, hi])]; omega_using [hd, hi])).symm).symm

/-- `Regs` through a change that keeps `scratch`. -/
theorem Regs.ofIn {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (hL : L.Ok) (h : Regs s L key sig)
    (k : Keep rs s t) (hin : ∀ x, ofs L.S x < L.Z → t.mem x = s.mem x)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra,
    by rw [in_word hin (by have := hL.z256; simp only [hLens]; omega_using [this]) (by have := hL.nowrap; omega_using [this])]; exact h.pl,
    by rw [in_word hin (by have := hL.z256; simp only [hLens]; omega_using [this]) (by have := hL.nowrap; omega_using [this])]; exact h.ql⟩

/-- The registers `output` writes. -/
def doutputRegs : List Reg := [.t2, .t3, .t4, .t5, .s0, .a0]

theorem doutput_ok {s : State} {L : Lay} {key x out : Addr} {c : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x) (h4 : s.gpr .a4 = mask c) (hw : word s.mem L.S Sign.hOut = out)
    (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (hout : ∀ i < 3 * L.pl + 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + (3 * L.pl + 2 * L.ql) ≤ 2 ^ 64) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa output s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) = (if c then Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) ++
            Spec.Rsa.bytesAt s.mem L.Buf L.pl ++ Spec.Rsa.bytesAt s.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        Outside out 0 (3 * L.pl + 2 * L.ql) s.mem t.mem ∧ t.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0)) ∧
        Keep doutputRegs s t := by
  have hZ := hL.z256
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega_using [e]
  have hbe := hL.buf_end
  have hnw := hL.nowrap
  obtain hT : 3 * L.pl + 2 * L.ql < 2 ^ 64 := by omega_using [hql, hpl]
  -- The buffer is apart from `out`.
  obtain hbo : ∀ i < L.pl, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off L.Buf i ≠ y := by
    intro i hi y hy he
    subst he
    refine hos.sep (ofs out (off L.Buf i)) hy (off L.Buf i) ?_ (off_ofs _ _)
    rw [(bufAt hL (d := i) (by omega_using [hi])).2]
    simp only [Lay.bOff] at hbe ⊢; omega_using [hbe, hi]
  unfold output
  -- `out`, the domain and its length.
  obtain ⟨hin24, hal24⟩ := ScrL.hdr hs hL (d := 24) (by decide) (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4, .t3] (Q := fun u => u.gpr .t4 = out ∧ u.gpr .t3 = key ∧ u.mem = s.mem)
    (by brun [Sign.hOut, hr.s6, hr.s11, hin24, hal24, BitVec.add_zero]; exact hw) (by decide) (by rfl))
    fun u ⟨⟨a4', a3, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun v ⟨⟨b5, mv⟩, kv⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (ku.trans kv).2.2) hL ((hr.keepM ku mu).keepM kv mv) .t2)
    fun w ⟨⟨b2, mw⟩, kw⟩ => ?_
  refine WP.mono (WP.keep [.t5] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (2 * L.pl + L.ql) ∧ u.mem = w.mem)
    (by
      brun [kw.gpr (r := .t5) (by decide), b5, b2]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, m1'⟩, k1'⟩ => ?_
  obtain k1 := ((ku.trans kv).trans kw).trans k1'
  obtain m1 : s₁.mem = s.mem := by rw [m1', mw, mv, mu]
  obtain a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a4'
  obtain a3₁ : s₁.gpr .t3 = key := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a3
  obtain N1 : 0 < 2 * L.pl + L.ql := by omega_using [hql]
  refine WP.seq (WP.mono (maskCopy_ok (c := c) N1 (by omega_using [hno])
      (fun i hi => by rw [k1.2.2]; exact hout i (by omega_using [hi])) (by omega_using [hno])
      (fun i hi => by rw [k1.2.1, k1.2.2]; exact hk.rd i hi)
      (fun i hi y hy => hko i hi y (by omega_using [hy])) a3₁ a4₁ a5 ((k1.gpr (by decide)).trans h4))
    fun s₂ ⟨⟨v2, o2, _, b4⟩, k2⟩ => ?_)
  rw [m1] at v2 o2
  -- The buffer and `p_len`.
  obtain k12 := k1.trans k2
  obtain in2 : ∀ y, ofs L.S y < L.Z → s₂.mem y = s.mem y :=
    out_in (o := 0) (N := 3 * L.pl + 2 * L.ql) (by simpa only [off, BitVec.add_zero] using o2) (by omega_using []) hT hos.sep
  obtain hr2 : Regs s₂ L key x := Regs.ofIn hL hr k12 in2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bufBase_ok (hs.congr k12.2.2) hL hr2 (rd := .t3) (t := .t2) (by decide) (by decide)
    (by decide)) fun s₃ ⟨⟨c3, m3⟩, k3⟩ => ?_
  refine WP.mono (getP_ok (hs.congr (k12.trans k3).2.2) hL (hr2.keepM k3 m3) .t5) fun s₄ ⟨⟨c5, m4⟩, k4⟩ => ?_
  obtain k34 := k3.trans k4
  obtain hm4 : s₄.mem = s₂.mem := by rw [m4, m3]
  obtain k14 := k12.trans k34
  obtain hoa : (off out (2 * L.pl + L.ql)).toNat = out.toNat + (2 * L.pl + L.ql) := off_toNat (by omega_using [hno])
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.pl) (by omega_using [hpl]) (by omega_using [hno])
      (fun i hi => by rw [k14.2.2, off_off]; exact hout _ (by omega_using [hi])) (by omega_using [hno, hoa])
      (by have := bufRd hL (hs.congr k14.2.2) (o := 0) (k := L.pl) (by omega_using [])
          simpa only [off, BitVec.add_zero] using this)
      (sep_part (by omega_using []) hT hbo) ((k4.gpr (by decide)).trans c3)
      ((k34.gpr (by decide)).trans b4) c5 ((k14.gpr (by decide)).trans h4))
    fun s₅ ⟨⟨v5, o5, _, d4⟩, k5⟩ => ?_)
  rw [hm4] at v5 o5
  -- x and `q_len`.
  obtain k15 := k14.trans k5
  obtain in5 : ∀ y, ofs L.S y < L.Z → s₅.mem y = s.mem y := fun y hy =>
    (out_in (o := 2 * L.pl + L.ql) (N := 3 * L.pl + 2 * L.ql) o5 (by omega_using []) hT hos.sep y hy).trans (in2 y hy)
  obtain hr5 : Regs s₅ L key x := Regs.ofIn hL hr k15 in5
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = x ∧ u.mem = s₅.mem)
    (by brun [hr5.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₆ ⟨⟨e3, m6⟩, k6⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (k15.trans k6).2.2) hL (hr5.keepM k6 m6) .t5) fun s₇ ⟨⟨e5, m7⟩, k7⟩ => ?_
  obtain k17 := (k15.trans k6).trans k7
  obtain hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
  obtain hob : (off out (3 * L.pl + L.ql)).toNat = out.toNat + (3 * L.pl + L.ql) := off_toNat (by omega_using [hno, hql])
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.ql) (src := x) (dst := off out (3 * L.pl + L.ql)) (by omega_using [hql]) (by omega_using [hno])
      (fun i hi => by rw [k17.2.2, off_off]; exact hout _ (by omega_using [hi])) (by omega_using [hno, hob])
      (fun i hi => by rw [k17.2.1, k17.2.2]; exact hx.rd i hi)
      (sep_part (by omega_using []) hT hxo) ((k7.gpr (by decide)).trans e3)
      (by rw [(k6.trans k7).gpr (by decide), d4, off_off, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega_using []]) e5
      ((k17.gpr (by decide)).trans h4))
    fun s₈ ⟨⟨v8, o8, _, _⟩, k8⟩ => ?_)
  rw [hm7] at v8 o8
  -- `a0 :=` the mask's low bit.
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₈.mem) (by brun [(k17.trans k8).gpr (r := .a4) (by decide), h4, mask_low]) (by decide) (by rfl))
    fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  obtain kall := (k17.trans k8).trans kt
  rw [mt]
  -- The frames, relative to `out`.
  obtain o5' : Outside out (2 * L.pl + L.ql) L.pl s₂.mem s₅.mem := by
    have := outside_shift (B := out) (a := 2 * L.pl + L.ql) o5 (by omega_using [hno]) (by omega_using [hno])
    rwa [Nat.add_zero] at this
  obtain o8' : Outside out (3 * L.pl + L.ql) L.ql s₅.mem s₈.mem := by
    have := outside_shift (B := out) (a := 3 * L.pl + L.ql) o8 (by omega_using [hno]) (by omega_using [hno])
    rwa [Nat.add_zero] at this
  -- The sources, unchanged.
  obtain eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s.mem L.Buf L.pl :=
    bytes_kept o2 fun i hi y hy => hbo i hi y (by omega_using [hy])
  obtain ex : Spec.Rsa.bytesAt s₅.mem x L.ql = Spec.Rsa.bytesAt s.mem x L.ql :=
    bytes_kept ((o2.mono (n' := 3 * L.pl + L.ql) (Nat.le_refl _) (by omega_using [])).trans
      (o5'.mono (Nat.zero_le _) (by omega_using []))) fun i hi y hy => hxo i hi y (by omega_using [hy])
  rw [eb] at v5
  rw [ex] at v8
  refine ⟨⟨?_, ((o2.mono (n' := 3 * L.pl + 2 * L.ql) (Nat.le_refl _) (by omega_using [])).trans
      (o5'.mono (Nat.zero_le _) (by omega_using []))).trans (o8'.mono (Nat.zero_le _) (by omega_using [])), t0⟩,
    kall.mono (by decide)⟩
  -- The three parts of `out`.
  rw [show 3 * L.pl + 2 * L.ql = 2 * L.pl + L.ql + L.pl + L.ql by omega_using [], bytesAt_add, bytesAt_add]
  obtain p1 : Spec.Rsa.bytesAt s₈.mem out (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₂.mem out (2 * L.pl + L.ql) := by
    obtain e1 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o8' (Or.inl (by omega_using [])) (by omega_using [hno])
    obtain e2 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o5' (Or.inl (by omega_using [])) (by omega_using [hno])
    simp only [off, BitVec.add_zero] at e1 e2
    rw [e1, e2]
  obtain p2 : Spec.Rsa.bytesAt s₈.mem (off out (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s₅.mem (off out (2 * L.pl + L.ql)) L.pl :=
    part_kept o8' (Or.inl (by omega_using [])) (by omega_using [hno])
  rw [p1, p2, v2, v5, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega_using [], v8]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
    congr 1; omega_using []
  · simp only [↓reduceIte, List.append_assoc]

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.DeriveX`, which only this module used -/

section

/-!
# DSA key derivation on RISC-V: x's range

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/X.lean`). `xRange_ok`: into the Q
space, x (the `q_len` octets at `ra`) into array 5, and `a4 &=` the mask of
`0 < x < q`, q in array 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The registers `xRange` writes. -/
def xRangeRegs : List Reg := enterRegs ++ [.s7, .s8] ++ loadRegs ++ [.s0, .t3, .t5] ++ inRangeRegs

/-- `xRange`: `a4 &=` the mask of `0 < x < q`. Memory changes only in the
Q space's arrays from array 1 on. -/
theorem xRange_ok {s : State} {L : Lay} {key x : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x) (hx : Src s L x L.ql) (h4 : s.gpr .a4 = mask b) :
    WP isa xRange s fun t =>
      (t.gpr .a4 = mask (b && decide (0 < kOf s.mem L x ∧ kOf s.mem L x < arrQ s.mem L 0)) ∧
        QS t L key x ∧ QArr L s.mem t.mem) ∧ Keep xRangeRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8; have e28 := e 28
  unfold xRange
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have Q1 : QS s₁ L key x := ⟨q1, hs.congr k1.2.2, hr.keepM k1 m1⟩
  refine WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_
  have Q2 := Q1.stepM k2 m2
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (hx.keep k12.2.1 k12.2.2) a7 a8
      (by omega_using [hql]) (by omega_using [hwq])) fun s₃ ⟨⟨Q3, v5, top5, o3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q3.inq.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega_using [hwq, e7]))
  have k14 := (k12.trans k3).trans k4
  have e5' : wordsVal s₄.mem L.Q (slot L.wq 5) L.wq = kOf s.mem L x := by
    rw [o4.wordsVal (by omega_using [e5, e7]) (by omega_arith)]
    refine v5.trans ?_
    rw [m21]; rfl
  have e0' : wordsVal s₄.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [o4.wordsVal (by omega_using [e0, e7]) (by omega_arith), o3.wordsVal (by omega_using [e0, e5]) (by omega_arith), m21]
  have top5' : word s₄.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by
    rw [o4.word (by omega_using [e5, e7]) (by omega_arith)]; exact top5
  refine WP.mono (inRange_ok Q4.inq.env (a := 5) (b := b) (by decide) (by decide) (by decide)
    top5' z7 ((k14.gpr (by decide)).trans h4)) fun t ⟨⟨c4, o5⟩, k5⟩ => ?_
  rw [e5', e0'] at c4
  have qa : QArr L s.mem t.mem := by
    have qa1 : QArr L s₂.mem s₃.mem := QArr.of o3 (by omega_using [e1, e5]) (by omega_using [e5, e28])
    have qa2 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega_using [e1, e7]) (by omega_using [e7, e28])
    have qa3 : QArr L s₄.mem t.mem := QArr.of o5 (by omega_using [e1, e3]) (by omega_using [e3, e28])
    rw [← m21]; exact (qa1.trans qa2).trans qa3
  exact ⟨⟨c4, Q4.step k5 (Body.ofQ hL o5 (by omega_using [hwq, e3])), qa⟩, (k14.trans k5).mono (by decide)⟩

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.DeriveY`, which only this module used -/

section

/-!
# DSA key derivation on RISC-V: y

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Y.lean`). `yValue_ok`: in the P
space with p in array 0 and `R² mod p` in array 24, `y = g^x mod p` (x the
`q_len` octets at `ra`) to the buffer's first `p_len` octets, and `a4 :=`
the mask of `y ≠ 0` and `y ≠ 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The registers `yValue` writes. -/
def yValueRegs : List Reg :=
  [.s9] ++ ptrRegs ++ powPRegs ++ [.s0, .t3, .t5] ++ [.a4] ++ nonZeroRegs ++ [.s0, .t3, .t5] ++ nonZeroRegs ++
    [.s7, .t2] ++ [.s8] ++ storeRegs

theorem yv_b1 (L : Lay) : 256 ≤ slot L.wp 1 ∧ slot L.wp 1 + 23 * (8 * (L.wp + 2)) ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega_using []

theorem yv_b7 (L : Lay) : 256 ≤ slot L.wp 7 ∧ slot L.wp 7 + 8 * L.wp ≤ L.qOff ∧ slot L.wp 8 ≤ L.qOff := by
  simp only [Lay.qOff, Lay.slot_eq]; omega_using []

/-- `yValue`: `y = g^x mod p` to the buffer's first `p_len` octets, and
`a4 :=` the mask of `y ≠ 0` and `y ≠ 1`. Memory changes only in the P
space's arrays and the buffer's first `p_len` octets. -/
theorem yValue_ok {s : State} {L : Lay} {key x : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (2 * L.pl + L.ql))
    (hx : Src s L x L.ql) (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa yValue s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L x % p ∧
        t.gpr .a4 = mask (decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 0) &&
          decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 1)) ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧
        Keep yValueRegs s t := by
  obtain hpb : L.pl ≤ 2 ^ 64 - 1600 := by rcases hL.pl with e | e | e <;> rw [e] <;> decide
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hpl := hL.pl
  have hbe := hL.buf_end
  obtain e : ∀ j, slot L.wp j = 256 + j * (8 * (L.wp + 2)) := fun _ => rfl
  obtain e1 := e 1; have e4 := e 4; have e7 := e 7; have e24 := e 24; have e28 := e 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold yValue
  -- The pointers: x into `s9`, g's octets into `s7`.
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = x ∧ u.mem = s.mem)
    (by brun [hr.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ =>
    WP.mono (ptrG_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨b7, _, m2⟩, k2⟩ => ?_))
  obtain k12 := k1.trans k2
  obtain hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := x) (p := p) hL (hs.congr k12.2.2)
      (hr.keepM k12 hm2) (hin.keep k12) (by
        show ((word s₂.mem L.S (slot L.wp 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [hm2, k12.gpr (by decide)]; exact hi)
      ((hk.keep k12.2.1 k12.2.2).sub (o := L.pl + L.ql) (k := L.pl) (by omega_using [])) b7 (hx.keep k12.2.1 k12.2.2)
      ((k2.gpr (by decide)).trans a9) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, _, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  obtain k13 := k12.trans k3
  have y4 : arrP s₃.mem L 4 = gOf s.mem L key ^ kOf s.mem L x % p := v4
  obtain hyp : gOf s.mem L key ^ kOf s.mem L x % p < p := Nat.mod_lt _ (by omega_using [hp])
  generalize gOf s.mem L key ^ kOf s.mem L x % p = y at y4 hyp ⊢
  -- 0 into array 7, `a4 :=` all ones.
  refine WP.seq (WP.mono (zeroArr_ok in3.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  obtain en4 := in3.env.keep k4
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask true ∧ u.mem = s₄.mem)
    (by brun [exec_li (show imm12 (-1) by decide)]; rfl) (by decide) (by rfl)) fun s₅ ⟨⟨a4, m5⟩, k5⟩ => ?_)
  obtain en5 := en4.keep k5
  obtain y5 : arrP s₅.mem L 4 = y := by
    rw [arrP, m5, o4.wordsVal (by omega_using [e4, e7]) (by omega_arith)]; exact y4
  -- `a4 &=` the masks of `y ≠ 0` and `y ≠ 1`.
  refine WP.seq (WP.mono (nonZero_ok en5 (a := 4) (c := 0) (by decide) (by rw [m5]; exact z7) a4)
    fun s₆ ⟨⟨b4, m6⟩, k6⟩ => ?_)
  rw [show wordsVal s₅.mem L.S (slot L.wp 4) L.wp = y from y5] at b4
  obtain en6 := en5.keep k6
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega_using [hw]) (by omega_using [hw]) (yv_b7 L).2.2 en6.a7 en6.s5 en6.t0)
    fun s₇ ⟨⟨v7, o7'⟩, k7⟩ => ?_)
  have o7 : Outside L.S (slot L.wp 7) (8 * L.wp) s₆.mem s₇.mem := o7'
  obtain en7 := en6.keep k7
  obtain y7 : arrP s₇.mem L 4 = y := by
    rw [arrP, o7.wordsVal (by omega_using [e4, e7]) (by omega_arith), m6]; exact y5
  refine WP.seq (WP.mono (nonZero_ok en7 (a := 4) (c := 1) (by decide) v7
    ((k7.gpr (by decide)).trans b4)) fun s₈ ⟨⟨c4, m8⟩, k8⟩ => ?_)
  rw [show wordsVal s₇.mem L.S (slot L.wp 4) L.wp = y from y7, Bool.true_and] at c4
  obtain en8 := en7.keep k8
  -- y to the buffer.
  obtain k18 := ((((k13.trans k4).trans k5).trans k6).trans k7).trans k8
  obtain hm6 : s₆.mem = s₄.mem := by rw [m6, m5]
  obtain o47 : Outside L.S (slot L.wp 7) (8 * L.wp) s₃.mem s₇.mem := by
    rw [← hm6] at o4; exact o4.trans o7
  obtain b18 : Body L s.mem s₈.mem := by
    rw [m8]
    exact (Body.ofP hL o3 (yv_b1 L).1 (yv_b1 L).2).trans (Body.ofP hL o47 (yv_b7 L).1 (yv_b7 L).2.1)
  obtain hr8 : Regs s₈ L key x := hr.keep k18 b18
  refine WP.seq (WP.block_append (WP.mono (bufBase_ok (hs.congr k18.2.2) hL hr8 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k18.trans ku).2.2) hL (hr8.keepM ku mu) .s8) fun s₉ ⟨⟨f8, m9⟩, k9⟩ => ?_))
  obtain hm9 : s₉.mem = s₇.mem := by rw [m9, mu, m8]
  obtain k19 := (k18.trans ku).trans k9
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (en8.keep (ku.trans k9)) (by decide)
    (by have := ScrL.bufSt (hs.congr k19.2.2) hL (o := 0) (k := L.pl) (by omega_using [])
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega_using []) (by omega_using [hpl]); simpa only [off, BitVec.add_zero] using this)
    ((k9.gpr (by decide)).trans f7) f8 (by omega_using [hpl]) (by omega_using [hw8]) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm9] at vt ot
  obtain hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega_using []]; exact wordsVal_lt _ _ _ _
  obtain kall := k19.trans kt
  refine ⟨⟨?_, (kt.gpr (by decide)).trans ((k9.gpr (by decide)).trans ((ku.gpr (by decide)).trans c4)),
    ⟨en8.keep ((ku.trans k9).trans kt), (kall.gpr (by decide)).trans hin.s6⟩,
    ((Body.ofP hL o3 (yv_b1 L).1 (yv_b1 L).2).trans (Body.ofP hL o47 (yv_b7 L).1 (yv_b7 L).2.1)).trans
      (Body.ofBuf hL ot (by omega_using [])),
    ((PBody.of o3 (yv_b1 L).1 (yv_b1 L).2).keepQ hL |>.trans ((PBody.of o47 (yv_b7 L).1 (yv_b7 L).2.1).keepQ hL)).trans
      (bufKeepQ ot hpb)⟩, by simp only [List.append_assoc] at kall; exact kall⟩
  rw [vt, read_low _ _ (w := L.wp) (by rw [hw8]) (by
    show arrP s₇.mem L 4 < 2 ^ (8 * L.pl); rw [y7]; exact Nat.lt_trans hyp hplt)]
  exact y7

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA key derivation on RISC-V: after the check of the domain

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Fn.lean`). `dbody_ok`:
`Derive.body` writes to `out` the domain's octets, then `y = g^x mod p`'s
`p_len` octets and x's `q_len` octets, and leaves 1 in `a0`, exactly when
`1 < y` and `0 < x < q`; else zeros and 0. Memory changes only in
`scratch` past its header and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The checks of derivation past the domain's, for `y = g^x mod p`. -/
def DeriveOk (p q g x : Nat) : Prop := 1 < g ^ x % p ∧ 0 < x ∧ x < q

instance (p q g x : Nat) : Decidable (DeriveOk p q g x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The registers `Derive.body` writes. -/
def dbodyRegs : List Reg := yValueRegs ++ xRangeRegs ++ doutputRegs

theorem dmask_eq (y k q : Nat) :
    (decide (y ≠ 0) && decide (y ≠ 1) && decide (0 < k ∧ k < q)) = decide (1 < y ∧ 0 < k ∧ k < q) := by
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1] <;> omega_using [h0, h1]

theorem dbody_ok {s₀ s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hP : ParamsOk s₀.mem L key)
    (hc : Checked s₀ s L key x 0) (hkp : Kept L s₀.mem s.mem) (hw : word s.mem L.S Sign.hOut = out)
    (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (hout : ∀ i < 3 * L.pl + 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + (3 * L.pl + 2 * L.ql) ≤ 2 ^ 64) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) =
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then
            Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) ++
              Spec.Dsa.encodeBE L.pl (gOf s₀.mem L key ^ kOf s₀.mem L x % pOf s₀.mem L key) ++
              Spec.Rsa.bytesAt s₀.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        t.gpr .a0 = BitVec.ofNat 64
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (3 * L.pl + 2 * L.ql) m t.mem) ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧
        Keep dbodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw8 := hL.wp_eq
  have hwq := hL.wq_ge
  obtain ⟨ip, scr, regs, p0, -, inv, p24, q0⟩ := hc
  obtain ⟨-, -, eg⟩ := params_kept hk hkp
  have ex : kOf s.mem L x = kOf s₀.mem L x := by simp only [kOf]; rw [hx.bytes hkp.out (by omega_using [])]
  have ekey : Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) :=
    hk.bytes hkp.out (by omega_using [])
  have exb : Spec.Rsa.bytesAt s.mem x L.ql = Spec.Rsa.bytesAt s₀.mem x L.ql := hx.bytes hkp.out (by omega_using [])
  have B := VG.Proof.Dsa.supported_bounds hP.1.1
  have hpo := hP.1.2.2
  have hplt : pOf s₀.mem L key < 256 ^ L.pl := by
    have := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s₀.mem key L.pl)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at p0 p24 B hpo hplt
  generalize qOf s₀.mem L key = q at q0 B
  generalize gOf s₀.mem L key = g at eg
  unfold body
  -- y.
  refine WP.seq (WP.mono (yValue_ok hL scr regs ip inv hk hx p0 (by omega_using [B]) hpo p24)
    fun s₁ ⟨⟨vy, my, ip1, b1, oq1⟩, k1⟩ => ?_)
  rw [eg, ex] at vy my
  generalize hy : g ^ kOf s₀.mem L x % p = y at vy my
  have hyp : y < p := by rw [← hy]; exact Nat.mod_lt _ (by omega_using [hpo])
  have hr1 := regs.keep k1 b1
  -- x's range.
  refine WP.seq (WP.mono (xRange_ok hL (scr.congr k1.2.2) hr1 (hx.keep k1.2.1 k1.2.2) my)
    fun s₂ ⟨⟨m2, Q2, qa2⟩, k2⟩ => ?_)
  have aq : arrQ s₁.mem L 0 = q := by
    rw [← q0]
    exact oq1.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega_using [hwq])) (by simp only [Lay.slot_eq]; omega_using [hwq])
  have ex1 : kOf s₁.mem L x = kOf s₀.mem L x := by
    rw [kOf, kOf, hx.bytes b1 (by omega_using [hZ]), exb]
  rw [aq, ex1] at m2
  -- The output.
  have b12 : Body L s.mem s₂.mem := b1.trans (qa2.body hL)
  have k12 := k1.trans k2
  refine WP.mono (doutput_ok hL Q2.scr Q2.regs m2 (by rw [b12.word (by decide)]; exact hw)
    (hk.keep k12.2.1 k12.2.2) (hx.keep k12.2.1 k12.2.2) (fun i hi => by rw [k12.2.2]; exact hout i hi) hno
    (hos.keep k12.2.1 k12.2.2) hko hxo) fun t ⟨⟨vt, ot, t0⟩, kt⟩ => ?_
  have hD : DeriveOk p q g (kOf s₀.mem L x) = (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    unfold DeriveOk; rw [hy]
  rw [dmask_eq] at vt t0
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Dsa.encodeBE L.pl y := by
    rw [qa2.bufBytes hL (by omega_using [hno])]
    exact ((VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) (by omega_using [hplt, hyp])).mpr vy.symm).symm
  have kall := k12.trans kt
  have K2 := Kept.ofBody hL b12
  rw [eb, hk.bytes K2.out (by omega_using []), hx.bytes K2.out (by omega_using []), ekey, exb] at vt
  simp only [decide_eq_true_eq] at vt t0
  simp only [hD]
  refine ⟨⟨vt, t0, ⟨s₂.mem, K2, ot⟩, (kall.gpr (by decide)).trans regs.s6, scr.congr kall.2.2⟩, ?_⟩
  simp only [dbodyRegs, List.append_assoc] at kall ⊢
  exact kall

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.DeriveFront`, which this module and modules that import it used -/

section

/-!
# DSA key derivation on RISC-V: the contract on the registers, and the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Front.lean`). `dContract`:
`vg_dsa_derive_key(out = a0, out_len = a1, params = a2, params_len = a3,
p_len = a4, x = a5, q_len = a6, scratch = a7, scratch_len)`, `scratch_len`
on the stack. `dfront_ok`: `entry` saves the callee-saved registers and
`ra` in `scratch`'s header, keeps the domain and x in `s11` and `ra`
(`Regs`, with x as the signature), and `out` and the lengths in the header
(`Sign.hOut`, `hLens`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- The argument on the stack: `scratch_len`. -/
abbrev dStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The key `deriveKeyBytes` gives, on entry. -/
def dRes (s : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)

/-- `vg_dsa_derive_key`, on the registers and the stack. -/
def dContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ps : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let xr : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
    s.rd = [ps, xr, dStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint ps ∧ out.Disjoint xr ∧ out.Disjoint scr ∧ out.Disjoint (dStackArgs s) ∧
      ps.Disjoint scr ∧ xr.Disjoint scr ∧ scr.Disjoint (dStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a4).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a4).toNat + 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat + (s.gpr .a6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 0).toNat ∧
      (s.gpr .a7).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (dRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat = (dRes s).getD (List.replicate (s.gpr .a1).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₁)] =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₂)]

/-- A call's layout. -/
def dlayOf (s : State) : Lay := ⟨s.gpr .a7, (stackArg s 0).toNat * 8, (s.gpr .a4).toNat, (s.gpr .a6).toNat⟩

theorem dlayOf_ok {s : State} (h : dContract.pre s) : (dlayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw, -, -⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [dlayOf]; omega_using [hv], by simp only [dlayOf]; omega_using [hv], by simp only [dlayOf]; omega_using [hsw], nw⟩

/-- The registers `Derive.entry` writes. -/
def dentryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3]

/-- What `Derive.entry` leaves. -/
structure DFront (s t : State) : Prop where
  regs : Regs t (dlayOf s) (s.gpr .a2) (s.gpr .a5)
  scr : ScrL t (dlayOf s)
  lens : word t.mem (s.gpr .a7) hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0
  outw : word t.mem (s.gpr .a7) Sign.hOut = s.gpr .a0
  sav : ∀ i < 13, word t.mem (s.gpr .a7) (saveOff i) = s.gpr (saved i)
  out : Outside (s.gpr .a7) 0 256 s.mem t.mem

/-- `entry`: `scratch` into `s6`, the callee-saved registers and `ra` saved in
its header, the domain and x into `s11` and `ra`, and `out` and the lengths
into the header. Memory changes only in the header. -/
theorem dfront_ok {s : State} (h : dContract.pre s) :
    WP isa (.block Derive.entry) s fun t => DFront s t ∧ Keep dentryRegs s t := by
  obtain hL := dlayOf_ok h
  have hZ := hL.z256
  obtain hpl : (s.gpr .a4).toNat < 2 ^ 16 := by have := hL.pl; simp only [dlayOf] at this; omega_using [this]
  obtain hql : (s.gpr .a6).toNat < 2 ^ 16 := by have := hL.ql; simp only [dlayOf] at this; omega_using [this]
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, nw, -, -, -, -, alS, -⟩ := h
  obtain hscr : ∀ t : State, t.wr = s.wr → ScrL t (dlayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [dlayOf]) nw alS
  unfold Derive.entry
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = s.gpr .a7 ∧
    u.mem = s.mem) (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  obtain hs₁ := hscr s₁ k1.2.2
  obtain hin : ∀ i < 13, InRegions s₁.wr (off (savW (s.gpr .a7)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.st (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
  obtain hal : ∀ i < 13, (off (savW (s.gpr .a7)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.al8 (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
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
  obtain ⟨_, hal24⟩ := ScrL.hdr hs₂ hL (d := 24) (by decide) (by decide)
  obtain ⟨_, hal16⟩ := ScrL.hdr hs₂ hL (d := 16) (by decide) (by decide)
  have hal24' : (off (s.gpr .a7) 24).toNat % 8 = 0 := hal24
  have hal16' : (off (s.gpr .a7) 16).toNat % 8 = 0 := hal16
  obtain hst24 : InRegions s₂.wr (off (s.gpr .a7) 24) 8 := hs₂.st (d := 24) (by simp only [dlayOf] at hZ ⊢; omega_using [hZ])
  obtain hst16 : InRegions s₂.wr (off (s.gpr .a7) 16) 8 := hs₂.st (d := 16) (by simp only [dlayOf] at hZ ⊢; omega_using [hZ])
  obtain hpk := pack_entry0 (s.gpr .a4) (s.gpr .a6) hpl hql
  refine WP.mono (WP.keep [.s11, .ra, .t3] (Q := fun t =>
      t.mem = (s₂.mem.writeW (off (s.gpr .a7) 24) (s.gpr .a0)).writeW (off (s.gpr .a7) 16)
        (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 0) ∧
      t.gpr .s11 = s.gpr .a2 ∧ t.gpr .ra = s.gpr .a5) (by
        brun [hS₂.s6, e .a2 (by decide) (by decide), e .a0 (by decide) (by decide), e .a5 (by decide) (by decide),
          e .a4 (by decide) (by decide), e .a6 (by decide) (by decide), Sign.hOut, hLens, hst24, hal24', hst16,
          hal16', hpk, exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl))
    fun t ⟨⟨mt, t11, tra⟩, kt⟩ => ?_
  obtain k := k12.trans kt
  have hp16 : (dlayOf s).pl < 2 ^ 16 := hpl
  have hq16 : (dlayOf s).ql < 2 ^ 16 := hql
  obtain hnw : (s.gpr .a7).toNat + 256 ≤ 2 ^ 64 := by simp only [dlayOf] at hZ; omega_using [hZ, nw]
  obtain w16 := writeW_outside (s₂.mem.writeW (off (s.gpr .a7) 24) (s.gpr .a0)) (s.gpr .a7) (d := 16)
    (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 0) (by omega_using [])
  obtain w24 := writeW_outside s₂.mem (s.gpr .a7) (d := 24) (s.gpr .a0) (by omega_using [])
  obtain hlen : word t.mem (s.gpr .a7) hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 := by
    rw [mt]; exact word_writeW_self _ _ _ _
  have hlen' : word t.mem (dlayOf s).S hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 := hlen
  obtain f1 : Outside (s.gpr .a7) 128 104 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (base := s.gpr .a7) (d := 128) (len := 104) hS₂.frame (by omega_using [])
  refine ⟨⟨⟨(kt.gpr (by decide)).trans hS₂.s6, t11, tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) (by decide),
    by rw [hlen']; exact pack_ql hp16 hq16 (by decide) (by decide)⟩, hscr t k.2.2, hlen, ?_, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt, w16.word (by simp only [Sign.hOut]; omega_using []) (by simp only [Sign.hOut]; omega_using [])]
    exact word_writeW_self _ _ _ _
  · rw [mt, w16.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi]),
      w24.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])]
    show s₂.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (saveOff i)) 64 = _
    rw [saveOff_eq, hS₂.saved i hi]
    exact k1.gpr fun h => saved_ne_t2 i hi (List.mem_singleton.mp h)
  · rw [mt, ← m1]
    exact ((f1.mono (Nat.zero_le _) (by omega_using [])).trans (w24.mono (Nat.zero_le _) (by omega_using []))).trans
      (w16.mono (Nat.zero_le _) (by omega_using []))

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA key derivation on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Fn.lean`). `deriveKey_correct`:
`vg_dsa_derive_key` meets `dContract`. After `entry` (`dfront_ok`),
`checkParams` either runs `body` (`dbody_ok`) or `zeroOut` (`dzero_ok`), and
`restore` gives back the callee-saved registers (`sfinish_ok`); the result is
the specification's by `deriveKey_spec`, from `Proof/Dsa/Derive.lean`'s
`deriveKeyBytes_eq`. `deriveWith_ok` is this for any check of the domain
(`Prevalidated.setup` for a domain known to pass, `DeriveChecked.lean`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-- The registers `Derive.zeroOut` writes. -/
def dzeroRegs : List Reg := [.t4, .t5, .t2, .s0] ++ zeroLoopRegs ++ [.a0]

/-- `zeroOut`: `out`'s `3 p_len + 2 q_len` octets (`out` from the header's
`Sign.hOut`) := 0, and `a0 := 0`. -/
theorem dzero_ok {s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key x)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 3 * L.pl + 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + (3 * L.pl + 2 * L.ql) ≤ 2 ^ 64) :
    WP isa Derive.zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) = List.replicate (3 * L.pl + 2 * L.ql) 0 ∧
        Outside out 0 (3 * L.pl + 2 * L.ql) s.mem t.mem ∧ t.gpr .a0 = 0) ∧ Keep dzeroRegs s t := by
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega_using [e]
  obtain ⟨hin24, hal24⟩ := ScrL.hdr hs hL (d := 24) (by decide) (by decide)
  unfold Derive.zeroOut
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (Q := fun u => u.gpr .t4 = out ∧ u.mem = s.mem)
    (by brun [Sign.hOut, hr.s6, hin24, hal24]; exact hw) (by decide) (by rfl)) fun u ⟨⟨a4, mu⟩, ku⟩ => ?_
  refine WP.mono (getP_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .t5) fun v ⟨⟨b5, mv⟩, kv⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (ku.trans kv).2.2) hL ((hr.keepM ku mu).keepM kv mv) .t2)
    fun w ⟨⟨b2, mw⟩, kw⟩ => ?_
  refine WP.mono (WP.keep [.t2, .t5, .s0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 (3 * L.pl + 2 * L.ql) ∧
      u.gpr .s0 = 0 ∧ u.mem = w.mem)
    (by
      brun [kw.gpr (r := .t5) (by decide), b5, b2, exec_li_zero]
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega_using []) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, a0, m1'⟩, k1'⟩ => ?_
  obtain k1 := ((ku.trans kv).trans kw).trans k1'
  obtain m1 : s₁.mem = s.mem := by rw [m1', mw, mv, mu]
  obtain a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a4
  refine WP.seq (WP.mono (zeroLoop_ok (N := 3 * L.pl + 2 * L.ql) (by omega_using [hql]) (by omega_using [hql, hpl])
      (fun i hi => by rw [k1.2.2]; exact hout i hi) hno a0 a4₁ a5)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl))
    fun u ⟨⟨u0, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m1]; exact tout, u0⟩,
      ((k1.trans tk).trans ku).mono (by decide)⟩

/-- The specification's derivation, on the domain's and x's values. -/
theorem deriveKey_spec {m : Mem} {L : Lay} {key x : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.deriveKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)) (Spec.Rsa.bytesAt m x L.ql) =
      if ParamsOk m L key ∧ DeriveOk (pOf m L key) (qOf m L key) (gOf m L key) (kOf m L x) then
        some (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql) ++
          Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ Spec.Rsa.bytesAt m x L.ql)
      else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)
    (VG.Proof.Bignum.bytesAt_length _ _ _)]
  obtain ep : (Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).take L.pl = Spec.Rsa.bytesAt m key L.pl := by
    have := VG.Proof.Dsa.bytesAt_slice m key (offset := 0) (len := L.pl) (total := 2 * L.pl + L.ql) (by omega_using [])
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  obtain eq : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop L.pl).take L.ql =
      Spec.Rsa.bytesAt m (off key L.pl) L.ql :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega_using [])
  obtain eg : ((Spec.Rsa.bytesAt m key (2 * L.pl + L.ql)).drop (L.pl + L.ql)).take L.pl =
      Spec.Rsa.bytesAt m (off key (L.pl + L.ql)) L.pl :=
    VG.Proof.Dsa.bytesAt_slice m key (by omega_using [])
  simp only [VG.Proof.Dsa.paramsBytes_eq, ep, eq, eg, VG.Proof.Dsa.powMod_eq]
  change (if _ then some (_ ++ Spec.Dsa.encodeBE L.pl (gOf m L key ^ kOf m L x % pOf m L key) ++ _) else none) = _
  split <;> rename_i h₁ <;> split <;> rename_i h₂
  · rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, and_true] at h₁
    obtain ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, -⟩, hg, hx⟩ := h₁
    exact absurd ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ h₂
  · obtain ⟨⟨⟨hs, hq, hp⟩, hg, hd, hgq⟩, hy, hx⟩ := h₂
    obtain B := VG.Proof.Dsa.supported_bounds hs
    refine absurd ?_ h₁
    simp only [Bool.and_eq_true, decide_eq_true_eq, and_true]
    exact ⟨⟨hs, hp, hq⟩, hgq, hd, ⟨hy, Nat.mod_lt _ (show 0 < pOf m L key by omega_using [hp])⟩, hg, hx⟩
  · rfl

/-- `vg_dsa_derive_key`'s run, with any check `X` of the domain that runs
`rest` from what `checkParams` leaves exactly when the domain passes
`ParamsOk`, and `fail` otherwise, as `checkParams` does (`checkParams_ok`);
`X` may assume what the caller knows of the domain at entry. -/
theorem deriveWith_ok {X : Prog isa → Prog isa → Prog isa} (s : State) (h : dContract.pre s)
    (hX : ∀ {u : State} {Q : State → Prop} {rest fail : Prog isa},
      Outside (dlayOf s).S 0 (dlayOf s).Z s.mem u.mem → ScrL u (dlayOf s) →
      Regs u (dlayOf s) (s.gpr .a2) (s.gpr .a5) →
      word u.mem (dlayOf s).S hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 →
      Src u (dlayOf s) (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) →
      (∀ t, ParamsOk u.mem (dlayOf s) (s.gpr .a2) → Checked u t (dlayOf s) (s.gpr .a2) (s.gpr .a5) 0 →
        Kept (dlayOf s) u.mem t.mem → Keep cpRegs u t → WP isa rest t Q) →
      (∀ t, ¬ ParamsOk u.mem (dlayOf s) (s.gpr .a2) → Kept (dlayOf s) u.mem t.mem →
        Regs t (dlayOf s) (s.gpr .a2) (s.gpr .a5) → ScrL t (dlayOf s) → Keep cpRegs u t → WP isa fail t Q) →
      WP isa (X rest fail) u Q) :
    WP isa (.seq (.block Derive.entry) (.seq (X Derive.body Derive.zeroOut) (.block restore))) s fun t =>
      abiPreserved s t ∧ dContract.post s t := by
  suffices main : WP isa (.seq (.block Derive.entry) (.seq (X Derive.body Derive.zeroOut) (.block restore))) s
      fun t => ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ dContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  obtain hL := dlayOf_ok h
  have hZ := hL.z256
  have hnwS := hL.nowrap
  have hpre := h
  obtain ⟨hrd, hwr, dOP, dOX, dOS, -, dPS, dXS, -, nwO, nwP, nwX, -, hv, hol, hpl, -, -, -⟩ := h
  obtain mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (dlayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega_using [hk, hi]) (by omega_using [hnw, hk, hi])⟩, fun i hi => Pub.ne_of_disjoint hd (by omega_using [hnw]) i (by omega_using [hk, hi])⟩
  have h1 : (s.gpr .a1).toNat = 3 * (dlayOf s).pl + 2 * (dlayOf s).ql := hol
  have h3 : (s.gpr .a3).toNat = 2 * (dlayOf s).pl + (dlayOf s).ql := hpl
  obtain srcK := mkSrc (A := s.gpr .a2) (k := 2 * (dlayOf s).pl + (dlayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dPS nwP (s.gpr .a3).isLt (by omega_using [h3])
  obtain srcX := mkSrc (A := s.gpr .a5) (k := (dlayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dXS nwX
    (s.gpr .a6).isLt (Nat.le_refl _)
  obtain srcO := mkSrc (A := s.gpr .a0) (k := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql)
    (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO (s.gpr .a1).isLt (by omega_using [h1])
  obtain hno : (s.gpr .a0).toNat + (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) ≤ 2 ^ 64 := by rw [← h1]; exact nwO
  obtain hout : ∀ t : State, t.wr = s.wr → ∀ i < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql,
      InRegions t.wr (off (s.gpr .a0) i) 1 := fun t ht i hi =>
    ⟨_, by rw [ht, hwr]; exact List.mem_cons_self .., Offset.contains_base _ (by omega_using [h1, hi]) (by omega_using [h1, hi])⟩
  obtain hko : ∀ i < 2 * (dlayOf s).pl + (dlayOf s).ql, ∀ y, ofs (s.gpr .a0) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .a2) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOP) (by omega_using []) i (by omega_using [h3, hi]) y (by rw [h1]; exact hy)
  obtain hxo : ∀ i < (dlayOf s).ql, ∀ y, ofs (s.gpr .a0) y < 3 * (dlayOf s).pl + 2 * (dlayOf s).ql →
      off (s.gpr .a5) i ≠ y := fun i hi y hy =>
    Pub.ne_of_disjoint (Region.Disjoint.symm dOX) (by omega_using []) i (by simp only [dlayOf] at hi ⊢; omega_using [hi]) y
      (by rw [h1]; exact hy)
  -- A change in `out` keeps `scratch`'s header.
  obtain outSep : ∀ {m m' : Mem}, Outside (s.gpr .a0) 0 (3 * (dlayOf s).pl + 2 * (dlayOf s).ql) m m' →
      ∀ {d : Nat}, d + 8 ≤ 256 → word m' (dlayOf s).S d = word m (dlayOf s).S d := fun ho d hd =>
    in_word (out_in (o := 0) (N := 3 * (dlayOf s).pl + 2 * (dlayOf s).ql)
      (by simpa only [off, BitVec.add_zero] using ho) (by omega_using []) (by omega_using [h1]) (srcO s rfl rfl).sep)
      (by omega_using [hZ, hd]) (by omega_using [hnwS])
  obtain hspec : dRes s = if ParamsOk s.mem (dlayOf s) (s.gpr .a2) ∧ DeriveOk (pOf s.mem (dlayOf s) (s.gpr .a2))
        (qOf s.mem (dlayOf s) (s.gpr .a2)) (gOf s.mem (dlayOf s) (s.gpr .a2)) (kOf s.mem (dlayOf s) (s.gpr .a5))
      then some (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) ++
        Spec.Dsa.encodeBE (dlayOf s).pl (gOf s.mem (dlayOf s) (s.gpr .a2) ^ kOf s.mem (dlayOf s) (s.gpr .a5) %
          pOf s.mem (dlayOf s) (s.gpr .a2)) ++ Spec.Rsa.bytesAt s.mem (s.gpr .a5) (dlayOf s).ql)
      else none := by
    unfold dRes
    rw [h3]
    exact deriveKey_spec hv
  refine WP.seq (WP.mono (dfront_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  obtain hsav' : ∀ u : State, Kept (dlayOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (s.gpr .a7) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega_using [], by simp only [saveOff]; omega_using [hi]⟩)).trans (F.sav i hi)
  obtain hwo : ∀ u : State, Kept (dlayOf s) s₁.mem u.mem → word u.mem (dlayOf s).S Sign.hOut = s.gpr .a0 :=
    fun u hu => (hu.word (Or.inr ⟨by simp only [Sign.hOut, hLens]; omega_using [], by simp only [Sign.hOut]; omega_using []⟩)).trans F.outw
  obtain hwr' : ∀ u : State, ScrL u (dlayOf s) → ∀ i < 13, InRegions u.wr (off (savW (s.gpr .a7)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
  obtain hal' : ∀ i < 13, (off (savW (s.gpr .a7)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact F.scr.al8 (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega_using [])
  obtain Out₁ : Outside (dlayOf s).S 0 (dlayOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [dlayOf] at hZ ⊢; omega_using [hZ])
  obtain hk0 := srcK s rfl rfl
  obtain ep₁ : pOf s₁.mem (dlayOf s) (s.gpr .a2) = pOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [pOf]; rw [(hk0.take (k := (dlayOf s).pl) (by omega_using [])).bytes Out₁ (by omega_using [])]
  obtain eq₁ : qOf s₁.mem (dlayOf s) (s.gpr .a2) = qOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [qOf]; rw [(hk0.sub (o := (dlayOf s).pl) (k := (dlayOf s).ql) (by omega_using [])).bytes Out₁ (by omega_using [])]
  obtain eg₁ : gOf s₁.mem (dlayOf s) (s.gpr .a2) = gOf s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [gOf]
    rw [(hk0.sub (o := (dlayOf s).pl + (dlayOf s).ql) (k := (dlayOf s).pl) (by omega_using [])).bytes Out₁ (by omega_using [])]
  obtain ek₁ : kOf s₁.mem (dlayOf s) (s.gpr .a5) = kOf s.mem (dlayOf s) (s.gpr .a5) := by
    simp only [kOf]; rw [(srcX s rfl rfl).bytes Out₁ (by omega_using [])]
  obtain eb₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) =
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (2 * (dlayOf s).pl + (dlayOf s).ql) := (srcK s rfl rfl).bytes Out₁ (by omega_using [])
  obtain ex₁ : Spec.Rsa.bytesAt s₁.mem (s.gpr .a5) (dlayOf s).ql = Spec.Rsa.bytesAt s.mem (s.gpr .a5) (dlayOf s).ql :=
    (srcX s rfl rfl).bytes Out₁ (by omega_using [])
  obtain hPs : ParamsOk s₁.mem (dlayOf s) (s.gpr .a2) ↔ ParamsOk s.mem (dlayOf s) (s.gpr .a2) := by
    simp only [ParamsOk, ep₁, eq₁, eg₁]
  refine WP.seq (hX Out₁ F.scr F.regs F.lens (srcK s₁ k₁.2.1 k₁.2.2)
    (fun t hP hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    refine WP.mono (dbody_ok hL hP hc Kd (hwo t Kd) (srcK t kt.2.1 kt.2.2) (srcX t kt.2.1 kt.2.2)
      (hout t kt.2.2) hno (srcO t kt.2.1 kt.2.2) hko hxo) fun u ⟨⟨ob, r0u, ⟨m, Km, Om⟩, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok h6u (hwr' u scru) hal'
      (fun i hi => (outSep Om (by simp only [saveOff]; omega_using [hi])).trans
        ((Km.word (Or.inr ⟨by simp only [saveOff, hLens]; omega_using [], by simp only [saveOff]; omega_using [hi]⟩)).trans
          (hsav' t Kd i hi)))) fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    simp only [ep₁, eq₁, eg₁, ek₁, eb₁, ex₁] at ob r0u
    have hres := hspec
    simp only [hPs.mp hP, true_and] at hres
    refine ⟨?_, ?_⟩
    · rw [w0, r0u, ret_ofNat, hres, signStatus_ite]
    · rw [wm, h1, ob, hres]
      split <;> rfl
  · have kt := k₁.trans kc
    refine WP.mono (dzero_ok hL scrt hrt (hwo t Kd) (hout t kt.2.2) hno) fun u ⟨⟨ub, uo, u0⟩, ku⟩ => ?_
    refine WP.mono (sfinish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2)) hal'
      (fun i hi => (outSep uo (by simp only [saveOff]; omega_using [hi])).trans (hsav' t Kd i hi)))
      fun w ⟨hab, w0, wm⟩ => ⟨hab, ?_⟩
    obtain hres : dRes s = none := by
      rw [hspec]
      exact ite_eq_right_iff.mpr fun hx => absurd (hPs.mpr hx.1) hn
    refine ⟨?_, ?_⟩
    · rw [w0, u0, hres]; rfl
    · rw [wm, h1, ub, hres]; rfl

theorem deriveKey_correct (s : State) (h : dContract.pre s) :
    ∃ tr t, Exec isa Derive.derive s tr t ∧ abiPreserved s t ∧ dContract.post s t :=
  deriveWith_ok (X := checkParams) s h fun _ hs hr hl hk hrest hfail =>
    checkParams_ok (dlayOf_ok h) hs hr hl (by decide) hk hrest hfail

end VG.Proof.Dsa.RISCV64
