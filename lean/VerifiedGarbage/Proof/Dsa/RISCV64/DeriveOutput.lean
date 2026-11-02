module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
  have hi := List.mem_range.mp hi
  by_contra hc
  exact hsep i hi (D + BitVec.ofNat 64 i) (by omega) rfl

/-- A part of a range, unchanged by a change apart from it. -/
theorem part_kept {m m' : Mem} {O : Addr} {o n a k : Nat} (h : Outside O o n m m') (hd : a + k ≤ o ∨ o + n ≤ a)
    (hw : a + k < 2 ^ 64) : Spec.Rsa.bytesAt m' (off O a) k = Spec.Rsa.bytesAt m (off O a) k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  rw [show off O a + BitVec.ofNat 64 i = off O (a + i) from off_off O a i, ofs_off0 _ (by omega)]
  omega

/-- A separation from a whole range is one from a part of it. -/
theorem sep_part {D O : Addr} {k n a b : Nat} (hab : a + b ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ i < k, ∀ y, ofs O y < n → off D i ≠ y) : ∀ i < k, ∀ y, ofs (off O a) y < b → off D i ≠ y :=
  fun i hi y hy => h i hi y (by
    have := (Offset.lt_iff y O (d := a) (n := b) (by omega)).mp hy
    simp only [ofs]; omega)

theorem off_toNat {O : Addr} {a : Nat} (h : O.toNat + a < 2 ^ 64) : (off O a).toNat = O.toNat + a := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

/-- A change in a part of `out`, apart from `scratch`, keeps `scratch`. -/
theorem out_in {m m' : Mem} {out S : Addr} {o n N Z : Nat} (h : Outside (off out o) 0 n m m') (hon : o + n ≤ N)
    (hN : N < 2 ^ 64) (hsep : ∀ i < N, ∀ x, ofs S x < Z → off out i ≠ x) :
    ∀ x, ofs S x < Z → m' x = m x := by
  intro x hx
  refine h x (Or.inr ?_)
  by_contra hc
  have := (Offset.lt_iff x out (d := o) (n := n) (by omega)).mp (by simp only [ofs, off] at hc ⊢; omega)
  exact hsep (ofs out x) (by simp only [ofs] at this ⊢; omega) x hx (off_ofs _ _)

theorem in_word {m m' : Mem} {S : Addr} {Z d : Nat} (h : ∀ x, ofs S x < Z → m' x = m x) (hd : d + 8 ≤ Z)
    (hZ : Z ≤ 2 ^ 64) : word m' S d = word m S d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off S (by omega)]; omega)).symm).symm

/-- `Regs` through a change that keeps `scratch`. -/
theorem Regs.ofIn {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (hL : L.Ok) (h : Regs s L key sig)
    (k : Keep rs s t) (hin : ∀ x, ofs L.S x < L.Z → t.mem x = s.mem x)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra,
    by rw [in_word hin (by have := hL.z256; simp only [hLens]; omega) (by have := hL.nowrap; omega)]; exact h.pl,
    by rw [in_word hin (by have := hL.z256; simp only [hLens]; omega) (by have := hL.nowrap; omega)]; exact h.ql⟩

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
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hpl : 128 ≤ L.pl ∧ L.pl ≤ 384 := by rcases hL.pl with e | e | e <;> omega
  have hbe := hL.buf_end
  have hnw := hL.nowrap
  have hT : 3 * L.pl + 2 * L.ql < 2 ^ 64 := by omega
  -- The buffer is apart from `out`.
  have hbo : ∀ i < L.pl, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off L.Buf i ≠ y := by
    intro i hi y hy he
    subst he
    refine hos.sep (ofs out (off L.Buf i)) hy (off L.Buf i) ?_ (off_ofs _ _)
    rw [(bufAt hL (d := i) (by omega)).2]
    simp only [Lay.bOff] at hbe ⊢; omega
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
      simp only [BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide) (by rfl))
    fun s₁ ⟨⟨a5, m1'⟩, k1'⟩ => ?_
  have k1 := ((ku.trans kv).trans kw).trans k1'
  have m1 : s₁.mem = s.mem := by rw [m1', mw, mv, mu]
  have a4₁ : s₁.gpr .t4 = out := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a4'
  have a3₁ : s₁.gpr .t3 = key := by rw [(kv.trans kw).trans k1' |>.gpr (by decide)]; exact a3
  have N1 : 0 < 2 * L.pl + L.ql := by omega
  refine WP.seq (WP.mono (maskCopy_ok (c := c) N1 (by omega)
      (fun i hi => by rw [k1.2.2]; exact hout i (by omega)) (by omega)
      (fun i hi => by rw [k1.2.1, k1.2.2]; exact hk.rd i hi)
      (fun i hi y hy => hko i hi y (by omega)) a3₁ a4₁ a5 ((k1.gpr (by decide)).trans h4))
    fun s₂ ⟨⟨v2, o2, _, b4⟩, k2⟩ => ?_)
  rw [m1] at v2 o2
  -- The buffer and `p_len`.
  have k12 := k1.trans k2
  have in2 : ∀ y, ofs L.S y < L.Z → s₂.mem y = s.mem y :=
    out_in (o := 0) (N := 3 * L.pl + 2 * L.ql) (by simpa only [off, BitVec.add_zero] using o2) (by omega) hT hos.sep
  have hr2 : Regs s₂ L key x := Regs.ofIn hL hr k12 in2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (bufBase_ok (hs.congr k12.2.2) hL hr2 (rd := .t3) (t := .t2) (by decide) (by decide)
    (by decide)) fun s₃ ⟨⟨c3, m3⟩, k3⟩ => ?_
  refine WP.mono (getP_ok (hs.congr (k12.trans k3).2.2) hL (hr2.keepM k3 m3) .t5) fun s₄ ⟨⟨c5, m4⟩, k4⟩ => ?_
  have k34 := k3.trans k4
  have hm4 : s₄.mem = s₂.mem := by rw [m4, m3]
  have k14 := k12.trans k34
  have hoa : (off out (2 * L.pl + L.ql)).toNat = out.toNat + (2 * L.pl + L.ql) := off_toNat (by omega)
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.pl) (by omega) (by omega)
      (fun i hi => by rw [k14.2.2, off_off]; exact hout _ (by omega)) (by omega)
      (by have := bufRd hL (hs.congr k14.2.2) (o := 0) (k := L.pl) (by omega)
          simpa only [off, BitVec.add_zero] using this)
      (sep_part (by omega) hT hbo) ((k4.gpr (by decide)).trans c3)
      ((k34.gpr (by decide)).trans b4) c5 ((k14.gpr (by decide)).trans h4))
    fun s₅ ⟨⟨v5, o5, _, d4⟩, k5⟩ => ?_)
  rw [hm4] at v5 o5
  -- x and `q_len`.
  have k15 := k14.trans k5
  have in5 : ∀ y, ofs L.S y < L.Z → s₅.mem y = s.mem y := fun y hy =>
    (out_in (o := 2 * L.pl + L.ql) (N := 3 * L.pl + 2 * L.ql) o5 (by omega) hT hos.sep y hy).trans (in2 y hy)
  have hr5 : Regs s₅ L key x := Regs.ofIn hL hr k15 in5
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (Q := fun u => u.gpr .t3 = x ∧ u.mem = s₅.mem)
    (by brun [hr5.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₆ ⟨⟨e3, m6⟩, k6⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr (k15.trans k6).2.2) hL (hr5.keepM k6 m6) .t5) fun s₇ ⟨⟨e5, m7⟩, k7⟩ => ?_
  have k17 := (k15.trans k6).trans k7
  have hm7 : s₇.mem = s₅.mem := by rw [m7, m6]
  have hob : (off out (3 * L.pl + L.ql)).toNat = out.toNat + (3 * L.pl + L.ql) := off_toNat (by omega)
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.ql) (src := x) (dst := off out (3 * L.pl + L.ql)) (by omega) (by omega)
      (fun i hi => by rw [k17.2.2, off_off]; exact hout _ (by omega)) (by omega)
      (fun i hi => by rw [k17.2.1, k17.2.2]; exact hx.rd i hi)
      (sep_part (by omega) hT hxo) ((k7.gpr (by decide)).trans e3)
      (by rw [(k6.trans k7).gpr (by decide), d4, off_off, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega]) e5
      ((k17.gpr (by decide)).trans h4))
    fun s₈ ⟨⟨v8, o8, _, _⟩, k8⟩ => ?_)
  rw [hm7] at v8 o8
  -- `a0 :=` the mask's low bit.
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₈.mem) (by brun [(k17.trans k8).gpr (r := .a4) (by decide), h4, mask_low]) (by decide) (by rfl))
    fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have kall := (k17.trans k8).trans kt
  rw [mt]
  -- The frames, relative to `out`.
  have o5' : Outside out (2 * L.pl + L.ql) L.pl s₂.mem s₅.mem := by
    have := outside_shift (B := out) (a := 2 * L.pl + L.ql) o5 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  have o8' : Outside out (3 * L.pl + L.ql) L.ql s₅.mem s₈.mem := by
    have := outside_shift (B := out) (a := 3 * L.pl + L.ql) o8 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  -- The sources, unchanged.
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s.mem L.Buf L.pl :=
    bytes_kept o2 fun i hi y hy => hbo i hi y (by omega)
  have ex : Spec.Rsa.bytesAt s₅.mem x L.ql = Spec.Rsa.bytesAt s.mem x L.ql :=
    bytes_kept ((o2.mono (n' := 3 * L.pl + L.ql) (Nat.le_refl _) (by omega)).trans
      (o5'.mono (Nat.zero_le _) (by omega))) fun i hi y hy => hxo i hi y (by omega)
  rw [eb] at v5
  rw [ex] at v8
  refine ⟨⟨?_, ((o2.mono (n' := 3 * L.pl + 2 * L.ql) (Nat.le_refl _) (by omega)).trans
      (o5'.mono (Nat.zero_le _) (by omega))).trans (o8'.mono (Nat.zero_le _) (by omega)), t0⟩,
    kall.mono (by decide)⟩
  -- The three parts of `out`.
  rw [show 3 * L.pl + 2 * L.ql = 2 * L.pl + L.ql + L.pl + L.ql by omega, bytesAt_add, bytesAt_add]
  have p1 : Spec.Rsa.bytesAt s₈.mem out (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₂.mem out (2 * L.pl + L.ql) := by
    have e1 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o8' (Or.inl (by omega)) (by omega)
    have e2 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o5' (Or.inl (by omega)) (by omega)
    simp only [off, BitVec.add_zero] at e1 e2
    rw [e1, e2]
  have p2 : Spec.Rsa.bytesAt s₈.mem (off out (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s₅.mem (off out (2 * L.pl + L.ql)) L.pl :=
    part_kept o8' (Or.inl (by omega)) (by omega)
  rw [p1, p2, v2, v5, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega, v8]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
    congr 1; omega
  · simp only [↓reduceIte, List.append_assoc]

end VG.Proof.Dsa.RISCV64
