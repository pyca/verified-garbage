module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Copy
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA key derivation on PPC64LE: the output

`doutput_ok`: the domain's `2 p_len + q_len` octets (at `r27`), the buffer's
first `p_len` octets (y) and x's `q_len` octets (at `r28`), each and'ed with
the mask of `c` in `r20`, to `out` (`r26`); `r3 :=` 1 if `c`, else 0. Memory
changes only in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive

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
  rw [off_add, Bignum.PPC64LE.ofs_off0 _ (by omega)]
  omega

/-- A separation from a whole range is one from a part of it. -/
theorem sep_part {D O : Addr} {k n a b : Nat} (hab : a + b ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ i < k, ∀ y, ofs O y < n → off D i ≠ y) : ∀ i < k, ∀ y, ofs (off O a) y < b → off D i ≠ y :=
  fun i hi y hy => h i hi y (by
    have := (Offset.lt_iff y O (d := a) (n := b) (by omega)).mp hy
    simp only [ofs]; omega)

/-- The registers `output` writes. -/
def doutputRegs : List Reg := [.r0, .r3, .r6, .r12, .r14, .r16, .r17]

theorem doutput_ok {s : State} {L : Lay} {key x out : Addr} {c : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x out) (h20 : s.gpr .r20 = mask c)
    (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (ho : Scr s out (3 * L.pl + 2 * L.ql)) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa output s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) = (if c then Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) ++
            Spec.Rsa.bytesAt s.mem L.Buf L.pl ++ Spec.Rsa.bytesAt s.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        Outside out 0 (3 * L.pl + 2 * L.ql) s.mem t.mem ∧ t.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0)) ∧
        Keep doutputRegs s t := by
  have hZ := hL.z256
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hnw := hL.nowrap
  have hno := ho.nowrap
  have hw8 := hL.wp_eq
  have hT : 3 * L.pl + 2 * L.ql < 2 ^ 64 := by omega
  -- The buffer is apart from `out`.
  have hbo : ∀ i < L.pl, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off L.Buf i ≠ y := by
    intro i hi y hy he
    subst he
    refine hos.sep (ofs out (off L.Buf i)) hy (off L.Buf i) ?_ (off_ofs _ _)
    rw [Lay.Buf, off_off, Bignum.PPC64LE.ofs_off0 _ (by omega)]
    simp only [Lay.bOff] at hbe ⊢; omega
  unfold output
  -- `out`, the domain and its length.
  refine WP.seq (WP.mono (WP.keep [.r16, .r14, .r17, .r0] (Q := fun u => u.gpr .r16 = out ∧ u.gpr .r14 = key ∧
      u.gpr .r17 = BitVec.ofNat 64 (2 * L.pl + L.ql) ∧ u.mem = s.mem) (by
      unfold getP getQ
      prun [hr.r26, hr.r27, Regs.p_eq hr, Regs.q_eq hr, BitVec.add_zero]
      simp only [off, BitVec.ofNat_add_ofNat]; congr 1; omega) (by decide))
    fun s₁ ⟨⟨a16, a14, a17, m1⟩, k1⟩ => ?_)
  have N1 : 0 < 2 * L.pl + L.ql := by omega
  refine WP.seq (WP.mono (maskCopy_ok (c := c) N1 (by omega) (scr_prefix (ho.congr k1.wr) (by omega))
      (fun i hi => by rw [k1.rd, k1.wr]; exact hk.rd i hi)
      (fun i hi y hy => hko i hi y (by omega)) a14 a16 a17 ((k1.gpr .r20 (by decide)).trans h20))
    fun s₂ ⟨⟨v2, o2, b14, b16⟩, k2⟩ => ?_)
  rw [m1] at v2 o2
  -- The buffer and `p_len`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hr2 := (hr.keep k1).keep k2
  refine WP.mono (bufBase_ok hL hr2 (rd := .r12) (t := .r0) (by decide)) fun s₃ ⟨⟨c12, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r14] (Q := fun u => u.gpr .r14 = L.Buf ∧ u.mem = s₃.mem)
    (by prun [c12, BitVec.add_zero]) (by decide)) fun s₄ ⟨⟨c14, m4⟩, k4⟩ => ?_
  refine WP.mono (getP_ok ((hr2.keep k3).keep k4) .r17) fun s₅ ⟨⟨c17, m5⟩, k5⟩ => ?_
  have k35 := (k3.trans k4).trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  have k15 := (k1.trans k2).trans k35
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.pl) (by omega) (by omega)
      (scr_sub (ho.congr k15.wr) (o := 2 * L.pl + L.ql) (n := L.pl) (by omega) (by omega))
      (fun i hi => by rw [k15.rd, k15.wr]; exact (ScrL.bufN hs hL (n := L.pl) (by omega)).ld (show i + 1 ≤ L.pl by omega))
      (sep_part (by omega) hT hbo) ((k5.gpr .r14 (by decide)).trans c14)
      ((k35.gpr .r16 (by decide)).trans b16) c17 ((k15.gpr .r20 (by decide)).trans h20))
    fun s₆ ⟨⟨v6, o6, _, d16⟩, k6⟩ => ?_)
  rw [hm5] at v6 o6
  -- x and `q_len`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hr6 := (hr.keep k15).keep k6
  refine WP.mono (WP.keep [.r14] (Q := fun u => u.gpr .r14 = x ∧ u.mem = s₆.mem)
    (by prun [hr6.r28, BitVec.add_zero]) (by decide)) fun s₇ ⟨⟨e14, m7⟩, k7⟩ => ?_
  refine WP.mono (getQ_ok (hr6.keep k7) .r17) fun s₈ ⟨⟨e17, m8⟩, k8⟩ => ?_
  have k16 := k15.trans k6
  have k18 := (k16.trans k7).trans k8
  have hm8 : s₈.mem = s₆.mem := by rw [m8, m7]
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.ql) (by omega) (by omega)
      (scr_sub (ho.congr k18.wr) (o := 3 * L.pl + L.ql) (n := L.ql) (by omega) (by omega))
      (fun i hi => by rw [k18.rd, k18.wr]; exact hx.rd i hi)
      (sep_part (by omega) hT hxo) ((k8.gpr .r14 (by decide)).trans e14)
      (by rw [(k7.trans k8).gpr .r16 (by decide), d16, off_off]; congr 1; omega) e17
      ((k18.gpr .r20 (by decide)).trans h20))
    fun s₉ ⟨⟨v9, o9, _, _⟩, k9⟩ => ?_)
  rw [hm8] at v9 o9
  -- `r3 :=` the mask's low bit.
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₉.mem) (by prun [(k18.trans k9).gpr .r20 (by decide), h20, mask_low]) (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ?_
  have kall := (k18.trans k9).trans kt
  rw [mt]
  -- The frames, relative to `out`.
  have o6' : Outside out (2 * L.pl + L.ql) L.pl s₂.mem s₆.mem := by
    have := outside_shift (B := out) (a := 2 * L.pl + L.ql) o6 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  have o9' : Outside out (3 * L.pl + L.ql) L.ql s₆.mem s₉.mem := by
    have := outside_shift (B := out) (a := 3 * L.pl + L.ql) o9 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  -- The sources, unchanged.
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s.mem L.Buf L.pl :=
    bytes_kept o2 fun i hi y hy => hbo i hi y (by omega)
  have ex : Spec.Rsa.bytesAt s₆.mem x L.ql = Spec.Rsa.bytesAt s.mem x L.ql :=
    bytes_kept ((o2.mono (n' := 3 * L.pl + L.ql) (Nat.le_refl _) (by omega)).trans
      (o6'.mono (Nat.zero_le _) (by omega))) fun i hi y hy => hxo i hi y (by omega)
  rw [eb] at v6
  rw [ex] at v9
  refine ⟨⟨?_, ((o2.mono (n' := 3 * L.pl + 2 * L.ql) (Nat.le_refl _) (by omega)).trans (o6'.mono (Nat.zero_le _) (by omega))).trans
      (o9'.mono (Nat.zero_le _) (by omega)), t3⟩, kall.mono (by decide)⟩
  -- The three parts of `out`.
  rw [show 3 * L.pl + 2 * L.ql = 2 * L.pl + L.ql + L.pl + L.ql by omega, bytesAt_add, bytesAt_add]
  have p1 : Spec.Rsa.bytesAt s₉.mem out (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₂.mem out (2 * L.pl + L.ql) := by
    have e1 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o9' (Or.inl (by omega)) (by omega)
    have e2 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o6' (Or.inl (by omega)) (by omega)
    simp only [off, BitVec.add_zero] at e1 e2
    rw [e1, e2]
  have p2 : Spec.Rsa.bytesAt s₉.mem (off out (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s₆.mem (off out (2 * L.pl + L.ql)) L.pl :=
    part_kept o9' (Or.inl (by omega)) (by omega)
  rw [p1, p2, v2, v6, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega, v9]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
    congr 1; omega
  · simp only [↓reduceIte, List.append_assoc]

end VG.Proof.Dsa.PPC64LE
