module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.R
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA signing on PPC64LE: the output

`output_ok`: in the Q space with r in array 9 and s in array 6, `c := b ∧ s ≠
0` for the mask of `b` in the header's word `hMask`; `out` (in the header's
word `hOut`) gets r's then s's `q_len` octets, most significant first, if
`c`, else zeros, and `r3 := 1` if `c`, else 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

theorem mask_low (c : Bool) : mask c &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if c then 1 else 0) := by
  cases c <;> rfl

theorem off_ofs (O x : Addr) : off O (ofs O x) = x := by
  simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

/-- A buffer apart from `scratch` is past the Q space. -/
theorem Src.pastQ {s : State} {L : Lay} {O : Addr} {n : Nat} (h : Src s L O n) (hL : L.Ok) :
    ∀ x, ofs O x < n → 1600 ≤ ofs L.Q x := fun x hx => by
  by_contra hc
  exact h.sepQ hL _ hx x (by omega) (off_ofs O x)

/-- A change in such a buffer leaves the Q space. -/
theorem outside_pastQ {L : Lay} {O : Addr} {k : Nat} {m m' : Mem} (h : Outside O 0 k m m')
    (hsep : ∀ x, ofs O x < k → 1600 ≤ ofs L.Q x) : Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hlt := (x - L.Q).isLt
  refine h x (Or.inr ?_)
  by_contra hc
  have := hsep x (by omega)
  simp only [ofs] at hx this; omega

/-- The registers `output` writes. -/
def outputRegs : List Reg :=
  [.r0, .r14, .r17, .r22] ++ nonZeroRegs ++ [.r20] ++ selRegs ++ [.r12, .r6] ++ storeRegs ++ [.r3]

/-- `output`: r and s, selected with 0 by `b ∧ s ≠ 0`, to `out`; `r3 :=` 1
if `b ∧ s ≠ 0`, else 0. Memory changes only in the Q space's arrays and in
`out`'s `2 q_len` octets. -/
theorem output_ok {s : State} {L : Lay} {key nonce dig out : Addr} {b : Bool} (hL : L.Ok)
    (h : QS s L key nonce dig) (hw : word s.mem L.S hOut = out) (hm : word s.mem L.S hMask = mask b)
    (ho : Scr s out (2 * L.ql)) (hos : Src s L out (2 * L.ql))
    (h9 : arrQ s.mem L 9 < 2 ^ (8 * L.ql)) (h6 : arrQ s.mem L 6 < 2 ^ (8 * L.ql)) :
    WP isa output s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem out L.ql) =
          (if b && decide (arrQ s.mem L 6 ≠ 0) then arrQ s.mem L 9 else 0) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off out L.ql) L.ql) =
          (if b && decide (arrQ s.mem L 6 ≠ 0) then arrQ s.mem L 6 else 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if b && decide (arrQ s.mem L 6 ≠ 0) then 1 else 0) ∧
        ∃ m, QArr L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ Keep outputRegs s t := by
  have hql := hL.ql
  have hZ := hL.z256
  have hno := ho.nowrap
  unfold output
  -- 0 into array 7.
  refine WP.seq (WP.mono (zeroArr_ok h.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
  have Q1 := h.step k1 (by decide)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  -- The mask into `r22`.
  have hld : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [Q1.regs.r21]; exact Q1.scr.ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega)
  have hw1 : word s₁.mem L.S hMask = mask b := by
    rw [Outside.word (qa1.qbody.body hL) (Or.inl (by simp only [hMask]; omega)) (by simp only [hMask]; omega)]
    exact hm
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask b ∧ u.mem = s₁.mem)
    (by prun [exec_ld (by decide) hld]; rw [Q1.regs.r21, ← hw1]) (by decide)) fun s₂ ⟨⟨a22, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  -- `r22 &=` the mask of `s ≠ 0`.
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (by decide) (by rw [m2]; exact z7) a22)
    fun s₃ ⟨⟨b22, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.step k3 (by decide)
  have A6 : arr s₂.mem L.Q 4 6 = arrQ s.mem L 6 := by
    rw [m2]; exact Outside.val32 o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have A9 : arr s₁.mem L.Q 4 9 = arrQ s.mem L 9 :=
    Outside.val32 o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  rw [A6] at b22
  generalize (b && decide (arrQ s.mem L 6 ≠ 0)) = c at b22 ⊢
  refine WP.seq (WP.mono (WP.keep [.r20] (Q := fun u => u.gpr .r20 = mask c ∧ u.mem = s₃.mem)
    (by prun [b22, BitVec.add_zero]) (by decide)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.step k4 (by decide)
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  -- The selections into arrays 1 and 2.
  refine WP.seq (WP.mono (sel_ok Q4.inq.env (b := c) (o := 1) (a := 9) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨v1, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (by decide)
  refine WP.seq (WP.mono (sel_ok Q5.inq.env (b := c) (o := 2) (a := 6) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k5.gpr .r20 (by decide)).trans a20)) fun s₆ ⟨⟨v2, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (by decide)
  have V1 : val32 s₆.mem L.Q (slot 4 1) (2 * 4) = if c then arrQ s.mem L 9 else 0 := by
    rw [Outside.val32 o6 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega), v1]
    have z7' : val32 s₄.mem L.Q (slot 4 7) (2 * 4) = 0 := by rw [hm4]; exact z7
    rw [z7', show val32 s₄.mem L.Q (slot 4 9) (2 * 4) = arrQ s.mem L 9 by rw [hm4]; exact A9]
  have V2 : val32 s₆.mem L.Q (slot 4 2) (2 * 4) = if c then arrQ s.mem L 6 else 0 := by
    rw [v2, Outside.val32 o5 (d := slot 4 7) (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega),
      Outside.val32 o5 (d := slot 4 6) (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]
    have z7' : val32 s₄.mem L.Q (slot 4 7) (2 * 4) = 0 := by rw [hm4]; exact z7
    rw [z7', show val32 s₄.mem L.Q (slot 4 6) (2 * 4) = arrQ s.mem L 6 by rw [m4, m3]; exact A6]
  have qa6 : QArr L s.mem s₆.mem := by
    refine qa1.trans ?_
    rw [← hm4]
    exact (QArr.of o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)).trans
      (QArr.of o6 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  -- `out` into `r12`, `q_len` into `r6`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hld' : InRegions (s₆.rd ++ s₆.wr) (s₆.gpr .r21 + BitVec.ofNat 64 hOut) 8 := by
    rw [Q6.regs.r21]; exact Q6.scr.ld (show hOut + 8 ≤ L.Z by simp only [hOut]; omega)
  have hwo : word s₆.mem L.S hOut = out := by
    rw [Outside.word (qa6.qbody.body hL) (Or.inl (by simp only [hOut]; omega)) (by simp only [hOut]; omega)]
    exact hw
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = out ∧ u.mem = s₆.mem)
    (by prun [exec_ld (by decide) hld']; rw [Q6.regs.r21]; exact hwo) (by decide)) fun s₇ ⟨⟨a12, m7⟩, k7⟩ => ?_
  refine WP.mono (getQ_ok (Q6.regs.keep k7) .r6) fun s₈ ⟨⟨a6, m8⟩, k8⟩ => ?_
  have k78 := k7.trans k8
  have hm8 : s₈.mem = s₆.mem := m8.trans m7
  have Q8 := Q6.step k78 (by decide)
  have K8 := K6.trans k78
  -- r to `out`.
  have sep1 := hos.pastQ hL
  refine WP.seq (WP.mono (storeBE_ok (j := 1) (O := out) (k := L.ql) Q8.inq.env (by decide)
    (scr_prefix (ho.congr K8.wr) (by omega)) ((k8.gpr .r12 (by decide)).trans a12) a6 (by omega) (by omega)
    (fun x hx => sep1 x (by omega))) fun s₉ ⟨⟨vt1, ot1⟩, k9⟩ => ?_)
  have Q9 := Q8.step k9 (by decide)
  have kq1 := outside_pastQ (L := L) ot1 (fun x hx => sep1 x (by omega))
  -- `out + q_len` into `r12`.
  refine WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = off out L.ql ∧ u.mem = s₉.mem)
    (by prun [(k9.gpr .r12 (by decide)).trans ((k8.gpr .r12 (by decide)).trans a12),
      (k9.gpr .r6 (by decide)).trans a6]) (by decide)) fun s₁₀ ⟨⟨b12, m10⟩, k10⟩ => ?_)
  have Q10 := Q9.step k10 (by decide)
  have K10 := (K8.trans k9).trans k10
  -- s to `out + q_len`.
  have hos2 := hos.sub (o := L.ql) (k := L.ql) (by omega)
  have sep2 := hos2.pastQ hL
  refine WP.seq (WP.mono (storeBE_ok (j := 2) (O := off out L.ql) (k := L.ql) Q10.inq.env (by decide)
    (scr_sub (ho.congr K10.wr) (o := L.ql) (n := L.ql) (by omega) (by omega)) b12
    ((k10.gpr .r6 (by decide)).trans ((k9.gpr .r6 (by decide)).trans a6)) (by omega) (by omega) sep2)
    fun s₁₁ ⟨⟨vt2, ot2⟩, k11⟩ => ?_)
  -- `r3 :=` the mask's low bit.
  have c22 : s₁₁.gpr .r22 = mask c :=
    ((((((k4.trans k5).trans k6).trans k78).trans k9).trans k10).trans k11).gpr .r22 (by decide) |>.trans b22
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₁₁.mem) (by prun [c22, mask_low]) (by decide)) fun t ⟨⟨t3, mt⟩, kt⟩ => ?_
  have kall := (K10.trans k11).trans kt
  have ot2' : Outside out L.ql L.ql s₁₀.mem s₁₁.mem := by
    have := outside_shift (B := out) (a := L.ql) ot2 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  refine ⟨⟨?_, ?_, t3, ⟨s₆.mem, qa6, ?_⟩⟩, kall.mono (by decide)⟩
  · have hb : Spec.Rsa.bytesAt t.mem out L.ql = Spec.Rsa.bytesAt s₉.mem out L.ql := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [mt, ot2' _ (Or.inl (by rw [Mont.ofs_off0 out (by omega)]; omega)), m10]
    rw [hb, vt1, hm8, read_low (w := 4) _ _ (by omega) (by rw [V1]; split <;> omega), V1]
  · have e2 : val32 s₉.mem L.Q (slot 4 2) (2 * 4) = if c then arrQ s.mem L 6 else 0 := by
      rw [Outside.val32 kq1 (Or.inl (by simp only [slot_eq]; omega)) (by simp only [slot_eq]; omega), hm8, V2]
    rw [mt, vt2, m10, read_low (w := 4) _ _ (by omega) (by rw [e2]; split <;> omega), e2]
  · rw [mt, ← hm8]
    have o9 : Outside out 0 (2 * L.ql) s₈.mem s₉.mem := ot1.mono (Nat.le_refl _) (by omega)
    have o11 : Outside out 0 (2 * L.ql) s₁₀.mem s₁₁.mem := ot2'.mono (by omega) (by omega)
    rw [m10] at o11
    exact o9.trans o11

end VG.Proof.Dsa.PPC64LE
