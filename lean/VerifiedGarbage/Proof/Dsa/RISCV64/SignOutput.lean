module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignAdd
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
  have al := slot_al8 w
  have hO := slot_lt (w := w) ho; have hA := slot_lt (w := w) ha; have hT := slot_lt (w := w) ht
  have sa := slot_sep' (w := w) hoa; have st := slot_sep' (w := w) hot
  unfold sel
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .a2) (by decide) o) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1
  refine WP.mono (e1.base (rd := .a5) (by decide) a) fun t₂ ⟨⟨a5, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2
  refine WP.mono (e2.base (rd := .a6) (by decide) t) fun t₃ ⟨⟨a6, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3
  have k13 := (k1.trans k2).trans k3
  have hm3 : t₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.mono (selectAcc64_ok (w := w) (dA := slot w a) (dT := slot w t) (dO := slot w o) (b := c) e3.hs
    ((k3.gpr (by decide)).trans a5) a6 ((k2.trans k3).gpr (by decide) |>.trans a2) e3.t0
    ((k13.gpr (by decide)).trans h4) (by omega) (by have := e3.w48; omega) (al a) (al t) (al o)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun u ⟨hv, ou, ku⟩ => ?_
  rw [hm3] at hv ou
  exact ⟨⟨hv, ou⟩, (k13.trans ku).mono (by decide)⟩

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

/-- A change in such a buffer keeps `scratch`'s header word `hLens`. -/
theorem out_hdr {s : State} {L : Lay} (hL : L.Ok) {O : Addr} {n k : Nat} (hos : Src s L O n) {m m' : Mem}
    (h : Outside O 0 k m m') (hk : k ≤ n) : word m' L.S hLens = word m L.S hLens := by
  have := hL.z256
  have := hL.nowrap
  refine (Mem.readW_congr fun i hi => (h _ (Or.inr ?_)).symm).symm
  by_contra hc
  exact hos.sep (ofs O (off L.S hLens + BitVec.ofNat 64 i)) (by simp only [ofs] at hc ⊢; omega) _
    (by rw [ofs_off L.S (by simp only [hLens]; omega)]; simp only [hLens]; omega) (off_ofs _ _)

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
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hZ := hL.z256
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e6 := e 6; have e7 := e 7
  have e8 := e 8; have e25 := e 25; have e26 := e 26; have e28 := e 28
  unfold output
  -- 0 into array 7.
  refine WP.seq (WP.mono (zeroArr_ok h.inq.env (j := 7) (by decide)) fun s₁ ⟨⟨z7, o1⟩, k1⟩ => ?_)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega) (by omega)
  have Q1 := h.step k1 (qa1.body hL)
  -- The mask into `a4`.
  obtain ⟨hld, hal⟩ := ScrL.hdr Q1.scr hL (d := 0) (by decide) (by decide)
  have hw1 : word s₁.mem L.S hMask = mask b := by rw [(qa1.body hL).word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₁.mem)
    (by brun [hMask, Q1.regs.s6, hld, hal]; exact hw1) (by decide) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
  have Q2 := Q1.stepM k2 m2
  -- `a4 &=` the mask of `s ≠ 0`.
  refine WP.seq (WP.mono (nonZero_ok Q2.inq.env (a := 6) (c := 0) (by decide) (by rw [m2]; exact z7) a4)
    fun s₃ ⟨⟨b4, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.stepM k3 m3
  have A6 : wordsVal s₂.mem L.Q (slot L.wq 6) L.wq = arrQ s.mem L 6 := by
    rw [m2]; exact o1.wordsVal (by omega) (by omega)
  have A25 : wordsVal s₁.mem L.Q (slot L.wq 25) L.wq = arrQ s.mem L 25 := o1.wordsVal (by omega) (by omega)
  rw [A6] at b4
  generalize (b && decide (arrQ s.mem L 6 ≠ 0)) = c at b4 ⊢
  refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = mask c ∧ u.mem = s₃.mem)
    (by brun [b4, BitVec.add_zero]) (by decide) (by rfl)) fun s₄ ⟨⟨a20, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.stepM k4 m4
  have hm4 : s₄.mem = s₁.mem := by rw [m4, m3, m2]
  -- The selections into arrays 1 and 2.
  refine WP.seq (WP.mono (sel_ok Q4.inq.env (c := c) (o := 1) (a := 25) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) a20) fun s₅ ⟨⟨v1, o5⟩, k5⟩ => ?_)
  have Q5 := Q4.step k5 (Body.ofQ hL o5 (by omega))
  refine WP.seq (WP.mono (sel_ok Q5.inq.env (c := c) (o := 2) (a := 6) (t := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) ((k5.gpr (by decide)).trans a20)) fun s₆ ⟨⟨v2, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega))
  have z7' : wordsVal s₄.mem L.Q (slot L.wq 7) L.wq = 0 := by rw [hm4]; exact z7
  have V1 : wordsVal s₆.mem L.Q (slot L.wq 1) L.wq = if c then arrQ s.mem L 25 else 0 := by
    rw [o6.wordsVal (by omega) (by omega), v1, z7', hm4, A25]
  have V2 : wordsVal s₆.mem L.Q (slot L.wq 2) L.wq = if c then arrQ s.mem L 6 else 0 := by
    rw [v2, o5.wordsVal (d := slot L.wq 7) (by omega) (by omega), o5.wordsVal (d := slot L.wq 6) (by omega) (by omega),
      z7', show wordsVal s₄.mem L.Q (slot L.wq 6) L.wq = arrQ s.mem L 6 by rw [m4, m3]; exact A6]
  have qa6 : QArr L s.mem s₆.mem := by
    refine qa1.trans ?_
    rw [← hm4]
    exact (QArr.of o5 (by omega) (by omega)).trans (QArr.of o6 (by omega) (by omega))
  have K6 := ((((k1.trans k2).trans k3).trans k4).trans k5).trans k6
  -- `out` into `s7`, `q_len` into `s8`.
  obtain ⟨hld', hal'⟩ := ScrL.hdr Q6.scr hL (d := 24) (by decide) (by decide)
  have hwo : word s₆.mem L.S Sign.hOut = out := by rw [(qa6.body hL).word (by decide)]; exact hw
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = out ∧ u.mem = s₆.mem)
    (by brun [Sign.hOut, Q6.regs.s6, hld', hal']; exact hwo) (by decide) (by rfl)) fun s₇ ⟨⟨a7, m7⟩, k7⟩ =>
    WP.mono (getQ_ok (Q6.scr.congr k7.2.2) hL (Q6.regs.keepM k7 m7) .s8) fun s₈ ⟨⟨a8, m8⟩, k8⟩ => ?_))
  have k78 := k7.trans k8
  have hm8 : s₈.mem = s₆.mem := m8.trans m7
  have Q8 := Q6.stepM k78 hm8
  have K8 := K6.trans k78
  -- r to `out`.
  have sep1 := hos.pastQ hL
  refine WP.seq (WP.mono (storeBE_ok (j := 1) (O := out) (k := L.ql) Q8.inq.env (by decide)
    (fun i hi => by rw [K8.2.2]; exact hout i (by omega)) (by omega) ((k8.gpr (by decide)).trans a7) a8
    (by omega) (by omega) (fun x hx => sep1 x (by omega))) fun s₉ ⟨⟨vt1, ot1⟩, k9⟩ => ?_)
  have kq1 := outside_pastQ (L := L) ot1 (fun x hx => sep1 x (by omega))
  have Q9 : QS s₉ L key nonce := ⟨Q8.inq.keep k9, Q8.scr.congr k9.2.2, Q8.regs.keepHdr k9
    (out_hdr hL hos ot1 (by omega))⟩
  -- `out + q_len` into `s7`.
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = off out L.ql ∧ u.mem = s₉.mem)
    (by brun [(k9.gpr (r := .s7) (by decide)).trans ((k8.gpr (r := .s7) (by decide)).trans a7),
      (k9.gpr (r := .s8) (by decide)).trans a8]) (by decide) (by rfl)) fun s₁₀ ⟨⟨b7, m10⟩, k10⟩ => ?_)
  have Q10 := Q9.stepM k10 m10
  have K10 := (K8.trans k9).trans k10
  -- s to `out + q_len`.
  have hos2 := hos.sub (o := L.ql) (k := L.ql) (by omega)
  have sep2 := hos2.pastQ hL
  have hoa : (off out L.ql).toNat = out.toNat + L.ql := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show L.ql < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.seq (WP.mono (storeBE_ok (j := 2) (O := off out L.ql) (k := L.ql) Q10.inq.env (by decide)
    (fun i hi => by rw [K10.2.2, off_off]; exact hout _ (by omega)) (by omega) b7
    ((k10.gpr (by decide)).trans ((k9.gpr (by decide)).trans a8)) (by omega) (by omega) sep2)
    fun s₁₁ ⟨⟨vt2, ot2⟩, k11⟩ => ?_)
  -- `a0 :=` the mask's low bit.
  have c4 : s₁₁.gpr .a4 = mask c :=
    ((((((k5.trans k6).trans k78).trans k9).trans k10).trans k11).gpr (by decide)).trans
      ((k4.gpr (by decide)).trans b4)
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0) ∧
    u.mem = s₁₁.mem) (by brun [c4, mask_low]) (by decide) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have kall := (K10.trans k11).trans kt
  have ot2' : Outside out L.ql L.ql s₁₀.mem s₁₁.mem := by
    have := outside_shift (B := out) (a := L.ql) ot2 (by omega) (by omega)
    rwa [Nat.add_zero] at this
  refine ⟨⟨?_, ?_, t0, ⟨s₆.mem, qa6, ?_⟩⟩, ?_⟩
  · have hb : Spec.Rsa.bytesAt t.mem out L.ql = Spec.Rsa.bytesAt s₉.mem out L.ql := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [mt, ot2' _ (Or.inl (by rw [show out + BitVec.ofNat 64 i = off out i from rfl, ofs_off0 out (by omega)]; omega)),
        m10]
    rw [hb, vt1, hm8, read_low (w := L.wq) _ _ (by omega) (by rw [V1]; split <;> omega), V1]
  · have e2' : wordsVal s₉.mem L.Q (slot L.wq 2) L.wq = if c then arrQ s.mem L 6 else 0 := by
      rw [kq1.wordsVal (Or.inl (by omega)) (by omega), hm8, V2]
    rw [mt, vt2, m10, read_low (w := L.wq) _ _ (by omega) (by rw [e2']; split <;> omega), e2']
  · rw [mt, ← hm8]
    have o9 : Outside out 0 (2 * L.ql) s₈.mem s₉.mem := ot1.mono (Nat.le_refl _) (by omega)
    have o11 : Outside out 0 (2 * L.ql) s₁₀.mem s₁₁.mem := ot2'.mono (by omega) (by omega)
    rw [m10] at o11
    exact o9.trans o11
  · simp only [outputRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64
