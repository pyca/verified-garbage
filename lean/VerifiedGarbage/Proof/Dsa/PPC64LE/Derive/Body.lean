module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.R
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Pow
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.X
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.PPC64LE.Derive.Y`, which only this module used -/

section

/-!
# DSA key derivation on PPC64LE: y

`yValue_ok`: in the P space with p in array 0 and `R² mod p` in array 24,
`y = g^x mod p` (x the `q_len` octets at `r28`) to the buffer's first
`p_len` octets, and `r22 :=` the mask of `y ≠ 0` and `y ≠ 1`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The registers `yValue` writes. -/
def yValueRegs : List Reg :=
  [.r24, .r0, .r6, .r12] ++ combPowRegs ++ [.r14, .r17, .r22] ++ nonZeroRegs ++ storeRegs

/-- `yValue`: `y = g^x mod p` to the buffer's first `p_len` octets, and
`r22 :=` the mask of `y ≠ 0` and `y ≠ 1`. Memory changes only in the P
space's arrays and the buffer's first `p_len` octets. -/
theorem yValue_ok {s : State} {L : Lay} {key x out : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key x out) (hin : InP s L) (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa yValue s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L x % p ∧
        t.gpr .r22 = mask (decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 0) &&
          decide (gOf s.mem L key ^ kOf s.mem L x % p ≠ 1)) ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧
        Keep yValueRegs s t := by
  have hZ := hL.z256
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega_using [hbe]
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e7 := Lay.slot_eq L.wp 7; have e8 := Lay.slot_eq L.wp 8; have e24 := Lay.slot_eq L.wp 24; have e28 := Lay.slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  unfold yValue
  -- The pointers: x into `r24`, g's octets into `r12`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r24] (Q := fun u => u.gpr .r24 = x ∧ u.mem = s.mem)
    (by prun [hr.r28, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a24, m1⟩, k1⟩ => ?_
  refine WP.mono (ptrG_ok (hr.keep k1)) fun s₂ ⟨⟨b12, _, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^x mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := x) (p := p) hL
      (hr.keep k12) (hin.keep k12 (by decide))
      ((hk.keep k12.rd k12.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega_using [])) b12 (hx.keep k12.rd k12.wr)
      ((k2.gpr .r24 (by decide)).trans a24) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  have y4 : arr s₃.mem L.S L.wp 4 = gOf s.mem L key ^ kOf s.mem L x % p := v4
  have hyp : gOf s.mem L key ^ kOf s.mem L x % p < p := Nat.mod_lt _ (by omega_using [hp])
  generalize gOf s.mem L key ^ kOf s.mem L x % p = y at y4 hyp ⊢
  -- 0 into array 7, `r22 :=` all ones.
  refine WP.seq (WP.mono (zeroArr_ok in3.env (j := 7) (by decide)) fun s₄ ⟨⟨z7, o4⟩, k4⟩ => ?_)
  have en4 := in3.env.keep k4 (by decide)
  refine WP.seq (WP.mono (WP.keep [.r22] (Q := fun u => u.gpr .r22 = mask true ∧ u.mem = s₄.mem)
    (by prun []; rfl) (by decide)) fun s₅ ⟨⟨a22, m5⟩, k5⟩ => ?_)
  have en5 := en4.keep k5 (by decide)
  have y5 : arr s₅.mem L.S L.wp 4 = y := by
    rw [m5, arr, Outside.val32 o4 (by omega_using [e4, e7]) (by omega_using [hw, e4])]; exact y4
  -- `r22 &=` the masks of `y ≠ 0` and `y ≠ 1`.
  refine WP.seq (WP.mono (nonZero_ok en5 (a := 4) (c := 0) (by decide) (by rw [m5]; exact z7) a22)
    fun s₆ ⟨⟨b22, m6⟩, k6⟩ => ?_)
  rw [y5] at b22
  have en6 := en5.keep k6 (by decide)
  refine WP.seq (WP.mono (Pub.oneP_ok en6.hs (by omega_using [hw]) (by omega_using [hw]) (by omega_using [e8, e28, hq28]) en6.h10 en6.h29 en6.h11)
    fun s₇ ⟨⟨v7, o7⟩, k7⟩ => ?_)
  have en7 := en6.keep k7 (by decide)
  have y7 : arr s₇.mem L.S L.wp 4 = y := by
    rw [arr, Outside.val32 o7 (by omega_using [e4, e7]) (by omega_using [hw, e4]), m6]; exact y5
  refine WP.seq (WP.mono (nonZero_ok en7 (a := 4) (c := 1) (by decide) v7
    ((k7.gpr .r22 (by decide)).trans b22)) fun s₈ ⟨⟨c22, m8⟩, k8⟩ => ?_)
  rw [y7, Bool.true_and] at c22
  have en8 := en7.keep k8 (by decide)
  -- y to the buffer.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have k18 := (((((k13.trans k4).trans k5).trans k6).trans k7).trans k8)
  refine WP.mono (bufBase_ok hL (hr.keep k18) (rd := .r12) (t := .r0) (by decide)) fun s₉ ⟨⟨c12, m9⟩, k9⟩ => ?_
  refine WP.mono (getP_ok ((hr.keep k18).keep k9) .r6) fun s₁₀ ⟨⟨c6, m10⟩, k10⟩ => ?_
  have k910 := k9.trans k10
  have hm10 : s₁₀.mem = s₇.mem := by rw [m10, m9, m8]
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) (en8.keep k910 (by decide)) (by decide)
    (ScrL.bufN (hs.congr (k18.trans k910).wr) hL (by omega_using [])) ((k10.gpr .r12 (by decide)).trans c12) c6
    (by omega_using [hpl]) (by omega_using [hw8]) (combBufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm10] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 32 * (2 * L.wp) by omega_using []]; exact val32_lt _ _ _ _
  have y7' : val32 s₇.mem L.S (slot L.wp 4) (2 * L.wp) = y := y7
  have hm6 : s₆.mem = s₄.mem := by rw [m6, m5]
  have o47 : Outside L.S (slot L.wp 7) (8 * L.wp) s₃.mem s₇.mem := by
    rw [← hm6] at o4; exact o4.trans o7
  have kall := (k18.trans k910).trans kt
  refine ⟨⟨?_, (kt.gpr .r22 (by decide)).trans ((k910.gpr .r22 (by decide)).trans c22),
    ⟨en8.keep (k910.trans kt) (by decide), (kall.gpr .r21 (by decide)).trans hin.h21,
      (kall.gpr .r23 (by decide)).trans hin.h23⟩,
    ((Body.ofP hL o3 (by omega_using [e1]) (by omega_using [e1, e24, e28, hq28])).trans (Body.ofP hL o47 (by omega_using [e7]) (by omega_using [e7, e28, hq28]))).trans
      (Body.ofBuf hL ot (by omega_using [])),
    ((comb_pbody_keepQ hL (o3.mono (by omega_using [e1]) (by omega_using [e1, e24, e28, hq28]))).trans
      (comb_pbody_keepQ hL (o47.mono (by omega_using [e7]) (by omega_using [e7, e28, hq28])))).trans (combBufKeepQ ot (by omega_using [hpl]))⟩,
    kall.mono (by decide)⟩
  rw [vt, read_low (w := L.wp) _ _ (by omega_using [hw8]) (by rw [y7']; exact Nat.lt_trans hyp hplt), y7']

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Derive.Output`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Derive.Copy`, which only this module used -/

section

/-!
# DSA key derivation on PPC64LE: the masked copy

`maskCopy_ok`: the `N` octets at `src`, each and'ed with the mask of `c` in
`r20`, to `dst`, a buffer apart from them: `dst` gets the octets if `c`,
else zeros.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

theorem mask_byte (v : BitVec 64) (c : Bool) : (v &&& mask c).setWidth 8 = if c then v.setWidth 8 else 0 := by
  cases c
  · have : mask false = 0#64 := rfl
    rw [this, BitVec.and_zero]; rfl
  · have : mask true = BitVec.allOnes 64 := rfl
    rw [this, BitVec.and_allOnes]; rfl

/-- The registers `maskCopy` writes. -/
def maskCopyRegs : List Reg := [.r0, .r14, .r16, .r17]

/-- `maskCopy`: the `N` octets at `src` (`r14`), and'ed with the mask of `c`
(`r20`), to `dst` (`r16`); the pointers past them. -/
theorem maskCopy_ok {s : State} {src dst : Addr} {N : Nat} {c : Bool} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : Scr s dst N) (hrd : ∀ i < N, InRegions (s.rd ++ s.wr) (off src i) 1)
    (hsep : ∀ i < N, ∀ x, ofs dst x < N → off src i ≠ x)
    (h14 : s.gpr .r14 = src) (h16 : s.gpr .r16 = dst) (h17 : s.gpr .r17 = BitVec.ofNat 64 N)
    (h20 : s.gpr .r20 = mask c) :
    WP isa Derive.maskCopy s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = (if c then Spec.Rsa.bytesAt s.mem src N else List.replicate N 0) ∧
        Outside dst 0 N s.mem t.mem ∧ t.gpr .r14 = off src N ∧ t.gpr .r16 = off dst N) ∧
        Keep maskCopyRegs s t := by
  have hno := ho.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off src i ∧ t.gpr .r16 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off dst i') = if c then s.mem (off src i') else 0) ∧ Keep maskCopyRegs s t
  unfold Derive.maskCopy Precompute.countLoop
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r14 0, .logic .and .r0 .r0 .r20, .stb .r0 .r16 0,
      .addi .r14 .r14 1, .addi .r16 .r16 1] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := N) hN' hN Inv (fun i hi t ⟨t14, t16, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h14, off, BitVec.add_zero], by rw [h16, off, BitVec.add_zero], Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_using []), Keep.refl _ _⟩ h17)
    fun t ⟨t14, t16, tout, tb, tk⟩ => ⟨⟨?_, tout, t14, t16⟩, tk⟩
  · have t20 : t.gpr .r20 = mask c := (tk.gpr .r20 (by decide)).trans h20
    have hst : WP isa (.block [.lbz .r0 .r14 0, .logic .and .r0 .r0 .r20, .stb .r0 .r16 0, .addi .r14 .r14 1,
        .addi .r16 .r16 1, .subi .r17 .r17 1]) t fun t' =>
        (t'.gpr .r14 = off src (i + 1) ∧ t'.gpr .r16 = off dst (i + 1) ∧
          t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off dst i) 1 ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8)) ∧
          Keep maskCopyRegs t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [t14, t16, t20, exec_lbz' (show Reg.r14 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        (by rw [tk.rd, tk.wr]; exact hrd i hi : InRegions (t.rd ++ t.wr) (off src i) 1),
        (ho.congr tk.wr).st (d := i) (n := 1) (by omega_using [hi])]
    refine WP.mono hst fun t' ⟨⟨a14, a16, a17, am⟩, ka⟩ => ⟨⟨a14, a16, ?_, ?_, tk.trans' ka⟩, a17⟩
    · have hw1 := write1_outside t.mem dst (d := i)
        ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8) (by omega_using [hN', hi])
      rw [am]; exact (tout.mono (Nat.le_refl _) (by omega_using [])).trans (hw1.mono (by omega_using []) (by omega_using []))
    · intro i' hi'
      have hw1 := write1_outside t.mem dst (d := i)
        ((((t.mem.read (off src i) 1).setWidth 64) &&& mask c).setWidth 8) (by omega_using [hN', hi])
      rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [Bignum.PPC64LE.ofs_off0 dst (by omega_arith)]; omega_using [hi'])]; exact tb i' hi'
      · have hs : t.mem (off src i') = s.mem (off src i') := by
          refine tout _ (Or.inr ?_)
          by_contra hcon
          exact hsep i' hi (off src i') (by omega_using [hi, hcon]) rfl
        rw [write1_self, mask_byte, read_one', hs]
  · rw [Spec.Rsa.bytesAt]
    rw [show (List.range N).map (fun i => t.mem (dst + BitVec.ofNat 64 i)) =
        (List.range N).map (fun i => if c then s.mem (off src i) else 0) from
      List.map_congr_left fun i hi => tb i (List.mem_range.mp hi)]
    cases c
    · refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      rfl
    · rfl

end VG.Proof.Dsa.PPC64LE

end

end


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
  rw [off_add, Bignum.PPC64LE.ofs_off0 _ (by omega_using [hw, hi])]
  omega_using [hd, hi]

/-- A separation from a whole range is one from a part of it. -/
theorem sep_part {D O : Addr} {k n a b : Nat} (hab : a + b ≤ n) (hn : n < 2 ^ 64)
    (h : ∀ i < k, ∀ y, ofs O y < n → off D i ≠ y) : ∀ i < k, ∀ y, ofs (off O a) y < b → off D i ≠ y :=
  fun i hi y hy => h i hi y (by
    have := (Offset.lt_iff y O (d := a) (n := b) (by omega_using [hab, hn])).mp hy
    simp only [ofs]; omega_using [hab, this])

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
  have hT : 3 * L.pl + 2 * L.ql < 2 ^ 64 := by omega_using [hql, hpl]
  -- The buffer is apart from `out`.
  have hbo : ∀ i < L.pl, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off L.Buf i ≠ y := by
    intro i hi y hy he
    subst he
    refine hos.sep (ofs out (off L.Buf i)) hy (off L.Buf i) ?_ (off_ofs _ _)
    rw [Lay.Buf, off_off, Bignum.PPC64LE.ofs_off0 _ (by omega_using [hbe, hnw, hi])]
    simp only [Lay.bOff] at hbe ⊢; omega_using [hbe, hi]
  unfold output
  -- `out`, the domain and its length.
  refine WP.seq (WP.mono (WP.keep [.r16, .r14, .r17, .r0] (Q := fun u => u.gpr .r16 = out ∧ u.gpr .r14 = key ∧
      u.gpr .r17 = BitVec.ofNat 64 (2 * L.pl + L.ql) ∧ u.mem = s.mem) (by
      unfold getP getQ
      prun [hr.r26, hr.r27, Regs.p_eq hr, Regs.q_eq hr, BitVec.add_zero]
      simp only [off, BitVec.ofNat_add_ofNat]; congr 1; omega_using []) (by decide))
    fun s₁ ⟨⟨a16, a14, a17, m1⟩, k1⟩ => ?_)
  have N1 : 0 < 2 * L.pl + L.ql := by omega_using [hql]
  refine WP.seq (WP.mono (maskCopy_ok (c := c) N1 (by omega_using [hql, hpl]) (scr_prefix (ho.congr k1.wr) (by omega_using []))
      (fun i hi => by rw [k1.rd, k1.wr]; exact hk.rd i hi)
      (fun i hi y hy => hko i hi y (by omega_using [hy])) a14 a16 a17 ((k1.gpr .r20 (by decide)).trans h20))
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
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.pl) (by omega_using [hpl]) (by omega_using [hpl])
      (scr_sub (ho.congr k15.wr) (o := 2 * L.pl + L.ql) (n := L.pl) (by omega_using []) (by omega_using [hpl]))
      (fun i hi => by rw [k15.rd, k15.wr]; exact (ScrL.bufN hs hL (n := L.pl) (by omega_using [])).ld (show i + 1 ≤ L.pl by omega_using [hi]))
      (sep_part (by omega_using []) hT hbo) ((k5.gpr .r14 (by decide)).trans c14)
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
  refine WP.seq (WP.mono (maskCopy_ok (c := c) (N := L.ql) (by omega_using [hql]) (by omega_using [hql])
      (scr_sub (ho.congr k18.wr) (o := 3 * L.pl + L.ql) (n := L.ql) (by omega_using []) (by omega_using [hql]))
      (fun i hi => by rw [k18.rd, k18.wr]; exact hx.rd i hi)
      (sep_part (by omega_using []) hT hxo) ((k8.gpr .r14 (by decide)).trans e14)
      (by rw [(k7.trans k8).gpr .r16 (by decide), d16, off_off]; congr 1; omega_using []) e17
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
    have := outside_shift (B := out) (a := 2 * L.pl + L.ql) o6 (by omega_using [hql, hpl]) (by omega_using [hql, hpl])
    rwa [Nat.add_zero] at this
  have o9' : Outside out (3 * L.pl + L.ql) L.ql s₆.mem s₉.mem := by
    have := outside_shift (B := out) (a := 3 * L.pl + L.ql) o9 (by omega_using [hql, hpl]) (by omega_using [hql, hpl])
    rwa [Nat.add_zero] at this
  -- The sources, unchanged.
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s.mem L.Buf L.pl :=
    bytes_kept o2 fun i hi y hy => hbo i hi y (by omega_using [hy])
  have ex : Spec.Rsa.bytesAt s₆.mem x L.ql = Spec.Rsa.bytesAt s.mem x L.ql :=
    bytes_kept ((o2.mono (n' := 3 * L.pl + L.ql) (Nat.le_refl _) (by omega_using [])).trans
      (o6'.mono (Nat.zero_le _) (by omega_using []))) fun i hi y hy => hxo i hi y (by omega_using [hy])
  rw [eb] at v6
  rw [ex] at v9
  refine ⟨⟨?_, ((o2.mono (n' := 3 * L.pl + 2 * L.ql) (Nat.le_refl _) (by omega_using [])).trans (o6'.mono (Nat.zero_le _) (by omega_using []))).trans
      (o9'.mono (Nat.zero_le _) (by omega_using [])), t3⟩, kall.mono (by decide)⟩
  -- The three parts of `out`.
  rw [show 3 * L.pl + 2 * L.ql = 2 * L.pl + L.ql + L.pl + L.ql by omega_using [], bytesAt_add, bytesAt_add]
  have p1 : Spec.Rsa.bytesAt s₉.mem out (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₂.mem out (2 * L.pl + L.ql) := by
    have e1 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o9' (Or.inl (by omega_using [])) (by omega_using [hql, hpl])
    have e2 := part_kept (a := 0) (k := 2 * L.pl + L.ql) o6' (Or.inl (by omega_using [])) (by omega_using [hql, hpl])
    simp only [off, BitVec.add_zero] at e1 e2
    rw [e1, e2]
  have p2 : Spec.Rsa.bytesAt s₉.mem (off out (2 * L.pl + L.ql)) L.pl =
      Spec.Rsa.bytesAt s₆.mem (off out (2 * L.pl + L.ql)) L.pl :=
    part_kept o9' (Or.inl (by omega_using [])) (by omega_using [hql, hpl])
  rw [p1, p2, v2, v6, show 2 * L.pl + L.ql + L.pl = 3 * L.pl + L.ql by omega_using [], v9]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
    congr 1; omega_using []
  · simp only [↓reduceIte, List.append_assoc]

end VG.Proof.Dsa.PPC64LE

end

end


/-!
# DSA key derivation on PPC64LE: after the check of the domain

`dbody_ok`: `Derive.body` writes to `out` the domain's octets, then
`y = g^x mod p`'s `p_len` octets and x's `q_len` octets, and leaves 1 in
`r3`, exactly when `1 < y` and `0 < x < q`; else zeros and 0. Memory changes
only in `scratch` past its header and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The checks of derivation past the domain's, for `y = g^x mod p`. -/
def DeriveOk (p q g x : Nat) : Prop := 1 < g ^ x % p ∧ 0 < x ∧ x < q

instance (p q g x : Nat) : Decidable (DeriveOk p q g x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The registers `Derive.body` writes. -/
def dbodyRegs : List Reg := yValueRegs ++ xRangeRegs ++ doutputRegs

theorem dbody_ok {s₀ s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hP : ParamsOk s₀.mem L key)
    (hc : Checked s₀ s L key x out 0) (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (2 * L.pl + L.ql))
    (hx : Src s L x L.ql) (ho : Scr s out (3 * L.pl + 2 * L.ql)) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) =
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then
            Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) ++
              Spec.Dsa.encodeBE L.pl (gOf s₀.mem L key ^ kOf s₀.mem L x % pOf s₀.mem L key) ++
              Spec.Rsa.bytesAt s₀.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        t.gpr .r3 = BitVec.ofNat 64
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (3 * L.pl + 2 * L.ql) m t.mem) ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧
        Keep dbodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw8 := hL.wp_eq
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, -⟩ := hc
  obtain ⟨-, -, eg⟩ := params_kept hk hkp.out
  have ex : kOf s.mem L x = kOf s₀.mem L x := by simp only [kOf]; rw [hx.kept hkp.out]
  have ekey : Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) :=
    hk.kept hkp.out
  have exb : Spec.Rsa.bytesAt s.mem x L.ql = Spec.Rsa.bytesAt s₀.mem x L.ql := hx.kept hkp.out
  have B := VG.Proof.Dsa.supported_bounds hP.1.1
  have hpo := hP.1.2.2
  have hplt : pOf s₀.mem L key < 256 ^ L.pl := by
    have := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s₀.mem key L.pl)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at p0 p8 B hpo hplt
  generalize qOf s₀.mem L key = q at q0 B
  generalize gOf s₀.mem L key = g at eg
  unfold body
  -- y.
  refine WP.seq (WP.mono (yValue_ok hL scr regs ip hk hx p0 (by omega_using [B]) hpo p8) fun s₁ ⟨⟨vy, my, ip1, b1, oq1⟩, k1⟩ => ?_)
  rw [eg, ex] at vy my
  generalize hy : g ^ kOf s₀.mem L x % p = y at vy my
  have hyp : y < p := by rw [← hy]; exact Nat.mod_lt _ (by omega_using [hpo])
  have hr1 := regs.keep k1
  -- x's range.
  refine WP.seq (WP.mono (xRange_ok hL (scr.congr k1.wr) hr1 (hx.keep k1.rd k1.wr) my) fun s₂ ⟨⟨m2, Q2, qa2⟩, k2⟩ => ?_)
  have aq : arrQ s₁.mem L 0 = q := by
    rw [← q0]
    exact Outside.val32 oq1 (Or.inl (by simp only [slot_eq]; omega_using [])) (by simp only [slot_eq]; omega_using [])
  have ex1 : kOf s₁.mem L x = kOf s₀.mem L x := by
    rw [kOf, kOf, hx.kept (Kept.ofBody hL b1).out, exb]
  rw [aq, ex1] at m2
  -- The output.
  have b12 : Body L s.mem s₂.mem := b1.trans (qa2.qbody.body hL)
  have k12 := k1.trans k2
  refine WP.mono (doutput_ok hL Q2.scr Q2.regs m2 (hk.keep k12.rd k12.wr) (hx.keep k12.rd k12.wr)
    (ho.congr k12.wr) (hos.keep k12.rd k12.wr) hko hxo) fun t ⟨⟨vt, ot, t3⟩, kt⟩ => ?_
  have hD : DeriveOk p q g (kOf s₀.mem L x) = (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    unfold DeriveOk; rw [hy]
  have hc : (decide (y ≠ 0) && decide (y ≠ 1) && decide (0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q)) =
      decide (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1] <;> omega_using [h0, h1]
  rw [hc] at vt t3
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Dsa.encodeBE L.pl y := by
    have hb : L.Buf = off L.Q 1600 := by simp only [Lay.Buf, Lay.Q, Lay.bOff, off_off]
    have hb2 : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s₁.mem L.Buf L.pl := by
      rw [hb]; exact part_kept qa2 (Or.inr (by simp only [slot_eq]; omega_using [])) (by omega_using [hpl])
    rw [hb2]
    exact ((VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) (by omega_using [hplt, hyp])).mpr vy.symm).symm
  have kall := k12.trans kt
  have K2 := Kept.ofBody hL b12
  rw [eb, hk.kept K2.out, hx.kept K2.out, ekey, exb] at vt
  simp only [decide_eq_true_eq] at vt t3
  simp only [hD]
  exact ⟨⟨vt, t3, ⟨s₂.mem, K2, ot⟩, (kall.gpr .r21 (by decide)).trans regs.r21, scr.congr kall.wr⟩,
    kall.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
