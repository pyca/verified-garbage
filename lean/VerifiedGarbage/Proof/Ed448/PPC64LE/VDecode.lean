module

import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecodeCheck
public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VSel
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseEncode
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseSel
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VChecks
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseBits
import VerifiedGarbage.Proof.X448.PPC64LE.Setup
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecodeY

/-! ### `Ed448.PPC64LE.VDecodeNeg`, which only this module used -/

section

/-!
# Ed448's verification on PPC64LE: the negated point

`decodeNeg xo yo` writes `-x'` to `xo` and `y` to `yo`, for `x'` the decoded
x-coordinate: `(x - x) - x` if the low bit of `x` (fully reduced at `OUT`) is
the sign, else `x` (`decodeNeg_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (X2 Y ACC)
open VG.Spec.X448 (P Fe)

section
variable {b : Addr}

theorem xor_le_one' {x y : Nat} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with rfl | rfl <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with rfl | rfl <;> decide

/-- The slots of `-x'` and `y`, above the field area and below `PK`. -/
def NegOut (xo yo : Nat) : Prop :=
  1064 ≤ xo ∧ xo + 56 ≤ PK ∧ 1064 ≤ yo ∧ yo + 56 ≤ PK ∧ (xo + 56 ≤ yo ∨ yo + 56 ≤ xo)

theorem decodeNeg_ok {s : State} (hc : VCtx b s) {xo yo : Nat} (ho : NegOut xo yo) {x y : Fe}
    (hx : FS s.mem b DXX = x) (hy : FS s.mem b DY = y)
    (hout : VG.Spec.X448.bytesAt s.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 x.val)
    {sg : Nat} (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa (.block (decodeNeg xo yo)) s fun t => VCtx b t ∧ Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩] s.mem t.mem ∧
      FS t.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x ∧ FS t.mem b yo = y ∧
      FS t.mem b DK = FS s.mem b DK := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  obtain ⟨hx1, hx2, hy1, hy2, hxy⟩ := ho
  have hPK : PK = 3288 := rfl
  have hDY : DY = 168 := rfl
  have hA := ACC_eq
  unfold decodeNeg
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS0 : SlotsOk s.mem b [DXX, DY, DK] (FS s.mem b) := fun _ _ => rfl
  refine WP.append (subS (o := DTMP) (x := DXX) (y := DXX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    hc.ctx hS0) fun s1 ⟨hr1, hf1, hS1⟩ => ?_
  have hc1 : VCtx b s1 := hc.of_rest hr1 (by decide) (by decide)
  refine WP.append (subS (o := DNEG) (x := DTMP) (y := DXX) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    hc1.ctx hS1) fun s2 ⟨hr2, hf2, hS2⟩ => ?_
  have hc2 : VCtx b s2 := hc1.of_rest hr2 (by decide) (by decide)
  have hf12 : Frame [FA b] s.mem s2.mem := hf1.trans hf2
  -- The mask: the low bit of `x` against the sign.
  have hb2 : s2.mem (b + BitVec.ofNat 64 OUT) = BitVec.ofNat 8 x.val := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := OUT) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact byte0 hout
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [hf12 _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) h]
    exact hs
  refine wp_lbz (a := b + BitVec.ofNat 64 OUT) (by decide) (by decide) (by rw [hc2.r3, BitVec.add_zero])
    (by rw [← BitVec.add_zero (b + BitVec.ofNat 64 OUT)]; exact (by rw [Offset.add_add]; exact hc2.inR (by omega_arith)))
    fun s3 u3 => wp_li (by decide) fun s4 u4 => wp_and fun s5 u5 => ?_
  refine wp_lbz (a := b + BitVec.ofNat 64 SIGN) (by decide) (by omega_arith)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), hc2.ctx.r6])
    (by rw [u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr]; exact hc2.inR (by omega_arith)) fun s6 u6 => wp_xor fun s7 u7 => ?_
  refine wp_li (by decide) fun s8 u8 => wp_sub fun s9 u9 => ?_
  have hm9 : s9.mem = s2.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
  have hr9 : Rest [.r7, .r8, .r9, .r11] s2 s9 := (u3.rest (by decide)).trans ((u4.rest (by decide)).trans
    ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans
      ((u8.rest (by decide)).trans (u9.rest (by decide)))))))
  have hc9 : VCtx b s9 := hc2.of_rest hr9 (by decide) (by decide)
  have hsg' : sg < 2 ^ 64 := by omega_arith
  have hm : x.val % 2 ^^^ sg ≤ 1 := xor_le_one' (by omega_arith) hsg
  have e5 : (s5.gpr .r8).toNat = x.val % 2 := by
    rw [u5.gpr, BitVec.toNat_and, u4.other _ (by decide), u4.gpr, u3.gpr, hb2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.and_one_is_mod]
    omega_arith
  have e6 : (s6.gpr .r7).toNat = sg := by
    rw [u6.gpr, u5.mem, u4.mem, u3.mem, hs2]
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    omega_arith
  have e7 : s7.gpr .r8 = BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    apply BitVec.eq_of_toNat_eq
    rw [u7.gpr, BitVec.toNat_xor, u6.other _ (by decide), e5, e6, toNat_imm (by omega_arith)]
  have e11 : s9.gpr .r11 = 0 - BitVec.ofNat 64 (x.val % 2 ^^^ sg) := by
    rw [u9.gpr, u8.gpr, u8.other _ (by decide), e7]; rfl
  -- The selections.
  refine WP.append (sel_ok (b := b) (o := xo) (q := DNEG) (r := DXX) (by omega_arith) (by decide) (by decide)
    (by unfold DNEG; omega_arith) (by unfold DXX; omega_arith) hc9.ctx hm e11) fun s10 h10 => ?_
  have hc10 : VCtx b s10 := hc9.of_rest h10.rest (by decide) (by decide)
  refine WP.mono (sel_ok (b := b) (o := yo) (q := DY) (r := DY) (by omega_arith) (by decide) (by decide)
    (by unfold DY; omega_arith) (by unfold DY; omega_arith) hc10.ctx hm (by rw [h10.rest.gpr _ (by decide), e11]))
    fun t ht => ?_
  have hrt : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s t :=
    (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans ((hr9.mono (by decide)).trans
      ((h10.rest.mono (by decide)).trans (ht.rest.mono (by decide)))))
  -- The values.
  have v2 : ∀ q ∈ [DNEG, DXX, DY, DK], FS s2.mem b q = upd (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX))
      DNEG (upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DTMP -
        upd (FS s.mem b) DTMP (FS s.mem b DXX - FS s.mem b DXX) DXX) q := fun q hq => hS2 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl | rfl | rfl <;> decide)
  have hx' : FS s.mem b 672 = x := hx
  have hy' : FS s.mem b 168 = y := hy
  have eN : FS s2.mem b DNEG = (x - x) - x := by
    rw [v2 DNEG (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eX : FS s2.mem b DXX = x := by
    rw [v2 DXX (by simp)]; simp only [upd, DNEG, DTMP, DXX, Nat.reduceEqDiff, ↓reduceIte, hx']
  have eY : FS s2.mem b DY = y := by
    rw [v2 DY (by simp)]; simp only [upd, DNEG, DTMP, DY, Nat.reduceEqDiff, ↓reduceIte, hy']
  have hxo : FS s10.mem b xo = pick (x.val % 2 ^^^ sg) ((x - x) - x) x := by
    rw [fs_pick hm h10.lo, hm9, eN, eX]
  have eK : FS s2.mem b DK = FS s.mem b DK := by
    rw [v2 DK (by simp)]; simp only [upd, DNEG, DTMP, DK, Nat.reduceEqDiff, ↓reduceIte]
  refine ⟨hc.of_rest hrt (by decide) (by decide), hrt, ?_, ?_, ?_, ?_⟩
  · refine (hf12.mono (by simp)).trans ?_
    rw [← hm9]
    exact (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  · -- `xo` is kept by the write of `yo`.
    rw [← hxo]
    have e := limb_frame (o := xo) ht.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := xo + 4 * k) (n := 4) (e := yo) (k := 4 * 14) (by omega_arith) (by omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl
  · -- `y`, kept by the write of `xo`.
    rw [fs_pick hm ht.lo]
    have e := limb_frame (o := DY) h10.frame fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by unfold DY; omega_arith) (by omega_arith) (by omega_arith)
    rw [show FS s10.mem b DY = FS s9.mem b DY by rw [FS, V, val32_congr e]; rfl, hm9, eY]
    unfold pick X25519.PPC64LE.sel; split <;> rfl

  · -- `d`, kept by both writes.
    rw [← eK, ← hm9]
    have f : Frame [⟨b + BitVec.ofNat 64 xo, 4 * 14⟩, ⟨b + BitVec.ofNat 64 yo, 4 * 14⟩] s9.mem t.mem :=
      (h10.frame.mono (by simp)).trans (ht.frame.mono (by simp))
    have e := limb_frame (o := DK) f fun r hr k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by unfold DK; omega_arith) (by unfold DK; omega_arith) (by omega_arith)
    rw [FS, V, val32_congr e]; rfl

end

end VG.Proof.Ed448.PPC64LE

end

end

/-! ### `Ed448.PPC64LE.VDecodeX`, which only this module used -/

section

/-! ### `Ed448.PPC64LE.VRoot`, which only this module used -/

section

/-!
# Ed448 on PPC64LE: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2` by
square-and-multiply over the bits of `(p - 3) / 4` from 445 down to 0
(`rootQ_ok`), as X448's inversion computes `z^(p-2)`
(`Proof/X448/PPC64LE/Invert.lean`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (R Z2 one)
open VG.Spec.X448 (P Fe)

/-! ## The bits of `(p - 3) / 4` -/

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

def rbitsB : Nat → Bool
  | 0 => true
  | t + 1 => (RE >>> t % 2 == if t = 222 then 0 else 1) && rbitsB t

theorem rbitsB_ok : rbitsB 446 = true := by decide +kernel

/-- Every bit of `RE = 2⁴⁴⁶ - 2²²² - 1` below 446 but bit 222 is 1. -/
theorem rbits : ∀ t < 446, RE >>> t % 2 = if t = 222 then 0 else 1 := by
  have : ∀ n, rbitsB n = true → ∀ t < n, RE >>> t % 2 = if t = 222 then 0 else 1 := by
    intro n; induction n with
    | zero => intro _ t ht; omega_using [ht]
    | succ n ih =>
      intro h t ht
      simp only [rbitsB, Bool.and_eq_true, beq_iff_eq] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
      · exact ih h.2 t ht
      · exact h.1
  exact this 446 rbitsB_ok

theorem r446 : RE >>> 446 = 0 := by decide +kernel

section
variable {b : Addr}

/-- `z^(((p - 3) / 4) >> n)` in `R`, for `z` at `Z2`. -/
def rootV (v : Nat → Fe) (n : Nat) : Nat → Fe := upd v R (VG.Proof.X448.pw (v Z2) (RE >>> n))

/-- The loop invariant of `root` from `sI`, before the step for the bit `n - 1`. -/
structure RootInv (b : Addr) (sI : State) (a : BitVec 64) (qs : List Nat) (v : Nat → Fe) (n : Nat)
    (s : State) : Prop where
  cur : Cur b sI a (BitVec.ofNat 64 n) qs (rootV v n) s

theorem rootStep_ok {sI : State} {a : BitVec 64} {qs : List Nat} (hq : Sep1 R qs = true) (hR : R ∈ qs)
    (hZ : Z2 ∈ qs) {v : Nat → Fe} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 446)
    {s : State} (h : RootInv b sI a qs v n s) :
    WP isa rootStep s fun s' => RootInv b sI a qs v (n - 1) s' ∧ (s'.gpr .r12 != 0) = decide (n - 1 ≠ 0) := by
  obtain ⟨hcur⟩ := h
  have hb := rbits (n - 1) (by omega_using [hn'])
  have he := shr_step RE (n - 1)
  rw [Nat.sub_add_cancel hn] at he
  unfold rootStep
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have h1 : Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v n) s1 := by
    refine ⟨hcur.ctx.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide),
      hcur.stp.trans (Stp.of_rest (u1.rest (ws := [.r12]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), hcur.r0], ?_, by rw [u1.mem]; exact hcur.slots⟩
    rw [u1.gpr, hcur.r12, ofNat_sub_one hn (by omega_using [hn'])]
  refine WP.seq (WP.mono (opMul (o := R) (x := R) (y := R) hq (by decide) hR hR (by decide) (by decide) (by decide) h1)
    fun s2 h2 => ?_)
  have hsq : ∀ q ∈ qs, upd (rootV v n) R (rootV v n R * rootV v n R) q =
      upd v R (VG.Proof.X448.pw (v Z2) (2 * (RE >>> n))) q := by
    intro q _
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, upd_self, Nat.two_mul, ← VG.Proof.X448.pw_mul]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq, upd_of_ne _ _ hq]
  have h2' := h2.congr (qs' := qs) (fun q hq' => List.mem_cons_of_mem _ hq') hsq
  refine WP.seq (WP.mono (cmp_ok (d := 222) (by omega_using [hn']) (by decide) h2') fun s3 ⟨h3, hz3⟩ => ?_)
  refine WP.mono (Q := Cur b sI a (BitVec.ofNat 64 (n - 1)) qs (rootV v (n - 1))) ?_ fun s4 h4 =>
    ⟨⟨h4⟩, by rw [h4.r12, ofNat_ne_zero (by omega_using [hn'])]⟩
  refine WP.ite _ hz3 (fun ht => WP.block_nil (h3.congr (fun q hq => hq) fun q _ => ?_)) (fun hf => ?_)
  · have h4 : n - 1 = 222 := by simpa using ht
    by_cases hq : q = R
    · subst hq; rw [upd_self, rootV, upd_self, he, hb, iteT h4, Nat.add_zero]
    · rw [upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]
  · have h4 : n - 1 ≠ 222 := by simpa using hf
    refine WP.mono (opMul (o := R) (x := R) (y := Z2) hq (by decide) hR hZ (by decide) (by decide) (by decide) h3)
      fun s5 h5 => h5.congr (fun q hq' => List.mem_cons_of_mem _ hq') fun q _ => ?_
    by_cases hq : q = R
    · subst hq
      rw [upd_self, upd_self, upd_of_ne _ _ (by decide : Z2 ≠ R), rootV, upd_self, he, hb,
        iteF h4, ← VG.Proof.X448.pw_mul, VG.Proof.X448.pw_one]
    · rw [upd_of_ne _ _ hq, upd_of_ne _ _ hq, rootV, upd_of_ne _ _ hq]

theorem rootQ_ok {qs : List Nat} (hq : Sep1 R qs = true) (hR' : R ∈ qs) (hZ : Z2 ∈ qs)
    {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .r0 = a) :
    WP isa root s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (RE))) := by
  have hR : R = 840 := rfl
  unfold root
  refine WP.seq ?_
  simp only [one, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r4, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  refine sw0_ok hc2 (d := R) (by decide) fun s3 u3 => ?_
  refine WP.append (stores_ok (o := R + 4) (n := 13) (by decide) (hc2.of_rest (u3.rest []) (by decide)))
    fun s4 ⟨h4w, h4f, h4g, h4r⟩ => ?_
  refine wp_li (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r4, .r5, .r12] s s5 :=
    (hr2.mono (by decide)).trans ((u3.rest _).trans ((h4r.mono (by decide)).trans (u5.rest (by decide))))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  -- The limbs of `R`: 1, then zeros.
  have hlimb : ∀ k < 14, limb s5.mem b R k = if k = 0 then 1 else 0 := by
    intro k hk
    rw [limb, u5.mem]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_frame h4f fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide),
        u3.mem, wd_write_self, toNat_lo32, u2.other _ (by decide), u1.gpr]; rfl
    · have := h4w (k - 1) (by omega_using [hk])
      rw [show R + 4 + 4 * (k - 1) = R + 4 * k by omega_using [hk0], u3.gpr, u2.gpr] at this
      rw [this]; simp only [show k ≠ 0 by omega_using [hk0], ite_false]; rfl
  have hf5 : Frame [⟨b + BitVec.ofNat 64 R, 56⟩] s.mem s5.mem := by
    rw [u5.mem, ← hm2]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) ((s2.gpr .r4).setWidth 32)
      (Offset.contains b (d := R) (n := 32 / 8) (e := R) (k := 56) (Nat.le_refl _) (by decide)
        (by decide))).trans ?_
    rw [← u3.mem]
    exact h4f.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  have hst5 : Stp b s s5 := ⟨hr5.mono (by decide), hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩⟩
  have hS5 : SlotsOk s5.mem b qs (rootV v 446) := by
    have hA := ACC_eq
    intro q hq'
    by_cases hqR : q = R
    · subst hqR
      rw [FS, V, val32_congr hlimb, rootV, upd_self, r446, pw_zero, val32_single _ (by decide)]
      rfl
    · obtain ⟨h1, h3⟩ := sep1_get hq hq'
      have e := limb_frame (o := q) hf5 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (by omega_using [hqR, h1, hk]) (by omega_using [hA, h3, hk]) (by omega_using [hR])
      rw [FS, V, val32_congr e, rootV, upd_of_ne _ _ hqR]; exact hS q hq' hqR
  have h446 : RootInv b s5 a qs v 446 s5 :=
    ⟨⟨hc5, Stp.refl _ _, by rw [hr5.gpr _ (by decide), h0], u5.gpr, hS5⟩⟩
  refine WP.mono (Q := RootInv b s5 a qs v 0) (WP.loop (M := isa)
    (fun m s' => 1 ≤ m ∧ m ≤ 446 ∧ RootInv b s5 a qs v m s') ?_ 446 s5 ⟨by decide, Nat.le_refl _, h446⟩)
    fun s' ⟨h'⟩ => ⟨hst5.trans h'.stp, h'.ctx, h'.slots.congr fun q _ => by
      simp only [rootV, Nat.shiftRight_zero]⟩
  rintro m s' ⟨h1, h2, hl⟩
  refine WP.mono (rootStep_ok hq hR' hZ h1 h2 hl) fun s'' ⟨hl', hz⟩ => ?_
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega_using [hm], by omega_using [hm], by omega_using [h2], hl'⟩


end

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# Ed448's verification on PPC64LE: the candidate x-coordinate

`decodeX` computes, from `y` at `DY`, `1` at `DON` and `d` at `DK`,
`u = y² - 1` (at `DU`), `v = d y² - 1` (at `DV`), `t = u³v` (at `DT`) and
`x = t (t (uv)²)^((p-3)/4)` (at `DXX`) (`decodeX_ok`), as `recoverRef` has
them.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Impl.X448.PPC64LE (R Z2)
open VG.Spec.X448 (P Fe)

/-- The field operations of `decodeX` before the power. -/
def xOps : List FOp :=
  [.mul DYY DY DY, .sub DU DYY DON, .mul DV DK DYY, .sub DV DV DON, .mul DT DU DU, .mul DT DT DU,
    .mul DT DT DV, .mul DW DU DV, .mul DW DW DW, .mul Z2 DT DW]

theorem decodeX_eq : decodeX = opsCode xOps (.seq root (Impl.X448.PPC64LE.mul DXX DT R)) := rfl

/-- The slots `decodeX` reads, and `R` and `Z2`. -/
def XQ : List Nat := [DY, DON, DK, R, Z2]

theorem xOps_ok : opsOk xOps XQ = true := by decide

/-- `u`, `v`, `t` and the candidate `x` for `y`. -/
def uOf (y : Fe) : Fe := y * y - 1
def vOf (y : Fe) : Fe := Spec.Ed448.d * (y * y) - 1
def tOf (y : Fe) : Fe := uOf y * uOf y * uOf y * vOf y
def xOf (y : Fe) : Fe :=
  tOf y * VG.Proof.X448.pw (tOf y * ((uOf y * vOf y) * (uOf y * vOf y))) RE

section
variable {b : Addr}

theorem decodeX_ok {s : State} (hc : Ctx b s) {y : Fe} (hy : FS s.mem b DY = y) (hon : FS s.mem b DON = 1)
    (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa decodeX s fun t => Stp b s t ∧ Ctx b t ∧ FS t.mem b DXX = xOf y ∧ FS t.mem b DV = vOf y ∧
      FS t.mem b DU = uOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d := by
  have hy' : FS s.mem b 168 = y := hy
  have hon' : FS s.mem b 224 = 1 := hon
  have hd' : FS s.mem b 336 = Spec.Ed448.d := hd
  have h0 : Cur b s (s.gpr .r0) (s.gpr .r12) XQ (FS s.mem b) s := ⟨hc, Stp.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  rw [decodeX_eq]
  refine ops_ok xOps XQ _ s xOps_ok h0 fun s1 h1 => ?_
  refine WP.seq (WP.mono (rootQ_ok (qs := outsQ xOps XQ) (by decide) (by decide) (by decide) h1.ctx
    (fun q hq _ => h1.slots q hq) h1.r0) fun s2 ⟨hst2, hc2, hS2⟩ => ?_)
  refine WP.mono (mulS (o := DXX) (x := DT) (y := R) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hc2 hS2)
    fun t ⟨hrt, hft, hSt⟩ => ?_
  refine ⟨h1.stp.trans (hst2.trans ⟨hrt.mono (by decide), hft⟩), hc2.of_rest hrt (by decide), ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | rw [hSt DXX (by decide)] | rw [hSt DV (by decide)] | rw [hSt DU (by decide)]
    | rw [hSt DY (by decide)] | rw [hSt DK (by decide)]
  all_goals
    simp only [upd, runOps, xOps, FOp.out, FOp.val, DXX, DT, DV, DU, DY, DK, DW, DYY, DON, R, Z2,
      Nat.reduceEqDiff, ↓reduceIte, hy', hon', hd', xOf, tOf, uOf, vOf]
end

end VG.Proof.Ed448.PPC64LE

end

end


/-!
# Ed448's verification on PPC64LE: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (X2 Y ACC)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

theorem fin_neg_neg {n : Nat} [NeZero n] (x : Fin n) : 0 - (0 - x) = x := by grind

theorem fin_neg_sub {n : Nat} [NeZero n] (x : Fin n) : (x - x) - x = 0 - x := by rw [Fin.sub_self]

/-- The negation of the decoded x-coordinate, as `decodeNeg` selects it. -/
theorem neg_pick (x : Fe) {sg : Nat} (hsg : sg ≤ 1) :
    pick (x.val % 2 ^^^ sg) ((x - x) - x) x =
      0 - (if (x.val % 2 == 1) == (sg == 1) then x else (x - x) - x) := by
  rw [fin_neg_sub]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl <;>
    simp only [h, pick, X25519.PPC64LE.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeX (.seq decodeCheck (.block (decodeNeg xo yo)))) := rfl

/-- The 57 bytes at `p` in terms of the words and the last byte. -/
theorem bytes57 (m : Mem) (p : Nat) :
    Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).take 56) = yw m b p ∧
      ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).getD 56 0).toNat =
        (m (b + BitVec.ofNat 64 (p + 56))).toNat := by
  constructor
  · rw [show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
      List.take_left' (by simp [Spec.X25519.bytesAt]), Proof.Ed448.decodeLE_eq, show (56 : Nat) = 4 * 14 from rfl]
    rw [show Spec.X25519.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) =
      VG.Spec.X448.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) from rfl, leNum_bytesAt4]
    exact val32_congr fun k _ => wd_shift _ _ _ _
  · rw [getD_bytesAt _ _ (by decide), Offset.add_add]

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 3520) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp') fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  have hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  have hsg : B / 128 ≤ 1 := by omega_using [hB]
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  have hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  have hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeX_ok hc1.ctx hy hon (hk1.trans hd))
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  have hc2 : VCtx b s2 := hc1.of_rest hst2.rest (by decide) (by decide)
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 (B / 128) := by
    rw [← hs1]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.seq (WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_)
  have hb2 : bad s2.mem b = bad s1.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  refine WP.mono (decodeNeg_ok hc3 ho (x := xOf y) (y := y) (by rw [hk3 DXX (by simp), hx2])
    (by rw [hk3 DY (by simp), hy2]) hout3 hsg (by rw [hs3, hs2])) fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := ho
  have hPK : PK = 3288 := rfl
  obtain ⟨o1, o2, o3, o4⟩ := offs
  -- The code's view of `decodePoint`.
  obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem p
  rw [hB] at eB
  have hdp := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)
    (by simp [Spec.Ed448.bytesAt]) _ B e56 eB y (uOf y) (vOf y) (tOf y) (xOf y) hY rfl rfl rfl (by
      rw [xOf, Proof.Ed448.rootPow_eq, VG.Proof.X448.pow_pw]; rfl)
  have hbt : bad t.mem b = bad s3.mem b := by
    unfold bad
    rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      all_goals exact Offset.disjoint _ (by omega_arith) (by omega_using [o3]) (by omega_arith)) (by decide)]
  refine ⟨hct, hr1.mono (by decide) |>.trans (hst2.rest.trans (hr3.trans (hrt.mono (by decide)))), ?_,
    by rw [hkt, hk3 DK (by simp), hd2], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hst2.frame.mono (by simp [decW])).trans ((hf3.mono (by simp [decW])).trans
      (hft.mono ?_)))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb2, hb1, hdp]
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC, Option.isSome_some]
      exact ⟨fun h => ⟨h.1.1, rfl⟩, fun h => ⟨⟨h.1, hC.1.2, hC.1.1⟩, hC.2⟩⟩
    · rw [ite_eq_right hC, Option.isSome_none]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => absurd ⟨⟨h3, h2⟩, h4⟩ hC, fun h => absurd h.2 (by decide)⟩
  · intro pt hpt
    rw [hdp] at hpt
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC] at hpt
      cases Option.some.inj hpt
      exact ⟨by rw [hxt, neg_pick _ hsg], hyt, rfl⟩
    · rw [ite_eq_right hC] at hpt
      exact absurd hpt (by simp)

end

end VG.Proof.Ed448.PPC64LE
