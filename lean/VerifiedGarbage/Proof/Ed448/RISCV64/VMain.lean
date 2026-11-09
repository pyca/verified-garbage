module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VSetup
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecode
public import VerifiedGarbage.Proof.Ed448.RISCV64.VJoint
import VerifiedGarbage.Proof.Ed448.RISCV64.VCheckScalar
import VerifiedGarbage.Proof.Ed448.RISCV64.VFinish
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeY
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# Ed448's verification equation on RISCV64: the whole function

`vg_ed448_verify_equation` returns 1 exactly when `verifyEquation` holds
(`verifyEquation_correct`), given that `recoverX` is `recoverRef`
(`RecoverOk`, proven in `Proof/Ed448/Facts.lean` and passed in by the
registration): with `-A` and `-R` decoded, `S` checked, the digits of `S`
and `k` recoded and the two tables built, the joint loop leaves `Q`
representing `[S]B + [k](-A)` (`joint_ok`); `[4](Q + (-R))` is the neutral
point exactly when `[4]Q = [4]R`, the equation (`neutral_eq`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)
open VG.Proof.Ed25519.RISCV64 (base)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Impl.Ed448.WnafWide (digitAt residual)

/-! ## The equation -/

theorem pointEqual_identity (q : Point) :
    Spec.Ed448.pointEqual q Spec.Ed448.identity = (decide (q.X = 0) && decide (q.Y = q.Z)) := by
  simp only [Spec.Ed448.pointEqual, Spec.Ed448.identity, Fin.mul_one, Fin.zero_mul, Fin.one_mul]
  rfl

/-- `[4](Q + (-R))` is neutral exactly when the equation holds, for `Q = [S]B + [k](-A)`. -/
theorem neutral_eq {pk sig ch : List Byte} (hl : pk.length = 57) (hs : sig.length = 114) (hc : ch.length = 57)
    {a r : Point} (ha : Spec.Ed448.decodePoint pk = some a) (hr : Spec.Ed448.decodePoint (sig.take 57) = some r)
    {Q : Point} (hQ : Rep Q (Spec.Ed448.decodeLE (sig.drop 57) • baseAff +
      Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a))) :
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual (Proof.Ed448.double (Proof.Ed448.double
          (Spec.Ed448.pointAdd Q (Proof.Ed448.negPoint r)))) Spec.Ed448.identity) := by
  have hR := Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hr)
  rw [Proof.Ed448.verifyEquation_some hl hs hc ha hr hQ hR]
  congr 1
  generalize Spec.Ed448.decodeLE (sig.drop 57) • baseAff + Spec.Ed448.decodeLE ch • (-Proof.Ed448.toAffine a) = x at hQ
  have h1 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hQ)
  have h2 := Proof.Ed448.double_rep (Proof.Ed448.double_rep hR)
  have h3 := Proof.Ed448.double_rep (Proof.Ed448.double_rep (Proof.Ed448.pointAdd_rep hQ hR.neg))
  rw [Bool.eq_iff_iff, Proof.Ed448.pointEqual_rep h1 h2, Proof.Ed448.pointEqual_rep h3 Proof.Ed448.identity_rep,
    Proof.Ed448.four_smul, Proof.Ed448.four_smul, Proof.Ed448.four_smul, smul_add, smul_neg, add_neg_eq_zero]

/-! ## The digits -/

theorem residual_tail {k : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) :
    ∀ n, 464 ≤ n → residual false k n = 0
  | n, h => by
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 464 with h' | h'
      · have e : n = 463 := by omega
        subst e
        exact residual_464 hk
      · show Impl.Ed448.WnafWide.next false (residual false k n) = 0
        rw [ih h']; rfl

theorem digit_tail {k n : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hn : 464 ≤ n) : digitAt false k n = 0 := by
  unfold digitAt; rw [residual_tail hk n hn]; rfl

theorem bit_tail {k i : Nat} (hk : k < Impl.Ed448.WnafWide.scalarLimit) (hi : 456 ≤ i) :
    Proof.Ed448.WnafWide.bit k i = 0 := by
  unfold Proof.Ed448.WnafWide.bit; rw [Proof.Ed448.WnafWide.tail_quotient hk hi]

/-- The bits written by `bitsOf`. -/
theorem tbSet_bit {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : tbSet 1 K (tbSet 0 S fun _ => 0) h =
      if h % 4 = 0 then Proof.Ed448.WnafWide.bit S (h / 4) else if h % 4 = 1 then Proof.Ed448.WnafWide.bit K (h / 4)
      else 0 := by
  unfold tbSet
  by_cases h0 : h % 4 = 0
  · rw [ite_eq_right (by omega), ite_eq_left h0]
    by_cases hi : h / 4 < 456
    · rw [ite_eq_left ⟨h0, hi⟩, Proof.Ed448.WnafWide.bit_shift]
    · rw [ite_eq_right (fun c => hi c.2), bit_tail hS (by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : h % 4 = 1
    · rw [ite_eq_left h1]
      by_cases hi : h / 4 < 456
      · rw [ite_eq_left ⟨h1, hi⟩, Proof.Ed448.WnafWide.bit_shift]
      · rw [ite_eq_right (fun c => hi c.2), ite_eq_right (by omega), bit_tail hK (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem dig_eq {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit) (hK : K < Impl.Ed448.WnafWide.scalarLimit)
    (h : Nat) : recCur 1 K (recCur 0 S (tbSet 1 K (tbSet 0 S fun _ => 0)) 464) 464 h = digV S K h := by
  unfold recCur digV
  rw [tbSet_bit hS hK]
  rcases (by omega : h % 4 = 0 ∨ h % 4 = 1 ∨ h % 4 = 2 ∨ h % 4 = 3) with e | e | e | e <;>
    simp only [e, Nat.reduceEqDiff, false_and, ite_false, ite_true, true_and, Nat.reduceAdd]
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hS (by omega)]; rfl
  · by_cases hn : h / 4 < 464
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn, digit_tail hK (by omega)]; rfl

section
variable {b : Addr}

/-! ## Frames -/

/-- An element whose slot is apart from a frame's regions stays. -/
theorem fs_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) :
    FS m' b q = FS m b q := fsD hf hd

theorem disj_decW {d n xo yo : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 1696) (hxo : d + n ≤ xo ∨ xo + 56 ≤ d)
    (hyo : d + n ≤ yo ∨ yo + 56 ≤ d) (hx : xo + 56 ≤ 2048) (hy : yo + 56 ≤ 2048) :
    ∀ r ∈ decW b xo yo, Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hRA : DECODE_RA = 1712 := rfl
  intro r hr
  simp only [decW, yW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  all_goals exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_FAB {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) (h3 : d + n ≤ 1696 ∨ 1704 ≤ d) :
    ∀ r ∈ [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem disj_one {d n e k : Nat} (h1 : d + n ≤ e ∨ e + k ≤ d) (h2 : d + n ≤ 8192) (h3 : e + k ≤ 8192) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 e, k⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ h1 (by omega) (by omega)

theorem disj_FA {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)

theorem disj_FAK {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3976) :
    ∀ r ∈ [FA b, KR b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by unfold ACC; omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by unfold KT; omega) (by omega) (by unfold KT; omega)

theorem bytes_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.take_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem bytes_drop (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem keyOk_BT {a : VG.Proof.EdwardsLaw.EPoint dZ} {m m' : Mem}
    (hf : Frame [⟨b + BitVec.ofNat 64 BT, 896⟩] m m') (h : KeyOk b a m) : KeyOk b a m' := fun i hi => by
  have hK : KT = 3976 := rfl
  have hB : BT = 5320 := rfl
  rw [kpt_keep hf fun o ho r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rw [List.mem_singleton.mp hr]
    rcases ho with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)]
  exact h i hi

theorem limit_of {bs : List Byte} (h : bs.length = 57) :
    Spec.Ed448.decodeLE bs < Impl.Ed448.WnafWide.scalarLimit := by
  have := Proof.Ed448.decodeLE_below h
  unfold Impl.Ed448.WnafWide.scalarLimit Impl.Ed448.WnafWide.pow2
  exact this

theorem bad_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 BAD, 8⟩ r) : bad m' b = bad m b := by
  unfold bad
  rw [hf.readW (Region.contains_self _ (64 / 8)) hd (by decide)]

/-- What the code before the joint loop leaves, for the inputs of `s`. -/
def PreOk (s u : State) : Prop :=
  VCtx (base (s.gpr .a3)) u ∧ u.sp = s.sp ∧
    JFix (base (s.gpr .a3)) (Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57))
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57)) u.mem ∧
    FS u.mem (base (s.gpr .a3)) DK = Spec.Ed448.d ∧
    (bad u.mem (base (s.gpr .a3)) = 0 ↔
      (Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57)).isSome ∧
      (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)).isSome ∧
      Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) < Spec.Ed448.L) ∧
    (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) = some a →
      KeyOk (base (s.gpr .a3)) (-Proof.Ed448.toAffine a) u.mem) ∧
    (∀ r, Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) = some r →
      FS u.mem (base (s.gpr .a3)) NRX = 0 - r.X ∧ FS u.mem (base (s.gpr .a3)) NRY = r.Y ∧ r.Z = 1)

theorem pre_run (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s fun u => PreOk s u ∧
    Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s u := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hTB : TB = 2104 := rfl
  have hKT : KT = 3976 := rfl
  have hBT : BT = 5320 := rfl
  have hSG : SG = 1516 := rfl
  have hSS : SGS = 1576 := rfl
  have hPK : PK = 1456 := rfl
  have hCH : CH = 1636 := rfl
  have hNAX : NAX = 1176 := rfl
  have hNAY : NAY = 1232 := rfl
  have hNRX : NRX = 1288 := rfl
  have hNRY : NRY = 1344 := rfl
  have hONE : ONE = 1400 := rfl
  have hDK : DK = 336 := rfl
  unfold PreOk
  generalize hb : base (s.gpr .a3) = b
  unfold vPrefix
  refine WP.seq (WP.mono (vSetup_ok hp) fun s1 ⟨hc1, hr1, hf1, ePK, eSG, eSS, eCH, hb1, hd1, hone⟩ => ?_)
  rw [hb] at hc1 ePK eSG eSS eCH hb1 hd1 hone
  refine WP.seq (WP.mono (decode_ok hR hc1 (p := SG) (by decide) (by decide) (by decide) (xo := NRX) (yo := NRY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd1)
    fun s2 ⟨hc2, hr2, hf2, hd2, hb2, hv2⟩ => ?_)
  refine WP.seq (WP.mono (decode_ok hR hc2 (p := PK) (by decide) (by decide) (by decide) (xo := NAX) (yo := NAY)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ hd2)
    fun s3 ⟨hc3, hr3, hf3, hd3, hb3, hv3⟩ => ?_)
  refine WP.seq (WP.mono (checkS_ok hc3) fun s4 ⟨hc4, hr4, hf4, hk4, hb4⟩ => ?_)
  refine WP.seq (WP.mono (bitsZero_ok hc4) fun s5 ⟨hc5, hr5, hf5, ht5⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc5 (src := SGS) (e := 0) (by decide) (by decide) (by decide) ht5)
    fun s6 ⟨hc6, hr6, hf6, ht6⟩ => ?_)
  refine WP.seq (WP.mono (bitsOf_ok hc6 (src := CH) (e := 1) (by decide) (by decide) (by decide) ht6)
    fun s7 ⟨hc7, hr7, hf7, ht7⟩ => ?_)
  -- What the digits' phases keep: everything below `TB`.
  have dTB : ∀ {d n : Nat}, d + n ≤ 2104 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 TB, 1872⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega)) (by omega) (by omega)
  -- The inputs, as the phases read them.
  have kA : Spec.Ed448.bytesAt s2.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57 := by
    rw [bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
      (by decide), ePK]
  have kR : Spec.Ed448.bytesAt s1.mem (b + BitVec.ofNat 64 SG) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57 := by rw [eSG, bytes_take]
  have kS3 : Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eSS, bytes_drop]
  have kS5 : Spec.Ed448.bytesAt s5.mem (b + BitVec.ofNat 64 SGS) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57 := by
    rw [bytes_keep hf5 (dTB (by omega)) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), kS3]
  have kK : Spec.Ed448.bytesAt s6.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57 := by
    rw [bytes_keep hf6 (dTB (by omega)) (by decide), bytes_keep hf5 (dTB (by omega)) (by decide),
      bytes_keep hf4 (disj_FAB (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      bytes_keep hf3 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide),
      bytes_keep hf2 (disj_decW (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) (by decide))
        (by decide), eCH]
  rw [kS5] at ht6 ht7
  rw [kK] at ht7
  have hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of hl5
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (recode_ok hc7 (e := 0) (k := S) (by decide) (fun i _ => by
      rw [tbSet_bit hSl hKl, ite_eq_left (by omega), show (4 * i + 0) / 4 = i by omega]) ht7)
    fun s8 ⟨hc8, hr8, hf8, ht8⟩ => ?_)
  refine WP.seq (WP.mono (recode_ok hc8 (e := 1) (k := K) (by decide) (fun i _ => by
      rw [recCur, ite_eq_right (by omega), tbSet_bit hSl hKl, ite_eq_right (by omega), ite_eq_left (by omega),
        show (4 * i + 1) / 4 = i by omega]) ht8)
    fun s9 ⟨hc9, hr9, hf9, ht9⟩ => ?_)
  have hdig : TbIs b s9.mem (digV S K) := fun h hh => by rw [ht9 h hh, dig_eq hSl hKl]
  -- The slots above the field area, from the checks to the digits.
  have k49 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s9.mem b q = FS s4.mem b q := fun h1 h2 => by
    rw [fs_disj hf9 (dTB (by omega)), fs_disj hf8 (dTB (by omega)), fs_disj hf7 (dTB (by omega)),
      fs_disj hf6 (dTB (by omega)), fs_disj hf5 (dTB (by omega))]
  have k34 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s4.mem b q = FS s3.mem b q := fun h1 h2 =>
    fs_disj hf4 (disj_FAB (by omega) (by omega) (by omega))
  have kFS1 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1176 ∨ 1400 ≤ q → q + 56 ≤ 1456 → FS s3.mem b q = FS s1.mem b q :=
    fun h1 h2 h3 => by
      rw [fs_disj hf3 (disj_decW (by omega_arith) (by omega_arith) (by unfold NAX; omega_arith)
          (by unfold NAY; omega_arith) (by decide) (by decide)),
        fs_disj hf2 (disj_decW (by omega_arith) (by omega_arith) (by unfold NRX; omega_arith)
          (by unfold NRY; omega_arith) (by decide) (by decide))]
  have kR3 : ∀ {q : Nat}, q = NRX ∨ q = NRY → FS s3.mem b q = FS s2.mem b q := fun h => by
    rcases h with rfl | rfl <;>
      exact fs_disj hf3 (disj_decW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `-A` and `d` before the tables.
  let A' : Point := ⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩
  have hpA : Pt s9.mem b NAX NAY ONE A' := ⟨rfl, rfl, rfl⟩
  have hd9 : FS s9.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf9 (dTB (by omega)), fs_disj hf8 (dTB (by omega)), fs_disj hf7 (dTB (by omega)),
      fs_disj hf6 (dTB (by omega)), fs_disj hf5 (dTB (by omega)), hk4, hd3]
  refine WP.seq (WP.mono (keyTable_ok hc9 hpA hd9) fun s10 hK10 => ?_)
  have hc10 : VCtx b s10 := hK10.1
  refine WP.mono (baseTable_ok hc10) fun s11 ⟨hc11, hr11, hf11, hB11⟩ => ?_
  have dBT : ∀ {d n : Nat}, d + n ≤ 5320 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 BT, 896⟩ : Region)],
      Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := fun h => disj_one (.inl (by omega)) (by omega) (by omega)
  have hfx : JFix b S K s11.mem := ⟨fun h hh => by
      have e1 := hf11 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact fun hc => (dBT (d := TB + h) (n := 1) (by omega) _ (List.mem_singleton_self _)) _
          (Region.contains_self _ _) hc
      have e2 := hK10.2.2.1 (b + BitVec.ofNat 64 (TB + h)) fun r hr => by
        exact fun hc => (disj_FAK (d := TB + h) (n := 1) (by omega) (by omega) r hr) _ (Region.contains_self _ _) hc
      rw [e1, e2]; exact hdig h hh, hB11⟩
  have hd11 : FS s11.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf11 (dBT (by omega))]; exact hK10.2.2.2.2.2.2.2.1
  have dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega) (by omega)
  have k911 : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s11.mem b q = FS s9.mem b q := fun h1 h2 => by
    rw [fs_disj hf11 (dBT (by omega)), fs_disj hK10.2.2.1 (disj_FAK (by omega) (by omega))]
  refine ⟨?_, (hr1.mono (by decide)).trans ((hr2.mono (by decide)).trans
    ((hr3.mono (by decide)).trans ((hr4.mono (by decide)).trans
    ((hr5.mono (by decide)).trans ((hr6.mono (by decide)).trans
    ((hr7.mono (by decide)).trans ((hr8.mono (by decide)).trans
    ((hr9.mono (by decide)).trans ((hK10.2.1.mono (by decide)).trans (hr11.mono (by decide)))))))))))⟩
  refine ⟨hc11, ?_, hfx, hd11, ?_, fun a hA => ?_, fun r hRr => ?_⟩
  · rw [hr11.sp, hK10.2.1.sp, hr9.sp, hr8.sp, hr7.sp, hr6.sp, hr5.sp, hr4.sp, hr3.sp, hr2.sp, hr1.sp]
  · rw [bad_keep hf11 (dBT (by omega)), bad_keep hK10.2.2.1 (disj_FAK (by omega) (by omega)),
      bad_keep hf9 (dTB (by omega)), bad_keep hf8 (dTB (by omega)), bad_keep hf7 (dTB (by omega)),
      bad_keep hf6 (dTB (by omega)), bad_keep hf5 (dTB (by omega)), hb4, hb3, hb2, kA, kR, kS3, hS]
    simp only [hb1, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · obtain ⟨ax, ay, az⟩ := hv3 a (by rw [kA]; exact hA)
    have eA : A' = Proof.Ed448.negPoint a := by
      show (⟨FS s9.mem b NAX, FS s9.mem b NAY, FS s9.mem b ONE⟩ : Point) = ⟨0 - a.X, a.Y, a.Z⟩
      rw [k49 (by decide) (by decide), k49 (by decide) (by decide), k49 (by decide) (by decide),
        k34 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide), ax, ay,
        kFS1 (by decide) (by decide) (by decide), hone, az]
    have hArep : Rep A' (-Proof.Ed448.toAffine a) := by
      rw [eA]; exact (Proof.Ed448.rep_toAffine (Proof.Ed448.decodePoint_valid hA)).neg
    exact keyOk_BT hf11 (keyOk_of hArep hK10)
  · obtain ⟨rx, ry, rz⟩ := hv2 r (by rw [kR]; exact hRr)
    rw [k911 (by decide) (by decide), k911 (by decide) (by decide), k49 (by decide) (by decide),
      k49 (by decide) (by decide), k34 (by decide) (by decide), k34 (by decide) (by decide),
      kR3 (.inl rfl), kR3 (.inr rfl), rx, ry, rz]
    exact ⟨rfl, rfl, rfl⟩

theorem pre_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) : WP isa vPrefix s (PreOk s) :=
  WP.mono (pre_run hR hp) fun _ h => h.1

theorem verifyEquation_correct (hR : Proof.Ed448.RecoverOk) {s : State} (hp : VPre s) :
    WP isa verifyEquation s fun t => ((t.gpr .a0).setWidth 32 =
      if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
        (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0) ∧
      Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s t := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  have hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of hl5
  unfold verifyEquation
  refine WP.seq (WP.mono (pre_run hR hp) fun u ⟨⟨hcu, _, hfx, hdu, hbad, hkey, hnr⟩, hru⟩ => ?_)
  generalize hb : base (s.gpr .a3) = b at hcu hfx hdu hbad hkey hnr
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) = K at *
  refine WP.seq (WP.mono (joint_ok hSl hKl hcu hfx hdu) fun s12 ⟨sL, hvL, fL, rL, ⟨⟨t2', C12⟩, d12, rep12⟩⟩ => ?_)
  refine WP.seq (WP.mono (addNegR_ok hvL C12 d12) fun s13 ⟨hc13, st13, sl13⟩ => ?_)
  obtain ⟨tf, t, hef, ht, hk⟩ := WP.keep
    [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (vFinish_ok hc13 sl13) (by decide +kernel)
  have rf : Rest [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s13 t :=
    ⟨hk.1, hk.2.1, hk.2.2, Exec.sp hef⟩
  refine ⟨tf, t, hef, ?_, hru.trans ((rL.mono (by decide)).trans
    ((st13.rest.mono (by decide)).trans rf))⟩
  rw [ht]
  have dF := disj_FA (b := b) (d := BAD) (n := 8) (by omega) (by omega)
  have hb13 : bad s13.mem b = bad u.mem b := by rw [bad_keep st13.frame dF, bad_keep fL dF]
  have kU : ∀ {q : Nat}, 1064 ≤ q → q + 56 ≤ 1696 → FS s12.mem b q = FS u.mem b q := fun h1 h2 => by
    rw [fs_hi C12.stp.frame (by omega) (by omega), fs_hi fL (by omega) (by omega)]
  rw [hb13] at *
  have res : ∀ (c : Prop) [Decidable c] (v : Bool), (c ↔ v = true) →
      (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if v then 1 else 0 := by
    intro c _ v h
    by_cases hc : c
    · rw [ite_eq_left hc, ite_eq_left (h.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun hv => hc (h.mpr hv))]; rfl
  refine res _ _ ?_
  cases hA : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57) with
  | none =>
    rw [Proof.Ed448.verifyEquation_none (.inl hA)]
    exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).2.1; rw [hA] at this; exact absurd this (by decide),
      fun h => absurd h (by decide)⟩
  | some a =>
    cases hRr : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114).take 57) with
    | none =>
      rw [Proof.Ed448.verifyEquation_none (.inr hRr)]
      exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).1; rw [hRr] at this; exact absurd this (by decide),
        fun h => absurd h (by decide)⟩
    | some r =>
      have hQ := rep12 _ (keyOk_FA fL (hkey a hA))
      simp only [Impl.Ed448.WnafWide.residual, natCast_zsmul] at hQ
      obtain ⟨rx, ry, rz⟩ := hnr r hRr
      have eR : (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = Proof.Ed448.negPoint r := by
        show (⟨FS s12.mem b NRX, FS s12.mem b NRY, 1⟩ : Point) = ⟨0 - r.X, r.Y, r.Z⟩
        rw [kU (by decide) (by decide), kU (by decide) (by decide), rx, ry, rz]
      rw [← hS, ← hK] at hQ
      rw [neutral_eq hl3 hl4 hl5 hA hRr hQ, hS, pointEqual_identity, hbad]
      simp only [hA, hRr, Option.isSome_some, true_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [eR]

end

end VG.Proof.Ed448.RISCV64
