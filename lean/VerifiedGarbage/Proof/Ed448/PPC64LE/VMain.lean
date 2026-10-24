module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.VSetup
public import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecode
import VerifiedGarbage.Proof.Ed448.PPC64LE.VCheckS
import VerifiedGarbage.Proof.Ed448.PPC64LE.VTab
import VerifiedGarbage.Proof.Ed448.PPC64LE.VStep
import VerifiedGarbage.Proof.Ed448.PPC64LE.VFinish
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Impl.Ed448.PPC64LE.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.PPC64LE.Slots
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Ed448.PPC64LE.VDecodeY

/-!
# Ed448's verification equation on PPC64LE: the whole function

`vg_ed448_verify_equation` returns 1 exactly when `verifyEquation` holds
(`verifyEquation_correct`), given that `recoverX` is `recoverRef`
(`RecoverOk`) and the four-iteration ladder decides the equation
(`VerifyEq4Ok`), both proven in `Proof/Ed448/Facts.lean` and passed in by the
registration.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (ACC BITS)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

section
variable {b : Addr}

/-- An element whose slot is apart from a frame's regions stays. -/
theorem fs_disj {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {q : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 q, 56⟩ r) :
    FS m' b q = FS m b q := by
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => (hd r hr).sub_left (Offset.sub b (d := q + 4 * k) (n := 4) (e := q) (k := 56)
      (by omega) (by omega))
  rw [FS, V, val32_congr e]; rfl

theorem disj_decW {d n xo yo : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3520) (hxo : d + n ≤ xo ∨ xo + 56 ≤ d)
    (hyo : d + n ≤ yo ∨ yo + 56 ≤ d) (hx : xo + 56 ≤ 4096) (hy : yo + 56 ≤ 4096) :
    ∀ r ∈ decW b xo yo, Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [decW, yW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  all_goals exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem disj_FAB {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 3520) :
    ∀ r ∈ [FA b, ⟨b + BitVec.ofNat 64 BAD, 8⟩], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem disj_TAB {d n : Nat} (h1 : TAB + 1832 ≤ d ∨ d + n ≤ TAB) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 TAB, 1832⟩ : Region)], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (by unfold TAB BITS at h1 ⊢; omega) (by omega) (by decide)

theorem disj_FA {d n : Nat} (h1 : 1064 ≤ d) (h2 : d + n ≤ 8192) :
    ∀ r ∈ [FA b], Region.Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ (by unfold ACC; omega) (by omega)

theorem bytes_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.take_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem bytes_drop (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [show (114 : Nat) = 57 + 57 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
    List.drop_left' (by simp [Spec.X25519.bytesAt])]; rfl

theorem pointEqual_identity (q : Point) :
    Spec.Ed448.pointEqual q Spec.Ed448.identity = (decide (q.X = 0) && decide (q.Y = q.Z)) := by
  simp only [Spec.Ed448.pointEqual, Spec.Ed448.identity, Fin.mul_one, Fin.zero_mul, Fin.one_mul]
  rfl

theorem verifyEquation_correct (hR : Proof.Ed448.RecoverOk) (hV : Proof.Ed448.VerifyEq4Ok) {s : State}
    (hp : VPre s) :
    WP isa verifyEquation s fun t => (t.gpr .r3).setWidth 32 =
      if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57)
        (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) then 1 else 0 := by
  obtain ⟨o1, o2, o3, o4⟩ := offs
  generalize hb : s.gpr .r6 = b
  unfold verifyEquation
  refine WP.seq (WP.mono (vSetup_ok hp) fun s1 ⟨hc1, hr1, hf1, ePK, eSG, eCH, hb1, hd1, hbx, hby, hone⟩ => ?_)
  rw [hb] at hc1 ePK eSG eCH hb1 hd1 hbx hby hone
  refine WP.seq (WP.mono (decode_ok hR hc1 (p := SG) (by decide) (by decide) (xo := NRX) (yo := NRY)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ hd1) fun s2 ⟨hc2, hr2, hf2, hd2, hb2, hv2⟩ => ?_)
  refine WP.seq (WP.mono (decode_ok hR hc2 (p := PK) (by decide) (by decide) (xo := NAX) (yo := NAY)
    ⟨by decide, by decide, by decide, by decide, by decide⟩ hd2) fun s3 ⟨hc3, hr3, hf3, hd3, hb3, hv3⟩ => ?_)
  refine WP.seq (WP.mono (checkS_ok hc3) fun s4 ⟨hc4, hr4, hf4, hk4, hb4⟩ => ?_)
  refine WP.seq (WP.mono (tabFill_ok hc4) fun s5 ⟨hc5, hr5, hf5, ht5⟩ => ?_)
  refine WP.seq (WP.mono (tabBits_ok hc5 (src := SG + 57) (e := 2) (by decide) (by decide) (by decide) ht5)
    fun s6 ⟨hc6, hr6, hf6, ht6⟩ => ?_)
  refine WP.seq (WP.mono (tabBits_ok hc6 (src := CH) (e := 1) (by decide) (by decide) (by decide) ht6)
    fun s7 ⟨hc7, hr7, hf7, ht7⟩ => ?_)
  have hTB : TAB = 1064 := rfl
  have hSG : SG = 3345 := rfl
  have hPK : PK = 3288 := rfl
  have hCH : CH = 3459 := rfl
  -- The inputs, as the phases read them.
  have kA : Spec.Ed448.bytesAt s2.mem (b + BitVec.ofNat 64 PK) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57 := by
    rw [bytes_keep hf2 (disj_decW (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)) (by decide),
      ePK]
  have kR : Spec.Ed448.bytesAt s1.mem (b + BitVec.ofNat 64 SG) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57 := by rw [← eSG, bytes_take]
  have sS : ∀ {m : Mem}, Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 SG + BitVec.ofNat 64 57) 57 =
      Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 (SG + 57)) 57 := by intro m; rw [Offset.add_add]
  have kS3 : Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 (SG + 57)) 57 =
      (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57 := by
    rw [bytes_keep hf3 (disj_decW (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)) (by decide),
      bytes_keep hf2 (disj_decW (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)) (by decide),
      ← eSG, bytes_drop, sS]
  have kS5 : Spec.Ed448.bytesAt s5.mem (b + BitVec.ofNat 64 (SG + 57)) 57 =
      Spec.Ed448.bytesAt s3.mem (b + BitVec.ofNat 64 (SG + 57)) 57 := by
    rw [bytes_keep hf5 (disj_TAB (by omega) (by omega)) (by decide),
      bytes_keep hf4 (disj_FAB (by omega) (by omega)) (by decide)]
  have kK : Spec.Ed448.bytesAt s6.mem (b + BitVec.ofNat 64 CH) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57 := by
    rw [bytes_keep hf6 (disj_TAB (by omega) (by omega)) (by decide),
      bytes_keep hf5 (disj_TAB (by omega) (by omega)) (by decide),
      bytes_keep hf4 (disj_FAB (by omega) (by omega)) (by decide),
      bytes_keep hf3 (disj_decW (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)) (by decide),
      bytes_keep hf2 (disj_decW (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)) (by decide), eCH]
  generalize hS : Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).drop 57) = S at *
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57) = K at *
  have hT : TabIs b s7.mem (tabV S K) := fun h hh => by
    rw [ht7 h hh, kK, hK, kS5, kS3, hS, tab_eq S K h hh]
  -- The points.
  have kFS : ∀ {q : Nat}, 2896 ≤ q → q + 56 ≤ 3288 → FS s7.mem b q = FS s3.mem b q := fun h1 h2 => by
    rw [fs_disj hf7 (disj_TAB (by omega) (by omega)), fs_disj hf6 (disj_TAB (by omega) (by omega)),
      fs_disj hf5 (disj_TAB (by omega) (by omega)), fs_disj hf4 (disj_FAB (by omega) (by omega))]
  have kFS1 : ∀ {q : Nat}, 2896 ≤ q → q + 56 ≤ 3008 ∨ 3232 ≤ q → q + 56 ≤ 3288 → FS s3.mem b q = FS s1.mem b q :=
    fun h1 h2 h3 => by
      rw [fs_disj hf3 (disj_decW (by omega) (by omega) (by unfold NAX; omega) (by unfold NAY; omega) (by decide)
          (by decide)),
        fs_disj hf2 (disj_decW (by omega) (by omega) (by unfold NRX; omega) (by unfold NRY; omega) (by decide)
          (by decide))]
  have kR3 : ∀ {q : Nat}, q = NRX ∨ q = NRY → FS s3.mem b q = FS s2.mem b q := fun h => by
    rcases h with rfl | rfl <;>
      exact fs_disj hf3 (disj_decW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  let A' : Point := ⟨FS s7.mem b NAX, FS s7.mem b NAY, 1⟩
  let R' : Point := ⟨FS s7.mem b NRX, FS s7.mem b NRY, 1⟩
  have hP : PtsOk b s7.mem A' R' :=
    ⟨by rw [kFS (by decide) (by decide), kFS1 (by decide) (by decide) (by decide), hbx],
      by rw [kFS (by decide) (by decide), kFS1 (by decide) (by decide) (by decide), hby], rfl, rfl, rfl, rfl,
      by rw [kFS (by decide) (by decide), kFS1 (by decide) (by decide) (by decide), hone], rfl, rfl⟩
  have hd7 : FS s7.mem b DK = Spec.Ed448.d := by
    rw [fs_disj hf7 (disj_TAB (by decide) (by decide)), fs_disj hf6 (disj_TAB (by decide) (by decide)),
      fs_disj hf5 (disj_TAB (by decide) (by decide)), hk4, hd3]
  -- The loop and the result.
  refine WP.seq (WP.mono (vloop_ok hc7.ctx hT hP hd7) fun s8 ⟨hst8, _, hS8⟩ => ?_)
  have hc8 : VCtx b s8 := hc7.of_rest hst8.rest (by decide) (by decide)
  refine WP.mono (vFinish_ok hc8 hS8) fun t ht => ?_
  rw [ht]
  have hb8 : bad s8.mem b = bad s4.mem b := by
    unfold bad
    rw [hst8.frame.readW (Region.contains_self _ (64 / 8)) (disj_FA (by omega) (by omega)) (by decide),
      hf7.readW (Region.contains_self _ (64 / 8)) (disj_TAB (by omega) (by omega)) (by decide),
      hf6.readW (Region.contains_self _ (64 / 8)) (disj_TAB (by omega) (by omega)) (by decide),
      hf5.readW (Region.contains_self _ (64 / 8)) (disj_TAB (by omega) (by omega)) (by decide)]
  have hbad : bad s8.mem b = 0 ↔ (Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57)).isSome ∧
      (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57)).isSome ∧ S < Spec.Ed448.L := by
    rw [hb8, hb4, hb3, hb2, kA, kR, kS3, hS]
    simp only [hb1, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  have hl3 : (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have hl4 : (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hl5 : (Spec.Ed448.bytesAt s.mem (s.gpr .r5) 57).length = 57 := by simp [Spec.Ed448.bytesAt]
  have res : ∀ (c : Prop) [Decidable c] (v : Bool), (c ↔ v = true) →
      (BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32 = if v then 1 else 0 := by
    intro c _ v h
    by_cases hc : c
    · rw [ite_eq_left hc, ite_eq_left (h.mp hc)]; rfl
    · rw [ite_eq_right hc, ite_eq_right (fun hv => hc (h.mpr hv))]; rfl
  refine res _ _ ?_
  cases hA : Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .r3) 57) with
  | none =>
    rw [Proof.Ed448.verifyEquation_none (.inl hA)]
    exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).2.1; rw [hA] at this; exact absurd this (by decide), fun h => absurd h (by decide)⟩
  | some a =>
    cases hRr : Spec.Ed448.decodePoint ((Spec.Ed448.bytesAt s.mem (s.gpr .r4) 114).take 57) with
    | none =>
      rw [Proof.Ed448.verifyEquation_none (.inr hRr)]
      exact ⟨fun ⟨h, _⟩ => by have := (hbad.mp h).1; rw [hRr] at this; exact absurd this (by decide),
        fun h => absurd h (by decide)⟩
    | some r =>
      rw [hV _ _ _ a r hl3 hl4 hl5 hA hRr, hS, hK, pointEqual_identity]
      -- The negated points.
      obtain ⟨ax, ay, az⟩ := hv3 a (by rw [kA]; exact hA)
      obtain ⟨rx, ry, rz⟩ := hv2 r (by rw [kR]; exact hRr)
      have eA : A' = Proof.Ed448.negPoint a := by
        show (⟨FS s7.mem b NAX, FS s7.mem b NAY, 1⟩ : Point) = ⟨0 - a.X, a.Y, a.Z⟩
        rw [kFS (by decide) (by decide), kFS (by decide) (by decide), ax, ay, az]
      have eR : R' = Proof.Ed448.negPoint r := by
        show (⟨FS s7.mem b NRX, FS s7.mem b NRY, 1⟩ : Point) = ⟨0 - r.X, r.Y, r.Z⟩
        rw [kFS (by decide) (by decide), kFS (by decide) (by decide), kR3 (.inl rfl), kR3 (.inr rfl), rx, ry, rz]
      rw [← eA, ← eR, hbad]
      simp only [hA, hRr, Option.isSome_some, true_and, Bool.and_eq_true, decide_eq_true_eq]

end

end VG.Proof.Ed448.PPC64LE
