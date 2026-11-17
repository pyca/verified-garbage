module

import VerifiedGarbage.Proof.X448.PPC64LE.Slots
public import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X448.Ladder
public import VerifiedGarbage.Spec.X448.Contract

/-! ### `X448.PPC64LE.Setup`, which this module and modules that import it used -/

section

/-!
# X448 on PPC64LE: the setup

The u-coordinate as 32-bit limbs (`decode_val`: the number of its 56 bytes), and the setup of the working space: `x1 = x3 = u`, `x2 = z3 =
1` and `z2 = 0` (`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leNum leNum_append)
open VG.Proof.X448 (bytesAt_add length_bytesAt toFe)

/-! ## The u-coordinate as limbs -/

/-- Word `k` at `p`. -/
def uWord (m : Mem) (p : Addr) (k : Nat) : Nat := wd m p (4 * k)

/-- Limb `k` of the decoded u-coordinate: word `k`. -/
abbrev uLimb (m : Mem) (p : Addr) (k : Nat) : Nat := uWord m p k

theorem leNum_bytesAt4 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (4 * n)) = val32 (uWord m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 from rfl, bytesAt_add, leNum_append, leNum_bytesAt4 m p n, val32_succ,
      length_bytesAt, Proof.X448.leNum_bytesAt_read, show (Mem.read m (p + BitVec.ofNat 64 (4 * n)) 4).toNat =
        (m.readW (p + BitVec.ofNat 64 (4 * n)) 32).toNat by simp [Mem.readW], show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]
    rfl

theorem uLimb_lt (m : Mem) (p : Addr) : ∀ k < 14, uLimb m p k < 2 ^ 32 := fun k _ => wd_lt m p (4 * k)

/-- The limbs of the decoded u-coordinate. -/
theorem decode_val (m : Mem) (p : Addr) :
    val32 (uLimb m p) 14 = VG.Spec.X448.decodeUCoordinate (bytesAt m p 56) := by
  rw [VG.Proof.X448.decodeUCoordinate_eq (length_bytesAt m p 56), show 56 = 4 * 14 from rfl,
    leNum_bytesAt4]

section
variable {b : Addr}

/-! ## Decoding the u-coordinate -/

theorem decodeStep_ok {k : Nat} (hk : k < 14) {s : State} (hc : Ctx b s) {pt : Addr}
    (h5 : s.gpr .r5 = pt) (hin : (⟨pt, 56⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      wd s'.mem b (X1 + 4 * k) = uLimb s.mem pt k ∧
      wd s'.mem b (X3 + 4 * k) = uLimb s.mem pt k ∧
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (X1 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k))).writeW
        (b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k)) ∧
      Rest [.r7] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  have hlt := uLimb_lt s.mem pt k hk
  -- The limb in `r7`, then the stores.
  have key : ∀ (is : List Instr) (s2 : State), Rest [.r7] s s2 → s2.mem = s.mem →
      (s2.gpr .r7).toNat = uLimb s.mem pt k →
      is = [.store .w .r7 .r6 (X1 + 4 * k), .store .w .r7 .r6 (X3 + 4 * k)] →
      WP isa (.block is) s2 fun s' =>
        wd s'.mem b (X1 + 4 * k) = uLimb s.mem pt k ∧
        wd s'.mem b (X3 + 4 * k) = uLimb s.mem pt k ∧
        s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (X1 + 4 * k))
          (BitVec.ofNat 32 (uLimb s.mem pt k))).writeW
          (b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k)) ∧
        Rest [.r7] s s' := by
    intro is s2 hr2 hm2 e7 his
    subst his
    have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
    have ev : (s2.gpr .r7).setWidth 32 = BitVec.ofNat 32 (uLimb s.mem pt k) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_lo32, e7, BitVec.toNat_ofNat]
    refine sw0_ok hc2 (d := X1 + 4 * k) (by omega_arith) fun s4 u4 => ?_
    refine sw0_ok (hc2.of_rest (u4.rest []) (by decide)) (d := X3 + 4 * k) (by omega_arith) fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_, hr2.trans ((u4.rest _).trans (u5.rest _))⟩
    · rw [u5.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u4.mem, wd_write_self, ev,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · rw [u5.mem, wd_write_self, u4.gpr, ev, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · rw [u5.mem, u4.gpr, u4.mem, hm2, ev]
  unfold decodeStep
  refine wp_lw (a := pt + BitVec.ofNat 64 (4 * k)) (by decide) (by omega_arith) (by rw [h5])
    (in_base hin (by omega_arith) (by omega_arith)) fun s1 u1 => ?_
  have e7 : (s1.gpr .r7).toNat = uWord s.mem pt k := by rw [u1.gpr, toNat_ext32]; rfl
  exact key _ s1 (u1.rest (by decide)) u1.mem e7 rfl

theorem decode_ok {s0 : State} (hc : Ctx b s0) {pt : Addr} (h5 : s0.gpr .r5 = pt)
    (hin : (⟨pt, 56⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨pt, 56⟩ ⟨b, 4096⟩) :
    WP isa (.block ((List.range 14).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 14, limb s'.mem b X1 k = uLimb s0.mem pt k ∧ limb s'.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s0.mem s'.mem ∧ Rest [.r7] s0 s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, limb s.mem b X1 k = uLimb s0.mem pt k ∧ limb s.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s0.mem s.mem ∧ Rest [.r7] s0 s)
    (fun k s hk ⟨h1, hf, hr⟩ => ?_) 14 (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s' h => h
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.mono (decodeStep_ok hk hcs (pt := pt) (by rw [hr.gpr _ (by decide), h5])
    (by rw [hr.rd, hr.wr]; exact hin)) fun s' ⟨e1, e3, hm, hr'⟩ => ⟨fun j hj => ?_, ?_, hr.trans hr'⟩
  · -- The words of the u-coordinate are as in `s0`.
    have hu : uLimb s.mem pt k = uLimb s0.mem pt k :=
      wd_frame hf fun r hr' => by
        rw [List.mem_singleton.mp hr']
        exact (hd.sub_left (Offset.sub_base pt (d := 4 * k) (n := 4) (by omega_arith))).sub_right
          (Offset.sub_base b (d := X1) (n := 224) (by omega_arith))
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [limb, limb, hm, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h1 j hj
    · rw [limb, limb, e1, e3, hu]; exact ⟨rfl, rfl⟩
  · rw [hm]
    exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))

/-- A word outside a range that code wrote. -/
theorem wd_keep {m m' : Mem} {B : Addr} {o n d : Nat} (hf : Frame [⟨B + BitVec.ofNat 64 o, n⟩] m m')
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 4096) (ho : o + n ≤ 4096) : wd m' B d = wd m B d :=
  wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_arith) (by omega_arith)

/-- The ranges `consts` writes. -/
abbrev constsR (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 X2, 112⟩, ⟨b + BitVec.ofNat 64 Z3, 56⟩]

theorem constsR_sub (e k o n : Nat) (he : (⟨b + BitVec.ofNat 64 e, k⟩ : Region) ∈ constsR b)
    (h1 : e ≤ o) (h2 : o + n ≤ e + k) : ∃ r ∈ constsR b, Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ r :=
  ⟨_, he, Offset.sub b h1 h2⟩

theorem consts_ok {s : State} (hc : Ctx b s) :
    WP isa (.block consts) s fun s' =>
      (∀ k < 14, limb s'.mem b X2 k = if k = 0 then 1 else 0) ∧
      (∀ k < 14, limb s'.mem b Z2 k = 0) ∧
      (∀ k < 14, limb s'.mem b Z3 k = if k = 0 then 1 else 0) ∧
      Frame (constsR b) s.mem s'.mem ∧ Rest [.r5, .r7, .r8] s s' := by
  have hX2 : X2 = 56 := rfl
  have hZ2 : Z2 = 112 := rfl
  have hZ3 : Z3 = 224 := rfl
  simp only [consts, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.r5, .r7, .r8] s s3 := (u1.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have g7 : (s3.gpr .r7).setWidth 32 = 1 := by
    rw [u3.other _ (by decide), u1.gpr]; rfl
  have g8 : s3.gpr .r8 = 0 := by rw [u3.gpr]; rfl
  refine sw0_ok hc3 (d := X2) (by omega_arith) fun s4 u4 => ?_
  refine sw0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := Z2) (by omega_arith) fun s5 u5 => ?_
  refine sw0_ok (hc3.of_rest ((u4.rest []).trans (u5.rest [])) (by decide)) (d := Z3) (by omega_arith)
    fun s8 u8 => ?_
  have hr8 : Rest [] s3 s8 := (u4.rest []).trans ((u5.rest []).trans (u8.rest []))
  have hc8 : Ctx b s8 := hc3.of_rest hr8 (by decide)
  have hg8 : ∀ r, s8.gpr r = s3.gpr r := fun r => hr8.gpr r (by simp)
  have hm8 : s8.mem = ((s3.mem.writeW (b + BitVec.ofNat 64 X2) ((s3.gpr .r7).setWidth 32)).writeW
      (b + BitVec.ofNat 64 Z2) ((s3.gpr .r8).setWidth 32)).writeW (b + BitVec.ofNat 64 Z3)
      ((s3.gpr .r7).setWidth 32) := by
    rw [u8.mem, u5.gpr, u5.mem, u4.gpr, u4.mem]
  refine WP.append (stores_ok (r := .r8) (o := X2 + 4) (n := 13) (by omega_arith) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (stores_ok (r := .r8) (o := Z2 + 4) (n := 13) (by omega_arith) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.mono (stores_ok (r := .r8) (o := Z3 + 4) (n := 13) (by omega_arith) hc10)
    fun s11 ⟨w11, f11, g11, r11⟩ => ?_
  have e8 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .r8).toNat % 2 ^ 32 = 0 := fun t ht => by
    rw [ht, hg8, g8]; rfl
  -- Words written by the first stores, through the later ones.
  have k8 : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ X2 + 4 ∨ X2 + 56 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 56 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 56 ≤ d) → wd s11.mem b d = wd s8.mem b d := fun d hd h1 h2 h3 => by
    rw [wd_keep f11 h3 hd (by omega_arith), wd_keep f10 h2 hd (by omega_arith),
      wd_keep f9 h1 hd (by omega_arith)]
  have g9' : s9.gpr = s8.gpr := g9
  have g10' : s10.gpr = s8.gpr := g10.trans g9
  have t1 : (1 : BitVec 32).toNat = 1 := rfl
  have t0 : ((s3.gpr .r8).setWidth 32).toNat = 0 := by rw [g8]; rfl
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_self, g7, t1]; rfl
    · rw [limb, wd_keep f11 (by omega_arith) (by omega_arith) (by omega_arith),
        wd_keep f10 (by omega_arith) (by omega_arith) (by omega_arith), show X2 + 4 * k = X2 + 4 + 4 * (k - 1) by omega_arith,
        w9 (k - 1) (by omega_arith), e8 _ rfl]
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_self, t0]
    · rw [limb, wd_keep f11 (by omega_arith) (by omega_arith) (by omega_arith),
        show Z2 + 4 * k = Z2 + 4 + 4 * (k - 1) by omega_arith, w10 (k - 1) (by omega_arith), e8 _ g9']
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_self, g7, t1]; rfl
    · rw [limb, show Z3 + 4 * k = Z3 + 4 + 4 * (k - 1) by omega_arith, w11 (k - 1) (by omega_arith), e8 _ g10']
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · -- Every write is in `constsR`.
    have m1 : (⟨b + BitVec.ofNat 64 X2, 112⟩ : Region) ∈ constsR b := List.mem_cons_self ..
    have m2 : (⟨b + BitVec.ofNat 64 Z3, 56⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have f8 : Frame (constsR b) s.mem s8.mem := by
      rw [hm8, u3.mem, u1.mem]
      exact (((Frame.refl _ _).writeW m1 _ (Offset.contains _ (d := X2) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))).writeW m1 _ (Offset.contains _ (d := Z2) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))).writeW m2 _ (Offset.contains _ (d := Z3) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))
    exact f8.trans ((f9.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega_arith) (by omega_arith)).trans
      ((f10.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega_arith) (by omega_arith)).trans
      (f11.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m2 (by omega_arith) (by omega_arith))))
  · exact hr3.trans ((hr8.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      (r11.mono (by decide)))))

/-- The base point's u-coordinate, 5, as limbs. -/
abbrev fiveLimb (k : Nat) : Nat := if k = 0 then 5 else 0

theorem five_ok {s : State} (hc : Ctx b s) :
    WP isa (.block five) s fun s' =>
      (∀ k < 14, limb s'.mem b X1 k = fiveLimb k ∧ limb s'.mem b X3 k = fiveLimb k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s.mem s'.mem ∧ Rest [.r7, .r8] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  simp only [five, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r7, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have g4 : (s2.gpr .r7).setWidth 32 = 5 := by rw [u2.other _ (by decide), u1.gpr]; rfl
  have g5 : s2.gpr .r8 = 0 := by rw [u2.gpr]; rfl
  refine sw0_ok hc2 (d := X1) (by omega_arith) fun s3 u3 => ?_
  refine sw0_ok (hc2.of_rest (u3.rest []) (by decide)) (d := X3) (by omega_arith) fun s4 u4 => ?_
  have hr4 : Rest [] s2 s4 := (u3.rest []).trans (u4.rest [])
  have hc4 : Ctx b s4 := hc2.of_rest hr4 (by decide)
  have hg4 : ∀ r, s4.gpr r = s2.gpr r := fun r => hr4.gpr r (by simp)
  have hm4 : s4.mem = (s2.mem.writeW (b + BitVec.ofNat 64 X1) ((s2.gpr .r7).setWidth 32)).writeW
      (b + BitVec.ofNat 64 X3) ((s2.gpr .r7).setWidth 32) := by
    rw [u4.mem, u3.gpr, u3.mem]
  refine WP.append (stores_ok (r := .r8) (o := X1 + 4) (n := 13) (by omega_arith) hc4)
    fun s5 ⟨w5, f5, g5', r5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest r5 (by decide)
  refine WP.mono (stores_ok (r := .r8) (o := X3 + 4) (n := 13) (by omega_arith) hc5)
    fun s6 ⟨w6, f6, _, r6⟩ => ?_
  have e5 : (s4.gpr .r8).toNat % 2 ^ 32 = 0 := by rw [hg4, g5]; rfl
  have e6 : (s5.gpr .r8).toNat % 2 ^ 32 = 0 := by rw [g5', hg4, g5]; rfl
  refine ⟨fun k hk => ⟨?_, ?_⟩, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, wd_keep f6 (by omega_arith) (by omega_arith) (by omega_arith),
        wd_keep f5 (by omega_arith) (by omega_arith) (by omega_arith), hm4,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_self, g4]; rfl
    · rw [limb, wd_keep f6 (by omega_arith) (by omega_arith) (by omega_arith),
        show X1 + 4 * k = X1 + 4 + 4 * (k - 1) by omega_arith, w5 (k - 1) (by omega_arith), e5]
      simp only [fiveLimb, show k ≠ 0 by omega_arith, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, wd_keep f6 (by omega_arith) (by omega_arith) (by omega_arith),
        wd_keep f5 (by omega_arith) (by omega_arith) (by omega_arith), hm4, wd_write_self, g4]; rfl
    · rw [limb, show X3 + 4 * k = X3 + 4 + 4 * (k - 1) by omega_arith, w6 (k - 1) (by omega_arith), e6]
      simp only [fiveLimb, show k ≠ 0 by omega_arith, ite_false]
  · have m1 : (⟨b + BitVec.ofNat 64 X1, 224⟩ : Region) ∈ [(⟨b + BitVec.ofNat 64 X1, 224⟩ : Region)] :=
      List.mem_singleton_self _
    have f4 : Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s.mem s4.mem := by
      rw [hm4, u2.mem, u1.mem]
      exact ((Frame.refl _ _).writeW m1 _ (Offset.contains _ (d := X1) (n := 32 / 8) (by omega_arith)
        (by omega_arith) (by omega_arith))).writeW m1 _ (Offset.contains _ (d := X3) (n := 32 / 8)
        (by omega_arith) (by omega_arith) (by omega_arith))
    exact f4.trans ((f5.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, m1, Offset.sub b (by omega_arith) (by omega_arith)⟩).trans
      (f6.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, m1, Offset.sub b (by omega_arith) (by omega_arith)⟩))
  · exact hr2.trans ((hr4.mono (by decide)).trans ((r5.mono (by decide)).trans (r6.mono (by decide))))

end

/-! ## The whole setup -/

/-- The precondition of `vg_x448(out = r3, scalar = r4, point = r5, scratch = r6)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 56⟩, ⟨s.gpr .r5, 56⟩]
  wr : s.wr = [⟨s.gpr .r3, 56⟩, ⟨s.gpr .r6, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r4, 56⟩
  out_pt : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r5, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r6, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .r4, 56⟩ ⟨s.gpr .r6, 8192⟩
  pt_ws : Region.Disjoint ⟨s.gpr .r5, 56⟩ ⟨s.gpr .r6, 8192⟩

/-- A region disjoint from the working space is disjoint from its first 4096 bytes. -/
theorem disj4096 {r : Region} {b : Addr} (h : Region.Disjoint r ⟨b, 8192⟩) : Region.Disjoint r ⟨b, 4096⟩ :=
  h.sub_right (Region.sub_prefix (by decide))

/-- The u-coordinate, decoded. -/
def uOf (s : State) : Fe :=
  toFe (VG.Spec.X448.decodeUCoordinate (bytesAt s.mem (s.gpr .r5) 56))

theorem slot_of {m : Mem} {B : Addr} {o : Nat} {f : Nat → Nat} (h : ∀ k < 14, limb m B o k = f k) :
    FS m B o = toFe (val32 f 14) := by rw [FS, V, val32_congr h]

/-- The setup after the code that writes the u-coordinate's limbs `f` into `X1`
and `X3` (`decode` or `five`): `consts`, and the ladder's initial state for
`u = f`. -/
theorem consts_post {s s4 : State} {f : Nat → Nat} (hc : Ctx (s.gpr .r6) s)
    (hl4 : ∀ k < 14, limb s4.mem (s.gpr .r6) X1 k = f k ∧ limb s4.mem (s.gpr .r6) X3 k = f k)
    (hf4 : Frame [⟨s.gpr .r6 + BitVec.ofNat 64 X1, 224⟩] s.mem s4.mem) (hr4 : Rest [.r7, .r8] s s4) :
    WP isa (.block consts) s4 fun s' =>
      Ctx (s.gpr .r6) s' ∧ Frame [⟨s.gpr .r6, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (s.gpr .r6) LQ (ladV (toFe (val32 f 14)) (VG.Proof.X448.init (toFe (val32 f 14)))) ∧
      Rest [.r5, .r7, .r8] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX2 : X2 = 56 := rfl
  have hZ2 : Z2 = 112 := rfl
  have hX3 : X3 = 168 := rfl
  have hZ3 : Z3 = 224 := rfl
  have hc4 : Ctx (s.gpr .r6) s4 := hc.of_rest hr4 (by decide)
  refine WP.mono (consts_ok hc4) fun s5 ⟨hx2, hz2, hz3, hf5, hr5⟩ => ?_
  -- `x1` and `x3` through the constants.
  have hkeep : ∀ o, (o = X1 ∨ o = X3) → ∀ k < 14, limb s5.mem (s.gpr .r6) o k = f k := by
    intro o ho k hk
    have e := limb_frame (o := o) hf5 fun r hr j hj => by
      simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [e k hk]
    rcases ho with rfl | rfl
    · exact (hl4 k hk).1
    · exact (hl4 k hk).2
  refine ⟨hc4.of_rest hr5 (by decide), ?_, ?_, ?_⟩
  · have hsub : ∀ o n, o + n ≤ 8192 → Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 o, n⟩
        ⟨s.gpr .r6, 8192⟩ := fun o n h => Offset.sub_base _ h
    refine (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact hsub _ _ (by omega_arith)⟩).trans ?_
    refine hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hsub _ _ (by omega_arith)
  · intro q hq
    simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [slot_of (hkeep _ (.inl rfl))]; simp only [ladV, ite_true]
    · rw [slot_of hx2, val32_single _ (by decide)]
      simp only [ladV, VG.Proof.X448.init, iteF (show X2 ≠ X1 by decide), ite_true]; rfl
    · rw [slot_of hz2, val32_zero_fn]
      simp only [ladV, VG.Proof.X448.init, iteF (show Z2 ≠ X1 by decide), iteF (show Z2 ≠ X2 by decide),
        ite_true]; rfl
    · rw [slot_of (hkeep _ (.inr rfl))]
      simp only [ladV, VG.Proof.X448.init, iteF (show X3 ≠ X1 by decide), iteF (show X3 ≠ X2 by decide),
        iteF (show X3 ≠ Z2 by decide), ite_true]
    · rw [slot_of hz3, val32_single _ (by decide)]
      simp only [ladV, VG.Proof.X448.init, iteF (show Z3 ≠ X1 by decide), iteF (show Z3 ≠ X2 by decide),
        iteF (show Z3 ≠ Z2 by decide), iteF (show Z3 ≠ X3 by decide)]; rfl
  · exact (hr4.mono (by decide)).trans hr5

theorem setup_ok {s : State} (hp : XPre s) :
    WP isa (.block setup) s fun s' =>
      Ctx (s.gpr .r6) s' ∧ Frame [⟨s.gpr .r6, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (s.gpr .r6) LQ (ladV (uOf s) (VG.Proof.X448.init (uOf s))) ∧
      Rest [.r5, .r7, .r8] s s' := by
  have hws : (⟨s.gpr .r6, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hc : Ctx (s.gpr .r6) s := ⟨rfl, 8192, by decide, hws⟩
  unfold setup
  refine WP.append (decode_ok hc (pt := s.gpr .r5) rfl (by rw [hp.rd]; simp) (disj4096 hp.pt_ws))
    fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  have e : toFe (val32 (uLimb s.mem (s.gpr .r5)) 14) = uOf s := by rw [decode_val]; rfl
  rw [← e]
  exact consts_post hc hl4 hf4 (hr4.mono (by decide))

theorem val32_five :
    toFe (val32 fiveLimb 14) = toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint) := by
  rw [val32_single _ (by decide), VG.Proof.X448.decodeUCoordinate_eq (by rfl)]; rfl

/-- `setupBase`: the ladder's initial state for the base point. -/
theorem setupBase_ok {s : State} (hws : (⟨s.gpr .r6, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block setupBase) s fun s' =>
      Ctx (s.gpr .r6) s' ∧ Frame [⟨s.gpr .r6, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (s.gpr .r6) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint))
        (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint)))) ∧
      Rest [.r5, .r7, .r8] s s' := by
  have hc : Ctx (s.gpr .r6) s := ⟨rfl, 8192, by decide, hws⟩
  unfold setupBase
  refine WP.append (five_ok hc) fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  rw [← val32_five]
  exact consts_post hc hl4 hf4 hr4

end VG.Proof.X448.PPC64LE

end

end

/-!
# X448 on PPC64LE: the final reduction and the output

`freeze` stores the 56 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes leNum)

/-- Fourteen little-endian words in memory are the 56 bytes of their number. -/
theorem bytesAt_words14 (m : Mem) (p : Addr) {r : Nat → Nat} (h : ∀ j < 14, wd m p (4 * j) = r j) :
    bytesAt m p 56 = leBytes 56 (val32 r 14) := by
  obtain e : bytesAt m p 56 = leBytes 56 (leNum (bytesAt m p 56)) := by
    rw [Proof.X448.leNum_bytesAt_read]; exact Proof.X25519.bytesAt_leBytes m p 56
  rw [e, show (56 : Nat) = 4 * 14 from rfl, leNum_bytesAt4, val32_congr (f := uWord m p) h]

section
variable {b : Addr}

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨O, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem O (4 * i) = r i

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : Addr} (h3 : s0.gpr .r3 = o)
    (hout : ∀ k < 14, InRegions s0.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 56⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block ((List.range 14).flatMap outStep)) s0
      (OutInv o (fun k => sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k)) s0 14) := by
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  obtain hw : ∀ d, d + 4 ≤ 4096 → wd s.mem b d = wd s0.mem b d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega_using [hk]))
  unfold outStep
  refine lw0_ok hcs (d := X2 + 4 * k) (by omega_using [hX, hk]) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.r5]) (by decide)) (by decide)) (d := Y + 4 * k)
    (by omega_using [hY, hk]) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => ?_
  obtain hr5 : Rest [.r5, .r7] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  obtain e3 : t5.gpr .r3 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h3]
  obtain hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_sw (a := o + BitVec.ofNat 64 (4 * k)) (by decide) (by omega_using [hk])
    (by rw [e3]) (by rw [hwr]; exact hout k hk)
    fun t6 v6 => WP.block_nil ?_
  -- The limb selected.
  obtain ev : ((t5.gpr .r5).setWidth 32).toNat = sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k) := by
    obtain ex : t2.gpr .r5 = (s.mem.readW (b + BitVec.ofNat 64 (X2 + 4 * k)) 32).setWidth 64 := by
      rw [v2.other _ (by decide), v1.gpr]
    obtain ey : t2.gpr .r7 = (s.mem.readW (b + BitVec.ofNat 64 (Y + 4 * k)) 32).setWidth 64 := by
      rw [v2.gpr, v1.mem]
    obtain em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
    rw [v5.gpr, v4.other .r5 (by decide), v4.gpr, v3.other .r5 (by decide), v3.gpr, em, ex, ey]
    obtain hx := hw (X2 + 4 * k) (by omega_using [hX, hk])
    obtain hy := hw (Y + 4 * k) (by omega_using [hY, hk])
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, lo32_ext, hx]; rfl
    · rw [sel1r, lo32_ext, hy]; rfl
  obtain hm6 : t6.mem = s.mem.writeW (o + BitVec.ofNat 64 (4 * k)) ((t5.gpr .r5).setWidth 32) := by
    rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨h.rest.trans (hr5.trans (v6.rest _)), ?_, fun i hi => ?_⟩
  · rw [hm6]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
  · rw [hm6]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hi]) (by omega_using [hk, hi]) (by omega_using [hk])]; exact h.words i hi
    · rw [wd_write_self, ev]

theorem freeze_ok {s : State} (hc : Ctx b s) {o : Addr}
    (h3 : s.gpr .r3 = o) (hout : ∀ k < 14, InRegions s.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 56⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem o 56 = leBytes 56 (V s.mem b X2 % P) ∧ Rest clob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s.mem s'.mem ∧
      val32 (fun j => wd s'.mem o (4 * j)) 14 = V s.mem b X2 % P := by
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  have hA := ACC_eq
  obtain hl : ∀ k < 14, limb s.mem b X2 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨hf1, -, -⟩ := fold1_facts hl (c := 1) (by decide)
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  obtain hr2 : Rest [.r8, .r10] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain e10 : (s2.gpr .r10).toNat = 1 := by rw [u2.gpr]; rfl
  refine WP.append (pass_ok (rb := .r6) (o := Y) (s0 := s2) (c := foldL (limb s.mem b X2) 1)
    (cin := 1) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc2.r6]; exact hc2.inW (by omega_using [hY, hk]))
    (by rw [u2.other _ (by decide), u1.gpr]; rfl) hf1 (by decide) ?_) fun s3 hp3 => ?_
  · intro k hk s' hp
    obtain hc' : Ctx b s' := hc2.of_rest hp.rest (by decide)
    obtain ew : wd s'.mem b (X2 + 4 * k) = limb s.mem b X2 k := by
      rw [wd_pass hc2 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), hm2]; rfl
    unfold foldSrc
    refine WP.append (ldSrc_ok hc' (by omega_using [hX, hk])) fun t ⟨h7, hr, hm⟩ => ?_
    by_cases h7k : k = 7
    · simp only [h7k, ite_true]
      refine wp_add fun t1 v1 => WP.block_nil ⟨?_, (hr.trans (v1.rest (by decide))).mono (by decide),
        by rw [v1.mem, hm]⟩
      obtain e : (t.gpr .r10).toNat = 1 := by rw [hr.gpr _ (by decide), hp.rest.gpr _ (by decide), e10]
      have := limb_lt s.mem b X2 k
      rw [v1.gpr, toNat_add_lt (by rw [h7, ew, e]; omega_using [this]), h7, ew, e, foldL, h7k]; rfl
    · simp only [h7k, ite_false]
      exact WP.block_nil ⟨by rw [h7, ew, foldL]; simp only [h7k, ite_false, Nat.add_zero],
        hr.mono (by decide), hm⟩
  obtain hc3 : Ctx b s3 := hc2.of_rest hp3.rest (by decide)
  obtain hpo3 : ∀ j < 14, wd s3.mem b (Y + 4 * j) = fold1 (limb s.mem b X2) 1 j :=
    fun j hj => by have := hp3.outs j hj; rwa [hc2.r6] at this
  obtain hpf3 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩] s2.mem s3.mem := by
    have := hp3.frame; rwa [hc2.r6] at this
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  obtain hr5 : Rest [.r4, .r11] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  obtain hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  obtain hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  obtain h11 : s5.gpr .r11 = 0 - BitVec.ofNat 64 (fold1C (limb s.mem b X2) 1) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hp3.r8, toNat_imm (by omega_using [hS])]; rfl
  obtain hx5 : ∀ k < 14, limb s5.mem b X2 k = limb s.mem b X2 k := by
    intro k hk
    rw [limb, hm5, wd_frame hpf3 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      hm2]; rfl
  obtain hy5 : ∀ k < 14, limb s5.mem b Y k = fold1 (limb s.mem b X2) 1 k := by
    intro k hk; rw [limb, hm5, hpo3 k hk]
  obtain hr45 : Rest [.r4, .r5, .r7, .r8, .r10, .r11] s s5 :=
    (hr2.mono (by decide)).trans ((hp3.rest.mono (by decide)).trans (hr5.mono (by decide)))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h3]) (by rw [hr45.wr]; exact hout)
    hdisj hS h11) fun s6 h6' => ⟨?_, ?_, ?_, ?_⟩
  · rw [V, ← hv]
    refine bytesAt_words14 _ _ fun j hj => ?_
    rw [h6'.words j hj, hx5 j hj, hy5 j hj]; rfl
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have f1 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s2.mem s3.mem :=
      frame_sub1 hpf3 (Region.sub_prefix (Nat.le_refl _)) (List.mem_cons_self ..)
    obtain f2 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩, ⟨o, 56⟩] s5.mem s6.mem :=
      frame_sub1 h6'.frame (Region.sub_prefix (by omega_using []))
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rw [hm5] at f2
    rw [← hm2]
    exact f1.trans f2
  · rw [V, ← hv]
    exact val32_congr fun j hj => by rw [h6'.words j hj, hx5 j hj, hy5 j hj]; rfl

end

end VG.Proof.X448.PPC64LE
