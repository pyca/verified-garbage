module
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X448.Bytes

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X448.Ladder
public import VerifiedGarbage.Spec.X448.Contract

/-!
# X448 on RISCV64: the setup

The u-coordinate as 32-bit limbs (`decode_val`: the number of its 56 bytes), and the setup of the working space: `x1 = x3 = u`, `x2 = z3 =
1`, `z2 = 0` and `a24`, in the working space rounded up to a multiple of 8
(`setup_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Impl.Words.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P Fe bytesAt a24)
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
    (h5 : s.gpr .a2 = pt) (hin : (⟨pt, 56⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      wd s'.mem b (X1 + 4 * k) = uLimb s.mem pt k ∧
      wd s'.mem b (X3 + 4 * k) = uLimb s.mem pt k ∧
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (X1 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k))).writeW
        (b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k)) ∧
      Rest [.a4, .a5] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  have hlt := uLimb_lt s.mem pt k hk
  -- The limb in `a4`, then the stores.
  have key : ∀ (is : List Instr) (s2 : State), Rest [.a4, .a5] s s2 → s2.mem = s.mem →
      (s2.gpr .a4).toNat = uLimb s.mem pt k →
      is = [.store .w .a4 .a3 (X1 + 4 * k), .store .w .a4 .a3 (X3 + 4 * k)] →
      WP isa (.block is) s2 fun s' =>
        wd s'.mem b (X1 + 4 * k) = uLimb s.mem pt k ∧
        wd s'.mem b (X3 + 4 * k) = uLimb s.mem pt k ∧
        s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (X1 + 4 * k))
          (BitVec.ofNat 32 (uLimb s.mem pt k))).writeW
          (b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k)) ∧
        Rest [.a4, .a5] s s' := by
    intro is s2 hr2 hm2 e7 his
    subst his
    have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
    have ev : (s2.gpr .a4).setWidth 32 = BitVec.ofNat 32 (uLimb s.mem pt k) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_lo32, e7, BitVec.toNat_ofNat]
    refine sw0_ok hc2 (d := X1 + 4 * k) (by omega_arith) (by omega_arith) fun s4 u4 => ?_
    refine sw0_ok (hc2.of_rest (u4.rest []) (by decide)) (d := X3 + 4 * k) (by omega_arith) (by omega_arith) fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_, hr2.trans ((u4.rest _).trans (u5.rest _))⟩
    · rw [u5.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u4.mem, wd_write_self, ev,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · rw [u5.mem, wd_write_self, u4.gpr, ev, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · rw [u5.mem, u4.gpr, u4.mem, hm2, ev]
  unfold decodeStep
  refine WP.append (ByteLoad.loadLE32_ok (by decide) (by decide) (by decide) (by omega_arith)
    (by rw [h5]; exact in_base hin (by omega_arith) (by omega_arith))) fun s1 e1 => ?_
  have u1 : Rest [.a4, .a5] s s1 := by
    rw [e1]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ hr.1, RegUpd.gpr_write_of_ne _ _ hr.2]
  have hm1 : s1.mem = s.mem := by rw [e1]; rfl
  have e7 : (s1.gpr .a4).toNat = uWord s.mem pt k := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, h5]; rfl
  exact key _ s1 u1 hm1 e7 rfl

theorem decode_ok {s0 : State} (hc : Ctx b s0) {pt : Addr} (h5 : s0.gpr .a2 = pt)
    (hin : (⟨pt, 56⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨pt, 56⟩ ⟨b, 2048⟩) :
    WP isa (.block ((List.range 14).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 14, limb s'.mem b X1 k = uLimb s0.mem pt k ∧ limb s'.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s0.mem s'.mem ∧ Rest [.a4, .a5] s0 s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, limb s.mem b X1 k = uLimb s0.mem pt k ∧ limb s.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s0.mem s.mem ∧ Rest [.a4, .a5] s0 s)
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
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hb : d + 4 ≤ 2048) (ho : o + n ≤ 2048) : wd m' B d = wd m B d :=
  wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_arith) (by omega_arith)

/-- The ranges `consts` writes. -/
abbrev constsR (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 X2, 112⟩, ⟨b + BitVec.ofNat 64 Z3, 56⟩, ⟨b + BitVec.ofNat 64 A24, 56⟩]

theorem constsR_sub (e k o n : Nat) (he : (⟨b + BitVec.ofNat 64 e, k⟩ : Region) ∈ constsR b)
    (h1 : e ≤ o) (h2 : o + n ≤ e + k) : ∃ r ∈ constsR b, Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ r :=
  ⟨_, he, Offset.sub b h1 h2⟩

theorem consts_ok {s : State} (hc : Ctx b s) :
    WP isa (.block consts) s fun s' =>
      (∀ k < 14, limb s'.mem b X2 k = if k = 0 then 1 else 0) ∧
      (∀ k < 14, limb s'.mem b Z2 k = 0) ∧
      (∀ k < 14, limb s'.mem b Z3 k = if k = 0 then 1 else 0) ∧
      (∀ k < 14, limb s'.mem b A24 k = if k = 0 then 39081 else 0) ∧
      Frame (constsR b) s.mem s'.mem ∧ Rest [.a2, .a4, .a5] s s' := by
  have hX2 : X2 = 56 := rfl
  have hZ2 : Z2 = 112 := rfl
  have hZ3 : Z3 = 224 := rfl
  have hA : A24 = 784 := rfl
  simp only [consts, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 =>
    WP.append (ByteLoad.li32_ok (d := .a2) 39081) fun s3 e3 => ?_
  have u3 : Upd s2 s3 .a2 (sext32 39081) := by rw [e3]; exact Upd.write _ _ _
  have hr3 : Rest [.a2, .a4, .a5] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have g7 : (s3.gpr .a4).setWidth 32 = 1 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  have g8 : s3.gpr .a5 = 0 := by rw [u3.other _ (by decide), u2.gpr]; rfl
  have g5 : (s3.gpr .a2).setWidth 32 = BitVec.ofNat 32 39081 := by
    rw [u3.gpr]; decide
  refine sw0_ok hc3 (d := X2) (by omega_arith) (by decide) fun s4 u4 => ?_
  refine sw0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := Z2) (by omega_arith) (by decide) fun s5 u5 => ?_
  refine sw0_ok (hc3.of_rest ((u4.rest []).trans (u5.rest [])) (by decide)) (d := Z3) (by omega_arith) (by decide)
    fun s6 u6 => ?_
  have hr6 : Rest [] s3 s6 := (u4.rest []).trans ((u5.rest []).trans (u6.rest []))
  refine sw0_ok (hc3.of_rest hr6 (by decide)) (d := A24) (by omega_arith) (by decide) fun s8 u8 => ?_
  have hr8 : Rest [] s3 s8 := hr6.trans (u8.rest [])
  have hc8 : Ctx b s8 := hc3.of_rest hr8 (by decide)
  have hg8 : ∀ r, s8.gpr r = s3.gpr r := fun r => hr8.gpr r (by simp)
  have hm8 : s8.mem = (((s3.mem.writeW (b + BitVec.ofNat 64 X2) ((s3.gpr .a4).setWidth 32)).writeW
      (b + BitVec.ofNat 64 Z2) ((s3.gpr .a5).setWidth 32)).writeW (b + BitVec.ofNat 64 Z3)
      ((s3.gpr .a4).setWidth 32)).writeW (b + BitVec.ofNat 64 A24) ((s3.gpr .a2).setWidth 32) := by
    rw [u8.mem, u6.gpr, u6.mem, u5.gpr, u5.mem, u4.gpr, u4.mem]
  refine WP.append (stores_ok (r := .a5) (o := X2 + 4) (n := 13) (by omega_arith) (by decide) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (stores_ok (r := .a5) (o := Z2 + 4) (n := 13) (by omega_arith) (by decide) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.append (stores_ok (r := .a5) (o := Z3 + 4) (n := 13) (by omega_arith) (by decide) hc10)
    fun s11 ⟨w11, f11, g11, r11⟩ => ?_
  have hc11 : Ctx b s11 := hc10.of_rest r11 (by decide)
  refine WP.mono (stores_ok (r := .a5) (o := A24 + 4) (n := 13) (by omega_arith) (by decide) hc11)
    fun s12 ⟨w12, f12, g12, r12⟩ => ?_
  have e8 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .a5).toNat % 2 ^ 32 = 0 := fun t ht => by
    rw [ht, hg8, g8]; rfl
  -- Words written by the first stores, through the later ones.
  have k8 : ∀ d, d + 4 ≤ 2048 → (d + 4 ≤ X2 + 4 ∨ X2 + 56 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 56 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 56 ≤ d) → (d + 4 ≤ A24 + 4 ∨ A24 + 56 ≤ d) →
      wd s12.mem b d = wd s8.mem b d := fun d hd h1 h2 h3 h4 => by
    rw [wd_keep f12 h4 hd (by omega_arith), wd_keep f11 h3 hd (by omega_arith), wd_keep f10 h2 hd (by omega_arith),
      wd_keep f9 h1 hd (by omega_arith)]
  have g9' : s9.gpr = s8.gpr := g9
  have g10' : s10.gpr = s8.gpr := g10.trans g9
  have g11' : s11.gpr = s8.gpr := g11.trans g10'
  have t1 : (1 : BitVec 32).toNat = 1 := rfl
  have t0 : ((s3.gpr .a5).setWidth 32).toNat = 0 := by rw [g8]; rfl
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_self, g7, t1]; rfl
    · rw [limb, wd_keep f12 (by omega_arith) (by omega_arith) (by omega_arith), wd_keep f11 (by omega_arith) (by omega_arith) (by omega_arith),
        wd_keep f10 (by omega_arith) (by omega_arith) (by omega_arith), show X2 + 4 * k = X2 + 4 + 4 * (k - 1) by omega_arith,
        w9 (k - 1) (by omega_arith), e8 _ rfl]
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_self, t0]
    · rw [limb, wd_keep f12 (by omega_arith) (by omega_arith) (by omega_arith), wd_keep f11 (by omega_arith) (by omega_arith) (by omega_arith),
        show Z2 + 4 * k = Z2 + 4 + 4 * (k - 1) by omega_arith, w10 (k - 1) (by omega_arith), e8 _ g9']
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero, k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        wd_write_self, g7, t1]; rfl
    · rw [limb, wd_keep f12 (by omega_arith) (by omega_arith) (by omega_arith), show Z3 + 4 * k = Z3 + 4 + 4 * (k - 1) by omega_arith,
        w11 (k - 1) (by omega_arith), e8 _ g10']
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [limb, Nat.mul_zero, Nat.add_zero,
        k8 _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), hm8,
        wd_write_self, g5]; rfl
    · rw [limb, show A24 + 4 * k = A24 + 4 + 4 * (k - 1) by omega_arith, w12 (k - 1) (by omega_arith), e8 _ g11']
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · -- Every write is in `constsR`.
    have m1 : (⟨b + BitVec.ofNat 64 X2, 112⟩ : Region) ∈ constsR b := List.mem_cons_self ..
    have m2 : (⟨b + BitVec.ofNat 64 Z3, 56⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have m3 : (⟨b + BitVec.ofNat 64 A24, 56⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have f8 : Frame (constsR b) s.mem s8.mem := by
      rw [hm8, u3.mem, u2.mem, u1.mem]
      exact ((((Frame.refl _ _).writeW m1 _ (Offset.contains _ (d := X2) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))).writeW m1 _ (Offset.contains _ (d := Z2) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))).writeW m2 _ (Offset.contains _ (d := Z3) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))).writeW m3 _ (Offset.contains _ (d := A24) (n := 32 / 8) (by omega_arith) (by omega_arith)
        (by omega_arith))
    exact f8.trans ((f9.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega_arith) (by omega_arith)).trans
      ((f10.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m1 (by omega_arith) (by omega_arith)).trans
      ((f11.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m2 (by omega_arith) (by omega_arith)).trans
      (f12.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact constsR_sub _ _ _ _ m3 (by omega_arith) (by omega_arith)))))
  · exact hr3.trans ((hr8.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      ((r11.mono (by decide)).trans (r12.mono (by decide))))))

end

/-! ## The whole setup -/

/-- The precondition of `vg_x448(out = a0, scalar = a1, point = a2, scratch = a3)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 56⟩, ⟨s.gpr .a2, 56⟩]
  wr : s.wr = [⟨s.gpr .a0, 56⟩, ⟨s.gpr .a3, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a1, 56⟩
  out_pt : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a2, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a3, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .a1, 56⟩ ⟨s.gpr .a3, 8192⟩
  pt_ws : Region.Disjoint ⟨s.gpr .a2, 56⟩ ⟨s.gpr .a3, 8192⟩

/-- A region disjoint from the working space is disjoint from its first 2048 bytes. -/
theorem disj2048 {r : Region} {b : Addr} (h : Region.Disjoint r ⟨b, 8192⟩) : Region.Disjoint r ⟨b, 2048⟩ :=
  h.sub_right (Region.sub_prefix (by decide))

/-- The u-coordinate, decoded. -/
def uOf (s : State) : Fe :=
  toFe (VG.Spec.X448.decodeUCoordinate (bytesAt s.mem (s.gpr .a2) 56))

theorem slot_of {m : Mem} {B : Addr} {o : Nat} {f : Nat → Nat} (h : ∀ k < 14, limb m B o k = f k) :
    FS m B o = toFe (val32 f 14) := by rw [FS, V, val32_congr h]

/-- The working space rounded up to a multiple of 8, as `align` leaves it in
`a3`. -/
abbrev wsB (s : State) : Addr := s.gpr .a3 + BitVec.ofNat 64 (Align.pad (s.gpr .a3))

/-- A range of the rounded working space, in the working space. -/
theorem wsB_sub (s : State) {o n : Nat} (h : o + n ≤ 2048) :
    Region.Sub ⟨wsB s + BitVec.ofNat 64 o, n⟩ ⟨s.gpr .a3, 8192⟩ := by
  have := Align.pad_lt (s.gpr .a3)
  rw [Offset.add_add]
  exact Offset.sub_base _ (by omega_arith)

theorem align_ok {s : State} (hp : XPre s) :
    WP isa (.block align) s fun s' => Ctx (wsB s) s' ∧ Rest [.a3] s s' ∧ s'.mem = s.mem := by
  have hws : (⟨s.gpr .a3, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold align
  refine wp_addi (by decide) fun s1 u1 => wp_andi (by decide) fun s2 u2 => WP.block_nil ?_
  have e7 : (BitVec.ofNat 64 7 : BitVec 64) = BitVec.ofInt 64 7 := by decide
  have e : s2.gpr .a3 = wsB s := by
    rw [u2.gpr, u1.gpr, e7, Align.align_eq]
  have hr : Rest [.a3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ⟨⟨e, Align.align_al _, fun d n hd => ?_⟩, hr, by rw [u2.mem, u1.mem]⟩
  have := Align.pad_lt (s.gpr .a3)
  rw [hr.wr, Offset.add_add]
  exact in_base hws (by omega_arith) (by omega_arith)

theorem setup_ok {s : State} (hp : XPre s) :
    WP isa (.block (align ++ setup)) s fun s' =>
      Ctx (wsB s) s' ∧ Frame [⟨s.gpr .a3, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (wsB s) LQ (ladV (uOf s) (VG.Proof.X448.init (uOf s))) ∧
      Rest [.a2, .a3, .a4, .a5] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX2 : X2 = 56 := rfl
  have hZ2 : Z2 = 112 := rfl
  have hX3 : X3 = 168 := rfl
  have hZ3 : Z3 = 224 := rfl
  have hA : A24 = 784 := rfl
  refine WP.append (align_ok hp) fun s0 ⟨hc, hr0, hm0⟩ => ?_
  unfold setup
  refine WP.append (decode_ok hc (pt := s.gpr .a2) (hr0.gpr _ (by decide))
    (by rw [hr0.rd, hr0.wr, hp.rd]; simp) (hp.pt_ws.sub_right (Offset.sub_base _
      (by have := Align.pad_lt (s.gpr .a3); omega_arith))))
    fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  rw [hm0] at hl4 hf4
  have hc4 : Ctx (wsB s) s4 := hc.of_rest hr4 (by decide)
  refine WP.mono (consts_ok hc4) fun s5 ⟨hx2, hz2, hz3, ha24, hf5, hr5⟩ => ?_
  -- `x1` and `x3` through the constants.
  have hkeep : ∀ o, (o = X1 ∨ o = X3) → ∀ k < 14,
      limb s5.mem (wsB s) o k = uLimb s.mem (s.gpr .a2) k := by
    intro o ho k hk
    have e := limb_frame (o := o) hf5 fun r hr j hj => by
      simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [e k hk]
    rcases ho with rfl | rfl
    · exact (hl4 k hk).1
    · exact (hl4 k hk).2
  refine ⟨hc4.of_rest hr5 (by decide), ?_, ?_, ?_⟩
  · refine (hf4.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact wsB_sub s (by omega_arith)⟩).trans ?_
    refine hf5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [constsR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact wsB_sub s (by omega_arith)
  · intro q hq
    simp only [LQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [slot_of (hkeep _ (.inl rfl)), decode_val]; simp only [ladV, ite_true]; rfl
    · rw [slot_of hx2, val32_single _ (by decide)]
      simp only [ladV, VG.Proof.X448.init, iteF (show X2 ≠ X1 by decide), ite_true]; rfl
    · rw [slot_of hz2, val32_zero_fn]
      simp only [ladV, VG.Proof.X448.init, iteF (show Z2 ≠ X1 by decide), iteF (show Z2 ≠ X2 by decide),
        ite_true]; rfl
    · rw [slot_of (hkeep _ (.inr rfl)), decode_val]
      simp only [ladV, VG.Proof.X448.init, iteF (show X3 ≠ X1 by decide), iteF (show X3 ≠ X2 by decide),
        iteF (show X3 ≠ Z2 by decide), ite_true]; rfl
    · rw [slot_of hz3, val32_single _ (by decide)]
      simp only [ladV, VG.Proof.X448.init, iteF (show Z3 ≠ X1 by decide), iteF (show Z3 ≠ X2 by decide),
        iteF (show Z3 ≠ Z2 by decide), iteF (show Z3 ≠ X3 by decide), ite_true]; rfl
    · rw [slot_of ha24, val32_single _ (by decide)]
      simp only [ladV, iteF (show A24 ≠ X1 by decide), iteF (show A24 ≠ X2 by decide),
        iteF (show A24 ≠ Z2 by decide), iteF (show A24 ≠ X3 by decide), iteF (show A24 ≠ Z3 by decide)]; rfl
  · exact (hr0.mono (by decide)).trans ((hr4.mono (by decide)).trans (hr5.mono (by decide)))

end VG.Proof.X448.RISCV64
