module

import VerifiedGarbage.Proof.X448.RISCV64.Slots
public import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X448.Ladder
public import VerifiedGarbage.Spec.X448.Contract

/-! ### `X448.RISCV64.Setup`, which this module and modules that import it used -/

section

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
  obtain hlt := uLimb_lt s.mem pt k hk
  -- The limb in `a4`, then the stores.
  obtain key : ∀ (is : List Instr) (s2 : State), Rest [.a4, .a5] s s2 → s2.mem = s.mem →
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
    obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
    obtain ev : (s2.gpr .a4).setWidth 32 = BitVec.ofNat 32 (uLimb s.mem pt k) := by
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
  obtain u1 : Rest [.a4, .a5] s s1 := by
    rw [e1]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ hr.1, RegUpd.gpr_write_of_ne _ _ hr.2]
  obtain hm1 : s1.mem = s.mem := by rw [e1]; rfl
  obtain e7 : (s1.gpr .a4).toNat = uWord s.mem pt k := by
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
  obtain hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.mono (decodeStep_ok hk hcs (pt := pt) (by rw [hr.gpr _ (by decide), h5])
    (by rw [hr.rd, hr.wr]; exact hin)) fun s' ⟨e1, e3, hm, hr'⟩ => ⟨fun j hj => ?_, ?_, hr.trans hr'⟩
  · -- The words of the u-coordinate are as in `s0`.
    obtain hu : uLimb s.mem pt k = uLimb s0.mem pt k :=
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
  obtain u3 : Upd s2 s3 .a2 (sext32 39081) := by rw [e3]; exact Upd.write _ _ _
  obtain hr3 : Rest [.a2, .a4, .a5] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  obtain hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  obtain g7 : (s3.gpr .a4).setWidth 32 = 1 := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; rfl
  obtain g8 : s3.gpr .a5 = 0 := by rw [u3.other _ (by decide), u2.gpr]; rfl
  obtain g5 : (s3.gpr .a2).setWidth 32 = BitVec.ofNat 32 39081 := by
    rw [u3.gpr]; decide
  refine sw0_ok hc3 (d := X2) (by omega_arith) (by decide) fun s4 u4 => ?_
  refine sw0_ok (hc3.of_rest (u4.rest []) (by decide)) (d := Z2) (by omega_arith) (by decide) fun s5 u5 => ?_
  refine sw0_ok (hc3.of_rest ((u4.rest []).trans (u5.rest [])) (by decide)) (d := Z3) (by omega_arith) (by decide)
    fun s6 u6 => ?_
  obtain hr6 : Rest [] s3 s6 := (u4.rest []).trans ((u5.rest []).trans (u6.rest []))
  refine sw0_ok (hc3.of_rest hr6 (by decide)) (d := A24) (by omega_arith) (by decide) fun s8 u8 => ?_
  obtain hr8 : Rest [] s3 s8 := hr6.trans (u8.rest [])
  obtain hc8 : Ctx b s8 := hc3.of_rest hr8 (by decide)
  obtain hg8 : ∀ r, s8.gpr r = s3.gpr r := fun r => hr8.gpr r (by simp)
  obtain hm8 : s8.mem = (((s3.mem.writeW (b + BitVec.ofNat 64 X2) ((s3.gpr .a4).setWidth 32)).writeW
      (b + BitVec.ofNat 64 Z2) ((s3.gpr .a5).setWidth 32)).writeW (b + BitVec.ofNat 64 Z3)
      ((s3.gpr .a4).setWidth 32)).writeW (b + BitVec.ofNat 64 A24) ((s3.gpr .a2).setWidth 32) := by
    rw [u8.mem, u6.gpr, u6.mem, u5.gpr, u5.mem, u4.gpr, u4.mem]
  refine WP.append (stores_ok (r := .a5) (o := X2 + 4) (n := 13) (by omega_arith) (by decide) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  obtain hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (stores_ok (r := .a5) (o := Z2 + 4) (n := 13) (by omega_arith) (by decide) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  obtain hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.append (stores_ok (r := .a5) (o := Z3 + 4) (n := 13) (by omega_arith) (by decide) hc10)
    fun s11 ⟨w11, f11, g11, r11⟩ => ?_
  obtain hc11 : Ctx b s11 := hc10.of_rest r11 (by decide)
  refine WP.mono (stores_ok (r := .a5) (o := A24 + 4) (n := 13) (by omega_arith) (by decide) hc11)
    fun s12 ⟨w12, f12, g12, r12⟩ => ?_
  obtain e8 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .a5).toNat % 2 ^ 32 = 0 := fun t ht => by
    rw [ht, hg8, g8]; rfl
  -- Words written by the first stores, through the later ones.
  obtain k8 : ∀ d, d + 4 ≤ 2048 → (d + 4 ≤ X2 + 4 ∨ X2 + 56 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 56 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 56 ≤ d) → (d + 4 ≤ A24 + 4 ∨ A24 + 56 ≤ d) →
      wd s12.mem b d = wd s8.mem b d := fun d hd h1 h2 h3 h4 => by
    rw [wd_keep f12 h4 hd (by omega_arith), wd_keep f11 h3 hd (by omega_arith), wd_keep f10 h2 hd (by omega_arith),
      wd_keep f9 h1 hd (by omega_arith)]
  have g9' : s9.gpr = s8.gpr := g9
  obtain g10' : s10.gpr = s8.gpr := g10.trans g9
  obtain g11' : s11.gpr = s8.gpr := g11.trans g10'
  have t1 : (1 : BitVec 32).toNat = 1 := rfl
  obtain t0 : ((s3.gpr .a5).setWidth 32).toNat = 0 := by rw [g8]; rfl
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
    obtain m1 : (⟨b + BitVec.ofNat 64 X2, 112⟩ : Region) ∈ constsR b := List.mem_cons_self ..
    obtain m2 : (⟨b + BitVec.ofNat 64 Z3, 56⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_self ..)
    obtain m3 : (⟨b + BitVec.ofNat 64 A24, 56⟩ : Region) ∈ constsR b :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain f8 : Frame (constsR b) s.mem s8.mem := by
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

/-- The base point's u-coordinate, 5, as limbs. -/
abbrev fiveLimb (k : Nat) : Nat := if k = 0 then 5 else 0

theorem five_ok {s : State} (hc : Ctx b s) :
    WP isa (.block five) s fun s' =>
      (∀ k < 14, limb s'.mem b X1 k = fiveLimb k ∧ limb s'.mem b X3 k = fiveLimb k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s.mem s'.mem ∧ Rest [.a4, .a5] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 168 := rfl
  simp only [five, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  obtain hr2 : Rest [.a4, .a5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain g4 : (s2.gpr .a4).setWidth 32 = 5 := by rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain g5 : s2.gpr .a5 = 0 := by rw [u2.gpr]; rfl
  refine sw0_ok hc2 (d := X1) (by omega_arith) (by decide) fun s3 u3 => ?_
  refine sw0_ok (hc2.of_rest (u3.rest []) (by decide)) (d := X3) (by omega_arith) (by decide) fun s4 u4 => ?_
  obtain hr4 : Rest [] s2 s4 := (u3.rest []).trans (u4.rest [])
  obtain hc4 : Ctx b s4 := hc2.of_rest hr4 (by decide)
  obtain hg4 : ∀ r, s4.gpr r = s2.gpr r := fun r => hr4.gpr r (by simp)
  obtain hm4 : s4.mem = (s2.mem.writeW (b + BitVec.ofNat 64 X1) ((s2.gpr .a4).setWidth 32)).writeW
      (b + BitVec.ofNat 64 X3) ((s2.gpr .a4).setWidth 32) := by
    rw [u4.mem, u3.gpr, u3.mem]
  refine WP.append (stores_ok (r := .a5) (o := X1 + 4) (n := 13) (by omega_arith) (by decide) hc4)
    fun s5 ⟨w5, f5, g5', r5⟩ => ?_
  obtain hc5 : Ctx b s5 := hc4.of_rest r5 (by decide)
  refine WP.mono (stores_ok (r := .a5) (o := X3 + 4) (n := 13) (by omega_arith) (by decide) hc5)
    fun s6 ⟨w6, f6, _, r6⟩ => ?_
  obtain e5 : (s4.gpr .a5).toNat % 2 ^ 32 = 0 := by rw [hg4, g5]; rfl
  obtain e6 : (s5.gpr .a5).toNat % 2 ^ 32 = 0 := by rw [g5', hg4, g5]; rfl
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
    obtain f4 : Frame [⟨b + BitVec.ofNat 64 X1, 224⟩] s.mem s4.mem := by
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

/-- The precondition of `vg_x448(out = a0, scalar = a1, point = a2, scratch = a3)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 56⟩, ⟨s.gpr .a2, 56⟩]
  wr : s.wr = [⟨s.gpr .a0, 56⟩, ⟨s.gpr .a3, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a1, 56⟩
  out_pt : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a2, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .a0, 56⟩ ⟨s.gpr .a3, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .a1, 56⟩ ⟨s.gpr .a3, 8192⟩
  pt_ws : Region.Disjoint ⟨s.gpr .a2, 56⟩ ⟨s.gpr .a3, 8192⟩

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

theorem align_ok {s : State} (hws : (⟨s.gpr .a3, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block align) s fun s' => Ctx (wsB s) s' ∧ Rest [.a3] s s' ∧ s'.mem = s.mem := by
  unfold align
  refine wp_addi (by decide) fun s1 u1 => wp_andi (by decide) fun s2 u2 => WP.block_nil ?_
  obtain e7 : (BitVec.ofNat 64 7 : BitVec 64) = BitVec.ofInt 64 7 := by decide
  obtain e : s2.gpr .a3 = wsB s := by
    rw [u2.gpr, u1.gpr, e7, Align.align_eq]
  obtain hr : Rest [.a3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ⟨⟨e, Align.align_al _, fun d n hd => ?_⟩, hr, by rw [u2.mem, u1.mem]⟩
  have := Align.pad_lt (s.gpr .a3)
  rw [hr.wr, Offset.add_add]
  exact in_base hws (by omega_arith) (by omega_arith)

/-- The setup after `align` and the code that writes the u-coordinate's limbs
`f` into `X1` and `X3` (`decode` or `five`): `consts`, and the ladder's
initial state for `u = f`. -/
theorem consts_post {s s0 s4 : State} {f : Nat → Nat} (hc : Ctx (wsB s) s0) (hr0 : Rest [.a3] s s0)
    (hm0 : s0.mem = s.mem)
    (hl4 : ∀ k < 14, limb s4.mem (wsB s) X1 k = f k ∧ limb s4.mem (wsB s) X3 k = f k)
    (hf4 : Frame [⟨wsB s + BitVec.ofNat 64 X1, 224⟩] s0.mem s4.mem) (hr4 : Rest [.a4, .a5] s0 s4) :
    WP isa (.block consts) s4 fun s' =>
      Ctx (wsB s) s' ∧ Frame [⟨s.gpr .a3, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (wsB s) LQ (ladV (toFe (val32 f 14)) (VG.Proof.X448.init (toFe (val32 f 14)))) ∧
      Rest [.a2, .a3, .a4, .a5] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX2 : X2 = 56 := rfl
  have hZ2 : Z2 = 112 := rfl
  have hX3 : X3 = 168 := rfl
  have hZ3 : Z3 = 224 := rfl
  have hA : A24 = 784 := rfl
  rw [hm0] at hf4
  obtain hc4 : Ctx (wsB s) s4 := hc.of_rest hr4 (by decide)
  refine WP.mono (consts_ok hc4) fun s5 ⟨hx2, hz2, hz3, ha24, hf5, hr5⟩ => ?_
  -- `x1` and `x3` through the constants.
  obtain hkeep : ∀ o, (o = X1 ∨ o = X3) → ∀ k < 14, limb s5.mem (wsB s) o k = f k := by
    intro o ho k hk
    obtain e := limb_frame (o := o) hf5 fun r hr j hj => by
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
        iteF (show Z3 ≠ Z2 by decide), iteF (show Z3 ≠ X3 by decide), ite_true]; rfl
    · rw [slot_of ha24, val32_single _ (by decide)]
      simp only [ladV, iteF (show A24 ≠ X1 by decide), iteF (show A24 ≠ X2 by decide),
        iteF (show A24 ≠ Z2 by decide), iteF (show A24 ≠ X3 by decide), iteF (show A24 ≠ Z3 by decide)]; rfl
  · exact (hr0.mono (by decide)).trans ((hr4.mono (by decide)).trans (hr5.mono (by decide)))

theorem setup_ok {s : State} (hp : XPre s) :
    WP isa (.block (align ++ setup)) s fun s' =>
      Ctx (wsB s) s' ∧ Frame [⟨s.gpr .a3, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (wsB s) LQ (ladV (uOf s) (VG.Proof.X448.init (uOf s))) ∧
      Rest [.a2, .a3, .a4, .a5] s s' := by
  refine WP.append (align_ok (by rw [hp.wr]; simp)) fun s0 ⟨hc, hr0, hm0⟩ => ?_
  unfold setup
  refine WP.append (decode_ok hc (pt := s.gpr .a2) (hr0.gpr _ (by decide))
    (by rw [hr0.rd, hr0.wr, hp.rd]; simp) (hp.pt_ws.sub_right (Offset.sub_base _
      (by have := Align.pad_lt (s.gpr .a3); omega_arith))))
    fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  rw [hm0] at hl4
  obtain e : toFe (val32 (uLimb s.mem (s.gpr .a2)) 14) = uOf s := by rw [decode_val]; rfl
  rw [← e]
  exact consts_post hc hr0 hm0 hl4 hf4 hr4

theorem val32_five : toFe (val32 fiveLimb 14) = toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint) := by
  rw [val32_single _ (by decide), VG.Proof.X448.decodeUCoordinate_eq (by rfl)]; rfl

/-- `setupBase`: the ladder's initial state for the base point. -/
theorem setupBase_ok {s : State} (hws : (⟨s.gpr .a3, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (align ++ setupBase)) s fun s' =>
      Ctx (wsB s) s' ∧ Frame [⟨s.gpr .a3, 8192⟩] s.mem s'.mem ∧
      SlotsOk s'.mem (wsB s) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint))
        (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate VG.Spec.X448.basePoint)))) ∧
      Rest [.a2, .a3, .a4, .a5] s s' := by
  refine WP.append (align_ok hws) fun s0 ⟨hc, hr0, hm0⟩ => ?_
  unfold setupBase
  refine WP.append (five_ok hc) fun s4 ⟨hl4, hf4, hr4⟩ => ?_
  rw [← val32_five]
  exact consts_post hc hr0 hm0 hl4 hf4 hr4

end VG.Proof.X448.RISCV64

end

end

/-!
# X448 on RISCV64: the final reduction and the output

`freeze` stores the 56 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
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
  rest : Rest [.a2, .a4] s0 s
  frame : Frame [⟨O, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem O (4 * i) = r i

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : Addr} (h3 : s0.gpr .a0 = o)
    (hout : ∀ k < 14, InRegions s0.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 2048⟩ ⟨o, 56⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .t0 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block ((List.range 14).flatMap outStep)) s0
      (OutInv o (fun k => sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k)) s0 14) := by
  have hX : X2 = 56 := rfl
  have hY : Y = 896 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  obtain hw : ∀ d, d + 4 ≤ 2048 → wd s.mem b d = wd s0.mem b d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega_using [hk]))
  unfold outStep
  refine lw0_ok hcs (d := X2 + 4 * k) (by omega_using [hX, hk]) (by omega_arith) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.a2]) (by decide)) (by decide)) (d := Y + 4 * k)
    (by omega_using [hY, hk]) (by omega_arith) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => ?_
  obtain hr5 : Rest [.a2, .a4] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  obtain e3 : t5.gpr .a0 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h3]
  obtain hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine WP.mono (ByteLoad.storeLE32_ok (by decide) (by decide) (by omega_using [hk])
    (by rw [e3, hwr]; exact hout k hk)) fun t6 e6 => ?_
  obtain v6 : Rest [.a4] t5 t6 := by
    rw [e6]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩
  -- The limb selected.
  obtain ev : ((t5.gpr .a2).setWidth 32).toNat = sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k) := by
    obtain ex : t2.gpr .a2 = (s.mem.readW (b + BitVec.ofNat 64 (X2 + 4 * k)) 32).setWidth 64 := by
      rw [v2.other _ (by decide), v1.gpr]
    obtain ey : t2.gpr .a4 = (s.mem.readW (b + BitVec.ofNat 64 (Y + 4 * k)) 32).setWidth 64 := by
      rw [v2.gpr, v1.mem]
    obtain em : t3.gpr .t0 = 0 - BitVec.ofNat 64 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
    rw [v5.gpr, v4.other .a2 (by decide), v4.gpr, v3.other .a2 (by decide), v3.gpr, em, ex, ey]
    obtain hx := hw (X2 + 4 * k) (by omega_using [hX, hk])
    obtain hy := hw (Y + 4 * k) (by omega_using [hY, hk])
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, lo32_ext, hx]; rfl
    · rw [sel1r, lo32_ext, hy]; rfl
  obtain hm6 : t6.mem = s.mem.writeW (o + BitVec.ofNat 64 (4 * k)) ((t5.gpr .a2).setWidth 32) := by
    rw [e6, RegUpd.mem_write, e3]
    show t5.mem.writeW _ _ = _
    rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨h.rest.trans (hr5.trans (v6.mono (by decide))), ?_, fun i hi => ?_⟩
  · rw [hm6]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
  · rw [hm6]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hi]) (by omega_using [hk, hi]) (by omega_using [hk])]; exact h.words i hi
    · rw [wd_write_self, ev]

theorem freeze_ok {s : State} (hc : Ctx b s) {o : Addr}
    (h3 : s.gpr .a0 = o) (hout : ∀ k < 14, InRegions s.wr (o + BitVec.ofNat 64 (4 * k)) 4)
    (hdisj : Region.Disjoint ⟨b, 2048⟩ ⟨o, 56⟩) :
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
  obtain hr2 : Rest [.a5, .a7] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain e10 : (s2.gpr .a7).toNat = 1 := by rw [u2.gpr]; rfl
  refine WP.append (pass_ok (rb := .a3) (o := Y) (s0 := s2) (c := foldL (limb s.mem b X2) 1)
    (cin := 1) (by decide) (by decide)
    (fun k hk => by rw [hc2.a3]; exact hc2.inW (by omega_using [hY, hk]))
    (fun k hk => by rw [hc2.a3]; exact al4 hc2.al (by omega_using [hY]))
    (by rw [u2.other _ (by decide), u1.gpr]; rfl) hf1 (by decide) ?_) fun s3 hp3 => ?_
  · intro k hk s' hp
    obtain hc' : Ctx b s' := hc2.of_rest hp.rest (by decide)
    obtain ew : wd s'.mem b (X2 + 4 * k) = limb s.mem b X2 k := by
      rw [wd_pass hc2 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), hm2]; rfl
    unfold foldSrc
    refine WP.append (ldSrc_ok hc' (by omega_using [hX, hk]) (by omega_using [hX])) fun t ⟨h7, hr, hm⟩ => ?_
    by_cases h7k : k = 7
    · simp only [h7k, ite_true]
      refine wp_add fun t1 v1 => WP.block_nil ⟨?_, (hr.trans (v1.rest (by decide))).mono (by decide),
        by rw [v1.mem, hm]⟩
      obtain e : (t.gpr .a7).toNat = 1 := by rw [hr.gpr _ (by decide), hp.rest.gpr _ (by decide), e10]
      have := limb_lt s.mem b X2 k
      rw [v1.gpr, toNat_add_lt (by rw [h7, ew, e]; omega_using [this]), h7, ew, e, foldL, h7k]; rfl
    · simp only [h7k, ite_false]
      exact WP.block_nil ⟨by rw [h7, ew, foldL]; simp only [h7k, ite_false, Nat.add_zero],
        hr.mono (by decide), hm⟩
  obtain hc3 : Ctx b s3 := hc2.of_rest hp3.rest (by decide)
  obtain hpo3 : ∀ j < 14, wd s3.mem b (Y + 4 * j) = fold1 (limb s.mem b X2) 1 j :=
    fun j hj => by have := hp3.outs j hj; rwa [hc2.a3] at this
  obtain hpf3 : Frame [⟨b + BitVec.ofNat 64 Y, 56⟩] s2.mem s3.mem := by
    have := hp3.frame; rwa [hc2.a3] at this
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => ?_
  obtain hr5 : Rest [.a1, .t0] s3 s5 := (u4.rest (by decide)).trans (u5.rest (by decide))
  obtain hc5 : Ctx b s5 := hc3.of_rest hr5 (by decide)
  obtain hm5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  obtain h11 : s5.gpr .t0 = 0 - BitVec.ofNat 64 (fold1C (limb s.mem b X2) 1) := by
    rw [u5.gpr, u4.gpr, u4.other _ (by decide)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [hp3.a5, toNat_imm (by omega_using [hS])]; rfl
  obtain hx5 : ∀ k < 14, limb s5.mem b X2 k = limb s.mem b X2 k := by
    intro k hk
    rw [limb, hm5, wd_frame hpf3 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      hm2]; rfl
  obtain hy5 : ∀ k < 14, limb s5.mem b Y k = fold1 (limb s.mem b X2) 1 k := by
    intro k hk; rw [limb, hm5, hpo3 k hk]
  obtain hr45 : Rest [.a1, .a2, .a4, .a5, .a7, .t0] s s5 :=
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

end VG.Proof.X448.RISCV64
