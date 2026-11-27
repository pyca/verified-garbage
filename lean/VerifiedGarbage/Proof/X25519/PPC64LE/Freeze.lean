module

public import VerifiedGarbage.Proof.X25519.Bytes
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `X25519.PPC64LE.Setup`, which this module and modules that import it used -/

section

/-!
# X25519 on PPC64LE: the setup

The u-coordinate as 32-bit limbs (`decode_val`: the number of its 32 bytes
modulo `2²⁵⁵`), and the two halves of `setup`: `x1 = x3 = u` (`decode_ok`),
then `x2 = z3 = 1` and `z2 = 0` (`consts_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leNum leNum_append bytesAt_add length_bytesAt toFe)

/-! ## The u-coordinate as limbs -/

/-- Word `k` at `p`. -/
def uWord (m : Mem) (p : Addr) (k : Nat) : Nat := wd m p (4 * k)

/-- Limb `k` of the decoded u-coordinate: word `k`, the top bit masked. -/
def uLimb (m : Mem) (p : Addr) (k : Nat) : Nat := mask31 (uWord m p) k

theorem leNum_bytesAt4 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (4 * n)) = val32 (uWord m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 from rfl, bytesAt_add, leNum_append, leNum_bytesAt4 m p n, val32_succ,
      length_bytesAt, Proof.X25519.leNum_bytesAt_32bit, show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]
    rfl

theorem uLimb_lt (m : Mem) (p : Addr) : ∀ k < 8, uLimb m p k < 2 ^ 32 :=
  (mask31_facts fun k _ => wd_lt m p (4 * k)).2.2.1

/-- The limbs of the decoded u-coordinate. -/
theorem decode_val (m : Mem) (p : Addr) :
    val32 (uLimb m p) 8 = VG.Spec.X25519.decodeUCoordinate (bytesAt m p 32) := by
  rw [VG.Proof.X25519.decodeUCoordinate_eq (length_bytesAt m p 32), show 32 = 4 * 8 from rfl,
    leNum_bytesAt4]
  obtain ⟨e, hlt, -, -⟩ := mask31_facts (l := uWord m p) fun k _ => wd_lt m p (4 * k)
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rfl

theorem low31_val (x : BitVec 64) : ((x <<< 33) >>> 33).toNat = x.toNat % 2 ^ 31 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 64 = 2 ^ 31 * 2 ^ 33 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

section
variable {b : Addr}

/-! ## Decoding the u-coordinate -/

theorem decodeStep_ok {k : Nat} (hk : k < 8) {s : State} (hc : Ctx b s) {pt : Addr}
    (h5 : s.gpr .r5 = pt) (hin : (⟨pt, 32⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (decodeStep k)) s fun s' =>
      wd s'.mem b (X1 + 4 * k) = uLimb s.mem pt k ∧
      wd s'.mem b (X3 + 4 * k) = uLimb s.mem pt k ∧
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 (X1 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k))).writeW
        (b + BitVec.ofNat 64 (X3 + 4 * k)) (BitVec.ofNat 32 (uLimb s.mem pt k)) ∧
      Rest [.r7] s s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 96 := rfl
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
  by_cases h7 : k = 7
  · simp only [h7, ite_true, low31]
    refine wp_lsl (by decide) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
    subst h7
    refine key _ s3 ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
      (by rw [u3.mem, u2.mem, u1.mem]) ?_ rfl
    rw [u3.gpr, u2.gpr, low31_val, e7]; rfl
  · simp only [h7, ite_false]
    exact key _ s1 (u1.rest (by decide)) u1.mem (by rw [e7]; simp only [uLimb, mask31, h7, ite_false]) rfl

theorem decode_ok {s0 : State} (hc : Ctx b s0) {pt : Addr} (h5 : s0.gpr .r5 = pt)
    (hin : (⟨pt, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨pt, 32⟩ ⟨b, 4096⟩) :
    WP isa (.block ((List.range 8).flatMap decodeStep)) s0 fun s' =>
      (∀ k < 8, limb s'.mem b X1 k = uLimb s0.mem pt k ∧ limb s'.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 128⟩] s0.mem s'.mem ∧ Rest [.r7] s0 s' := by
  have hX1 : X1 = 0 := rfl
  have hX3 : X3 = 96 := rfl
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s => (∀ k < n, limb s.mem b X1 k = uLimb s0.mem pt k ∧ limb s.mem b X3 k = uLimb s0.mem pt k) ∧
      Frame [⟨b + BitVec.ofNat 64 X1, 128⟩] s0.mem s.mem ∧ Rest [.r7] s0 s)
    (fun k s hk ⟨h1, hf, hr⟩ => ?_) 8 (Nat.le_refl _) s0
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s' h => h
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.mono (decodeStep_ok hk hcs (pt := pt) (by rw [hr.gpr _ (by decide), h5])
    (by rw [hr.rd, hr.wr]; exact hin)) fun s' ⟨e1, e3, hm, hr'⟩ => ⟨fun j hj => ?_, ?_, hr.trans hr'⟩
  · -- The words of the u-coordinate are as in `s0`.
    have hu : uLimb s.mem pt k = uLimb s0.mem pt k := by
      have hw : ∀ j < 8, uWord s.mem pt j = uWord s0.mem pt j := fun j hj =>
        wd_frame hf fun r hr' => by
          rw [List.mem_singleton.mp hr']
          exact (hd.sub_left (Offset.sub_base pt (d := 4 * j) (n := 4) (by omega_arith))).sub_right
            (Offset.sub_base b (d := X1) (n := 128) (by omega_arith))
      simp only [uLimb, mask31]
      split
      · rename_i h; subst h; rw [hw 7 (by decide)]
      · exact hw k hk
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
  [⟨b + BitVec.ofNat 64 X2, 64⟩, ⟨b + BitVec.ofNat 64 Z3, 32⟩]

theorem constsR_sub (e k o n : Nat) (he : (⟨b + BitVec.ofNat 64 e, k⟩ : Region) ∈ constsR b)
    (h1 : e ≤ o) (h2 : o + n ≤ e + k) : ∃ r ∈ constsR b, Region.Sub ⟨b + BitVec.ofNat 64 o, n⟩ r :=
  ⟨_, he, Offset.sub b h1 h2⟩

theorem consts_ok {s : State} (hc : Ctx b s) :
    WP isa (.block consts) s fun s' =>
      (∀ k < 8, limb s'.mem b X2 k = if k = 0 then 1 else 0) ∧
      (∀ k < 8, limb s'.mem b Z2 k = 0) ∧
      (∀ k < 8, limb s'.mem b Z3 k = if k = 0 then 1 else 0) ∧
      Frame (constsR b) s.mem s'.mem ∧ Rest [.r7, .r8] s s' := by
  have hX2 : X2 = 32 := rfl
  have hZ2 : Z2 = 64 := rfl
  have hZ3 : Z3 = 128 := rfl
  simp only [consts, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.r7, .r8] s s3 := (u1.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have g7 : (s3.gpr .r7).setWidth 32 = 1 := by rw [u3.other _ (by decide), u1.gpr]; rfl
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
  refine WP.append (stores_ok (r := .r8) (o := X2 + 4) (n := 7) (by omega_arith) hc8) fun s9 ⟨w9, f9, g9, r9⟩ => ?_
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.append (stores_ok (r := .r8) (o := Z2 + 4) (n := 7) (by omega_arith) hc9) fun s10 ⟨w10, f10, g10, r10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  refine WP.mono (stores_ok (r := .r8) (o := Z3 + 4) (n := 7) (by omega_arith) hc10)
    fun s11 ⟨w11, f11, _, r11⟩ => ?_
  have e8 : ∀ t : State, t.gpr = s8.gpr → (t.gpr .r8).toNat % 2 ^ 32 = 0 := fun t ht => by
    rw [ht, hg8, g8]; rfl
  -- Words written by the first stores, through the later ones.
  have k8 : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ X2 + 4 ∨ X2 + 32 ≤ d) → (d + 4 ≤ Z2 + 4 ∨ Z2 + 32 ≤ d) →
      (d + 4 ≤ Z3 + 4 ∨ Z3 + 32 ≤ d) → wd s11.mem b d = wd s8.mem b d := fun d hd h1 h2 h3 => by
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
    · rw [limb, show Z3 + 4 * k = Z3 + 4 + 4 * (k - 1) by omega_arith,
        w11 (k - 1) (by omega_arith), e8 _ g10']
      simp only [show k ≠ 0 by omega_arith, ite_false]
  · -- Every write is in `constsR`.
    have m1 : (⟨b + BitVec.ofNat 64 X2, 64⟩ : Region) ∈ constsR b := List.mem_cons_self ..
    have m2 : (⟨b + BitVec.ofNat 64 Z3, 32⟩ : Region) ∈ constsR b :=
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

end

/-! ## The precondition -/

/-- The precondition of `vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`, by field. -/
structure XPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩, ⟨s.gpr .r5, 32⟩]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 4096⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r4, 32⟩
  out_pt : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r5, 32⟩
  out_ws : Region.Disjoint ⟨s.gpr .r3, 32⟩ ⟨s.gpr .r6, 4096⟩
  sc_ws : Region.Disjoint ⟨s.gpr .r4, 32⟩ ⟨s.gpr .r6, 4096⟩
  pt_ws : Region.Disjoint ⟨s.gpr .r5, 32⟩ ⟨s.gpr .r6, 4096⟩

end VG.Proof.X25519.PPC64LE

end

end

/-!
# X25519 on PPC64LE: the final reduction and the output

`freeze` stores the 32 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)

/-- The field area `[0, ACC + 64)` of the working space: the elements and
the product at `ACC`. -/
abbrev FA (b : Addr) : Region := ⟨b, ACC + 64⟩

theorem sel0r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 0)) = a := by simp

theorem sel1r (a c : BitVec 64) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 64 1)) = c := by
  have : (0 : BitVec 64) - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

section
variable {b : Addr}

/-- The start of `freeze`: bit 255 of `[X2]` cleared, 19 times it in `r8`. -/
theorem freezeA_ok {X2 : Nat} (hX : X2 + 32 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (freezeAAt X2)) s fun s' =>
      (s'.gpr .r8).toNat = 19 * (limb s.mem b X2 7 / 2 ^ 31) ∧
      (∀ k < 8, limb s'.mem b X2 k = mask31 (limb s.mem b X2) k) ∧
      Frame [⟨b + BitVec.ofNat 64 X2, 32⟩] s.mem s'.mem ∧
      Rest [.r5, .r7, .r8] s s' := by
  simp only [freezeAAt, low31, List.cons_append, List.nil_append]
  refine lw0_ok hc (d := X2 + 28) (by omega_using [hX]) fun s2 u2 => ?_
  refine wp_lsr (by decide) fun s3 u3 => wp_lsl (by decide) fun s4 u4 =>
    wp_lsr (by decide) fun s5 u5 => ?_
  have hr5 : Rest [.r7, .r8] s s5 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine sw0_ok hc5 (d := X2 + 28) (by omega_using [hX]) fun s6 u6 => ?_
  refine wp_li (by decide) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl7 := limb_lt s.mem b X2 7
  have e2 : (s2.gpr .r7).toNat = limb s.mem b X2 7 := by rw [u2.gpr, toNat_ext32]; rfl
  have e5 : (s5.gpr .r7).toNat = limb s.mem b X2 7 % 2 ^ 31 := by
    rw [u5.gpr, u4.gpr, low31_val, u3.other .r7 (by decide), e2]
  have e3 : (s3.gpr .r8).toNat = limb s.mem b X2 7 / 2 ^ 31 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (b + BitVec.ofNat 64 (X2 + 28)) ((s5.gpr .r7).setWidth 32) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
  have t19 : (BitVec.ofNat 64 19).toNat = 19 := rfl
  refine ⟨?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.gpr, u7.gpr, u7.other _ (by decide), u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3, t19]; omega_using [hl7]), e3, t19, Nat.mul_comm]
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 7 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hX, h]) (by omega_using [hX])]
      simp only [mask31, show k ≠ 7 by omega_using [h], ite_false]; rfl
    · rw [show X2 + 4 * k = X2 + 28 by omega_using [hk, h], wd_write_self, toNat_lo32, e5,
        show k = 7 by omega_using [hk, h], Nat.mod_eq_of_lt (by omega_using [])]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := X2 + 28) (n := 32 / 8) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hX]))
  · exact hr5.mono (by decide) |>.trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [Y])` in `r11`, and bit 255 of `[Y]` cleared. -/
theorem freezeB_ok {Y : Nat} (hY : Y + 32 ≤ 4096) {s : State} (hc : Ctx b s) :
    WP isa (.block (freezeBAt Y)) s fun s' =>
      s'.gpr .r11 = 0 - BitVec.ofNat 64 (limb s.mem b Y 7 / 2 ^ 31) ∧
      (∀ k < 8, limb s'.mem b Y k = mask31 (limb s.mem b Y) k) ∧
      Frame [⟨b + BitVec.ofNat 64 Y, 32⟩] s.mem s'.mem ∧ Rest [.r4, .r7, .r11] s s' := by
  simp only [freezeBAt, low31, List.cons_append, List.nil_append]
  refine lw0_ok hc (d := Y + 28) (by omega_using [hY]) fun s1 u1 => ?_
  refine wp_lsr (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 =>
    wp_sub fun s4 u4 => wp_lsl (by decide) fun s5 u5 => wp_lsr (by decide) fun s6 u6 => ?_
  have hr6 : Rest [.r4, .r7, .r11] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine sw0_ok (hc.of_rest hr6 (by decide)) (d := Y + 28) (by omega_using [hY]) fun s7 u7 => WP.block_nil ?_
  have e1 : (s1.gpr .r7).toNat = limb s.mem b Y 7 := by rw [u1.gpr, toNat_ext32]; rfl
  have hm7 : s7.mem = s.mem.writeW (b + BitVec.ofNat 64 (Y + 28)) ((s6.gpr .r7).setWidth 32) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := limb_lt s.mem b Y 7; omega_using [this])]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 7 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hY, h]) (by omega_using [hY])]
      simp only [mask31, show k ≠ 7 by omega_using [h], ite_false]; rfl
    · have hl7 := limb_lt s.mem b Y 7
      rw [show Y + 4 * k = Y + 28 by omega_using [hk, h], wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val,
        u4.other .r7 (by decide), u3.other .r7 (by decide), u2.other .r7 (by decide), e1,
        show k = 7 by omega_using [hk, h], Nat.mod_eq_of_lt (by omega_using [])]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := Y + 28) (n := 32 / 8) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hY]))

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5, .r7] s0 s
  frame : Frame [⟨O, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem O (4 * i) = r i

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : Addr} (h3 : s0.gpr .r3 = o)
    (hout : (⟨o, 32⟩ : Region) ∈ s0.wr)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 32⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h11 : s0.gpr .r11 = 0 - BitVec.ofNat 64 sw) :
    WP isa (.block ((List.range 8).flatMap outStep)) s0
      (OutInv o (fun k => sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k)) s0 8) := by
  have hX : X2 = 32 := rfl
  have hY : Y = 512 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 8 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  have hw : ∀ d, d + 4 ≤ 4096 → wd s.mem b d = wd s0.mem b d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega_using [hk]))
  unfold outStep
  refine lw0_ok hcs (d := X2 + 4 * k) (by omega_using [hX, hk]) fun t1 v1 => ?_
  refine lw0_ok (hcs.of_rest (v1.rest (ws := [.r5]) (by decide)) (by decide)) (d := Y + 4 * k)
    (by omega_using [hY, hk]) fun t2 v2 => ?_
  refine wp_xor fun t3 v3 => wp_and fun t4 v4 => wp_xor fun t5 v5 => ?_
  have hr5 : Rest [.r5, .r7] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  have e3 : t5.gpr .r3 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h3]
  have hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_sw (a := o + BitVec.ofNat 64 (4 * k)) (by decide) (by omega_using [hk])
    (by rw [e3]) (by rw [hwr]; exact in_base hout (by omega_using [hk]) (by omega_using [hk]))
    fun t6 v6 => WP.block_nil ?_
  -- The limb selected.
  have ev : ((t5.gpr .r5).setWidth 32).toNat = sel sw (limb s0.mem b X2 k) (limb s0.mem b Y k) := by
    have ex : t2.gpr .r5 = (s.mem.readW (b + BitVec.ofNat 64 (X2 + 4 * k)) 32).setWidth 64 := by
      rw [v2.other _ (by decide), v1.gpr]
    have ey : t2.gpr .r7 = (s.mem.readW (b + BitVec.ofNat 64 (Y + 4 * k)) 32).setWidth 64 := by
      rw [v2.gpr, v1.mem]
    have em : t3.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h11]
    rw [v5.gpr, v4.other .r5 (by decide), v4.gpr, v3.other .r5 (by decide), v3.gpr, em, ex, ey]
    have hx := hw (X2 + 4 * k) (by omega_using [hX, hk])
    have hy := hw (Y + 4 * k) (by omega_using [hY, hk])
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, lo32_ext, hx]; rfl
    · rw [sel1r, lo32_ext, hy]; rfl
  have hm6 : t6.mem = s.mem.writeW (o + BitVec.ofNat 64 (4 * k)) ((t5.gpr .r5).setWidth 32) := by
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

theorem frame_sub1 {m m' : Mem} {r r' : Region} {rs : List Region} (h : Frame [r] m m') (hs : Region.Sub r r')
    (hr : r' ∈ rs) : Frame rs m m' :=
  h.sub fun x hx => ⟨r', hr, by rw [List.mem_singleton.mp hx]; exact hs⟩

theorem freeze_ok {s : State} (hc : Ctx b s) {o : Addr}
    (h3 : s.gpr .r3 = o) (hout : (⟨o, 32⟩ : Region) ∈ s.wr)
    (hdisj : Region.Disjoint ⟨b, 4096⟩ ⟨o, 32⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem o 32 = leBytes 32 (V s.mem b X2 % P) ∧ Rest clob s s' ∧
      Frame [FA b, ⟨o, 32⟩] s.mem s'.mem := by
  have hX : X2 = 32 := rfl
  have hY : Y = 512 := rfl
  have hl : ∀ k < 8, limb s.mem b X2 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask31_facts hl
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeA_ok (by decide) hc) fun s1 ⟨h8, hl1, hf1, hr1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := X2) (s0 := s1) (c := mask31 (limb s.mem b X2))
    (cin := 19 * (limb s.mem b X2 7 / 2 ^ 31)) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_using [hX, hk])) h8
    (fun k hk => by have := lm k hk; omega_using [this]) (by omega_using [c1]) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk]))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega_using []) (by omega_using [hX, hk]) (by omega_using [hX, hk])]
    exact hl1 k hk
  have hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  have hpo2 : ∀ j < 8, wd s2.mem b (X2 + 4 * j) = frA (limb s.mem b X2) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r6] at this
  have hpf2 : Frame [⟨b + BitVec.ofNat 64 X2, 32⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r6] at this
  refine wp_li (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r8]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r6) (o := Y) (s0 := s3) (c := frA (limb s.mem b X2))
    (cin := 19) (by decide) (by decide) (by decide)
    (fun k hk => by rw [hc3.r6]; exact hc3.inW (by omega_using [hY, hk]))
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask31 (limb s.mem b X2)) (19 * (limb s.mem b X2 7 / 2 ^ 31)) k; unfold frA; omega_using [this]) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk]))
      fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), u3.mem]
    exact hpo2 k hk
  have hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  have hpo4 : ∀ j < 8, wd s4.mem b (Y + 4 * j) = frY (limb s.mem b X2) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r6] at this
  have hpf4 : Frame [⟨b + BitVec.ofNat 64 Y, 32⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r6] at this
  have hx4 : ∀ k < 8, limb s4.mem b X2 k = frA (limb s.mem b X2) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok (by decide) hc4) fun s5 ⟨h11, hy5, hf5, hr5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  have hx5 : ∀ k < 8, limb s5.mem b X2 k = frA (limb s.mem b X2) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY])]
    exact hx4 k hk
  have hy5' : ∀ k < 8, limb s5.mem b Y k = mask31 (frY (limb s.mem b X2)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask31]
    split
    · rename_i h; subst h; rw [limb, hpo4 7 (by decide)]
    · rw [limb, hpo4 k hk]
  have h11' : s5.gpr .r11 = 0 - BitVec.ofNat 64 (frS (limb s.mem b X2)) := by
    rw [h11, limb, hpo4 7 (by decide)]; rfl
  have hr45 : Rest [.r4, .r5, .r7, .r8, .r11] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h3]) (by rw [hr45.wr]; exact hout)
    hdisj hS h11') fun s6 h6' => ⟨?_, ?_, ?_⟩
  · have hr : ∀ k < 8, sel (frS (limb s.mem b X2)) (limb s5.mem b X2 k)
        (limb s5.mem b Y k) = frR (limb s.mem b X2) k := fun k hk => by
      rw [hx5 k hk, hy5' k hk]; rfl
    rw [V, ← hv]
    refine Proof.X25519.bytesAt_leBytes_words32 _ _ _ fun j hj => ?_
    have := h6'.words j hj
    unfold wd at this
    rw [this, hr j hj, val32_div hR hj]
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have hfa : ∀ z, z + 32 ≤ ACC → Region.Sub ⟨b + BitVec.ofNat 64 z, 32⟩ (FA b) :=
      fun z h1 => Offset.sub_base _ (by rw [ACC_eq] at h1 ⊢; omega_using [h1])
    have hA := ACC_eq
    refine (frame_sub1 hf1 (hfa X2 (by omega_using [hX, hA])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hpf2 (hfa X2 (by omega_using [hX, hA])) (List.mem_cons_self ..)).trans ?_
    rw [← u3.mem]
    refine (frame_sub1 hpf4 (hfa Y (by omega_using [hY, hA])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hf5 (hfa Y (by omega_using [hY, hA])) (List.mem_cons_self ..)).trans ?_
    exact frame_sub1 h6'.frame (Region.sub_prefix (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end

end VG.Proof.X25519.PPC64LE
