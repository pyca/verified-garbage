import VerifiedGarbage.Proof.Ed448.AArch64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry

/-!
# Ed448 verification's equation on AArch64: decoding `A`

Untrusted: everything here is checked by Lean. `vdecodeA_ok`: `A` decoded
and negated into slots 6, 7 and 10. The check ORs into `x20` a word that is 0
exactly when it passes.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E opCopy)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep mulOp subOp copyE)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Impl.X448.AArch64 (slot BITS ACC)

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (hf i (List.mem_range.mp hi)))

theorem pt_congr {e e' : Fin 22 → Spec.X448.Fe} {a b c : Fin 22} (ha : e' a = e a) (hb : e' b = e b)
    (hc : e' c = e c) : pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

/-- `A` decoded and negated into slots 6 and 7 (with 1 in slot 10): `x` (a product by 1, below
the products' bound) subtracted from zero in slot 13. -/
theorem vdecodeA_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    {p : Addr} (hp : s.gpr .x0 = p) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa vdecodeA s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some a →
        pt (E t.mem base) 6 7 10 = negPoint a) ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Scr t base ∧ BEnv t.mem base ∧ Keeps decClob s t ∧
      DFrame base s.mem t.mem := by
  rw [vdecodeA]
  refine WP.seq (WP.mono (decode_ok hR hs hb hp (Or.inl rfl) 6 7 (Or.inl ⟨rfl, rfl⟩) h11 hr hfar)
    fun s1 ⟨hc, v1, k1, one1, b1, g1, f1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps g1 (by decide)
  refine WP.seq (mulOp (rest := []) hs1 b1 6 6 10 (Or.inr (by decide)) fun s2 k2 b2 m2 sm2 e2 => WP.block_nil ?_)
  have hs2 := k2.scr hs1
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hs2 (o := slot 13) (by decide) (by decide) 0)
    fun s3 ⟨w3, o3, k3⟩ => ?_)
  have hs3 : Scr s3 base := hs2.of_keeps k3 (by decide)
  have l23 : ∀ i : Fin 22, i ≠ 13 → ∀ j < 8, limbs s3.mem base (slot i.val) j = limbs s2.mem base (slot i.val) j := by
    intro i hi j hj
    have h1 := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have h2 := i.isLt
    exact o3.limbs (by simp only [slot] at *; omega) (by simp only [slot]; omega) (by omega)
  have E23 : ∀ i : Fin 22, i ≠ 13 → E s3.mem base i = E s2.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (l23 i hi))
  have z13 : ∀ j < 8, limbs s3.mem base (slot (13 : Fin 22).val) j < 2 ^ 56 := fun j hj => by
    change (word s3.mem base (slot 13 + 8 * j)).toNat < _
    rw [w3 j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  have b3 : BEnv s3.mem base := fun i j hj => by
    by_cases h : i = 13
    · subst h; exact Nat.lt_trans (z13 j hj) (by decide)
    · rw [l23 i h j hj]; exact b2 i j hj
  have m3 : Bnd Mb s3.mem base (slot (6 : Fin 22).val) := fun j hj => by
    rw [l23 6 (by decide) j hj]; exact m2 j hj
  refine subOp (o := 12) (a := 13) (b := 6) hs3 b3 (fun j hj => Nat.lt_trans (z13 j hj) (by decide)) m3
    (by decide) (by decide) fun s4 k4 b4 _ e4 => ?_
  have hs4 := k4.scr hs3
  refine WP.seq (WP.mono (copyE hs4 b4 6 12) fun t ⟨kt, bt, _, _, et⟩ => WP.block_nil ?_)
  have h0 : E s3.mem base 13 = 0 := VG.Proof.X448.AArch64.Base.F_of_words w3
  have keep : ∀ i : Fin 22, i ≠ 6 → i ≠ 12 → i ≠ 13 → E t.mem base i = E s1.mem base i := fun i h6 h12 h13 => by
    rw [et, VG.Proof.X448.AArch64.opCopy, Function.update_of_ne h6, e4, Function.update_of_ne h12, E23 i h13, e2,
      Function.update_of_ne h6]
  have k1' : ∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 10 → i ≠ 6 → i ≠ 7 →
      E s1.mem base i = E s.mem base i := k1
  refine ⟨?_, fun a ha => ?_, ?_, hs4.of_keeps kt.regs (by decide), bt, ?_, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    exact ⟨c, hc1, by rw [kt.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide),
      k2.regs.1 _ (by decide), hc2]⟩
  · obtain ⟨vx, vy, vz⟩ := v1 a ha
    show (⟨E t.mem base 6, E t.mem base 7, E t.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [keep 7 (by decide) (by decide) (by decide), keep 10 (by decide) (by decide) (by decide), vy, vz, one1,
      et, VG.Proof.X448.AArch64.opCopy, Function.update_self, e4, Function.update_self, h0, E23 6 (by decide), e2, Function.update_self,
      one1, vx, Fin.mul_one]
  · rw [keep 11 (by decide) (by decide) (by decide), k1' 11 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h11]
  · exact (((g1.trans (k2.regs.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans (kt.regs.mono (by decide))
  · exact (((f1.trans (fkeep_dframe k2)).trans (DFrame.of_outside o3 (by simp only [slot]; omega))).trans
      (fkeep_dframe k4)).trans (fkeep_dframe kt)

end VG.Proof.Ed448.AArch64
