import VerifiedGarbage.Proof.Ed448.AArch64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry

/-!
# Ed448 verification's equation on AArch64: decoding `A`

`vdecodeA_ok`: `A` decoded and negated into slots 6, 7 and 10, and `Q` the
neutral point. The check ORs into `x20` a word that is 0 exactly when it
passes.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off Outside Outside2 ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
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

theorem sub6_keep (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : i ≠ 6) :
    evalOps [.sub 6 0 6] e i = e i :=
  Function.update_of_ne hi _ _

/-- `A` decoded and negated into slots 6, 7 and 10, and `Q` the neutral point. -/
theorem vdecodeA_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : Addr} (hp : s.gpr .x0 = p) (h0 : E s.mem base 0 = 0)
    (hB : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa vdecodeA s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some a →
        pt (E t.mem base) 6 7 10 = negPoint a) ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Scr t base ∧ BoundedEnv t.mem base ∧
      Keeps (.x17 :: .x19 :: .x20 :: workRegs) s t ∧ DFrame base s.mem t.mem := by
  have h10 : E s.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z hB
  rw [vdecodeA, WP.seq_iff]
  refine WP.mono (decode_ok hR hs hb hp (Or.inl rfl) 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11 hr hfar)
    fun s1 ⟨hc, v1, k1, b1, g1, f1⟩ => ?_
  have hs1 : Scr s1 base := hs.of_keeps g1 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (field_ok [.sub 6 0 6] (by decide) hs1 b1) fun s2 ⟨k2, b2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  have e2k : ∀ i : Fin 22, i ≠ 6 → E s2.mem base i = E s1.mem base i := fun i hi => by
    rw [e2, sub6_keep _ _ hi]
  have z2 : E s2.mem base 0 = 0 := by
    rw [e2k 0 (by decide), k1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h0]
  refine WP.mono (qInit_ok hs2 b2 z2) fun t ⟨bt, qt, ot, mt, kt⟩ => ?_
  have kk : ∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 →
      E t.mem base i = E s.mem base i := fun i h h1 h2 h3 h4 h5 h6 h7 => by
    rw [ot i h1 h2, e2k i h6, k1 i h h1 h3 h4 h5 h6 h7]
  refine ⟨?_, fun a ha => ?_, qt, ?_, ?_, hs2.of_keeps kt (by decide), bt, ?_, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    exact ⟨c, hc1, by rw [kt.1 _ (by decide), k2.regs.1 _ (by decide), hc2]⟩
  · obtain ⟨vx, vy, vz⟩ := v1 a ha
    show (⟨E t.mem base 6, E t.mem base 7, E t.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [ot 6 (by decide) (by decide), ot 7 (by decide) (by decide), ot 10 (by decide) (by decide),
      e2k 7 (by decide), e2k 10 (by decide), e2, vy, vz,
      k1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10]
    show (⟨E s1.mem base 0 - E s1.mem base 6, a.Y, 1⟩ : Spec.Ed448.Point) = _
    rw [vx, k1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h0]
  · rw [pt_congr (kk 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (kk 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (kk 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)), hB]
  · rw [kk 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h11]
  · exact (g1.trans (k2.regs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr)))).trans (kt.mono (by decide))
  · refine (f1.trans (keep_dframe k2)).trans ?_
    exact fun x h1 h2 _ => mt x (by simp only [ACC] at *; omega)

end VG.Proof.Ed448.AArch64
