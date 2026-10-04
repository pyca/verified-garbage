import VerifiedGarbage.Proof.Ed448.AArch64.VerifyFinish
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyLocal
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448 verification's equation on AArch64: the whole function

The correctness of `vg_ed448_verify_equation` against the contract the proof
is written against (`verifyEquationLocal`, `VerifyLocal.lean`): `x20` ends as
the OR of the checks of `S`, of decoding `A` and `R`, and of the comparison of
`[4]Q` with `[4]R`, for `Q` the reference ladder's `[S]B + [k](-A)`
(`vladder`), which decides the equation when `A` and `R` decode
(`VerifyEqOk`, as decoding `RecoverOk`, passed in by the registration files);
every write is in the working space, so the inputs are read unchanged, and
`x19` and `x20` are restored from it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside Outside2 Saved ofs workRegs far)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv E_outside)
open VG.Impl.X448.AArch64 (BITS ACC slot)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [Spec.Ed448.bytesAt]

theorem verifyEquation_correct (hR : RecoverOk) (hE : VerifyEqOk) {s : State}
    (hp : verifyEquationLocal.pre s) :
    WP isa verifyEquation s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ verifyEquationLocal.post s t := by
  obtain ⟨hr, hw, hdk, hds, hdc, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x3 = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hn hw
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .x0, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have rsg : ∀ i n, i + n ≤ 114 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .x1, 114⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 114) h (by omega)⟩
  have rch : ∀ i n, i + n ≤ 57 → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) n :=
    fun i n h => ⟨⟨s.gpr .x2, 57⟩, by rw [hr]; simp,
      Offset.contains_base _ (d := i) (n := n) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 114, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 i) := fun i hi => far hds hi (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  have hz : s.gpr .x2 + BitVec.ofNat 64 0 = s.gpr .x2 := BitVec.add_zero _
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s.mem (s.gpr .x2) 57) = K := ⟨_, rfl⟩
  rw [verifyEquation]
  -- The entry: the saves, `x20 = 0`, and the constants.
  refine WP.seq (WP.mono (ventry_ok hbase hws hn) fun s1 ⟨hs1, b1, sv1, x20₁, k1, o1, z1, pB1, d1⟩ => ?_)
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [k1.2.1, k1.2.2]
  -- The bits of `S` and `k`.
  refine WP.seq (WP.mono (vbits_ok (sig := s.gpr .x1) (ch := s.gpr .x2) hs1 (k1.1 _ (by decide))
    (k1.1 _ (by decide)) (fun q hq => by rw [rr1]; exact rsg _ _ (by omega))
    (fun q hq => by rw [rr1]; exact rch _ _ (by omega)) (fun q hq => fsg _ (by omega))
    (fun q hq => fch _ (by omega))) fun s2 ⟨bs2, bk2, g2, rd2, wr2, o2⟩ => ?_)
  rw [far_bytes o1 (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega)), hS] at bs2
  rw [hz, far_bytes o1 fch, hK] at bk2
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide)).trans hs1.x3, (g2 _ (by decide)).trans hs1.mask,
    wr2 ▸ hs1.wr, hn⟩
  have e2 : ∀ i : Fin 22, E s2.mem base i = E s1.mem base i := fun i =>
    E_outside o2 i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b2 : BoundedEnv s2.mem base := fun i j hj => by
    rw [o2.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega : j < 16)]
    exact b1 i j hj
  have O2 : Outside base 0 8192 s.mem s2.mem := o1.trans (o2.mono (by decide) (by decide))
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rr1]
  -- The check of `S`.
  refine WP.seq (WP.mono (sCheck_ok (p := s.gpr .x1) ((g2 _ (by decide)).trans (k1.1 _ (by decide)))
    (fun j hj => by rw [rr2]; exact rsg _ _ (by omega))) fun s3 ⟨⟨c0, hc0, x3'⟩, m3, k3⟩ => ?_)
  rw [far_bytes O2 (fun i hi => by rw [Offset.add_add]; exact fsg _ (by omega)), hS] at hc0
  have hs3 : Scr s3 base := hs2.of_keeps k3 (by decide)
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [k3.2.1, k3.2.2, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := by rw [m3]; exact O2
  -- `A`, decoded and negated, and `Q` the neutral point.
  refine WP.seq (WP.mono (vdecodeA_ok hR hs3 (m3 ▸ b2) (p := s.gpr .x0)
    ((k3.1 _ (by decide)).trans ((g2 _ (by decide)).trans (k1.1 _ (by decide))))
    (by rw [m3, e2]; exact z1)
    (by rw [m3, show pt (E s2.mem base) 8 9 10 = pt (E s1.mem base) 8 9 10 by simp only [pt, e2]]; exact pB1)
    (by rw [m3, e2]; exact d1) (fun j hj => by rw [rr3]; exact rpk _ _ (by omega)) fpk)
    fun s4 ⟨⟨cA, hcA, x4'⟩, na4, q4, pB4, d4, hs4, b4, k4, f4⟩ => ?_)
  rw [far_bytes O3 fpk] at hcA na4
  have O4 : Outside base 0 8192 s.mem s4.mem := O3.trans (f4.whole (by decide) (by decide))
  have bits4 : ∀ d, (3072 ≤ d ∧ d < 3584 ∨ 4096 ≤ d) → d < 8192 →
      s4.mem (off base d) = s2.mem (off base d) := fun d h1 h2 => by
    have hofs : ofs base (off base d) = d := Mem.sub_ofNat_toNat base (by omega)
    rw [f4 _ (Or.inr (by rw [hofs]; omega)) (by rw [hofs]; simp only [ACC]; omega), m3]
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (S := S) (K := K) (A := pt (E s4.mem base) 6 7 10)
    (fun t ht => by rw [bits4 _ (by simp only [BITS]; omega) (by simp only [BITS]; omega)]; exact bs2 t ht)
    (fun t ht => by rw [bits4 _ (by simp only [KOFF]; omega) (by simp only [KOFF]; omega)]; exact bk2 t ht)
    hs4 b4 pB4 rfl d4 q4) fun s5 I5 => ?_)
  have x1₅ : s5.gpr .x1 = s.gpr .x1 := by
    rw [I5.regs.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), g2 _ (by decide), k1.1 _ (by decide)]
  have rr5 : s5.rd ++ s5.wr = s.rd ++ s.wr := by
    rw [I5.regs.2.1, I5.regs.2.2, k4.2.1, k4.2.2, rr3]
  have O5 : Outside base 0 8192 s.mem s5.mem := O4.trans (I5.mem.whole (by decide) (by decide))
  -- `R`, decoded.
  refine WP.seq (WP.mono (vdecodeR_ok hR I5.scr I5.bounded x1₅ (congrArg Spec.Ed448.Point.Z I5.q) I5.d
    (fun j hj => by rw [rr5]; exact rsg _ _ (by omega)) (fun j hj => fsg _ (by omega)))
    fun s6 ⟨⟨cR, hcR, x6'⟩, v6, q6, hs6, b6, k6, f6⟩ => ?_)
  rw [far_bytes O5 (fun i hi => fsg _ (by omega)), ← bytesAt_take57] at hcR v6
  have sv6 : Saved base s.gpr s6.mem := by
    have sv3 : Saved base s.gpr s3.mem := by rw [m3]; exact sv1.outside o2 (by decide)
    exact ((sv3.outside2 f4 (by decide) (by decide)).outside2 I5.mem (by decide) (by decide)).outside2 f6
      (by decide) (by decide)
  -- `[4]Q` and `[4]R` compared, and the result.
  refine WP.mono (vfinish_ok hs6 b6 sv6) fun t ⟨x0t, x19t, x20t, gt, _, _, _⟩ => ?_
  refine ⟨fun r hpres => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact x19t
    · exact x20t
    all_goals rw [gt _ (by decide), k6.1 _ (by decide), I5.regs.1 _ (by decide), k4.1 _ (by decide),
      k3.1 _ (by decide), g2 _ (by decide), k1.1 _ (by decide)]
  · show t.gpr .x0 = _
    have hx : s6.gpr .x20 = 0 ||| c0 ||| cA ||| cR := by
      rw [x6', I5.regs.1 _ (by decide), x4', x3', g2 _ (by decide), x20₁]
    rw [x0t]
    refine if_congr ?_ rfl rfl
    rw [hx, or_eq_zero64, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x0) 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hRr : Spec.Ed448.decodePoint ((bytesAt s.mem (s.gpr .x1) 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hRr)]
        refine ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hRr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hRr]; rfl)
        have hQ : pt (E s6.mem base) 0 6 2 = vladder (decodeLE ((bytesAt s.mem (s.gpr .x1) 114).drop 57))
            (decodeLE (bytesAt s.mem (s.gpr .x2) 57)) (negPoint a) 456 := by
          have := I5.rep
          rw [Nat.sub_zero, na4 a ha] at this
          rw [bytesAt_drop57, hS, hK, q6]
          exact this
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hRr, ← hQ, ← v6 r hRr,
          Bool.and_eq_true, decide_eq_true_iff, bytesAt_drop57, hS, cA0, cR0, hc0]
        exact ⟨fun h => ⟨h.1.1.1.2, h.2⟩, fun h => ⟨⟨⟨⟨rfl, h.1⟩, rfl⟩, rfl⟩, h.2⟩⟩

end VG.Proof.Ed448.AArch64
