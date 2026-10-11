import VerifiedGarbage.Proof.Ed448.AArch64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry

/-!
# Ed448 verification's equation on AArch64: decoding `A`

Untrusted: everything here is checked by Lean. `negA_ok`: after `A` is
decoded into slots 8 and 9, `-A` into slots 6 and 7. `decodes_ok`: `A` and `R`
decoded by one copy of `decode`, its loop's two passes, `-A` into slots 6, 7
and 10 and `R` into 8, 9 and 10. Each check ORs into `x20` a word that is 0
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

/-- `x0 := x1`. -/
theorem mov01_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x1 0]) s fun t => t.gpr .x0 = s.gpr .x1 ∧ t.mem = s.mem ∧ Keeps [.x0] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩

/-- `x0 := x1`, `x1 := x3`. -/
theorem mov013_ok (s : State) :
    WP isa (.block [.addImm .x .x0 .x1 0, .addImm .x .x1 .x3 0]) s fun t =>
      t.gpr .x0 = s.gpr .x1 ∧ t.gpr .x1 = s.gpr .x3 ∧ t.mem = s.mem ∧ Keeps [.x0, .x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq,
    BitVec.add_zero, Option.some.injEq, exists_eq_left', RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x3 ≠ .x0),
    RegUpd.gpr_write_of_ne _ _ _ (by decide : Reg.x0 ≠ .x1)]
  refine ⟨trivial, trivial, rfl, fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

/-- After `A` is decoded into slots 8–9 (with 1 in slot 10): `-A` into slots 6 and 7, `x` (a
product by 1, below the products' bound) subtracted from zero in slot 13, `x0 := x1` and
`x1 := x3`. -/
theorem negA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (h10 : E s.mem base 10 = 1) :
    WP isa negA s fun t =>
      E t.mem base 6 = 0 - E s.mem base 8 ∧ E t.mem base 7 = E s.mem base 9 ∧
      (∀ i : Fin 22, i ≠ 6 → i ≠ 7 → i ≠ 12 → i ≠ 13 → E t.mem base i = E s.mem base i) ∧
      t.gpr .x0 = s.gpr .x1 ∧ t.gpr .x1 = s.gpr .x3 ∧ Scr t base ∧ BEnv t.mem base ∧
      Keeps (.x1 :: VG.Proof.X448.AArch64.Fast.fclob) s t ∧ DFrame base s.mem t.mem := by
  unfold negA
  refine WP.seq (mulOp (rest := [.copy (slot 7) (slot 9)]) hs hb 6 8 10 (Or.inr (by decide))
    fun s2 k2 b2 m2 sm2 e2 => ?_)
  have hs2 := k2.scr hs
  refine WP.seq (WP.mono (copyE hs2 b2 7 9) fun s2b ⟨k2b, b2b, _, sm2b, e2b⟩ => WP.block_nil ?_)
  have hs2b := k2b.scr hs2
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hs2b (o := slot 13) (by decide) (by decide) 0)
    fun s3 ⟨w3, o3, k3⟩ => ?_)
  have hs3 : Scr s3 base := hs2b.of_keeps k3 (by decide)
  have l23 : ∀ i : Fin 22, i ≠ 13 → ∀ j < 8, limbs s3.mem base (slot i.val) j = limbs s2b.mem base (slot i.val) j := by
    intro i hi j hj
    have h1 := VG.Proof.X448.AArch64.Weak.slot_sep hi
    have h2 := i.isLt
    exact o3.limbs (by simp only [slot] at *; omega) (by simp only [slot]; omega) (by omega)
  have E23 : ∀ i : Fin 22, i ≠ 13 → E s3.mem base i = E s2b.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (l23 i hi))
  have z13 : ∀ j < 8, limbs s3.mem base (slot (13 : Fin 22).val) j < 2 ^ 56 := fun j hj => by
    change (word s3.mem base (slot 13 + 8 * j)).toNat < _
    rw [w3 j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  have b3 : BEnv s3.mem base := fun i j hj => by
    by_cases h : i = 13
    · subst h; exact Nat.lt_trans (z13 j hj) (by decide)
    · rw [l23 i h j hj]; exact b2b i j hj
  have m3 : Bnd Mb s3.mem base (slot (6 : Fin 22).val) := fun j hj => by
    rw [l23 6 (by decide) j hj, sm2b 6 (by decide) j hj]; exact m2 j hj
  refine WP.seq (subOp (o := 12) (a := 13) (b := 6) (rest := [.copy (slot 6) (slot 12)]) hs3 b3
    (fun j hj => Nat.lt_trans (z13 j hj) (by decide)) m3 (by decide) (by decide) fun s4 k4 b4 _ e4 => ?_)
  have hs4 := k4.scr hs3
  refine WP.seq (WP.mono (copyE hs4 b4 6 12) fun s5 ⟨k5, b5, _, _, e5⟩ => WP.block_nil ?_)
  have hs5 := k5.scr hs4
  refine WP.mono (mov013_ok s5) fun t ⟨x0t, x1t, mt, kt⟩ => ?_
  have h0 : E s3.mem base 13 = 0 := VG.Proof.X448.AArch64.Base.F_of_words w3
  have Et : ∀ i, E t.mem base i = E s5.mem base i := fun i => by rw [mt]
  have keep : ∀ i : Fin 22, i ≠ 6 → i ≠ 7 → i ≠ 12 → i ≠ 13 → E t.mem base i = E s.mem base i :=
    fun i h6 h7 h12 h13 => by
      rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_of_ne h6, e4, Function.update_of_ne h12, E23 i h13, e2b, VG.Proof.X448.AArch64.opCopy,
        Function.update_of_ne h7, e2, Function.update_of_ne h6]
  refine ⟨?_, ?_, keep, ?_, ?_, hs5.of_keeps kt (by decide), by rw [mt]; exact b5, ?_, ?_⟩
  · rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_self, e4, Function.update_self, h0, E23 6 (by decide), e2b, VG.Proof.X448.AArch64.opCopy,
      Function.update_of_ne (by decide), e2, Function.update_self, h10, Fin.mul_one]
  · rw [Et, e5, VG.Proof.X448.AArch64.opCopy, Function.update_of_ne (by decide), e4, Function.update_of_ne (by decide),
      E23 7 (by decide), e2b, VG.Proof.X448.AArch64.opCopy, Function.update_self, e2, Function.update_of_ne (by decide)]
  · rw [x0t, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
      k2.regs.1 _ (by decide)]
  · rw [x1t, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.1 _ (by decide), k2b.regs.1 _ (by decide),
      k2.regs.1 _ (by decide)]
  · exact ((((k2.regs.mono (by decide)).trans (k2b.regs.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans ((k5.regs.mono (by decide)).trans (kt.mono (by decide)))
  · rw [mt]
    exact (((fkeep_dframe k2).trans (fkeep_dframe k2b)).trans (DFrame.of_outside o3 (by simp only [slot]; omega))).trans
      ((fkeep_dframe k4).trans (fkeep_dframe k5))

/-- `x19 := x1 - x3`. -/
theorem sub19_ok (s : State) :
    WP isa (.block [.sub .x .x19 .x1 .x3]) s fun t =>
      t.gpr .x19 = s.gpr .x1 - s.gpr .x3 ∧ Keeps [.x19] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl⟩, rfl⟩

/-- A loop whose body runs twice. -/
theorem WP.loop2 {b : Prog isa} {c : isa.Cond} {s : State} {Q : State → Prop}
    (h : WP isa b s fun t => isa.eval c t = some true ∧
      WP isa b t fun u => isa.eval c u = some false ∧ Q u) : WP isa (.loop b c) s Q := by
  obtain ⟨t₁, s₁, e₁, hc₁, t₂, s₂, e₂, hc₂, q⟩ := h
  exact ⟨_, _, Exec.loopNext e₁ hc₁ (Exec.loopExit e₂ hc₂), q⟩

theorem WP.ite_of {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop} {b : Bool}
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, _, Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, _, Exec.iteT hc e, q⟩

theorem eval19 {s : State} {b : Bool} (h : (s.gpr .x19 != 0) = b) :
    isa.eval (.nonzero .x .x19) s = some b := by
  simp only [eval, State.read, BitVec.setWidth_eq, h]

/-- An address at least 8192 bytes past the working space differs from its base. -/
theorem ne_of_far {base p : Addr} (h : 8192 ≤ ofs base (p + BitVec.ofNat 64 0)) : (p - base != 0) = true := by
  rw [BitVec.add_zero] at h
  have : p - base ≠ 0 := fun e => by rw [ofs, e] at h; exact absurd h (by decide)
  simpa using this

/-- **`A` and `R` decoded by one copy of `decode`**: the loop's first pass decodes `A` (from `x0`)
into slots 8–9 and negates it into 6–7 (`negA_ok`), the second decodes `R` (from `x1`, which
`negA` moved into `x0`) into 8–9. `x1 - x3`, after each, is nonzero after `A`, since `R` lies outside the
working space, and 0 after `R`, since `negA` moved `x3` into `x1`. -/
theorem decodes_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hrA : ∀ j < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 j) 1)
    (hfA : ∀ j < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 j))
    (hrR : ∀ j < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 j) 1)
    (hfR : ∀ j < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 j)) :
    WP isa decodes s fun t =>
      (∃ cA cR : BitVec 64,
        (cA = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57)).isSome) ∧
        (cR = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| cA ||| cR) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x0) 57) = some a →
        (⟨E t.mem base 6, E t.mem base 7, 1⟩ : Spec.Ed448.Point) = negPoint a) ∧
      (∀ r, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57) = some r →
        E t.mem base 8 = r.X ∧ E t.mem base 9 = r.Y ∧ r.Z = 1) ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Scr t base ∧ BEnv t.mem base ∧ Keeps (.x0 :: .x1 :: .x19 :: decClob) s t ∧
      DFrame base s.mem t.mem := by
  unfold decodes
  refine WP.loop2 ?_
  -- The first pass: `A`.
  refine WP.seq (WP.mono (decode_ok hR hs hb (p := s.gpr .x0) rfl (Or.inl rfl) 8 9 (Or.inr ⟨rfl, rfl⟩) h11 hrA hfA)
    fun s1 ⟨⟨cA, hcA, x1'⟩, v1, kp1, one1, b1, g1, f1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps g1 (by decide)
  refine WP.seq (WP.mono (sub19_ok s1) fun s2 ⟨c2, k2, m2⟩ => ?_)
  have hs2 := hs1.of_keeps k2 (by decide)
  have z2 : (s2.gpr .x19 != 0) = true := by
    rw [c2, g1.1 _ (by decide), hs1.x3]; exact ne_of_far (hfR 0 (by decide))
  refine WP.ite_of (eval19 z2) (fun _ => ?_) (fun h => absurd h (by decide))
  refine WP.mono (negA_ok hs2 (by rw [m2]; exact b1) (by rw [m2]; exact one1))
    fun s3 ⟨n6, n7, nk, x03, x13', hs3, b3, k3, f3⟩ => ⟨eval19 (by rw [k3.1 _ (by decide)]; exact z2), ?_⟩
  have O3 : Outside base 0 8192 s.mem s3.mem := (f1.trans (by rw [← m2]; exact f3)).whole
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by
    rw [k3.2.1, k3.2.2, k2.2.1, k2.2.2, g1.2.1, g1.2.2]
  have x13 : s3.gpr .x0 = s.gpr .x1 := by
    rw [x03, k2.1 _ (by decide), g1.1 _ (by decide)]
  have e11 : E s3.mem base 11 = Spec.Ed448.d := by
    rw [nk 11 (by decide) (by decide) (by decide) (by decide), m2,
      kp1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11]
  -- The second pass: `R`.
  refine WP.seq (WP.mono (decode_ok hR hs3 b3 (p := s.gpr .x1) x13 (Or.inl rfl) 8 9 (Or.inr ⟨rfl, rfl⟩) e11
    (by rw [rr3]; exact hrR) hfR) fun s4 ⟨⟨cR, hcR, x4'⟩, v4, kp4, one4, b4, g4, f4⟩ => ?_)
  rw [far_bytes O3 hfR] at hcR v4
  have hs4 : Scr s4 base := hs3.of_keeps g4 (by decide)
  refine WP.seq (WP.mono (sub19_ok s4) fun s5 ⟨c5, k5, m5⟩ => ?_)
  have z5 : (s5.gpr .x19 != 0) = false := by
    rw [c5, g4.1 _ (by decide), x13', hs4.x3, hs2.x3, BitVec.sub_self]; rfl
  refine WP.ite_of (eval19 z5) (fun h => absurd h (by decide)) (fun _ => ?_)
  refine WP.mono (mov01_ok s5) fun s6 ⟨_, m6, k6⟩ => ⟨eval19 (by rw [k6.1 _ (by decide)]; exact z5), ?_⟩
  have k46 : ∀ i : Fin 22, i = 6 ∨ i = 7 → E s4.mem base i = E s3.mem base i := by
    rintro i (rfl | rfl) <;>
      exact kp4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨cA, cR, hcA, hcR, ?_⟩, fun a ha => ?_, fun r hr => ?_, ?_, (hs4.of_keeps k5 (by decide)).of_keeps k6 (by decide),
    by rw [m6, m5]; exact b4, ?_, ?_⟩
  · rw [k6.1 _ (by decide), k5.1 _ (by decide), x4', k3.1 _ (by decide), k2.1 _ (by decide), x1']
  · obtain ⟨vx, vy, hz⟩ := v1 a ha
    rw [m6, m5, k46 6 (.inl rfl), k46 7 (.inr rfl), n6, n7, m2, vx, vy, VG.Proof.Ed448.negPoint, hz]
  · rw [m6, m5]; exact v4 r hr
  · rw [m6, m5, kp4 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), e11]
  · exact ((((g1.mono (by decide)).trans (k2.mono (by decide))).trans
      (k3.mono (by decide))).trans (g4.mono (by decide))).trans (k5.mono (by decide)) |>.trans (k6.mono (by decide))
  · rw [m6, m5]
    exact ((f1.trans (by rw [← m2]; exact f3)).trans f4)

end VG.Proof.Ed448.AArch64
