module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes

/-!
# DSA on PPC64LE: constant time of the check of the sizes, after p's scan

`sizes_rel`: two runs of `sizes rest fail` for the same public data leak the
same trace, when `rest` and `fail` do from the phases they start in.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)

theorem sP_le {v : VD} {s : State} (h : Base v s) : v.sP ≤ v.L.pl := by
  have := VG.Proof.Dsa.significant_fits v.pB
  rw [← h.bytesP, bytesAt_length] at this
  rw [VD.sP, ← h.bytesP]; exact this

theorem qb_le {v : VD} {s : State} (h : Base v s) : v.qb ≤ v.L.ql := by
  have := VG.Proof.Dsa.significant_fits v.qB
  rw [← h.bytesQ, bytesAt_length] at this
  rw [VD.qb, ← h.bytesQ]; exact this

/-- `Base` after `r2` gets q's octets. -/
theorem Base.step2 {v : VD} {s t : State} {rs : List Reg} {qb : Nat} (h : Base v s) (k : Keep rs s t)
    (ho : Body v.L s.mem t.mem) (h2 : t.gpr .r2 = pack v.L.pl v.L.ql qb v.d) (hqb : qb < 2 ^ 16)
    (hr : ∀ r ∈ ([.r21, .r26, .r27, .r28] : List Reg), r ∉ rs := by decide) : Base v t :=
  ⟨h.ok, Regs.of_pack h.ok ((k.gpr .r21 (hr _ (by decide))).trans h.regs.r21)
      ((k.gpr .r27 (hr _ (by decide))).trans h.regs.r27) ((k.gpr .r28 (hr _ (by decide))).trans h.regs.r28)
      ((k.gpr .r26 (hr _ (by decide))).trans h.regs.r26) h2 hqb (by simp only [VD.d]; omega),
    h.scr.congr k.wr, h.hk.keep k.rd k.wr, h.hsg.keep k.rd k.wr, h.hdg.keep k.rd k.wr,
    (h.hk.kept (ho.mono (Nat.zero_le _) (by have := h.ok.z256; omega))).trans h.kb, h.hx.keep k.rd k.wr,
    h.hdr_body ho, h.sgn⟩

/-- p's octets into `r24`. -/
theorem w_a24 {v : VD} {s : State} (h : S1 v s ∧ s.gpr .r0 = 0) :
    WP isa (.block [.addi .r24 .r16 0]) s (S2 v) := by
  obtain ⟨⟨B, r2, f, h0⟩, z⟩ := h
  have f16 : s.gpr .r16 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = BitVec.ofNat 64 v.sP ∧ t.mem = s.mem)
    (by prun [f16, BitVec.add_zero]) (by decide)) fun t ⟨⟨a24, m⟩, k⟩ =>
    ⟨B.step k (by rw [m]; exact Outside.refl _ _ _ _), by rw [k.gpr .r2 (by decide), r2], ?_, h0.mp z⟩
  simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact a24

/-- `ptrQ` and q's scan. -/
theorem w_scanQ {v : VD} {s : State} (h : S2 v s) : WP isa (.seq (.block ptrQ) sigLen) s (S2a v) := by
  obtain ⟨B, r2, f, tp⟩ := h
  have f24 : s.gpr .r24 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  have hq := B.ok.ql
  refine WP.seq (WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (sigLen_ok a12 a6 (by omega) (by omega)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega)).rd i hi)
    fun u ⟨⟨b16, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, tp⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r24 (by decide)).trans ((k1.gpr .r24 (by decide)).trans f24),
      (k2.gpr .r12 (by decide)).trans a12, (k2.gpr .r6 (by decide)).trans a6,
      by rw [b16, m1, B.bytesQ]; rfl⟩

/-- `ptrQ` and q's `bytesBits`. -/
theorem w_bitsQ {v : VD} {s : State} (h : S2 v s) : WP isa (.seq (.block ptrQ) bytesBits) s (S3 v) := by
  obtain ⟨B, r2, f, tp⟩ := h
  have f24 : s.gpr .r24 = BitVec.ofNat 64 v.sP := f _ (List.mem_singleton_self _)
  have hq := B.ok.ql
  refine WP.seq (WP.mono (ptrQ_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (bytesBits_ok a12 a6 (by omega) (by omega)
      fun i hi => (B1.hk.sub (o := v.L.pl) (k := v.L.ql) (by omega)).rd i hi)
    fun u ⟨⟨b16, b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, tp, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r24 (by decide)).trans ((k1.gpr .r24 (by decide)).trans f24),
      by rw [b16, m1, B.bytesQ]; rfl⟩
  · rw [b0, m1, B.bytesQ]; rfl

theorem ite16q_rel : RelCT isa (Two S2a) (.ite (.zero .d .r16) (.block [.li .r0 1]) (.block topBit))
    fun _ _ => True :=
  rel_ite_zero (fun v s₁ s₂ h₁ h₂ => by rw [pins_S2a v s₁ s₂ h₁ h₂ .r16 (by decide)])
    (rel_weaken (two_taint _ pins_S2a (by taint_decide))) (rel_weaken (two_taint _ pins_S2a (by taint_decide)))

theorem bitsQ_rel {G : VD → Prop} :
    RelCT isa (Two fun v s => S2 v s ∧ G v) (.seq (.block ptrQ) bytesBits) (Two fun v s => S3 v s ∧ G v) :=
  two_postG (RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_S2 (by taint_decide)) fun _ _ h => w_scanQ h)
    ite16q_rel)) fun _ _ h => w_bitsQ h

/-- q's octets into `r25` and `r2`, and `pairs`. -/
theorem w_pairs {v : VD} {s : State} (h : S3 v s ∧ s.gpr .r0 = 0) :
    WP isa (.seq (.block [.addi .r25 .r16 0, .lsl .r0 .r16 32, .add .r2 .r2 .r0]) pairs) s (S4 v) := by
  obtain ⟨⟨B, r2, f, tp, h0⟩, z⟩ := h
  simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true] at f
  obtain ⟨f24, f16⟩ := f
  have hp := sP_le B
  have hqb := qb_le B
  have hql := B.ok.ql
  have hpl := pl_bounds B
  refine WP.seq (WP.mono (WP.keep [.r25, .r0, .r2] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 v.qb ∧
      t.gpr .r2 = pack v.L.pl v.L.ql v.qb v.d ∧ t.mem = s.mem)
    (by prun [f16, r2, BitVec.add_zero, pack_add (show v.qb < 2 ^ 16 by omega)]) (by decide))
    fun t ⟨⟨a25, a2, m1⟩, k1⟩ => ?_)
  refine WP.mono (pairs_ok ((k1.gpr .r24 (by decide)).trans f24) a25 (by omega) (by omega))
    fun u ⟨⟨b0, m2⟩, k2⟩ => ⟨(B.step2 k1 (by rw [m1]; exact Outside.refl _ _ _ _) a2 (by omega)).step k2
      (by rw [m2]; exact Outside.refl _ _ _ _), by rw [k2.gpr .r2 (by decide), a2], fixL_nil u, tp, h0.mp z, b0⟩

/-- The check of the sizes, for public data satisfying `G`. -/
theorem sizes_rel {rest fail : Prog isa} {Q : State → State → Prop} {G : VD → Prop}
    (hrest : RelCT isa (Two fun v s => S5 v s ∧ G v) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two fun v s => S0 v s ∧ G v) (sizes rest fail) Q := by
  unfold sizes andThen
  refine RelCT.seq bitsP_rel (rel_ite_zeroG (zero_iff_agree (fun (v : VD) => 128 ≤ v.tP)
    fun _ _ h => h.2.2.2) ?_ (hfail _ fun _ _ h => h.1.1.1))
  refine RelCT.seq (two_postG (two_taint _ (pins_and pins_S1) (by taint_decide)) fun _ _ h => w_a24 h) ?_
  refine RelCT.seq bitsQ_rel (rel_ite_zeroG (zero_iff_agree (fun (v : VD) => 128 ≤ v.tQ)
    fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => h.1.1.1))
  refine RelCT.assoc (RelCT.seq (two_postG (two_taint _ (pins_and pins_S3) (by taint_decide))
    fun _ _ h => w_pairs h) ?_)
  refine rel_ite_zeroG (zero_iff_agree (fun (v : VD) => Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.qb))
    fun _ _ h => h.2.2.2.2.2) (hrest.mono (fun _ _ => two_mono fun v s ⟨⟨⟨B, r2, _, tp, tq, h0⟩, z⟩, g⟩ =>
      ⟨⟨B, r2, fixL_nil s, (VG.Proof.Dsa.supported_scans v.pB v.qB).mpr ⟨tp, tq, h0.mp z⟩⟩, g⟩) fun _ _ h => h)
    (hfail _ fun _ _ h => h.1.1.1)

end VG.Proof.Dsa.PPC64LE
