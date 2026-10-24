module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Base
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
public import VerifiedGarbage.Proof.Dsa.DomainShape
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Base
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
meta import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx

/-!
# DSA on PPC64LE: constant time of the check of the sizes

`sizes_rel`: two runs of `sizes` for the same public data leak the same
trace. Each scan's branches depend on the key's octets, which both runs share:
the phases fix the scans' results.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)

/-- p's and q's octets. -/
def VD.pB (v : VD) : List Byte := v.at 0 v.L.pl
def VD.qB (v : VD) : List Byte := v.at v.L.pl v.L.ql

theorem Base.bytesP {v : VD} {s : State} (h : Base v s) : Spec.Rsa.bytesAt s.mem v.key v.L.pl = v.pB := by
  have := h.kn
  have := h.bytes (o := 0) (k := v.L.pl) (by omega)
  rwa [off, BitVec.add_zero] at this

theorem Base.bytesQ {v : VD} {s : State} (h : Base v s) :
    Spec.Rsa.bytesAt s.mem (off v.key v.L.pl) v.L.ql = v.qB := by
  have := h.kn
  exact h.bytes (by omega)

/-- The sizes are supported, on the public data. -/
def SzOk (v : VD) : Prop :=
  Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE v.pB)) (Spec.Dsa.bitLength (Spec.Dsa.decodeBE v.qB))

/-- q's significant octets. -/
def VD.qb (v : VD) : Nat := (significant v.qB).1

/-- p's and q's scans: significant octets, and the first one's value. -/
def VD.sP (v : VD) : Nat := (significant v.pB).1
def VD.tP (v : VD) : Nat := (significant v.pB).2.toNat
def VD.tQ (v : VD) : Nat := (significant v.qB).2.toNat

/-- On entry to the checks. -/
def S0 : VD → State → Prop := Ph (fun _ => 0) fun _ s => FixL [] s ∧ True

/-- After p's scan of its octets. -/
def S0a : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r12, v.key), (.r6, BitVec.ofNat 64 v.L.pl), (.r16, BitVec.ofNat 64 v.sP)] s ∧ True

/-- After p's `bytesBits`. -/
def S1 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r16, BitVec.ofNat 64 v.sP)] s ∧ (s.gpr .r0 = 0 ↔ 128 ≤ v.tP)

/-- p's octets into `r24`. -/
def S2 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP)] s ∧ 128 ≤ v.tP

/-- After q's scan of its octets. -/
def S2a : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP), (.r12, off v.key v.L.pl), (.r6, BitVec.ofNat 64 v.L.ql),
    (.r16, BitVec.ofNat 64 v.qb)] s ∧ 128 ≤ v.tP

/-- After q's `bytesBits`. -/
def S3 : VD → State → Prop := Ph (fun _ => 0) fun v s =>
  FixL [(.r24, BitVec.ofNat 64 v.sP), (.r16, BitVec.ofNat 64 v.qb)] s ∧ 128 ≤ v.tP ∧
    (s.gpr .r0 = 0 ↔ 128 ≤ v.tQ)

/-- After `pairs`. -/
def S4 : VD → State → Prop := Ph VD.qb fun v s =>
  FixL [] s ∧ 128 ≤ v.tP ∧ 128 ≤ v.tQ ∧ (s.gpr .r0 = 0 ↔ Spec.Dsa.supportedSizes (8 * v.sP) (8 * v.qb))

/-- After `sizes`. -/
def S5 : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ SzOk v

theorem pins_S0 : Pins S0 (coreRegs ++ ([] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S0a : Pins S0a (coreRegs ++ ([.r12, .r6, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S1 : Pins S1 (coreRegs ++ ([.r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S2 : Pins S2 (coreRegs ++ ([.r24] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S2a : Pins S2a (coreRegs ++ ([.r24, .r12, .r6, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl
theorem pins_S3 : Pins S3 (coreRegs ++ ([.r24, .r16] : List Reg)) := pins_fixL _ _ fun _ => rfl

theorem fixL_nil (s : State) : FixL [] s := fun _ h => absurd h List.not_mem_nil

/-- A branch's assumption, dropped. -/
theorem rel_weaken {α : Type} {Φ E : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two Φ) c Q) : RelCT isa (Two fun a s => Φ a s ∧ E a s) c Q :=
  h.mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h

theorem pl_bounds {v : VD} {s : State} (h : Base v s) : 128 ≤ v.L.pl ∧ v.L.pl ≤ 384 := by
  rcases h.ok.pl with e | e | e <;> omega

/-- `ptrP` and p's scan. -/
theorem w_scanP {v : VD} {s : State} (h : S0 v s) : WP isa (.seq (.block ptrP) sigLen) s (S0a v) := by
  obtain ⟨B, r2, -⟩ := h
  have hb := pl_bounds B
  have := B.kn
  refine WP.seq (WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (sigLen_ok a12 a6 (by omega) (by omega) fun i hi => B1.hk.rd i (by omega))
    fun u ⟨⟨b16, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, trivial⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    exact ⟨(k2.gpr .r12 (by decide)).trans a12, (k2.gpr .r6 (by decide)).trans a6,
      by rw [b16, m1, B.bytesP]; rfl⟩

/-- `ptrP` and p's `bytesBits`. -/
theorem w_bitsP {v : VD} {s : State} (h : S0 v s) : WP isa (.seq (.block ptrP) bytesBits) s (S1 v) := by
  obtain ⟨B, r2, -⟩ := h
  have hb := pl_bounds B
  have := B.kn
  refine WP.seq (WP.mono (ptrP_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (bytesBits_ok a12 a6 (by omega) (by omega) fun i hi => B1.hk.rd i (by omega))
    fun u ⟨⟨b16, b0, m2⟩, k2⟩ => ⟨B1.step k2 (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · simp only [FixL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
    rw [b16, m1, B.bytesP]; rfl
  · rw [b0, m1, B.bytesP]; rfl

theorem ite16_rel : RelCT isa (Two S0a) (.ite (.zero .d .r16) (.block [.li .r0 1]) (.block topBit))
    fun _ _ => True :=
  rel_ite_zero (fun v s₁ s₂ h₁ h₂ => by rw [pins_S0a v s₁ s₂ h₁ h₂ .r16 (by decide)])
    (rel_weaken (two_taint _ pins_S0a (by taint_decide))) (rel_weaken (two_taint _ pins_S0a (by taint_decide)))

theorem bitsP_rel {G : VD → Prop} :
    RelCT isa (Two fun v s => S0 v s ∧ G v) (.seq (.block ptrP) bytesBits) (Two fun v s => S1 v s ∧ G v) :=
  two_postG (RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_S0 (by taint_decide)) fun _ _ h => w_scanP h)
    ite16_rel)) fun _ _ h => w_bitsP h

end VG.Proof.Dsa.PPC64LE
