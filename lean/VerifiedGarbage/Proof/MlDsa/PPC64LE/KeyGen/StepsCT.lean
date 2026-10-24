module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

/-!
# ML-DSA on PPC64LE: two runs in the buffers of a `Site`

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/StepsCT.lean`): two runs in the
same layout, with the same stack pointer (`Two`): a part that leaks the
same, and changes only what `Kept` allows, leaves two runs in it
(`RelCT.two`); and two runs of a part leak the same by taint analysis from
the pointers (`taint31`, `taint4`), or, for the sponge, by `hashS_tr`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Impl.MlKem.PPC64LE (Piece hash copy)
open VG.Spec.Sha3 (rates)

/-- Two runs in the layout `L`, with the same stack pointer. -/
def Two (L : Lay) (Wb : List Nat) (STK : Nat) (x y : State) : Prop :=
  Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp

section
variable {L : Lay} {Wb : List Nat} {STK : Nat}

theorem Two.r31 {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r31], x.gpr r = y.gpr r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h.1.r31, h.2.1.r31]

theorem Two.regs {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.r28, .r29, .r30, .r31], x.gpr r = y.gpr r :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.r28, h.2.1.r28]
    · rw [h.1.r29, h.2.1.r29]
    · rw [h.1.r30, h.2.1.r30]
    · rw [h.1.r31, h.2.1.r31]

/-- A part that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x, Site L Wb STK x → WP isa c x fun x' => ∃ rs, Kept rs x x') : RelCT isa P c (Two L Wb STK) :=
  (RelCT.wpDep htr (F := fun x x' => ∃ rs, Kept rs x x')
    fun x y h => ⟨hok x (hP x y h).1, hok y (hP x y h).2.1⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩ => ⟨(hP σ₁ σ₂ hp).1.kept hx, (hP σ₁ σ₂ hp).2.1.kept hy, by
      rw [hx.sp, hy.sp]; exact (hP σ₁ σ₂ hp).2.2⟩

/-- Taint analysis, from the pointer to `scratch`. -/
theorem taint31 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T} (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r31])
    (fun x y hxy => ⟨(hP x y hxy).2.2, fun r hr => (hP x y hxy).r31 r (Taint.mem_ofRegs.mp hr)⟩) h

/-- Taint analysis, from the pointers of the layout. -/
theorem taint4 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r28, .r29, .r30, .r31]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r28, .r29, .r30, .r31])
    (fun x y hxy => ⟨(hP x y hxy).2.2, fun r hr => (hP x y hxy).regs r (Taint.mem_ofRegs.mp hr)⟩) h

/-- Two runs of the sponge. -/
theorem hashS_tr {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hsfx : sfx < 32768) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
    (hin : ∀ s, Site L Wb STK s → ∀ p ∈ ins, PieceOk (hashLay L s K) ix s false p)
    (hq : ∀ s, Site L Wb STK s → PieceOk (hashLay L s K) ix s true q) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Two L Wb STK x y) : RelCT isa P (hash rate sfx ins [q]) fun _ _ => True :=
  RelCT.mono (RelCT.exists_ fun (s₀ : State) =>
    hash_ct (P := fun a b => s₀ = a ∧ P a b) (L := hashLay L s₀ K) (idx := ix) hrate hsfx hne
      fun a b ⟨e, hab⟩ => by
        subst e
        have ⟨ha, hb, hsp⟩ := hP s₀ b hab
        have hl : hashLay L s₀ K = hashLay L b K := by simp only [hashLay, hsp]
        refine ⟨⟨ha.ctx hK, hin s₀ ha, fun p hp => ?_⟩, ⟨hl ▸ hb.ctx hK, hl ▸ hin b hb, fun p hp => ?_⟩, hsp⟩ <;>
          rw [List.mem_singleton] at hp <;> subst hp
        · exact hq s₀ ha
        · exact hl ▸ hq b hb)
    (fun a b h => ⟨a, rfl, h⟩) fun _ _ h => h

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
