module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Steps
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT

/-!
# ML-DSA on RISC-V: two runs in the buffers of a `Site`

As on PPC64LE (`Proof/MlDsa/PPC64LE/KeyGen/StepsCT.lean`): two runs in the
same layout, with the same stack pointer (`Two`): a part that leaks the
same, and changes only what `Kept` allows, leaves two runs in it
(`RelCT.two`); and two runs of a part leak the same by taint analysis from
the pointers (`taint31`, `taint4`), or, for the sponge, by `hashS_tr`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.KeyGen

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Impl.MlDsa.RISCV64.KeyGen
open VG.Impl.MlKem.RISCV64 (Piece hash copy)
open VG.Spec.Sha3 (rates)

/-- Two runs in the layout `L`, with the same stack pointer. -/
def Two (L : Lay) (Wb : List Nat) (STK : Nat) (x y : State) : Prop :=
  Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp

section
variable {L : Lay} {Wb : List Nat} {STK : Nat}

theorem Two.s11 {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.s11], x.gpr r = y.gpr r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr; rw [h.1.s11, h.2.1.s11]

theorem Two.regs {x y : State} (h : Two L Wb STK x y) : ∀ r ∈ [Reg.s8, .s9, .s10, .s11], x.gpr r = y.gpr r :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.1.s8, h.2.1.s8]
    · rw [h.1.s9, h.2.1.s9]
    · rw [h.1.s10, h.2.1.s10]
    · rw [h.1.s11, h.2.1.s11]

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
    {hc : VG.Taint.Hint VG.RISCV64.taint.T} (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s11]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs [.s11])
    (fun x y hxy => ⟨(hP x y hxy).2.2, fun r hr => (hP x y hxy).s11 r (Taint.mem_ofRegs.mp hr)⟩) h

/-- Taint analysis, from the pointers of the layout. -/
theorem taint4 {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two L Wb STK x y)
    {hc : VG.Taint.Hint VG.RISCV64.taint.T}
    (h : (VG.RISCV64.taint.check (Taint.ofRegs [.s8, .s9, .s10, .s11]) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs [.s8, .s9, .s10, .s11])
    (fun x y hxy => ⟨(hP x y hxy).2.2, fun r hr => (hP x y hxy).regs r (Taint.mem_ofRegs.mp hr)⟩) h

/-- Two runs of the sponge. -/
theorem hashS_tr {K : Nat → Bool}
    (hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb)
    {rate sfx : Nat} (hrate : rate ∈ rates) (hsfx : sfx < 2048) {ins : List Piece} {q : Piece} (hne : ins ≠ [])
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

end VG.Proof.MlDsa.RISCV64.KeyGen
