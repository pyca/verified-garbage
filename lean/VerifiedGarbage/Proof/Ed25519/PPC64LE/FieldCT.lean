module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ed25519.PPC64LE.MulFn
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.MulFn

/-!
# Ed25519 on PPC64LE: the field and point functions are constant time

Only the working space's pointer in `r3`, and the low words of `mul`'s
offsets in `r4`–`r6`, are public; the taint analysis (`taint_decide`) finds
that every branch and address depends on them and on the loop counters
alone. It tracks whole registers, so `mul`'s first block, which
zero-extends the offsets, is related by its results (`mulZext_rel`): the
offsets agree in both runs after it.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE

/-- The pointer and the offsets agree. -/
def mulAgree (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r3, .r4, .r5, .r6], s₁.gpr r = s₂.gpr r

/-- The pointer and the offsets' low words agree. -/
def mulAgreeLo (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    ∀ r ∈ [Reg.r4, .r5, .r6], (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32

/-- What `mulZext` leaves from `σ`. -/
def zextF (σ s : State) : Prop :=
  s.sp = σ.sp ∧ s.gpr .r3 = σ.gpr .r3 ∧
    ∀ r ∈ [Reg.r4, .r5, .r6], s.gpr r = BitVec.ofNat 64 ((σ.gpr r).toNat % 2 ^ 32)

theorem mulZext_ok (σ : State) : WP isa (.block Impl.Ed25519.PPC64LE.mulZext) σ (zextF σ) := by
  refine wp_rotr0 fun s1 u1 => wp_rotr0 fun s2 u2 => wp_rotr0 fun s3 u3 => WP.block_nil
    ⟨by rw [u3.sp, u2.sp, u1.sp], by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)],
      fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  · rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
  · rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide)]

theorem mulZext_rel : RelCT isa mulAgreeLo (.block Impl.Ed25519.PPC64LE.mulZext) mulAgree := by
  have ht : RelCT isa mulAgreeLo (.block Impl.Ed25519.PPC64LE.mulZext) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r3])
      (fun _ _ ⟨hsp, h3, _⟩ => ⟨hsp, fun r h => by rw [show r = .r3 by simpa using h]; exact h3⟩)
      (by taint_decide)
  refine (ht.wpDep (F := zextF) fun σ₁ σ₂ _ => ⟨mulZext_ok σ₁, mulZext_ok σ₂⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨hsp, h3, hlo⟩, ⟨f1, g1, k1⟩, ⟨f2, g2, k2⟩⟩
  refine ⟨by rw [f1, f2, hsp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · rw [g1, g2, h3]
  · have hr' : r ∈ [Reg.r4, .r5, .r6] := by simpa using hr
    rw [k1 r hr', k2 r hr', ← BitVec.toNat_setWidth, ← BitVec.toNat_setWidth, hlo r hr']

theorem mulFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub Impl.Ed25519.PPC64LE.mulFn := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.Ed25519.PPC64LE.mulFn
  refine RelCT.seq (mulZext_rel.mono (fun _ _ ⟨h₁, h₂, hp⟩ => hpub _ _ h₁ h₂ hp) fun _ _ h => h) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ ⟨hsp, hr⟩ => ⟨hsp, fun r h => hr r (by simpa using h)⟩) (by taint_decide)

theorem pow250Fn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3) :
    ConstantTime isa Pre Pub Impl.Ed25519.PPC64LE.pow250Fn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => by rw [show r = .r3 by simpa using h]; exact hr⟩) (by taint_decide)

theorem addFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3) :
    ConstantTime isa Pre Pub Impl.Ed25519.PPC64LE.addFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3])
    (fun s₁ s₂ h₁ h₂ hp => by
      obtain ⟨hsp, hr⟩ := hpub s₁ s₂ h₁ h₂ hp
      exact ⟨hsp, fun r h => by rw [show r = .r3 by simpa using h]; exact hr⟩) (by taint_decide)

end VG.Proof.Ed25519.PPC64LE
