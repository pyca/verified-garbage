module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTPre
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Main
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: what two runs of the witnesses' loop share

Two runs of the loop are related at each iteration by `LI n (a, k)`: the
call's public data `a`, `k` witnesses passed and `n + 1` iterations left
(`MrAt`), the same in both runs. Whether the next witness passes
(`pass_agree`) and whether the loop goes on (`mc_agree`) are then the same:
both follow from the shape of the result of the test, which the leak fixes
(`shape_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-! ## Two runs -/

theorem two_cond {α : Type} {Φ : α → State → Prop} {c : isa.Cond} {b : Bool} {p : Prog isa}
    {Q : State → State → Prop}
    (hag : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval c s₁ = isa.eval c s₂)
    (h : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some b) p Q) :
    RelCT isa (fun s₁ s₂ => Two Φ s₁ s₂ ∧ isa.eval c s₁ = some b) p Q :=
  h.mono (fun _ _ ⟨⟨a, h₁, h₂, hsp⟩, e⟩ => ⟨a, ⟨h₁, e⟩, ⟨h₂, (hag a _ _ h₁ h₂) ▸ e⟩, hsp⟩) fun _ _ h => h

theorem two_ite {α : Type} {Φ : α → State → Prop} {c : isa.Cond} {t e : Prog isa} {Q : State → State → Prop}
    (hag : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some true) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some false) e Q) :
    RelCT isa (Two Φ) (.ite c t e) Q :=
  RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hag a _ _ h₁ h₂) (two_cond hag ht) (two_cond hag he)

theorem two_mono {α : Type} {Φ Ψ : α → State → Prop} {p : Prog isa} {Q : State → State → Prop}
    (hm : ∀ a s, Φ a s → Ψ a s) (h : RelCT isa (Two Ψ) p Q) : RelCT isa (Two Φ) p Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, hm a _ h₁, hm a _ h₂, hsp⟩) fun _ _ h => h

/-- The registers of `Env` agree for calls with the same public data. -/
theorem env_agree {a : CD} {s0 s0' s s' : State} {Z Z' : Nat} (k : KRel a s0) (k' : KRel a s0')
    (e : Env s (sB s0) Z (cw s0)) (e' : Env s' (sB s0') Z' (cw s0')) :
    ∀ r ∈ [Reg.r31, .r10, .r11, .r29], s.gpr r = s'.gpr r := by
  have hB : sB s0 = sB s0' := k.arg k' (i := 1) (by decide)
  have hw : cw s0 = cw s0' := by simp only [cw, k.oL_eq k']
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e.h31, e'.h31, hB]
  · rw [e.h10, e'.h10, hB, hw]
  · rw [e.h11, e'.h11, hw]
  · rw [e.h29, e'.h29, hw]

/-! ## The loop's context -/

/-- The call from `s0`, and its witnesses' loop from `sL`. -/
structure LCtx (a : CD) (s0 sL : State) : Prop where
  krel : KRel a s0
  t3 : T3 s0 (cw s0) (candOf s0) sL
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1

/-- The loop's `(a, m)`. -/
abbrev lA (s0 : State) : Nat := (Spec.Rsa.splitTwos (candOf s0 - 1)).1
abbrev lM (s0 : State) : Nat := (Spec.Rsa.splitTwos (candOf s0 - 1)).2

/-- After `k` witnesses passed, `n + 1` iterations left. -/
def LI (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) ak.2 s

theorem candS_eq {s0 : State} (hp : CIn s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 := by
  obtain ⟨hw, -, -⟩ := cw_facts hp
  unfold candS candOf rB
  rw [take_bytesAt _ _ hav, hw, show 8 * (8 * cw s0) = 64 * cw s0 by omega]

theorem LCtx.hav {a : CD} {s0 sL : State} (C : LCtx a s0 sL) : oL s0 ≤ rL s0 := by
  rw [C.t3.tc.hw]; exact C.t3.tc.h8

theorem shape_eq {a : CD} {s0 s0' sL sL' : State} (C : LCtx a s0 sL) (C' : LCtx a s0' sL') :
    VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0') ((rB s0').drop (8 * cw s0'))) := by
  have hp := C.krel.1
  have hp' := C'.krel.1
  have hav := C.hav
  have hav' := C'.hav
  obtain ⟨hw, -, -⟩ := cw_facts hp
  obtain ⟨hw', -, -⟩ := cw_facts hp'
  have e := shape_agree C.krel C'.krel hav
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact C.ncl)
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega]; exact C.t3.noc)
    (by rw [candS_eq hp hav]; exact C.gcd)
  rwa [candS_eq hp hav, candS_eq hp' hav', hw, hw'] at e

theorem rB_len (s0 : State) : (rB s0).length = rL s0 := bytesAt_length _ _ _

/-- The witness at offset `u` passes in both runs or in neither. -/
theorem pass_agree {a : CD} {s0 s0' sL sL' : State} {k n : Nat} (C : LCtx a s0 sL) (C' : LCtx a s0' sL')
    (ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n)
    (ha' : MrAt (candOf s0') (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0') (8 * cw s0') (rB s0') k n)
    (hav : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length) :
    Spec.RsaKeyGen.mrIteration (candOf s0) (lA s0) (lM s0) (wit (candOf s0) (8 * cw s0) (rB s0)
        (8 * cw s0 * (k + 1))).1 =
      Spec.RsaKeyGen.mrIteration (candOf s0') (lA s0') (lM s0') (wit (candOf s0') (8 * cw s0') (rB s0')
        (8 * cw s0' * (k + 1))).1 := by
  have hp := C.krel.1
  have hp' := C'.krel.1
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  have hl : (rB s0).length = (rB s0').length := by rw [rB_len, rB_len, C.krel.rL_eq C'.krel]
  obtain ⟨-, hw4, -⟩ := cw_facts hp
  obtain ⟨-, -, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ cw s0) C.t3.tc.shape
  obtain ⟨-, -, hwb'⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ cw s0') C'.t3.tc.shape
  have p₁ := VG.Proof.RsaKeyGen.mr_pass (a := lA s0) (m := lM s0) (r := rB s0) (used := 8 * cw s0 * (k + 1))
    ha.go hwb (by omega) hav
  have p₂ := VG.Proof.RsaKeyGen.mr_pass (a := lA s0') (m := lM s0') (r := rB s0') (used := 8 * cw s0' * (k + 1))
    ha'.go hwb' (by omega)
    (by rw [← hw, ← hl]; exact hav)
  have l₁ : VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (candOf s0)
      (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0)) ((mrS (candOf s0) (8 * cw s0) (rB s0) k).1,
      (mrS (candOf s0) (8 * cw s0) (rB s0) k).2) ((rB s0).drop (8 * cw s0 * (k + 1)))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))) := by
    rw [ha.loop]
  have l₂ : VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (candOf s0')
      (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0')) ((mrS (candOf s0') (8 * cw s0') (rB s0') k).1,
      (mrS (candOf s0') (8 * cw s0') (rB s0') k).2) ((rB s0').drop (8 * cw s0' * (k + 1)))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0') ((rB s0').drop (8 * cw s0'))) := by
    rw [ha'.loop]
  rw [l₁] at p₁
  rw [l₂] at p₂
  unfold wit
  rw [← p₁, ← p₂, shape_eq C C', hl, hw]

/-- The loop goes on in both runs or in neither. -/
theorem mc_agree {a : CD} {s0 s0' sL sL' : State} {k n : Nat} (C : LCtx a s0 sL) (C' : LCtx a s0' sL')
    (ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n)
    (ha' : MrAt (candOf s0') (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0') (8 * cw s0') (rB s0') k n) :
    MC (candOf s0) (cw s0) (rB s0) k n ↔ MC (candOf s0') (cw s0') (rB s0') k n := by
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  have hl : (rB s0).length = (rB s0').length := by rw [rB_len, rB_len, C.krel.rL_eq C'.krel]
  unfold MC
  constructor
  · rintro ⟨hav, hp, hn⟩
    refine ⟨by rw [← hw, ← hl]; exact hav, ?_, hn⟩
    rw [← pass_agree C C' ha ha' hav]; exact hp
  · rintro ⟨hav, hp, hn⟩
    have hav₁ : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length := by rw [hw, hl]; exact hav
    refine ⟨hav₁, ?_, hn⟩
    rw [pass_agree C C' ha ha' hav₁]; exact hp

end VG.Proof.RsaKeyGen.PPC64LE.Cand
