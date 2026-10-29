module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KcBody
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Spec.RsaKeyGen


/-! # Key-check arithmetic agrees with the shared RSA validity predicates -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

def validity (full : Bool) (k : Nat) (v : Vals) : Bool :=
  if full then Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI
  else Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI

structure Bounds (g : Geo) (k : Nat) (v : Vals) : Prop where
  pShort : v.p < 256 ^ (k - 1)
  qShort : v.q < 256 ^ (k - 1)
  pDouble : 2 * v.p ≤ 2 ^ (32 * g.w)
  qDouble : 2 * v.q ≤ 2 ^ (32 * g.w)

theorem ProdsOk.exact {g : Geo} {v : Vals} {k R₁ R₂ R₃ : Nat}
    (h : ProdsOk g v R₁ R₂ R₃) (b : Bounds g k v) (he : Spec.Rsa.exponentValid v.e = true) :
    (v.dP < 2 * (v.p / 2) → R₁ = v.e * v.dP % (2 * (v.p / 2))) ∧
    (v.dQ < 2 * (v.q / 2) → R₂ = v.e * v.dQ % (2 * (v.q / 2))) ∧
    (v.qI < v.p → R₃ = v.q * v.qI % v.p) := by
  have eBound : v.e < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    exact he.2
  refine ⟨fun hp => ?_, fun hq => ?_, fun hq => ?_⟩
  · rw [h.1 hp (by have := b.pDouble; omega), Nat.mod_eq_of_lt eBound]
  · rw [h.2.1 hq (by have := b.qDouble; omega), Nat.mod_eq_of_lt eBound]
  · exact h.2.2 hq b.pDouble

theorem checks_ok {g : Geo} {v : Vals} {s : State} {k : Nat} (h : BodyIn g v s)
    (b : Bounds g k v) (hm : Spec.Rsa.modulusValid v.n k = true)
    (he : Spec.Rsa.exponentValid v.e = true) :
    WP isa (if g.full then keyBody g.full else crtBody g.full) s fun t =>
      ∃ A live, Stg g s A live (validity g.full k v) t := by
  obtain ⟨B, Z, len, full⟩ := g
  cases full
  · refine WP.mono (crtBody_ok h) fun t ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, ht⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := hR.exact b he
    have eq := VG.Proof.Rsa.crtKeyValid_bits hm he b.pShort b.qShort
      (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3
    refine ⟨aFin v, liveFin, ?_⟩
    change Stg ⟨B, Z, len, false⟩ s (aFin v) liveFin (Spec.Rsa.crtKeyValid k v.n v.e v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
  · refine WP.mono (keyBody_ok h) fun t ⟨X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩ => ?_
    obtain ⟨h1, h2, h3⟩ := hR.exact b he
    have eq := VG.Proof.Rsa.keyValid_bits hm he b.pShort b.qShort
      (fun pos => ⟨(hX pos).2, (hX pos).1⟩) h1 h2 h3 hY₁ hY₂
    refine ⟨A, live, ?_⟩
    change Stg ⟨B, Z, len, true⟩ s A live (Spec.Rsa.keyValid k v.n v.e v.d v.p v.q v.dP v.dQ v.qI) t
    rw [eq]; exact ht
end VG.Proof.Rsa.X86.KeyCheck
