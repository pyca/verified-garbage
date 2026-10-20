module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterBody
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterBodyCT

/-! # A public seed slice determines the outer loop's status and next witness cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def ParameterPublic.expected (p : ParameterPublic) :=
  seedExpected p.plan ((p.plan.seeds.bytes.drop p.seedUsed).take p.plan.geometry.qLen) p.used

def ParameterAnswered (plen qlen : Nat) (p : ParameterPublic) (s : State) : Prop :=
  (∃ initial, PhaseResult p.plan (BitVec.ofNat 32 (p.seedUsed + p.plan.geometry.qLen)) p.expected initial s) ∧
    p.plan.geometry.pLen = plen ∧ p.plan.geometry.qLen = qlen ∧
    p.seedUsed + p.plan.geometry.qLen ≤ p.plan.seeds.bytes.length

theorem parameter_answer {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    {plen qlen : Nat} {p : ParameterPublic} {s : State}
    (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen)
    (Hpre : ParameterTaken plen qlen p s) :
    WP isa (parameterBody H plen qlen (finishDomain F.name F.code plen qlen)) s (ParameterAnswered plen qlen p) := by
  obtain ⟨⟨W, R, seedUsed, used, source⟩, pl, ql, room⟩ := Hpre
  have positive : 0 < p.plan.geometry.qLen := by have := p.plan.geometry.qWidth; omega
  let T := p.plan.seeds.slice p.seedUsed p.plan.geometry.qLen room positive
  have len : T.bytes.length = p.plan.geometry.qLen := by
    change ((p.plan.seeds.bytes.drop p.seedUsed).take p.plan.geometry.qLen).length = _
    simp only [List.length_take, List.length_drop]; omega
  rw [← pl, ← ql]
  refine WP.mono (parameterBody_ok K F R (R.seeds.slice _ _ room positive) len source used p.bound
    (digest.trans ql.symm) (final.trans ql.symm) (by simpa only [ql] using hash) (by simpa only [ql] using hashSize))
    fun t result => ?_
  rw [seedUsed] at result
  exact ⟨⟨s, result⟩, rfl, rfl, room⟩

theorem parameter_answer_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen) :
    RelCT isa (Two (ParameterTaken plen qlen))
      (parameterBody H plen qlen (finishDomain F.name F.code plen qlen)) (Two (ParameterAnswered plen qlen)) := by
  refine two_post ?_ (fun _ _ h => parameter_answer K F digest final hash hashSize h)
  intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
  have positive : 0 < p.plan.geometry.qLen := by have := p.plan.geometry.qWidth; omega
  let T := p.plan.seeds.slice p.seedUsed p.plan.geometry.qLen hs.2.2.2 positive
  have len : T.bytes.length = p.plan.geometry.qLen := by
    change ((p.plan.seeds.bytes.drop p.seedUsed).take p.plan.geometry.qLen).length = _
    simp only [List.length_take, List.length_drop]; have := hs.2.2.2; omega
  have pre : ∀ u, ParameterTaken plen qlen p u →
      ParameterBodyAt p.plan T (BitVec.ofNat 32 (p.seedUsed + p.plan.geometry.qLen)) p.used u := by
    rintro u ⟨⟨W, R, seed, used, source⟩, _⟩
    exact ⟨W, R, R.seeds.slice _ _ _ _, source, used, seed⟩
  have ct := parameterBody_ct K F p.plan T (BitVec.ofNat 32 (p.seedUsed + p.plan.geometry.qLen)) p.used
    len p.bound (digest.trans hs.2.2.1.symm) (final.trans hs.2.2.1.symm)
    (by simpa only [hs.2.2.1] using hash) (by simpa only [hs.2.2.1] using hashSize)
  rw [hs.2.1, hs.2.2.1] at ct
  exact ct _ _ _ _ _ _ ⟨(), by simpa only [hs.2.2.1] using pre s hs, by simpa only [hs.2.2.1] using pre t ht⟩ es et
end VG.Proof.Dsa.X86.Generation
