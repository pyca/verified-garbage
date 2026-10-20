module
public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Spec.Dsa.RandomSign

import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Omega

/-! Relate the remaining signing attempts to the original randomized result. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG VG.Spec.Dsa

structure RandomSignInput where
  pLen : Nat
  qLen : Nat
  key : List Byte
  digest : List Byte
  rand : List Byte

def randomSignRemaining (p : RandomSignInput) (used fuel : Nat) : RandomSignResult :=
  randomSignLoop p.pLen p.qLen p.key p.digest fuel (p.rand.drop used)

def randomSignDraw (p : RandomSignInput) (used : Nat) : VG.Spec.Dsa.Random.Sample :=
  VG.Spec.Dsa.Random.sample (privateKeyBytes p.pLen p.qLen p.key).params.q 128 (p.rand.drop used)

structure RandomSignResultRel (p : RandomSignInput) (start : Nat) (result : RandomSignResult)
    (used fuel : Nat) : Prop where
  signature : result.signature = (randomSignRemaining p used fuel).signature
  status : result.status = (randomSignRemaining p used fuel).status
  consumed : start + result.used = used + (randomSignRemaining p used fuel).used

theorem RandomSignResultRel.refl (p : RandomSignInput) (used fuel : Nat) :
    RandomSignResultRel p used (randomSignRemaining p used fuel) used fuel := ⟨rfl, rfl, rfl⟩

theorem randomSignRemaining_retry (p : RandomSignInput) (used fuel k : Nat)
    (hd : (randomSignDraw p used).scalar = some k)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = none) :
    randomSignRemaining p used (fuel + 1) =
      let next := randomSignRemaining p (used + (randomSignDraw p used).used) fuel
      { next with
        used := (randomSignDraw p used).used + next.used
        trace := (randomSignDraw p used).trace ++ [6] ++ next.trace } := by
  unfold randomSignRemaining
  rw [randomSignLoop_retry _ _ _ _ _ _ _ hd hs]
  simp only [List.drop_drop, Nat.add_comm used]
  rfl

theorem RandomSignResultRel.retry {p : RandomSignInput} {start used fuel k : Nat} {result : RandomSignResult}
    (h : RandomSignResultRel p start result used (fuel + 1))
    (hd : (randomSignDraw p used).scalar = some k)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = none) :
    RandomSignResultRel p start result (used + (randomSignDraw p used).used) fuel := by
  obtain ⟨hsig, hstatus, hused⟩ := h
  rw [randomSignRemaining_retry p used fuel k hd hs] at hsig hstatus hused
  exact ⟨hsig, hstatus, by dsimp only at hused; omega⟩

theorem RandomSignResultRel.exhausted {p : RandomSignInput} {start used : Nat} {result : RandomSignResult}
    (h : RandomSignResultRel p start result used 0) :
    result.signature = none ∧ result.status = 0 ∧ start + result.used = used := by
  obtain ⟨hsig, hstatus, hused⟩ := h
  exact ⟨hsig, hstatus, by simpa only [randomSignRemaining, randomSignLoop, Nat.add_zero] using hused⟩

theorem RandomSignResultRel.sample_none {p : RandomSignInput} {start used fuel : Nat} {result : RandomSignResult}
    (h : RandomSignResultRel p start result used (fuel + 1))
    (hd : (randomSignDraw p used).scalar = none) :
    result.signature = none ∧ result.status = Random.sampleStatus (randomSignDraw p used) ∧
      start + result.used = used + (randomSignDraw p used).used := by
  obtain ⟨hsig, hstatus, hused⟩ := h
  unfold randomSignRemaining at hsig hstatus hused
  rw [randomSignLoop_sample_none _ _ _ _ _ _ hd] at hsig hstatus hused
  exact ⟨hsig, hstatus, hused⟩

theorem RandomSignResultRel.success {p : RandomSignInput} {start used fuel k : Nat}
    {result : RandomSignResult} {sig : List Byte}
    (h : RandomSignResultRel p start result used (fuel + 1))
    (hd : (randomSignDraw p used).scalar = some k)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = some sig) :
    result.signature = some sig ∧ result.status = 1 ∧
      start + result.used = used + (randomSignDraw p used).used := by
  obtain ⟨hsig, hstatus, hused⟩ := h
  unfold randomSignRemaining at hsig hstatus hused
  rw [randomSignLoop_step_success _ _ _ _ _ _ _ _ hd hs] at hsig hstatus hused
  exact ⟨hsig, hstatus, hused⟩

end VG.Proof.Dsa
