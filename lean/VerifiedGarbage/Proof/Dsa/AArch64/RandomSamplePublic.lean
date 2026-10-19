module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomDrawCT
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomEncoding

/-! The public sampling trace determines the next draw's declassified decision. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomSamplePublic where
  draw : RandomDrawPublic
  trace : List Nat
  valid : 1 < Spec.Dsa.decodeBE draw.qBytes

def RandomSampleTracePre (p : RandomSamplePublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.draw.randLen, ∃ m,
    RandomReady (p.draw.context rand hlen m) p.draw.used p.draw.draws s ∧
    word s.mem p.draw.B Random.oStatus = 4 ∧
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) p.draw.draws (rand.drop p.draw.used)).trace = p.trace

def RandomSamplePublic.accept (p : RandomSamplePublic) : Bool := p.trace.head? == some 1

theorem RandomSampleTracePre.decision {p : RandomSamplePublic} {s : State} (h : RandomSampleTracePre p s) :
    RandomDrawDecisionPre ⟨p.draw, p.accept⟩ s := by
  obtain ⟨rand, hlen, m, hr, _, ht⟩ := h
  refine ⟨rand, hlen, m, hr, ?_⟩
  intro hfull
  have hwidth := VG.Proof.Dsa.random_drawBytes_scan p.draw.qBytes
  have hlen' : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE p.draw.qBytes) ≤ (rand.drop p.draw.used).length := by
    rw [hwidth, List.length_drop, hlen]
    exact Nat.le_sub_of_add_le' hfull
  have hp := p.draw.drawsPos
  obtain ⟨fuel, he⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.draw.draws ≠ 0)
  change p.draw.draws = fuel + 1 at he
  have hh := VG.Proof.Dsa.Random.sample_trace_head _ fuel _ p.valid hlen'
  rw [← he, ht, hwidth] at hh
  exact hh.symm

theorem RandomSampleTracePre.congr {p : RandomSamplePublic} {s t : State}
    (h : RandomSampleTracePre p s) (hm : t.mem = s.mem) (hk : Keep [.x0, .x4] s t) :
    RandomSampleTracePre p t := by
  obtain ⟨rand, hlen, m, hr, hs, ht⟩ := h
  exact ⟨rand, hlen, m, hr.congr hm hk, by rw [hm]; exact hs, ht⟩

def RandomSamplePublic.next (p : RandomSamplePublic)
    (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws) : RandomSamplePublic where
  draw := { p.draw with
    used := p.draw.used + p.draw.width
    draws := p.draw.draws - 1
    usedBound := hfull
    drawsPos := by omega
    drawsBound := by have := p.draw.drawsBound; omega }
  trace := p.trace.tail
  valid := p.valid

theorem random_sample_trace_next {p : RandomSamplePublic} {rand : List Byte}
    (hlen : rand.length = p.draw.randLen)
    (ht : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) p.draw.draws (rand.drop p.draw.used)).trace = p.trace)
    (hfull : p.draw.used + p.draw.width ≤ p.draw.randLen) (hf : 1 < p.draw.draws)
    (ha : p.accept = false) :
    (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE p.draw.qBytes) (p.draw.draws - 1)
      (rand.drop (p.draw.used + p.draw.width))).trace = p.trace.tail := by
  have hw := VG.Proof.Dsa.random_drawBytes_scan p.draw.qBytes
  have hlen' : Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE p.draw.qBytes) ≤ (rand.drop p.draw.used).length := by
    rw [hw, List.length_drop, hlen]
    exact Nat.le_sub_of_add_le' hfull
  have he : p.draw.draws - 1 + 1 = p.draw.draws := by omega
  have hh := VG.Proof.Dsa.Random.sample_trace_retry _ (p.draw.draws - 1) _ p.valid hlen'
    (by rw [he, ht]; exact ha)
  rw [he, ht, hw, List.drop_drop] at hh
  exact hh.symm

end VG.Proof.Dsa.AArch64
