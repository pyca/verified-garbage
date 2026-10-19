module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomState

import VerifiedGarbage.Proof.Framework.Omega

/-! Public draw parameters, with random bytes existential in the state predicate. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure RandomDrawPublic where
  B : Addr
  R : Addr
  Q : Addr
  qBytes : List Byte
  randLen : Nat
  used : Nat
  draws : Nat
  qlen : qBytes.length ≤ 32
  positive : 0 < (VG.Proof.Dsa.significant qBytes).1
  randBound : randLen < 2 ^ 64
  usedBound : used ≤ randLen
  drawsPos : 0 < draws
  drawsBound : draws < 2 ^ 64

def RandomDrawPublic.width (p : RandomDrawPublic) : Nat := (VG.Proof.Dsa.significant p.qBytes).1

def RandomDrawPublic.context (p : RandomDrawPublic) (rand : List Byte)
    (hlen : rand.length = p.randLen) (m : Mem) : RandomContext where
  B := p.B
  initialMem := m
  R := p.R
  Q := p.Q
  qBytes := p.qBytes
  rand := rand
  qlen := p.qlen
  positive := p.positive
  randBound := by rw [hlen]; exact p.randBound

def RandomDrawPre (p : RandomDrawPublic) (s : State) : Prop :=
  ∃ rand, ∃ hlen : rand.length = p.randLen, ∃ m,
    RandomReady (p.context rand hlen m) p.used p.draws s

def RandomDrawFullPre (p : RandomDrawPublic) (s : State) : Prop :=
  RandomDrawPre p s ∧ p.used + p.width ≤ p.randLen

theorem RandomDrawPre.sp {p : RandomDrawPublic} {s : State} (h : RandomDrawPre p s) : s.sp = p.B := by
  obtain ⟨_, _, _, hr⟩ := h
  exact hr.sp

end VG.Proof.Dsa.AArch64
