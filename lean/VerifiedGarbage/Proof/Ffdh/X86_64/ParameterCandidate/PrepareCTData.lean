module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.InnerCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: public modulus-preparation state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.MlKem.X86_64

structure PreparePublic where
  B : Addr
  Z : Nat
  w : Nat
  N : Nat
  wr : List Region

def PreparePublic.I (d : PreparePublic) : Addr := off d.B 256
def PreparePublic.IZ (d : PreparePublic) : Nat := d.Z - 256

def PreparePublic.inner (d : PreparePublic) : InnerPublic := ⟨d.B, d.w, d.wr, 0, 0, 0⟩

def HeaderGood (d : PreparePublic) (s : State) : Prop :=
  ∃ mi, Good s d.I d.IZ d.w mi ∧ MrDims d.I d.IZ d.w ∧ slot d.w 28 ≤ d.IZ ∧
    s.wr = d.wr ∧ InnerKW d.B d.wr

theorem HeaderGood.header {d : PreparePublic} {s : State} (h : HeaderGood d s) : InnerHeader d.inner s := by
  obtain ⟨_, hg, _, _, hw, hk⟩ := h
  exact ⟨hk, good_hp hg hw⟩

def PrepareBefore (d : PreparePublic) (s : State) : Prop :=
  HeaderGood d s ∧ wv s.mem d.I (slot d.w VG.Impl.Bignum.X86_64.Public.aN) d.w = d.N ∧
    d.N % 2 = 1 ∧ 1 < d.N ∧ 2 ^ (64 * (d.w - 1)) ≤ d.N

def R2Ready (d : PreparePublic) (s : State) : Prop :=
  ∃ mi, Good s d.I d.IZ d.w mi ∧ MrDims d.I d.IZ d.w ∧ slot d.w 28 ≤ d.IZ ∧
    s.wr = d.wr ∧ InnerKW d.B d.wr ∧
    ((word s.mem d.I (slot d.w VG.Impl.Bignum.X86_64.Public.aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem d.I (slot d.w VG.Impl.Bignum.X86_64.Public.aN) d.w = d.N ∧
    wv s.mem d.I (slot d.w VG.Impl.Bignum.X86_64.Public.aOne) d.w = 1 ∧
    wv s.mem d.I (slot d.w VG.Impl.Bignum.X86_64.Public.aR2) d.w = 2 ^ (64 * d.w) * 2 ^ (64 * d.w) % d.N ∧
    d.N % 2 = 1 ∧ 1 < d.N

theorem R2Ready.header {d : PreparePublic} {s : State} (h : R2Ready d s) : InnerHeader d.inner s := by
  obtain ⟨_, hg, _, _, hw, hk, _⟩ := h
  exact ⟨hk, good_hp hg hw⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
