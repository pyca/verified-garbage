module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestPre
public import VerifiedGarbage.Spec.Dsa.Derive

/-! # What parameter generation needs of the functions it calls

For one of the three sizes: the hash function's code and initial value,
proven to be the seed hash of FIPS 186-4 A.1.1.2 for the subgroup's size,
and the verified probable-prime tests and domain check it calls. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

structure GeoOk (g : Geo) where
  lengths : (g.pLen = 128 ∧ g.qLen = 20) ∨ (g.pLen = 256 ∧ g.qLen = 32) ∨ (g.pLen = 384 ∧ g.qLen = 32)
  hash : HashOk g.H g.iv
  N : g.H.N = g.qLen
  seedHash : ∀ m, hash.ok.hH.SH.H.hash m = Spec.Dsa.seedHash (8 * g.qLen) m
  e : g.e = (8 * g.pLen - 8 * g.qLen) / 32 + 1
  qv : Verified target g.qCode (ppContract (8 * g.qLen))
  qNoSp : NoSp g.qCode
  qStack : stackUse g.qCode ≤ 112
  pv : Verified target g.pCode (ppContract (8 * g.pLen))
  pNoSp : NoSp g.pCode
  pStack : stackUse g.pCode ≤ 112
  cv : Verified target g.checkCode (Spec.Dsa.checkParametersContract abi 32)
  cNoSp : NoSp g.checkCode
  cStack : stackUse g.checkCode ≤ 32

theorem GeoOk.bounds {g : Geo} (G : GeoOk g) :
    20 ≤ g.qLen ∧ g.qLen ≤ 32 ∧ 128 ≤ g.pLen ∧ g.pLen ≤ 384 ∧ (g.count + 1) * g.qLen ≤ g.pLen + 12 ∧
      g.pLen ≤ (g.count + 1) * g.qLen := by
  unfold Geo.count
  rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

end VG.Proof.Dsa.X86.Generation
