module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestPre
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.RelCT

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
  qStack : stackUse g.qCode ≤ 152
  pv : Verified target g.pCode (ppContract (8 * g.pLen))
  pNoSp : NoSp g.pCode
  pStack : stackUse g.pCode ≤ 152
  cv : Verified target g.checkCode (Proof.Dsa.checkParametersContract abi 108)
  cNoSp : NoSp g.checkCode
  cStack : stackUse g.checkCode ≤ 108
  /-- The hash's blocks: their traces depend only on `esp` and `edi`, and
  they keep `esp`. -/
  prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore g.iv ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (g.H.N + g.qLen) (padBytes g.qLen) ((64 - g.qLen) / 4) ++
      [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 g.H.N))] ++ scr .ebp sHScr)) fun _ _ => True
  outCt : ∀ dst, RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ g.H.out)) fun _ _ => True
  outNoSp : ∀ i ∈ g.H.out, Taint.clobbers i .esp = false

theorem GeoOk.bounds {g : Geo} (G : GeoOk g) :
    20 ≤ g.qLen ∧ g.qLen ≤ 32 ∧ 128 ≤ g.pLen ∧ g.pLen ≤ 384 ∧ (g.count + 1) * g.qLen ≤ g.pLen + 12 ∧
      g.pLen ≤ (g.count + 1) * g.qLen := by
  unfold Geo.count
  rcases G.lengths with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h, h'] <;> decide

end VG.Proof.Dsa.X86.Generation
