module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchInitCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchLoopCT

/-! # Full bounded p search from public seed, accepted q, and witness position -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem nativePSearch_ct {H : Hash} (K : HashOK H) (P : PSearchPlan) (used : Nat)
    (usedBound : used ≤ P.context.witnesses.bytes.length)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => PSearchStartAt P used)
      (nativePSearch H P.context.geometry.pLen P.context.geometry.qLen) (fun _ _ => True) := by
  let start : PSearchPublic P := ⟨0, used, by have := P.context.geometry.width; omega, usedBound⟩
  exact RelCT.seq (pSearchControl_ct P used) (RelCT.seq (pSearchInit_ct P used)
    (two_map (fun (_ : Unit) => start) (fun _ _ h => h) (pSearchLoop_ct K P digest final hash hashSize)))
end VG.Proof.Dsa.X86.Generation
