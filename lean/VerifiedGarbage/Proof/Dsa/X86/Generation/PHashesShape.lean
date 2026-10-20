module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShapeArguments
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86.Generation.PShapeValue

/-! # Hash every contribution, select its low bytes, and construct the shaped value -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pHashesShape_ok {H : Hash} {K : HashOK H} {G : ContributionPlan} {s : State} {parent : BitVec 32} {plen : Nat}
    (L : ContributionLayout K G) (R : ContributionReady K G s)
    (savedParent : s.mem.readW (off G.frame 20) 32 = parent)
    (minLen : 2 ≤ plen) (maxLen : plen < 2 ^ 32)
    (room : plen ≤ (G.count + 1) * G.seed.length)
    (fit : G.hashes.toNat + (G.count + 1) * G.seed.length ≤ 2 ^ 32)
    (outFit : (parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped).toNat + plen ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨(G.hashes + BitVec.ofNat 32 ((G.count + 1) * G.seed.length - plen)).setWidth 64, plen⟩
      ⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped).setWidth 64, plen⟩)
    (read : ∀ i < plen, InRegions (s.rd ++ s.wr)
      (off ((G.hashes + BitVec.ofNat 32 ((G.count + 1) * G.seed.length - plen)).setWidth 64) i) 1)
    (write : ∀ i < plen, InRegions s.wr
      (off ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped).setWidth 64) i) 1) :
    WP isa (pHashesShape H G.seed.length G.count plen) s fun t =>
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem
        ((parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped).setWidth 64) plen) = G.shapedValue K plen ∧
      Frame (G.allWrites K ++ [⟨(parent + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped).setWidth 64, plen⟩]) s.mem t.mem ∧
      VG.Proof.Mont.X86.Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold pHashesShape pHashes
  refine WP.seq (WP.mono (pHashPrefix_ok L R (Nat.le_refl _)) fun a ⟨Ra, hashes, Oa, Ka⟩ => ?_)
  have parentA : a.mem.readW (off G.frame 20) 32 = parent := by
    rw [Oa.readW (r := ⟨G.frame, frameBytes⟩)
      (VG.Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide)) ?_ (by decide), savedParent]
    intro r hr
    obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp hr
    exact L.frameApart j (by have := List.mem_range.mp hj; omega) r h
  refine WP.seq (WP.mono (pShapeFromFrameArgs_ok Ra.frame Ra.hashes parentA G.seed.length G.count plen)
    fun b ⟨si, di, mem, Kb⟩ => ?_)
  have sourceAddr : (G.hashes + BitVec.ofNat 32 ((G.count + 1) * G.seed.length - plen)).setWidth 64 =
      off (G.hashes.setWidth 64) ((G.count + 1) * G.seed.length - plen) := addr_eq (by omega)
  have sourceFit : (G.hashes + BitVec.ofNat 32 ((G.count + 1) * G.seed.length - plen)).toNat + plen ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (G.count + 1) * G.seed.length - plen < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : G.hashes.toNat + ((G.count + 1) * G.seed.length - plen) < 2 ^ 32)]
    omega
  have Ksb := Ka.trans (Kb.mono (by decide))
  refine WP.mono (pShape_value minLen maxLen sourceFit outFit apart si di
    (by intro i hi; rw [Ksb.2.1, Ksb.2.2]; exact read i hi)
    (by intro i hi; rw [Ksb.2.2]; exact write i hi)) fun t ⟨value, Ot, Kt⟩ => ?_
  rw [mem, sourceAddr, hash_shaped_value fit (fun j hj => hashes j (by omega)) (by omega) room] at value
  rw [mem] at Ot
  exact ⟨value, (Oa.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (Ot.mono (fun _ hr => List.mem_append_right _ hr)), Ksb.trans (Kt.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
