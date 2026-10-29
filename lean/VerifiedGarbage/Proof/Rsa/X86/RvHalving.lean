module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvHalfStep

import VerifiedGarbage.Proof.Rsa.X86.RvCountInit
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Initializing the halving loop and obtaining the odd exponent -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvHalfLoop.lean`, which only this module imported.
section

/-! # The public number of halving iterations -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Recover

theorem halfLoop_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {m c : Nat}
    (h : HI g s0 A m c 0 s) (positive : 0 < c) (bound : c ≤ 16384) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.halfBody .ne) s (HI g s0 A m c c) := by
  refine WP.loop (M := isa)
    (fun j u => ∃ k, k + j = c ∧ 0 < j ∧ HI g s0 A m c k u) ?_ c s ⟨0, by omega, positive, h⟩
  intro j u ⟨k, sum, pos, hu⟩
  refine WP.mono (halfBody_ok hu (by omega) bound) fun t ⟨ht, zt⟩ => ?_
  by_cases last : k + 1 = c
  · left
    refine ⟨?_, last ▸ ht⟩
    change t.zf.map (!·) = some false
    simp [zt, last]
  · right
    refine ⟨?_, j - 1, by omega, k + 1, by omega, by omega, ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show c - (k + 1) ≠ 0 from by omega]

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem halfInit_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {liveW ls : List Nat}
    {m eLen dLen : Nat}
    (h : KS g s0 A [aN] AW liveW V ls s) (hm : wM ∈ liveW) (value : AW wM = m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (bound : 8 * (dLen + eLen) < 2 ^ 32) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.halfInit s (HI g s0 A m (8 * (dLen + eLen)) 0) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.halfInit
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W (o := wR) (a := wM) (by decide) hm (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun u ⟨hu, _⟩ => ?_)
  rw [value] at hu
  refine WP.block_append (wp_movS rfl fun v U _ => ?_)
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine WP.mono (hv.storeSlot (d := sTc) (by decide) .eax) fun w ⟨hw, _, _⟩ => ?_
  rw [U.gpr, show (0 : BitVec 32).toNat = 0 from rfl] at hw
  refine WP.mono (hw.cntBits_ok ae ad bound) fun t ht => ?_
  refine ht.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [List.mem_singleton] at hj; subst j
    exact ⟨by simp, by rw [upd_self]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simp, by rw [upd_ne _ _ (by decide), upd_self]; rfl⟩
    · exact ⟨by simp, by rw [upd_self]; rfl⟩

theorem halving_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {liveW ls : List Nat}
    {m eLen dLen : Nat}
    (h : KS g s0 A [aN] AW liveW V ls s) (hm : wM ∈ liveW) (value : AW wM = m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (positive : 0 < 8 * (dLen + eLen)) (bound : 8 * (dLen + eLen) ≤ 16384) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.halving s (HI g s0 A m (8 * (dLen + eLen)) (8 * (dLen + eLen))) :=
  WP.seq (WP.mono (halfInit_ok h hm value ae ad (by omega)) fun _ ht => halfLoop_ok ht positive bound)

end VG.Proof.Rsa.X86.Recover
