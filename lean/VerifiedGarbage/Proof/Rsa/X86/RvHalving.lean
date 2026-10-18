module

public import VerifiedGarbage.Proof.Rsa.X86.RvHalfLoop
public import VerifiedGarbage.Proof.Rsa.X86.RvCountInit

/-! # Initializing the halving loop and obtaining the odd exponent -/

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
    WP isa (halfInit g.n) s (HI g s0 A m (8 * (dLen + eLen)) 0) := by
  unfold halfInit
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_W (o := wR) (a := wM) (by decide) hm
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
    WP isa (halving g.n) s (HI g s0 A m (8 * (dLen + eLen)) (8 * (dLen + eLen))) :=
  WP.seq (WP.mono (halfInit_ok h hm value ae ad (by omega)) fun _ ht => halfLoop_ok ht positive bound)

end VG.Proof.Rsa.X86.Recover
