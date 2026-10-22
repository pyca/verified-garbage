module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.RootPow
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.Law

/-! # Shared refinement interface for coordinate-recovery algorithms -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W0 W2)
open VG.Impl.EcKey.Compressed.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 def candidateSlots : List Nat := [ACC, T0, T1, T2, T3, T4, T5, W0, TMP, RX, RY, RZ, DX, DY, DZ, TX, TY, TZ]
 def candidateWrites (c : Cfg) : List (Nat × Nat) := rootWrites c ++ slW c candidateSlots

 structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s t : State) : Prop where
  keep : KeepRegs (powClob c.n) s t
  unch : Unch base (candidateWrites c) s.mem t.mem
  lt : sv c base t ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

 def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size →
    ModOkA c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (rootCandidate c) s (CandidatePost c root base s)

 theorem candidate_fixed {c : Cfg} (hc : BaseCfgOk c) : FixedOk c (candidateWrites c) :=
  (fixedOk_rootWrites hc).append (fixedOk_slW (l := candidateSlots) (by decide))

 theorem candidate_apart {c : Cfg} (hc : BaseCfgOk c) {i : Nat}
    (hi : i < 45) (hw : i ∉ ACC :: candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append
  · exact apart_rootWrites hc hi (fun h => hw
      ((by decide : ∀ i ∈ rootSlots, i ∈ ACC :: candidateSlots) i h))
  · exact apart_slW (fun h => hw (List.mem_cons_of_mem _ h))
      (by omega) (by decide)

 theorem candidateThree_correct {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 = 3)
    (hchain : ChainOk (rootChain c ((c.C.p + 1) / 4)) ((c.C.p + 1) / 4)) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hM hB _
  rw [rootCandidate, ite_eq_left hp]
  refine WP.mono (rootPower_ok hc hchain hs
    hM hB) fun t ⟨K, U, lt, v⟩ => ?_
  refine ⟨K, U.mono (by intro w hw; exact List.mem_append_left _ hw), lt, ?_⟩
  simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.AArch64
