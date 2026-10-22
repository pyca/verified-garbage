module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.RootPow
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed

/-! # The machine root candidate's shared refinement interface -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (W0 W2)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

/-- Writes shared by exponentiation and the P-224 descent. -/
def candidateSlots : List Nat := [ACC, PT, TMP, EXPP, EXPN, T0, T1, T2, T3, T4, T5, W0]
def candidateWrites (c : Cfg) : List (Nat × Nat) := slWk c candidateSlots ++
  [(bitsAt c.n 1, 64 * c.n), (bitsAt c.n 2, 64 * c.n)]

structure CandidatePost (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C)
    (base : Addr) (s s' : State) : Prop where
  keep : Rest powClob s s'
  unch : Unch base (candidateWrites c) s.mem s'.mem
  lt : sv c base s' ACC < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    root (toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2))

/-- This is discharged by the assembly proofs for each root method. -/
def CandidateCorrect (c : Cfg) (root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C) : Prop :=
  ∀ (base : Addr) (s : State), Scr s base size → Far s base 8192 →
    ModOkW c.MP' size c.C.p s.mem base → sv c base s W2 < c.C.p →
    sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p →
    WP isa (Impl.EcKey.Compressed.Arm.rootCandidate c) s (CandidatePost c root base s)

theorem candidate_fixed {c : Cfg} (hc : CfgOk c) : FixedOk c (candidateWrites c) :=
  (fixedOk_slWk hc.n10 (l := candidateSlots) (by decide)).append (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact fixedOk_tbl hc.n10 1 _ (by simp)
    · exact fixedOk_tbl hc.n10 2 _ (by simp))

theorem candidate_apart {c : Cfg} (hc : CfgOk c) {i : Nat} (hi : i < 45) (hw : i ∉ candidateSlots) :
    ∀ w ∈ candidateWrites c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  apply apart_append (apart_slWk hc.n10 hi hw)
  intro w h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact (apart_tbl hc.n10 hi 1) _ (by simp)
  · exact (apart_tbl hc.n10 hi 2) _ (by simp)

theorem candidateThree_correct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3) :
    CandidateCorrect c Impl.EcKey.Compressed.rootThreeModFour := by
  intro base s hs hf hM hB hO
  refine WP.mono (rootThree_ok hc hp hs hf hM hB hO) fun s' ⟨k, U, lt, v⟩ => ?_
  refine ⟨k, U.mono ?_, lt, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, powWx, powW,
      Impl.EcKey.Compressed.Arm.rootPow] at hw
    rcases hw with (rfl | rfl) | (rfl | rfl | rfl) | rfl
    all_goals simp [candidateWrites, candidateSlots, slWk, slW, MP'_n, MP'_tmp]
  · simpa only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow] using v

end VG.Proof.EcKey.Compressed.Arm
