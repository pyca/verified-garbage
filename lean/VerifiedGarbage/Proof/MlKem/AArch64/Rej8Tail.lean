module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Four scalar chunks at the end of the compacted polynomial -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def scalarFour : Prog isa := seqs [sampleBody,sampleBody,sampleBody,sampleBody]

theorem scalarFour_ok {initial : List Zq} {N t : Nat} {B : Nat → Byte}
    {bP aP : Addr} {s₀ s : State} (hp : Scalar.LPre N B bP aP s₀)
    (h : Scalar.Inv initial N B bP aP s₀ t s) (ht : t+4≤N) :
    WP isa scalarFour s fun u => Scalar.Inv initial N B bP aP s₀ (t+4) u ∧ u.v=s.v := by
  have hw : WP isa scalarFour s (Scalar.Inv initial N B bP aP s₀ (t+4)) := by
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega) h) fun a ⟨ha,_⟩ => ?_)
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega) ha) fun b ⟨hb,_⟩ => ?_)
    refine WP.seq (WP.mono (Scalar.body_ok hp (by omega) hb) fun c ⟨hc,_⟩ => ?_)
    exact WP.mono (Scalar.body_ok hp (by omega) hc) fun _ ⟨hd,_⟩ => hd
  obtain ⟨tr,u,he,hu⟩ := hw
  refine ⟨tr,u,he,hu,?_⟩
  funext r
  apply Exec.vec (c := scalarFour) (s := s) (s' := u) ?_ he
  intro i hi
  have hn : (instrs scalarFour).all (fun i => decide (vdstOf i=none))=true := by decide +kernel
  have hi' := of_decide_eq_true (List.all_eq_true.mp hn i hi)
  rw [hi']
  exact nofun

end VG.Proof.MlKem.AArch64.Rej8
