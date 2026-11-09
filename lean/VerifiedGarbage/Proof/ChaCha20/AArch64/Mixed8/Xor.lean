module
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.ChaCha20.Contract

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.XorContract
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Spec.ChaCha20.Contract
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.ChaCha20
meta import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (L)

variable {sve : Bool}

theorem nonzero_short {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 512)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from
    VG.Proof.ChaCha20.AArch64.Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 512 <;> simp [hn]

theorem correct_aux (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => GprAbi s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 ∧
      (u.v .v8).extractLsb' 0 64 = (s.v .v8).extractLsb' 0 64 ∧
      (u.v .v9).extractLsb' 0 64 = (s.v .v9).extractLsb' 0 64 := by
  have hp := VG.Proof.ChaCha20.AArch64.Xor.TPre.of s hs
  apply WP.seq
  refine (check_ok s).mono fun a ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ?_
  apply WP.seq
  have hb : WP isa (.ite (.nonzero .x .x5) (.block [])
      (.seq (.block enterFrom) (.seq (.loop (bodyFrom sve) (.zero .x .x5)) (.block leaveFrom)))) a
      fun u => ∃ t, TRest s t u := by
    apply WP.ite (decide (L s < 512)) (nonzero_short h5)
    · intro _
      refine WP.block_nil ⟨0,?_,?_,?_,?_,?_,by omega,?_,hr,hw,hsp,?_,?_,?_,?_,?_⟩
      · rw [hg _ (by decide)]
      · rw [hg _ (by decide)]; simp
      · rw [hg _ (by decide)]
        simp only [Nat.mul_zero,Nat.sub_zero]
        simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
      · rw [hg _ (by decide)]
      · rw [hg _ (by decide)]; simp
      · intro r hr
        exact hg r (by intro he; subst r; simp [preserved] at hr)
      · rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
      · intro k _; rw [hm]; simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
      · intro k _ _; rw [hm]
      · rw [hv]
      · rw [hv]
    · intro hshort
      have hge : 512 ≤ L s := by have hh := of_decide_eq_false hshort; omega
      apply WP.seq
      refine (tenter_ok hp hg hm hr hw hsp hv).mono fun b hb => ?_
      apply WP.seq
      refine (tbulk_ok hp hb hge).mono fun c ⟨t,_,hc⟩ => ?_
      exact (tleave_ok hp hc).mono fun d hd => ⟨t,hd⟩
  refine hb.mono fun u ⟨t,hu⟩ => ?_
  refine (WP.preservedV (ttail_ok hp hu) (hc := by cases sve <;> lit_decide)).mono ?_
  intro v ⟨⟨ha,hpost,h0,h1⟩,hvec⟩
  exact ⟨ha,hpost,h0,h1,by rw [hvec .v8 (by decide),hu.v8],by rw [hvec .v9 (by decide),hu.v9]⟩

theorem correct (s : State) (hs : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s fun u => abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  obtain ⟨t,u,he,ha,hp,h0,h1,h8,h9⟩ := correct_aux s hs
  refine ⟨t,u,he,⟨ha.1,ha.2,?_⟩,hp,h0,h1⟩
  intro r hr
  by_cases he8 : r = .v8
  · subst r; exact h8
  by_cases he9 : r = .v9
  · subst r; exact h9
  have hc : (Impl.ChaCha20.AArch64.Mixed8.xor sve).allInstrs Rows6.keepsOtherV = true := by cases sve <;> lit_decide
  rw [Exec.vec (fun i hi => Rows6.keepsOtherV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq Rows6.keepsOtherV (Impl.ChaCha20.AArch64.Mixed8.xor sve)) ▸ hc) i hi) hr he8 he9) he]

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa (Impl.ChaCha20.AArch64.Mixed8.xor sve) s t u ∧ abiPreserved s u ∧ xorAArch64.post s u :=
  (correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : (Impl.ChaCha20.AArch64.Mixed8.xor sve).noFrames = true := by cases sve <;> lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub (Impl.ChaCha20.AArch64.Mixed8.xor sve) := by
  cases sve <;>
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

end VG.Proof.ChaCha20.AArch64.Mixed8
