module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourLoopTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.Round.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Spec.MlDsa.RejNTT2
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourParseAddress
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBodyTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Env
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadMem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Tail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
meta import VerifiedGarbage.Proof.MlDsa.Round.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Spec.MlDsa.RejNTT2
meta import VerifiedGarbage.TCB.Axioms

/-! ## From `ResidentRejScalarTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Extraction may overread ignored bytes.  Its trace depends only on the input
and output cursors; candidate equality is re-established from the functional
three-byte extraction theorem before the next loop decision. -/
theorem scalarStep_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x2,.x3]))
    (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr))) :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

/-- Both executions take the same scalar iteration from equal meaningful input,
even when their original output buffers and ignored overread bytes differ. -/
theorem scalarLoopStep_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => ParseInv σ b p n L (d+1) s ∧ ParseInv τ b p n L (d+1) t ∧
        s.gpr .x16=t.gpr .x16 ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5 ∧
        t.gpr .x16=t.gpr .x4*t.gpr .x5) := by
  intro s t tr ur s' t' hp es et
  have he := hp.1.publicRegs hm hsp hp.2
  have ht' := scalarStep_ct s t tr ur s' t' trivial trivial
    ⟨he.1,fun r hr => he.2 r (by
      simp only [VG.AArch64.Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp)⟩ es et
  obtain ⟨_,u,eu,hu⟩ := scalarLoopStep_ok hs hp.1 hd hc
  obtain ⟨_,v,ev,hv⟩ := scalarLoopStep_ok ht hp.2 hd (by rw [← parsed_eq hm (by omega) L]; exact hc)
  obtain ⟨_,rfl⟩ := Exec.det es eu
  obtain ⟨_,rfl⟩ := Exec.det et ev
  have hg := hu.1.publicRegs hm hsp hv.1
  exact ⟨ht',hu.1,hv.1,(by rw [hu.2,hv.2,hg.2 .x4 (by simp),hg.2 .x5 (by simp)]),hu.2,hv.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWidePhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def WideReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=16 ∧
    s.gpr .x16=(if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0)

theorem widePhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop wideBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t ∧ j%4=d%4) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1,rfl⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4,hp.1.1.1.x5] at hg
    have hgood : 16≤256-(parsed σ b L d).length ∧ 16≤n-d := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    exact wideLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFourPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def FourReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x17=4 ∧
    s.gpr .x16=(if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0)

theorem fourPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) (.loop vectorBody (.nonzero .x .x16)))
      (fun s t => ∃j,ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t  ) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2.2,hp.2.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ hp => ⟨d,hp.1.1.1,hp.1.2.1⟩)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.1.2.2
    rw [hp.1.1.1.x4] at hg
    have hcap : 4≤256-(parsed σ b L d).length := by
      by_contra hn
      have he := hp.2
      rw [eval_zero,hg,ite_eq_right hn] at he
      contradiction
    have hcount : n-d≠0 := by
      intro hn
      have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq (hp.1.1.1.x5.trans hn)
      have he := hp.2
      rw [eval_zero,hg,ite_eq_left hcap,hx] at he
      contradiction
    have hb := hp.1.1.1.bound
    exact fourLoop_relCT hs ht hm hsp (by omega) hmod (by omega) _ _ _ _ _ _
      ⟨hp.1.1.1,hp.1.2.1,hp.1.1.2.1,hp.1.2.2.1⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarLoopTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem guard_nonzero {s : State} (he : isa.eval (.nonzero .x .x16) s=some true)
    (hg : s.gpr .x16=s.gpr .x4*s.gpr .x5) :
    (s.gpr .x4).toNat≠0 ∧ (s.gpr .x5).toNat≠0 := by
  have hn : s.gpr .x16≠0#64 := by
    intro hz
    rw [eval_nonzero,hz] at he
    contradiction
  constructor
  · intro hz
    have hx : s.gpr .x4=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.zero_mul]
  · intro hz
    have hx : s.gpr .x5=0#64 := BitVec.eq_of_toNat_eq hz
    apply hn
    rw [hg,hx,BitVec.mul_zero]

theorem scalarLoop_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hd : d<n)
    (hc : (parsed σ b L d).length<256) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.loop (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
        (.nonzero .x .x16)) (fun _ _ => True) := by
  let I := fun m s t => ∃j,j<n ∧ (parsed σ b L j).length<256 ∧ n-j=m ∧
    ParseInv σ b p n L j s ∧ ParseInv τ b p n L j t
  have hstep : ∀m,RelCT isa (I m)
      (.block (scalarChunk++rnAccept++([.mul .x .x16 .x4 .x5] : List Instr)))
      (fun s t => isa.eval (.nonzero .x .x16) s=isa.eval (.nonzero .x .x16) t ∧
        (isa.eval (.nonzero .x .x16) s=some false → True) ∧
        (isa.eval (.nonzero .x .x16) s=some true → ∃m'<m,I m' s t)) := by
    intro m s t tr ur s' t' hp es et
    obtain ⟨j,hj,hc',rfl,hp⟩ := hp
    obtain ⟨htrace,ha,hb,heq,hga,hgb⟩ := scalarLoopStep_relCT hs ht hm hsp hj hc' _ _ _ _ _ _ hp es et
    refine ⟨htrace,by rw [eval_nonzero,eval_nonzero,heq],fun _ => trivial,?_⟩
    intro hcontinue
    obtain ⟨h4,h5⟩ := guard_nonzero hcontinue hga
    rw [ha.x4] at h4
    rw [ha.x5] at h5
    have hj' : j+1<n := by have := ha.bound; omega
    have hc'' : (parsed σ b L (j+1)).length<256 := by omega
    exact ⟨n-(j+1),by omega,j+1,hj',hc'',rfl,ha,hb⟩
  exact (RelCT.loop I hstep (n-d)).mono
    (fun _ _ hp => ⟨d,hd,hc,rfl,hp⟩) (fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejScalarPhaseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def ScalarReady (σ : State) (b p : Addr) (n d : Nat) (L : List VG.Spec.MlDsa.Zq) (s : State) : Prop :=
  ParseInv σ b p n L d s ∧ s.gpr .x16=s.gpr .x4*s.gpr .x5

theorem scalarBranch_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
      (.ite (.zero .x .x16) (.block []) scalarLoop) (fun _ _ => True) := by
  apply RelCT.ite
  · intro s t hp
    have hr := hp.1.1.publicRegs hm hsp hp.2.1
    rw [eval_zero,eval_zero,hp.1.2,hp.2.2,hr.2 .x4 (by simp),hr.2 .x5 (by simp)]
  · exact RelCT.block_nil (fun _ _ _ => trivial)
  · intro s t tr ur s' t' hp es et
    have hnonzero : s.gpr .x16≠0#64 := by
      intro hz
      have hh := hp.2
      rw [eval_zero,hz] at hh
      contradiction
    have h4 : (s.gpr .x4).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x4=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.zero_mul]
    have h5 : (s.gpr .x5).toNat≠0 := by
      intro hz
      apply hnonzero
      rw [hp.1.1.2,show s.gpr .x5=0#64 from BitVec.eq_of_toNat_eq hz,BitVec.mul_zero]
    rw [hp.1.1.1.x4] at h4
    rw [hp.1.1.1.x5] at h5
    have hb := hp.1.1.1.bound
    exact scalarLoop_relCT hs ht hm hsp (by omega) (by omega) _ _ _ _ _ _ ⟨hp.1.1.1,hp.1.2.1⟩ es et

private theorem scalarSetup_ok {σ s : State} {b p : Addr} {n d : Nat} {L : List VG.Spec.MlDsa.Zq}
    (h : ParseInv σ b p n L d s) :
    WP isa (.block [.mul .x .x16 .x4 .x5]) s (ScalarReady σ b p n d L) := by
  have hw : WP isa (.block [.mul .x .x16 .x4 .x5]) s fun t =>
      Only [.x16] s t ∧ t.gpr .x16=s.gpr .x4*s.gpr .x5 :=
    wp_mul fun t ht et => wp_nil ⟨ht,et⟩
  refine WP.mono (WP.keepV (by decide) hw) fun t ⟨⟨ht,hg⟩,hv⟩ => ?_
  exact ⟨h.of_control (ht.mono (by decide)) hv,by rw [ht.get .x4,ht.get .x5]; exact hg⟩

theorem scalarPhase_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.seq (.block [.mul .x .x16 .x4 .x5])
        (.ite (.zero .x .x16) (.block []) scalarLoop)) (fun _ _ => True) := by
  apply RelCT.seq (R := fun s t => ScalarReady σ b p n d L s ∧ ScalarReady τ b p n d L t)
  · intro s t tr ur s' t' hp es et
    have hg := hp.1.publicRegs hm hsp hp.2
    have hct : RelCT isa (fun s t => s.sp=t.sp)
        (.block [.mul .x .x16 .x4 .x5]) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ h => ⟨h,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) (by taint_decide)
    obtain ⟨_,a,ea,ha⟩ := scalarSetup_ok hp.1
    obtain ⟨_,b,eb,hb⟩ := scalarSetup_ok hp.2
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det et eb
    exact ⟨(hct _ _ _ _ _ _ hg.1 es et).1,ha,hb⟩
  · exact scalarBranch_relCT hs ht hm hsp

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejControlTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem control_pair {P Q R S : State → Prop} {c : Prog isa}
    (hsp : ∀s t,P s → Q t → s.sp=t.sp)
    (hl : ∀s,P s → WP isa c s R) (hr : ∀s,Q s → WP isa c s S)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hc : (taint.check (Taint.ofRegs []) c hint).isSome=true) :
    RelCT isa (fun s t => P s ∧ Q t) c (fun s t => R s ∧ S t) := by
  have hh : RelCT isa (fun s t => P s ∧ Q t) c (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨hsp _ _ h.1 h.2,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) hc
  exact (hh.wp (fun _ _ h => ⟨hl _ h.1,hr _ h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem fourSetup_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (vectorSetup++guard))
      (fun s t => FourReady σ b p n d L s ∧ FourReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => fourSetup_ok h) (fun _ h => fourSetup_ok h) (by taint_decide)

theorem wideControl_relCT {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hsp : σ.sp=τ.sp) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard))
      (fun s t => WideReady σ b p n d L s ∧ WideReady τ b p n d L t) :=
  control_pair (fun _ _ hs ht => hs.keep.sp.trans (hsp.trans ht.keep.sp.symm))
    (fun _ h => wideControl_ok h) (fun _ h => wideControl_ok h) (by taint_decide)

theorem parseFour_relCT (v : Nat) {σ τ : State} {b p : Addr} {n d : Nat}
    {L : List VG.Spec.MlDsa.Zq} (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : d%4=n%4) :
    RelCT isa (fun s t => ParseInv σ b p n L d s ∧ ParseInv τ b p n L d t)
      (parse4 v) (fun _ _ => True) := by
  unfold parse4
  apply RelCT.seq (fourSetup_relCT hsp)
  apply RelCT.seq (fourPhase_relCT hs ht hm hsp hmod)
  exact RelCT.exists_ (fun j => scalarPhase_relCT hs ht hm hsp (d := j))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejParseTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def Start (s : State) (b p : Addr) (n : Nat) (L : List Zq) : Prop :=
  s.gpr .x2=b ∧ s.gpr .x3=coeffAddr p L.length ∧ (s.gpr .x4).toNat=256-L.length ∧
    (s.gpr .x5).toNat=n ∧ (s.gpr .x9).toNat=q ∧ Stored s.mem p L

theorem vectorSetup_start {σ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (h : Start σ b p n L) : WP isa (.block vectorSetup) σ (ParseInv σ b p n L 0) := by
  refine WP.mono (vectorSetup_ok (s := σ) h.2.2.2.2.1) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
    Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
  · rw [ha.only.get .x2,h.1]; exact (ptr_zero b).symm
  · rw [ha.only.get .x3]; exact h.2.1
  · rw [ha.only.get .x4]; exact h.2.2.1
  · rw [ha.only.get .x5]; exact h.2.2.2.1
  · rw [ha.only.mem]; exact h.2.2.2.2.2

theorem parse_relCT (v : Nat) {σ τ : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (ss : Start σ b p n L) (st : Start τ b p n L)
    (hm : InputEq σ τ b n) (hsp : σ.sp=τ.sp) (hmod : n%4=0) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (parse v) (fun _ _ => True) := by
  unfold parse
  apply RelCT.seq (R := fun s t => WideReady σ b p n 0 L s ∧ WideReady τ b p n 0 L t)
  · rw [List.append_assoc]
    apply RelCT.block_append
    apply RelCT.seq (R := fun s t => ParseInv σ b p n L 0 s ∧ ParseInv τ b p n L 0 t)
    · exact control_pair (fun _ _ h1 h2 => by subst h1; subst h2; exact hsp)
        (fun s h => by subst s; exact vectorSetup_start ss)
        (fun t h => by subst t; exact vectorSetup_start st) (by taint_decide)
    · exact wideControl_relCT hsp
  · apply RelCT.seq (widePhase_relCT hs ht hm hsp)
    intro s t tr ur s' t' hp es et
    obtain ⟨j,hj,hk,hjm⟩ := hp
    exact parseFour_relCT v hs ht hm hsp (by rw [hjm,hmod]) _ _ _ _ _ _ ⟨hj,hk⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem layout_only {s t : State} {b p : Addr} {n : Nat} {rs : List Reg}
    (h : StreamLayout s b p n) (ht : Only rs s t) : StreamLayout t b p n := by
  refine ⟨h.bound,?_,?_,?_,?_,h.disjoint⟩
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read16 j hj
  · intro j hj; rw [ht.rd,ht.wr]; exact h.read4 j hj
  · intro j hj; rw [ht.wr]; exact h.write4 j hj
  · intro j hj; rw [ht.wr]; exact h.write16 j hj

/-- Segment timing needs equality only for the consumed candidate bytes, not
for preexisting output bytes or the ignored fourth byte of scalar loads. -/
theorem segment_relCT (v n : Nat) (hn : n<65536)
    {hintSetup hintNext : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) hintSetup).isSome=true)
    (checkNext : (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) hintNext).isSome=true)
    {σ τ : State} {b p c : Addr} {L : List Zq} (hL : L.length≤256) (hmod : n%4=0)
    (hsp : σ.sp=τ.sp)
    (s24 : σ.gpr .x24=b) (s25 : σ.gpr .x25=p) (s26 : σ.gpr .x26=c)
    (t24 : τ.gpr .x24=b) (t25 : τ.gpr .x25=p) (t26 : τ.gpr .x26=c)
    (hs : StreamLayout σ b p n) (ht : StreamLayout τ b p n)
    (hrs : InRegions (σ.rd++σ.wr) c 8) (hrt : InRegions (τ.rd++τ.wr) c 8)
    (hcs : (σ.mem.readW c 64).toNat=256-L.length)
    (hct : (τ.mem.readW c 64).toNat=256-L.length)
    (hss : Stored σ.mem p L) (hst : Stored τ.mem p L)
    (hm : InputEq σ τ b n) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (segment v n) (fun _ _ => True) := by
  let P (a : State) (s : State) :=
    Only [.x2,.x3,.x4,.x5,.x6,.x9,.x10] a s ∧ Start s b p n L
  have ws : WP isa (.block (setup n)) σ (P σ) := by
    refine WP.mono (setup_ok n hn hL s24 s25 s26 hrs hcs) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hss⟩
  have wt : WP isa (.block (setup n)) τ (P τ) := by
    refine WP.mono (setup_ok n hn hL t24 t25 t26 hrt hct) fun s ⟨hh,h2,h3,h4,h5,h9⟩ => ?_
    exact ⟨hh,h2,h3,h4,h5,h9,by rw [hh.mem]; exact hst⟩
  unfold segment
  apply RelCT.seq (R := fun s t => P σ s ∧ P τ t)
  · have hc : RelCT isa (fun s t => s=σ ∧ t=τ) (.block (setup n)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x26])
        (fun s t h => by
          rcases h with ⟨rfl,rfl⟩
          exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,s26,t26]⟩) checkSetup
    exact (hc.wp (fun s t h => by rcases h with ⟨rfl,rfl⟩; exact ⟨ws,wt⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · intro s t tr ur s' t' hh es et
    have ls := layout_only hs hh.1.1
    have lt := layout_only ht hh.2.1
    have im : InputEq s t b n := by
      intro i hb
      rw [hh.1.1.mem,hh.2.1.mem]
      exact hm i hb
    have sp : s.sp=t.sp := hh.1.1.sp.trans (hsp.trans hh.2.1.sp.symm)
    have wpS := parse_ok v ls hmod hL hh.1.2.1 hh.1.2.2.1 hh.1.2.2.2.1
      hh.1.2.2.2.2.1 hh.1.2.2.2.2.2.1 hh.1.2.2.2.2.2.2
    have wpT := parse_ok v lt hmod hL hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
      hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2
    have pc := (parse_relCT v ls lt hh.1.2 hh.2.2 im sp hmod).wp
      (fun a b h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)
    apply RelCT.seq pc ?_ s t tr ur s' t' ⟨rfl,rfl⟩ es et
    exact RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => ⟨h.2.1.1.sp.trans (sp.trans h.2.2.1.sp.symm),by
        simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton]
        intro r hr
        subst r
        rw [h.2.1.1.get .x26,h.2.2.1.get .x26,hh.1.1.get .x26,hh.2.1.get .x26,s26,t26]⟩)
      checkNext

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejRowTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 theorem Pub.rowResult {v k off n : Nat} {σ τ : State} (h : Pub v σ τ)
    (hk : k<v) (L : List Zq) : rowResult σ k off n L=rowResult τ k off n L := by
  have hb : streamBytes σ k off (3*n)=streamBytes τ k off (3*n) := by
    unfold streamBytes
    apply List.map_congr_left
    intro i hi
    exact h.byte hk _
  exact congrArg (VG.Proof.MlDsa.Sample.rnFold L) hb

theorem Pub.ptrs {v off k : Nat} {σ τ : State} (h : Pub v σ τ) :
    bufP σ k+BitVec.ofNat 64 off=bufP τ k+BitVec.ofNat 64 off ∧ polyP σ k=polyP τ k ∧
      countP σ k=countP τ k := by
  refine ⟨by rw [h.buf k],h.poly k,?_⟩
  change scr σ+BitVec.ofNat 64 (counts+8*k)=scr τ+BitVec.ofNat 64 (counts+8*k)
  rw [h.2.2.1]

/-- One stream's segment of the loop, in two runs. -/
theorem segAt_relCT {v blocks off n k : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    {hintSetup hintNext : VG.Taint.Hint VG.AArch64.Taint.T}
    (checkSetup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) hintSetup).isSome=true)
    (checkNext : (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) hintNext).isSome=true) :
    RelCT isa (fun s t => SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (segment variant n)
      (fun s t => SegAt v blocks off n σ σ L (k+1) s ∧ SegAt v blocks off n τ σ L (k+1) t) := by
  have ct : RelCT isa (fun s t => SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (segment variant n) (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hb : off+3*n≤1008 := by have:=h.1.1.blockBound; omega
    have hs := h.1.1
    have ht := h.2.1
    have hks : (doneRows σ off n k L k).length≤256 := hs.length k hk
    have ls := segment_layout hp hs.env hk hb
    have lt := segment_layout hq ht.env hk hb
    rw [segment_input_eq hs.env,segment_output_eq hs.env] at ls
    rw [segment_input_eq ht.env,segment_output_eq ht.env] at lt
    obtain ⟨pb,pp,pc⟩ := pub.ptrs (off := off) (k := k)
    rw [←pb,←pp] at lt
    have crs : InRegions (s.rd++s.wr) (countP σ k) 8 :=
      in_scr_rd hp hs.env.wr (by unfold counts; have:=hp.streams; omega)
    have crt : InRegions (t.rd++t.wr) (countP σ k) 8 := by
      rw [pc]; exact in_scr_rd hq ht.env.wr (by unfold counts; have:=hq.streams; omega)
    have hm : InputEq s t (bufP σ k+BitVec.ofNat 64 off) n := rows_input_eq pub hs ht hk hn
    exact segment_relCT variant n (by omega) checkSetup checkNext hks hmod
      (hs.env.sp.trans (pub.2.2.2.1.trans ht.env.sp.symm))
      h.1.2.1.1 h.1.2.1.2.1 h.1.2.1.2.2
      (h.2.2.1.1.trans pb.symm) (h.2.2.1.2.1.trans pp.symm) (h.2.2.1.2.2.trans pc.symm)
      ls lt crs crt (hs.counts k hk) (by rw [pc]; exact ht.counts k hk)
      (hs.stored k hk) (by rw [pp]; exact ht.stored k hk)
      hm _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  refine (ct.wp (fun s t h => ⟨segAt_step hp (fun _ _ _ => rfl) hk hn hmod variant h.1,
    segAt_step hq (fun j hj M => (pub.rowResult hj M).symm) hk hn hmod variant h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejBatchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure SegmentChecks (n : Nat) where
  setupHint : VG.Taint.Hint VG.AArch64.Taint.T
  setup : (taint.check (Taint.ofRegs [.x26]) (.block (setup n)) setupHint).isSome=true

structure InitCheck (off count : Nat) where
  hint : VG.Taint.Hint VG.AArch64.Taint.T
  init : (taint.check (Taint.ofRegs []) (.block (segmentsInit off count)) hint).isSome=true

theorem segmentNext_check : ∃ h : VG.Taint.Hint VG.AArch64.Taint.T,
    (taint.check (Taint.ofRegs [.x26]) (.block segmentNext) h).isSome=true :=
  ⟨_,by taint_decide⟩

theorem segments_relCT {v blocks off n count : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hv : count=v)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off count) :
    RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
      (segments variant off n count)
      (fun s t => Rows v blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows v blocks τ (fun k => rowResult σ k off n (L k)) t) := by
  have hv4 : v≤4 := by have:=hp.streams; omega
  obtain ⟨_,checkNext⟩ := segmentNext_check
  unfold segments
  apply RelCT.seq (R := fun s t => SegAt v blocks off n σ σ L 0 s ∧ SegAt v blocks off n τ σ L 0 t)
  · have hc : RelCT isa (fun s t => Rows v blocks σ L s ∧ Rows v blocks τ L t)
        (.block (segmentsInit off count)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun s t h => ⟨h.1.env.sp.trans (pub.2.2.2.1.trans h.2.env.sp.symm),
          by simp [Taint.ofRegs,RegSet.mem_ofList]⟩) init.init
    exact (hc.wp (fun s t h =>
      ⟨segAt_init n hp h.1 hv (by have:=h.1.blockBound; omega),
       segAt_init n hq h.2 hv (by have:=h.1.blockBound; omega)⟩)).mono
      (fun _ _ h => h) (fun _ _ h => h.2)
  · refine (RelCT.loop (M := isa) (fun m s t => ∃ k, k<v ∧ m=v-k ∧
        SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)
      (fun m => ?_) v).mono (fun s t h => ⟨0,by have:=hp.streams; omega,by omega,h⟩)
      (fun _ _ h => h)
    apply RelCT.exists_
    intro k
    refine RelCT.mono (P := fun s t => k<v ∧ m=v-k ∧
        (SegAt v blocks off n σ σ L k s ∧ SegAt v blocks off n τ σ L k t)) ?_
      (fun _ _ h => h) (fun _ _ h => h)
    intro s t tr ur s' t' ⟨hk,hm,h⟩ es et
    obtain ⟨htr,h1,h2⟩ := segAt_relCT hp hq pub hk hn hmod variant checks.setup checkNext
      s t tr ur s' t' h es et
    refine ⟨htr,?_,?_,?_⟩
    · rw [segAt_eval h1 (by omega) hv4,segAt_eval h2 (by omega) hv4]
    · intro he
      rw [segAt_eval h1 (by omega) hv4] at he
      have hl : k+1=v := by simp at he; omega
      subst hl
      exact ⟨h1.last,h2.last⟩
    · intro he
      rw [segAt_eval h1 (by omega) hv4] at he
      have hl : k+1<v := by simp at he; omega
      exact ⟨v-(k+1),by omega,k+1,hl,rfl,h1,h2⟩

theorem batchFour_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off 4) :
    RelCT isa (fun s t => Rows 4 blocks σ L s ∧ Rows 4 blocks τ L t)
      (Four.batch variant off n)
      (fun s t => Rows 4 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 4 blocks τ (fun k => rowResult σ k off n (L k)) t) :=
  segments_relCT hp hq pub rfl hn hmod variant checks init

theorem batchTwo_relCT {blocks off n : Nat} {σ τ : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (variant : Nat)
    (checks : SegmentChecks n) (init : InitCheck off 2) :
    RelCT isa (fun s t => Rows 2 blocks σ L s ∧ Rows 2 blocks τ L t)
      (Two.batch variant off n)
      (fun s t => Rows 2 blocks σ (fun k => rowResult σ k off n (L k)) s ∧
        Rows 2 blocks τ (fun k => rowResult σ k off n (L k)) t) :=
  segments_relCT hp hq pub rfl hn hmod variant checks init

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
