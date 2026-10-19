module

import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailHead
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejDone
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailHead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTail
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailLoop
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Bswap
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue
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
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.Bswap
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
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBatch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEpi
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejRowStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejScalarStep
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueezeSetup
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTimingDone
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue
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

/-! ## From `ResidentRejTimingBlocks.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- Split a straight-line prefix while retaining its continuation. -/
theorem blockPrefix {P Q : State → State → Prop} {a b : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block a) (.seq (.block b) c)) Q) :
    RelCT isa P (.seq (.block (a++b)) c) Q := by
  intro s t tr ur s' t' hp es et
  cases es with
  | seq ea ec =>
    cases et with
    | seq eb ed =>
      rw [Exec.block_iff,execBlock_append] at ea eb
      obtain ⟨⟨sa,ta⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp ea
      obtain ⟨⟨sb,tb⟩,hc,hd⟩ := Option.map_eq_some_iff.mp hb
      obtain ⟨⟨ua,va⟩,he,hf⟩ := Option.bind_eq_some_iff.mp eb
      obtain ⟨⟨ub,vb⟩,hg,hh⟩ := Option.map_eq_some_iff.mp hf
      simp only [Prod.mk.injEq] at hd hh
      obtain ⟨rfl,rfl⟩ := hd
      obtain ⟨rfl,rfl⟩ := hh
      obtain ⟨hl,hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha) (.seq (.block hc) ec))
        (.seq (.block he) (.seq (.block hg) ed))
      exact ⟨by simpa only [List.append_assoc] using hl,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailReadValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok)

/-- Masking makes the legacy cleanup decision depend on exactly the final
three candidate bytes, independently of the fourth byte read by LDR. -/
theorem tailRead_value {s : State} {k : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailRead k)) s fun t => Only [.x6,.x7] s t ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  unfold tailRead
  simp only [List.cons_append,List.nil_append]
  refine wp_addImm (by omega) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_ldrw (a := s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) (by decide)
      (by rw [ptr_zero,eb,ea,Offset.add_add])
      (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hr) fun c hc ec =>
    wp_movz fun d hd ed => wp_movk1 fun e he ee =>
    wp_and fun f hf ef => movQ_ok fun t ht et => wp_nil ?_
  refine ⟨((((((ha.trans hb).trans hc).trans hd).trans he).trans hf).trans ht).mono (by decide),?_,et⟩
  have h7 : e.gpr .x7=0x7fffff := by rw [ee,ed]; rfl
  rw [ht.get .x6,ef,h7,he.get .x6,hd.get .x6,ec,hb.mem,ha.mem]
  exact scalar_candidate _ _

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem zeroTail_frame_ok {v k : Nat} {σ s : State} (hp : Pre v σ) (h : Done v σ s)
    (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (fun t => Done v σ t ∧ Frame [aR v σ] s.mem t.mem) := by
  have hk4 : k<4 := by have := hp.streams; omega
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail
  apply WP.seq
  refine wp_ldrx (a := countP σ k) (by
    unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
    (by rw [h.env.x19]; rfl) (in_scr_rd hp h.env.wr (by
      unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)) fun a ha ea => wp_nil ?_
  have hd : Done v σ a := h.of_control ha (by decide)
  have hc : (a.gpr .x4).toNat=256-(prefixRow σ k 1008).length := by
    rw [ea]; exact h.counts k hk
  by_cases hz : a.gpr .x4=0#64
  · refine WP.ite true (by rw [eval_zero,hz]; rfl) (fun _ => ?_) (by simp)
    exact WP.block_nil ⟨hd,by rw [ha.mem]; exact Frame.refl _ _⟩
  · refine WP.ite false (by
      rw [eval_zero]
      have he : (a.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz
      rw [he]) (by simp) (fun _ => ?_)
    apply WP.seq
    have hl : (prefixRow σ k 1008).length<256 := by
      have := h.length k hk
      have hn : (a.gpr .x4).toNat≠0 := by intro e; exact hz (BitVec.eq_of_toNat_eq e)
      omega
    change WP isa (.block (tailCursor k++tailRead k++tailAdjust)) a _
    refine WP.mono (tailSetup_ok hp hd.env hk hl hc) fun b hb => ?_
    have hdb : Done v σ b := hd.of_control hb.1 (by decide)
    obtain ⟨skip,hskip,hptr,hcount,hzero⟩ := hb.2
    by_cases hz' : b.gpr .x4=0#64
    · refine WP.ite true (by rw [eval_zero,hz']; rfl) (fun _ => ?_) (by simp)
      exact WP.block_nil ⟨hdb,by rw [hb.1.mem,ha.mem]; exact Frame.refl _ _⟩
    · refine WP.ite false (by
        rw [eval_zero]
        have he : (b.gpr .x4==0)=false := by simp only [beq_eq_false_iff_ne]; exact hz'
        rw [he]) (by simp) (fun _ => ?_)
      have hn : 0<256-((prefixRow σ k 1008).length+skip) := by
        have hn' : (b.gpr .x4).toNat≠0 := by intro e; exact hz' (BitVec.eq_of_toNat_eq e)
        omega
      refine WP.mono (tailLoop_ok hn (by omega) hptr hcount ?_) fun t ht => ?_
      · intro i hi
        rw [hdb.env.wr]
        refine ⟨aR v σ,by simp [hp.wr],?_⟩
        change (aR v σ).Contains (((aP σ+BitVec.ofNat 64 (1024*k))+
          BitVec.ofNat 64 (4*((prefixRow σ k 1008).length+skip)))+BitVec.ofNat 64 (4*i)) 4
        rw [Offset.add_add,Offset.add_add]
        exact Offset.contains_base (aP σ) (by omega) (by have := hp.streams; omega)
      · refine ⟨hdb.tailKeep hp hk (by omega) (by omega) ht.1 ht.2,?_⟩
        have hf : Frame [aR v σ] b.mem t.mem := ht.2.sub (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact ⟨aR v σ,by simp,fun x hx => poly_sub hk x (tailRange_sub (by omega) x hx)⟩)
        rw [hb.1.mem,ha.mem] at hf
        exact hf


end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailBuffers.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)

abbrev TailReady (v : Nat) (σ s : State) := Done v σ s ∧
  ∀k<v,∀j<1008,s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j

theorem zeroTail_ready {v k : Nat} {σ s : State} (hp : Pre v σ)
    (h : TailReady v σ s) (hk : k<v) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.zeroTail k) s (TailReady v σ) := by
  refine WP.mono (zeroTail_frame_ok hp h.1 hk) fun t ⟨ht,hf⟩ => ⟨ht,?_⟩
  intro j hj d hd
  have hb : (scrR σ).Contains (bufP σ j+BitVec.ofNat 64 d) 1 := by
    change (scrR σ).Contains ((scr σ+BitVec.ofNat 64 (840+1008*j))+BitVec.ofNat 64 d) 1
    rw [Offset.add_add]
    exact Offset.contains_base (scr σ) (by have:=hp.streams; omega) (by have:=hp.streams; omega)
  rw [hf (bufP σ j+BitVec.ofNat 64 d) (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.a_scr.symm _ hb)]
  exact h.2 j hj d hd

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailInspect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

theorem tailInspect_ok {s : State} {k len : Nat} (hk : k<4) (hl : len≤256)
    (hc : (s.gpr .x4).toNat=256-len)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailCursor k++tailRead k)) s fun t =>
      Only [.x3,.x6,.x7] s t ∧
      t.gpr .x3=coeffAddr (s.gpr .x21+BitVec.ofNat 64 (1024*k)) len ∧
      (t.gpr .x6).toNat=candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) ∧
      (t.gpr .x7).toNat=8380417 := by
  rw [WP.block_append_iff]
  refine WP.mono (tailCursor_ok hk hl hc) fun a ⟨ha,h3⟩ => ?_
  refine WP.mono (tailRead_value hk (by rw [ha.rd,ha.wr,ha.get .x19]; exact hr))
    fun t ⟨ht,h6,h7⟩ => ?_
  refine ⟨(ha.trans ht).mono (by decide),?_,?_,h7⟩
  · rw [ht.get .x3]; exact h3
  · rw [ha.mem,ha.get .x19] at h6
    exact h6

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

structure TailChecks (k : Nat) where
  countHint : VG.Taint.Hint VG.AArch64.Taint.T
  inspectHint : VG.Taint.Hint VG.AArch64.Taint.T
  count : (taint.check (Taint.ofRegs [.x19])
    (.block [.ldr .x .x4 .x19 (counts+8*k)]) countHint).isSome=true
  inspect : (taint.check (Taint.ofRegs [.x4,.x19,.x21])
    (.block (tailCursor k++tailRead k)) inspectHint).isSome=true

private theorem countLoad_ok {s : State} {k len : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (countAddress s k) 8)
    (hc : (s.mem.readW (countAddress s k) 64).toNat=256-len) :
    WP isa (.block [.ldr .x .x4 .x19 (counts+8*k)]) s fun t =>
      Only [.x4] s t ∧ (t.gpr .x4).toNat=256-len := by
  refine wp_ldrx (a := countAddress s k) (by unfold counts; omega) (by rfl) hr
    fun t ht et => wp_nil ⟨ht,?_⟩
  rw [et]; exact hc

/-- Cleanup's sole data-dependent decision is the masked final candidate;
its ignored overread byte is deliberately absent from this relation. -/
theorem zeroTailRaw_relCT {k len : Nat} {σ τ : State}
    (hk : k<4) (hl : len≤256) (checks : TailChecks k)
    (hsp : σ.sp=τ.sp) (h19 : σ.gpr .x19=τ.gpr .x19) (h21 : σ.gpr .x21=τ.gpr .x21)
    (crs : InRegions (σ.rd++σ.wr) (countAddress σ k) 8)
    (crt : InRegions (τ.rd++τ.wr) (countAddress τ k) 8)
    (cs : (σ.mem.readW (countAddress σ k) 64).toNat=256-len)
    (ct : (τ.mem.readW (countAddress τ k) 64).toNat=256-len)
    (rs : InRegions (σ.rd++σ.wr) (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (rt : InRegions (τ.rd++τ.wr) (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4)
    (hm : candidate σ.mem (σ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate τ.mem (τ.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))) :
    RelCT isa (fun s t => s=σ ∧ t=τ) (Four.zeroTail k) (fun _ _ => True) := by
  have loadCT : RelCT isa (fun s t => s=σ ∧ t=τ)
      (.block [.ldr .x .x4 .x19 (counts+8*k)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [.x19])
      (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨hsp,by simp [Taint.ofRegs,RegSet.mem_ofList,h19]⟩)
      checks.count
  unfold Four.zeroTail
  refine RelCT.seq (loadCT.wp (fun _ _ h => by
    rcases h with ⟨rfl,rfl⟩
    exact ⟨countLoad_ok hk crs cs,countLoad_ok hk crt ct⟩)) ?_
  apply RelCT.ite
  · intro s t h
    have he : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (h.2.1.2.trans h.2.2.2.symm)
    rw [eval_zero,eval_zero,he]
  · exact RelCT.block_nil (fun _ _ _ => True.intro)
  · intro s t tr ur s' t' h es et
    have ha := h.1.2.1.1
    have hb := h.1.2.2.1
    have hc := h.1.2.1.2
    have hd := h.1.2.2.2
    have sp : s.sp=t.sp := ha.sp.trans (hsp.trans hb.sp.symm)
    have e19 : s.gpr .x19=t.gpr .x19 := by rw [ha.get .x19,hb.get .x19]; exact h19
    have e21 : s.gpr .x21=t.gpr .x21 := by rw [ha.get .x21,hb.get .x21]; exact h21
    have e4 : s.gpr .x4=t.gpr .x4 := BitVec.eq_of_toNat_eq (hc.trans hd.symm)
    have wpS := tailInspect_ok hk hl hc (by rw [ha.rd,ha.wr,ha.get .x19]; exact rs)
    have wpT := tailInspect_ok hk hl hd (by rw [hb.rd,hb.wr,hb.get .x19]; exact rt)
    have inspectCT : RelCT isa (fun a b => a=s ∧ b=t)
        (.block (tailCursor k++tailRead k)) (fun _ _ => True) :=
      RelCT.taint (A := taint) (Taint.ofRegs [.x4,.x19,.x21])
        (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨sp,by simp [Taint.ofRegs,RegSet.mem_ofList,e4,e19,e21]⟩)
        checks.inspect
    have result : RelCT isa (fun a b => a=s ∧ b=t)
        (.seq (.block (tailCursor k++tailRead k++tailAdjust))
          (.ite (.zero .x .x4) (.block [])
            (.loop (.block [.str .w .x9 .x3 0,.addImm .x .x3 .x3 4,.subImm .x .x4 .x4 1])
              (.nonzero .x .x4)))) (fun _ _ => True) := by
      apply blockPrefix
      refine RelCT.seq (inspectCT.wp (fun _ _ h => by rcases h with ⟨rfl,rfl⟩; exact ⟨wpS,wpT⟩)) ?_
      exact RelCT.taint (A := taint) (Taint.ofRegs [.x3,.x4,.x6,.x7])
        (fun a b hh => by
          obtain ⟨_,⟨ka,a3,a6,a7⟩,⟨kb,b3,b6,b7⟩⟩ := hh
          refine ⟨ka.sp.trans (sp.trans kb.sp.symm),?_⟩
          simp only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false]
          intro r hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [a3,b3,e21]
          · rw [ka.get .x4,kb.get .x4,e4]
          · apply BitVec.eq_of_toNat_eq
            rw [a6,b6,ha.mem,hb.mem,ha.get .x19,hb.get .x19]
            exact hm
          · exact BitVec.eq_of_toNat_eq (a7.trans b7.symm)) (by taint_decide)
    exact result _ _ _ _ _ _ ⟨rfl,rfl⟩ es et

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejTailReadyTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 def tailChecks (k : Nat) (hk : k<4) : TailChecks k := by
  by_cases h0 : k=0
  · subst k; constructor <;> taint_decide
  by_cases h1 : k=1
  · subst k; constructor <;> taint_decide
  by_cases h2 : k=2
  · subst k; constructor <;> taint_decide
  have h3 : k=3 := by omega
  subst k
  constructor <;> taint_decide

private theorem tail_candidate_eq {v k : Nat} {σ τ s t : State}
    (pub : Pub v σ τ) (hs : TailReady v σ s) (ht : TailReady v τ t) (hk : k<v) :
    candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate t.mem (t.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) := by
  rw [hs.1.env.x19,ht.1.env.x19]
  rw [←Offset.add_add (scr σ) (840+1008*k) 1005,
    ←Offset.add_add (scr τ) (840+1008*k) 1005]
  change candidate s.mem (bufP σ k+BitVec.ofNat 64 1005)=
    candidate t.mem (bufP τ k+BitVec.ofNat 64 1005)
  unfold candidate
  have hb (j : Nat) (hj : j<1008) :
      s.mem (bufP σ k+BitVec.ofNat 64 j)=t.mem (bufP τ k+BitVec.ofNat 64 j) := by
    rw [hs.2 k hk j hj,ht.2 k hk j hj,pub.byte hk j]
  rw [hb 1005 (by decide)]
  have h1 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+1=p+BitVec.ofNat 64 1006 := by
    intro p; exact Offset.add_add p 1005 1
  have h2 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+2=p+BitVec.ofNat 64 1007 := by
    intro p; exact Offset.add_add p 1005 2
  rw [h1,h1,h2,h2,hb 1006 (by decide),hb 1007 (by decide)]

theorem zeroTail_relCT {v k : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  have h4 : k<4 := by have:=hp.streams; omega
  have ct : RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hs := h.1.1.env
    have ht := h.2.1.env
    exact zeroTailRaw_relCT h4 (h.1.1.length k hk) (tailChecks k h4)
      (hs.sp.trans (pub.2.2.2.1.trans ht.sp.symm))
      (by rw [hs.x19,ht.x19,pub.2.2.1]) (by rw [hs.x21,ht.x21,pub.2.1])
      (by rw [segment_count_eq hs]; exact in_scr_rd hp hs.wr (by unfold counts; omega))
      (by rw [segment_count_eq ht]; exact in_scr_rd hq ht.wr (by unfold counts; omega))
      (by rw [segment_count_eq hs]; exact h.1.1.counts k hk)
      (by rw [segment_count_eq ht,pub.prefix hk 1008]; exact h.2.1.counts k hk)
      (by rw [hs.x19]; exact in_scr_rd hp hs.wr (by omega))
      (by rw [ht.x19]; exact in_scr_rd hq ht.wr (by omega))
      (tail_candidate_eq pub h.1 h.2 hk) _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  exact (ct.wp (fun _ _ h => ⟨zeroTail_ready hp h.1 hk,zeroTail_ready hq h.2 hk⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem tailRows_relCT {v : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ)
    (ks : List Nat) (hks : ∀k∈ks,k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t)
      (ks.foldr (fun k rest => .seq (Four.zeroTail k) rest) (.block []))
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  induction ks with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons k ks ih =>
    exact RelCT.seq (zeroTail_relCT hp hq pub (hks k (by simp)))
      (ih (fun j hj => hks j (by simp [hj])))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
