module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Body
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generator.CT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Depth
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchCTState
public meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Public
public meta import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-! ### `Dsa.AArch64.Generator.Correct`, which only this module used -/

section

/-! # The generator stage meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

variable {pLen : Nat}

/-- No byte of `ws` but those of the stage's scratch ranges is in a region the stage changes. -/
theorem keeps_of_frame (hb : Supported pLen) {s : State} (A : StageABI pLen s) {m : Mem}
    (hf : Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (Impl.Dsa.AArch64.Generator.layout pLen).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have qn := hb.q_le
  have pn : pLen ≤ 384 := by rcases hb with rfl | rfl | rfl <;> decide
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  have part : ∀ {e k : Nat}, (e, k) ∈ (Impl.Dsa.AArch64.Generator.layout pLen).scratch →
      e + k ≤ 2 ^ 64 → ¬ (⟨off (s.gpr .x0) e, k⟩ : Region).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 := by
    intro e k he hek hx
    have h := hout (e, k) he
    have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := e) (k := k) (by simp only at h; omega_using [h]) (by omega_using [hi, hw]) hek
    exact hd _ (Region.contains_self _ _) hx
  apply hf
  intro r hr hx
  simp only [stageChanged, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact part (e := 0) (k := Impl.Dsa.Layout.activeBytes) (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, parent])
      (by decide) (by simpa [off] using hx)
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold g; omega_using [pn]) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by unfold packed; omega_using [qn, pn]) hx
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx
  · exact (A.stackWs.sub_left (frame_sub0 s (by unfold frameBytes; omega_using []))) _ hx hc
  · exact (A.stackWs.sub_left (frame_sub0 s (Nat.le_refl _))) _ hx hc
  · exact part (by simp [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch]) (by decide) hx

theorem correct (M : Mont) (hb : Supported pLen) (s : State) (pre : (contract pLen).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.AArch64.Generator.code M.mm pLen) s trace t ∧ abiPreserved s t ∧
      (contract pLen).post s t := by
  have A := stageABI_of pre
  obtain ⟨trace, t, he, hpre, hst, hpk, hf⟩ := alloc_frame_ok (bytes := 272) (by decide)
    (by have := A.stackLower; unfold stack at this; omega_using [this])
    (Q := fun t => abiPreserved s t ∧
      t.gpr .x0 = BitVec.ofNat 64 (endCode pLen s + 4 * (pLen * readCount pLen s)) ∧
      (∀ a, result pLen s = some a →
        Spec.Rsa.bytesAt t.mem (off (s.gpr .x0) packed) (2 * pLen + qLen pLen) = Spec.Dsa.encodeParams pLen (qLen pLen) a) ∧
      Frame (stageChanged pLen s ++ [⟨frameBase s, 272⟩, spillRegion s]) s.mem t.mem)
    (WP.mono (body_ok M hb A) fun t P => ⟨P.sp, P.wr, ⟨P.regs, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [P.sp]; exact BitVec.sub_add_cancel .., P.vectors⟩, P.status, P.packed, P.frame⟩)
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  exact ⟨hst, keeps_of_frame hb A hf, fun a ha => hpk a ha⟩

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Satisfiable`, which only this module used -/

section

/-! # A state meets the generator stage's precondition

p = 2^(8 * pLen) − 1 (all ones), q = 1 and the exponent p − 1 at their
offsets of a working space of the generation's size, and an empty h tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Dsa.Generation.Layout

def satBase : Addr := 0x100000

/-- The byte at offset `o` of the working space. -/
def satByte (pLen o : Nat) : Byte :=
  if p ≤ o ∧ o < p + pLen then 0xFF
  else if exponent ≤ o ∧ o < exponent + pLen then (if o + 1 = exponent + pLen then 0xFE else 0xFF)
  else if o + 1 = q + Impl.Dsa.AArch64.Generator.qLen pLen then 1 else 0

def satMemory (pLen : Nat) : Mem := fun a => satByte pLen (a - satBase).toNat

def satState (pLen : Nat) : State where
  gpr r := match r with
    | .x0 => satBase | .x1 => BitVec.ofNat 64 (usedBytes pLen / 8) | .x2 => 0x200000 | .x3 => 0
    | _ => 0
  sp := 0x400000
  mem := satMemory pLen
  rd := [⟨0x200000, 0⟩]
  wr := [⟨satBase, usedBytes pLen / 8 * 8⟩]

theorem sat_p {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase = 2 ^ (8 * pLen) - 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_odd {pLen : Nat} (hb : Supported pLen) : pOf pLen (satMemory pLen) satBase % 2 = 1 := by
  rw [sat_p hb]
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_bits {pLen : Nat} (hb : Supported pLen) :
    Spec.Dsa.bitLength (pOf pLen (satMemory pLen) satBase) = 8 * pLen := by
  rw [sat_p hb]
  have low : 1 ≤ 8 * pLen := by rcases hb with rfl | rfl | rfl <;> decide
  have half : 2 ^ (8 * pLen) = 2 ^ (8 * pLen - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  have pos := Nat.two_pow_pos (8 * pLen - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [low])).mpr ⟨by omega_using [half], by omega_using [half, pos]⟩

theorem sat_q {pLen : Nat} (hb : Supported pLen) : qOf pLen (satMemory pLen) satBase = 1 := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem sat_exponent {pLen : Nat} (hb : Supported pLen) :
    Spec.Rsa.bytesAt (satMemory pLen) (satBase + BitVec.ofNat 64 exponent) pLen =
      Spec.Dsa.encodeBE pLen ((pOf pLen (satMemory pLen) satBase - 1) / qOf pLen (satMemory pLen) satBase) := by
  rcases hb with rfl | rfl | rfl <;> decide +kernel

theorem satisfiable {pLen : Nat} (hb : Supported pLen) : ∃ s, (contract pLen).pre s := by
  refine ⟨satState pLen, ?_⟩
  sig_pre [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_bits hb
    | exact sat_exponent hb
    | (rw [sat_q hb]; decide)
    | (rcases hb with rfl | rfl | rfl <;> decide +kernel)
    | (rcases hb with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide +kernel))

end VG.Proof.Dsa.AArch64.Generator

end

end

/-! ### `Dsa.AArch64.Generator.Depth`, which only this module used -/

section

/-! # The generator stage's frames: its own 272 bytes

The stage itself has no frames (its arithmetic has none), so its stack is
its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem stage_noFrames (v : RoundImpl) (pLen : Nat) :
    (Impl.Dsa.AArch64.Generator.stage v.mont.mm pLen).noFrames = true := by
  simp only [Impl.Dsa.AArch64.Generator.stage, generatorSearch, tapeLoop, tapeIteration, generatorStep, generatorRangeFromFrame, generatorEvaluate, onSuccess, finishDomain, pack, packPart, validate, Code.noFrames, Impl.Bignum.AArch64.seqs, workspace, generatorRange, generatorResult, generatorPowerFresh, generatorModulus, generatorPower, generatorLoadPair, Impl.Dsa.AArch64.Random.copyRest, Impl.Dsa.AArch64.Generate.checkParameters, Impl.Dsa.AArch64.Core.publicPow, Impl.Dsa.AArch64.Checks.signingKey, Impl.Dsa.AArch64.Checks.publicPrefix, Impl.Dsa.AArch64.PublicPower.power, Impl.Dsa.AArch64.Core.reduce, Impl.Dsa.AArch64.Arithmetic.constants, Impl.Dsa.AArch64.PublicPower.powerCore, Impl.Dsa.AArch64.Arithmetic.load, Impl.Dsa.AArch64.Core.finish, Impl.Rsa.AArch64.r2Steps, Impl.Dsa.AArch64.Arithmetic.encodePower, Impl.Dsa.AArch64.PublicPower.encodedPower, Impl.Dsa.AArch64.Arithmetic.reduce, Impl.Bignum.AArch64.R2Div.choice, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs, Impl.Dsa.AArch64.PublicPower.expLoop, Impl.Dsa.AArch64.Arithmetic.reduceSetup, Impl.Dsa.AArch64.Arithmetic.reduceByte, Impl.Rsa.AArch64.Crt.tabBuild, Impl.Rsa.AArch64.Crt.toEnt, Impl.Rsa.AArch64.Crt.copyArr, Impl.Rsa.AArch64.Crt.nextEnt, Impl.Dsa.AArch64.PublicPower.window, Impl.Dsa.AArch64.PublicPower.applyWindow, Impl.Dsa.AArch64.Arithmetic.reduceStep, List.append_assoc, v.mmNoFrames, Bool.and_eq_true, List.cons_append, List.nil_append]
  and_intros
  all_goals decide +kernel

/-- The stage's frames: its own 272 bytes. -/
theorem code_depth (v : RoundImpl) (pLen : Nat) :
    16 * (Impl.Dsa.AArch64.Generator.code v.mont.mm pLen).aarch64Depth ≤ 272 := by
  have h := ProbablePrime.aarch64Depth_of_noFrames _ (stage_noFrames v pLen)
  simp only [Impl.Dsa.AArch64.Generator.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

end VG.Proof.Dsa.AArch64.Generator

end

end


/-! # `vg_dsa_generator_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation, whose Montgomery multiplication
the stage's arithmetic inlines. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The stage's code with the round implementation `v`'s arithmetic. -/
abbrev stageCode (v : RoundImpl) (pLen : Nat) : Prog isa :=
  Impl.Dsa.AArch64.Generator.code v.mont.mm pLen

theorem verified (v : RoundImpl) {pLen : Nat} (hb : Supported pLen) :
    Verified target (stageCode v pLen) (contract pLen) :=
  ⟨correct v.mont hb, code_ct v.mont hb, satisfiable hb⟩

/-- The stages with the round implementation `v`, as parameter generation
calls them. -/
def generatorStage (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.GeneratorStage where
  name pLen := s!"vg_dsa_generator_{8 * (Impl.Dsa.AArch64.Generator.layout pLen).pLen}" ++ v.suffix
  code := stageCode v
  verified _ hb := verified v hb
  depth := code_depth v

end VG.Proof.Dsa.AArch64.Generator
