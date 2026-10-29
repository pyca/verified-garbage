module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerDepth
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
import VerifiedGarbage.Proof.Framework.Offset
/-! # Functional correctness for the existing hash and primality backends -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashCode.lean`, which only this module imported.
section

/-! # Existing hash variants supply the generator's instruction and stack checks -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64

theorem generationSafe_of_noSp {c : Prog isa} (hs : NoSp c)
    (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) : generationSafe c := by
  have sp := VG.Proof.RsaOaep.X86_64.SpSafe.of_noSp hs
  rw [generationSafe, Code.allInstrs_eq]
  rw [Code.allInstrs_eq] at hm
  apply List.all_eq_true.mpr
  intro i hi
  rw [sp i hi, Bool.not_false, Bool.and_true]
  exact List.all_eq_true.mp hm i hi

theorem hashCode_safe (v : MdHash) : HashSafety v.H.stream :=
  ⟨generationSafe_of_noSp v.ok.initSp v.K.iMx,
    generationSafe_of_noSp v.ok.updSp v.ok.updMx,
    generationSafe_of_noSp v.ok.finSp v.ok.finMx⟩

theorem hashCode_depth (v : MdHash) : HashDepth v.H.stream where
  init := by
    change v.H.initC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.initSp]
    have hd := v.ok.initDepth
    omega
  update := by
    change v.H.updC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.updSp]
    have hd := v.ok.updDepth
    omega
  finish := by
    change v.H.finC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.finSp]
    have hd := v.ok.finDepth
    omega

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerDepth.lean`, which only this module imported.
section

/-! # Search controllers inherit their bodies’ stack bounds -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_depth {body : Prog isa} (hb : callerDepth body) (limit stride : Nat) :
    callerDepth (pSearch body limit stride) := by
  unfold callerDepth at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem tapeLoop_depth {body : Prog isa} (hb : callerDepth body) (slots : TapeSlots) (width : Nat) :
    callerDepth (tapeLoop slots width body) := by
  unfold callerDepth at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.x86_64Depth]
  simp only [Nat.max_le]
  and_intros
  all_goals first | exact hb | exact (show 0 ≤ 192 by decide)

theorem primeSearch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (pLen qLen : Nat) :
    callerDepth (primeSearch H1 H256 prime pLen qLen) :=
  (callerDepth.of (generationDepth.block _)).seq
    (pSearch_depth (pAttempt_depth h1 h256 prime hp pLen qLen) _ _)

theorem generatorSearch_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    callerDepth (generatorSearch sq mul len) :=
  tapeLoop_depth (callerDepth.of (generatorStep_depth sq mul hs hm len)) _ _

theorem onSuccess_depth {body : Prog isa} (hb : callerDepth body) :
    callerDepth (onSuccess body) :=
  (callerDepth.of (generationDepth.block _)).seq (hb.ite (callerDepth.of (generationDepth.block _)) _)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryDepth.lean`, which only this module imported.
section

/-! # Stack bound for the complete parameter-generation entry point -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)


variable {checkName : String}

theorem seedAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul)))
    (pLen qLen : Nat) : callerDepth (seedAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have finish : callerDepth (finishDomain (checkName := checkName) sq mul pLen qLen) :=
    callerDepth.of ((show generationDepth (pack pLen qLen) by exact (show 0 ≤ 128 by decide)).seq
      (validate_depth (checkName := checkName) sq mul hc pLen qLen))
  exact ((callerDepth.of (generationDepth.block _)).seq
    (subgroup_depth h1 h256 prime hp qLen)).seq
    (onSuccess_depth ((primeSearch_depth h1 h256 prime hp pLen qLen).seq
      (onSuccess_depth ((generatorSearch_depth sq mul hs hm pLen).seq (onSuccess_depth finish)))))

theorem generate_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul)))
    (pLen qLen : Nat) : callerDepth (generate (checkName := checkName) H1 H256 sq mul prime pLen qLen) :=
  (tapeLoop_depth (seedAttempt_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc pLen qLen) _ _).seq
    (callerDepth.of (show generationDepth finishOutput by exact (show 0 ≤ 128 by decide)))

theorem dispatch_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul))) :
    callerDepth (dispatch (checkName := checkName) H1 H256 sq mul prime) := by
  have h128 := generate_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc 128 20
  have h256' := generate_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc 256 32
  have h384 := generate_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc 384 32
  exact (callerDepth.of (generationDepth.block _)).seq
    (h128.ite ((callerDepth.of (generationDepth.block _)).seq (h256'.ite h384 .e)) .e)

theorem entry_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul))) :
    (code (checkName := checkName) H1 H256 sq mul prime).x86_64Depth ≤ 536 := by
  have body := dispatch_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc
  unfold callerDepth at body
  simp only [code, entryBody, Code.x86_64Depth, Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (Nat.add_le_add_right body 296) 48

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerSafety.lean`, which only this module imported.
section

/-! # Bounded seed, prime, and generator controllers inherit their bodies' safety -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_safe {body : Prog isa} (hb : generationSafe body) (limit stride : Nat) :
    generationSafe (pSearch body limit stride) := by
  unfold generationSafe at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, Code.allInstrs, hb]
  rfl

theorem tapeLoop_safe {body : Prog isa} (hb : generationSafe body) (slots : TapeSlots) (width : Nat) :
    generationSafe (tapeLoop slots width body) := by
  unfold generationSafe at hb ⊢
  simp only [tapeLoop, tapeIteration, Code.allInstrs, hb]
  rfl

theorem primeSearch_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (pLen qLen : Nat) :
    generationSafe (primeSearch H1 H256 prime pLen qLen) :=
  (show generationSafe (.block controlBase) from rfl).seq
    (pSearch_safe (pAttempt_safe h1 h256 prime hp pLen qLen) _ _)

theorem generatorSearch_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorSearch sq mul len) :=
  tapeLoop_safe (generatorStep_safe sq mul hs hm len) _ _

theorem onSuccess_safe {body : Prog isa} (hb : generationSafe body) :
    generationSafe (onSuccess body) :=
  (show generationSafe (.block successStatus) from rfl).seq (hb.ite (show generationSafe (.block []) from rfl) _)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntrySafety.lean`, which only this module imported.
section

/-! # Instruction safety of the complete parameter-generation entry point -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)


variable {checkName : String}

theorem seedAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime)
    (pLen qLen : Nat) : generationSafe (seedAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have finish : generationSafe (finishDomain (checkName := checkName) sq mul pLen qLen) :=
    (show generationSafe (pack pLen qLen) from rfl).seq (validate_safe (checkName := checkName) sq mul hs hm pLen qLen)
  exact ((show generationSafe (.block (seedArguments qLen)) from rfl).seq
    (subgroup_safe h1 h256 prime hp qLen)).seq
    (onSuccess_safe ((primeSearch_safe h1 h256 prime hp pLen qLen).seq
      (onSuccess_safe ((generatorSearch_safe sq mul hs hm pLen).seq (onSuccess_safe finish)))))

theorem generate_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime)
    (pLen qLen : Nat) : generationSafe (generate (checkName := checkName) H1 H256 sq mul prime pLen qLen) :=
  (tapeLoop_safe (seedAttempt_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp pLen qLen) _ _).seq
    (show generationSafe finishOutput from rfl)

theorem dispatch_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime) :
    generationSafe (dispatch (checkName := checkName) H1 H256 sq mul prime) := by
  have h128 := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 128 20
  have h256' := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 256 32
  have h384 := generate_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp 384 32
  exact (show generationSafe (.block [.mov .rax (.mem (Impl.Mgf1.X86_64.sp 136)),
    .alu .cmp .rax (.imm 128)]) from rfl).seq
    (h128.ite ((show generationSafe (.block [.alu .cmp .rax (.imm 256)]) from rfl).seq
      (h256'.ite h384 .e)) .e)

theorem generationSafe.frame {body : Prog isa} (h : generationSafe body) (bytes : Nat) :
    generationSafe (.frame (.alloc bytes) body (.free bytes)) := by
  change ((true && _) && true) = true
  rw [h]; rfl

theorem entry_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime) :
    generationSafe (code (checkName := checkName) H1 H256 sq mul prime) := by
  have body := (show generationSafe (.block (entryHeader ++ entryIncoming ++ entryDerived)) from rfl).seq
    (dispatch_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp)
  exact ((show generationSafe (.block saveRegisters) from rfl).seq
    ((body.frame 296).seq (show generationSafe (.block restoreRegisters) from rfl))).frame 48

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryPost.lean`, which only this module imported.
section

/-! # The entry result meets the shared parameter-generation postcondition -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem entry_shared_post {s t : State} (h : EntryResult s t) :
    (Spec.Dsa.generateParametersContract abi 536).post s t := by
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_post [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  refine ⟨?_, h.bytes⟩
  rw [h.status]
  change (BitVec.setWidth 32 (BitVec.ofNat 64 (Spec.Dsa.signStatus (abiResult s)))).toNat = Spec.Dsa.signStatus (abiResult s)
  cases abiResult s <;> rfl

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryRun.lean`, which only this module imported.
section

/-! # Complete native execution restores both frames and all saved registers -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem entryInner_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) (hr : u.rd = s.rd)
    (hw : u.wr = (allocState 48 s).wr)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem)
    (saved : Saved u.mem (savedBase s) s.gpr spillSlots) :
    WP isa (.frame (.alloc 296)
      (Impl.Dsa.X86_64.Generation.entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (.free 296)) u fun t =>
      EntryResult s t ∧ Saved t.mem (savedBase s) s.gpr spillSlots ∧
      t.gpr .rsp = u.gpr .rsp ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  apply alloc_frame_ok (by decide) (outer_stack_room h hg)
  apply WP.mono (entryBody_abi (checkName := checkName) H M Sq T h hg hr hw hf saved)
  intro t ⟨result, saved, sp, rd, wr⟩
  exact ⟨sp, wr, result.free 296, saved, freeState_rsp sp, rd, freeState_wr wr⟩

theorem entryRun_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s : State} (h : GenerationABI s) :
    WP isa (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) s fun t =>
      EntryResult s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.code
  apply alloc_frame_ok (by decide) (by have hl := h.stackLower; omega)
  refine WP.seq (WP.mono (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) ?_)
  intro u ⟨hg, hr, hw, saved, hf⟩
  have saved' : Saved u.mem (savedBase s) s.gpr spillSlots := by
    intro p hp
    have hh := saved p hp
    change u.mem.readW (Spill.slot (savedBase s) p.2) 64 = (allocState 48 s).gpr p.1 at hh
    change u.mem.readW _ 64 = _
    rw [hh]
    have hn : p.1 ≠ .rsp := by
      simp only [spillSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [allocState, State.setReg, hn]
  refine WP.seq (WP.mono (entryInner_ok (checkName := checkName) H M Sq T h hg hr hw hf saved') ?_)
  intro v ⟨result, sv, spv, rdv, wrv⟩
  have vsp : v.gpr .rsp = savedBase s := by rw [spv, hg]; rfl
  have vwr : (⟨v.gpr .rsp, 48⟩ : Region) ∈ v.wr := by
    rw [vsp, wrv, hw]
    exact List.mem_cons_self ..
  apply WP.mono (entryRestore_ok s.gpr vwr (by rw [vsp]; exact sv))
  intro t ⟨restore, rax, sp, mem, rd, wr⟩
  have tsp : t.gpr .rsp = (allocState 48 s).gpr .rsp := by rw [sp, spv, hg]
  have twr : t.wr = (allocState 48 s).wr := wr.trans (wrv.trans hw)
  refine ⟨tsp, twr, (result.congr rax mem).free 48, ?_, rd.trans (rdv.trans hr), freeState_wr twr⟩
  intro r hr
  by_cases hs : r = .rsp
  · subst r; exact freeState_rsp tsp
  · have hin : r ∈ spillSlots.map Prod.fst := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact False.elim (hs rfl) | decide
    have he := restore r hin
    simpa only [freeState, State.setReg, hs, ↓reduceIte] using he

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/Correct.lean`, which only this module imported.
section

/-! # Native parameter generation satisfies the shared functional contract -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem generation_correct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (sp : (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run).all
      (fun i => !isa.writesSp i) = true)
    (depth : (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run).x86_64Depth ≤ 536)
    (ctl : ctlOk (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) = true)
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 536).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 536).post s t := by
  have h := generationABI_of pre
  obtain ⟨trace, t, he, result, callee, _, _⟩ := entryRun_ok (checkName := checkName) H M Sq T h
  refine ⟨trace, t, he, ⟨callee, ?_, VG.X86_64.Exec.ctl ctl he⟩, entry_shared_post result⟩
  have hf := Exec.stackFrame (SpSafe.of_all sp) he (by omega)
  have hfb := VG.X86_64.Frame.below_mono hf depth (by decide)
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.retOut
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem backend_safe (v1 v256 : MdHash) (v : RoundImpl) :
    generationSafe (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) :=
  entry_safe (checkName := checkName) (hashCode_safe v1) (hashCode_safe v256) _ _ _
    (VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineSafe _ _ _) VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineSafe ((ProbablePrime.testCode_safe v).call _)

theorem backend_depth (v1 v256 : MdHash) (v : RoundImpl) :
    (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run).x86_64Depth ≤ 536 :=
  entry_depth (checkName := checkName) (hashCode_depth v1) (hashCode_depth v256) _ _ _
    (inlineMul_depth VG.Proof.Variants.MillerRabin.X86_64.Base.variant _ _ _) (inlineMul_depth VG.Proof.Variants.MillerRabin.X86_64.Base.variant) (by
      have := (ProbablePrime.primeTest v).depth
      have : ProbablePrime.stack = 184 := rfl
      change (ProbablePrime.primeTest v).code.x86_64Depth + 8 ≤ 192
      omega) (by
      have h := checkParameters_depth_bound VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm
        (n := 0) (by rw [VG.Proof.Bignum.X86_64.Mont.toS, VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineDepth])
        (fun o a b => by rw [VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineDepth])
      change (VG.Impl.Dsa.X86_64.Generate.checkParameters _ _).x86_64Depth + 8 ≤ 128
      omega)

theorem backend_correct (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256")
    (s : State) (pre : (Spec.Dsa.generateParametersContract abi 536).pre s) :
    ∃ trace t, Exec isa (Impl.Dsa.X86_64.Generation.code (checkName := checkName) v1.H.stream v256.H.stream
      VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateParametersContract abi 536).post s t :=
  generation_correct (checkName := checkName) (generationHashes v1 v256 h1 h256) VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v)
    (backend_safe (checkName := checkName) v1 v256 v).sp (backend_depth (checkName := checkName) v1 v256 v) (backend_safe (checkName := checkName) v1 v256 v).mx s pre

end VG.Proof.Dsa.X86_64.Generation
