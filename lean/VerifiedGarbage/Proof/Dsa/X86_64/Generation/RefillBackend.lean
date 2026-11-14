module

public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth
import Mathlib.Data.Nat.Basic
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
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Call
import Mathlib.Algebra.Group.Nat.Defs
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySave
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillWidths
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha1
import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
public import VerifiedGarbage.Proof.Dsa.X86_64.ParametersCT
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! ### `Dsa.X86_64.Generation.SharedChecker`, which only this module used -/

section

/-! # The domain checker parameter generation calls

Generation's own arithmetic (the generator search and this check) is a few
public exponentiations, against the many Miller–Rabin rounds its
probable-prime calls run: it multiplies with the baseline round's inlined
Montgomery multiplication on every backend, so one checker serves them all. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.SharedChecker

def name : String := "vg_dsa_generation_check_parameters"

end VG.Proof.Dsa.X86_64.Generation.SharedChecker

end

end

/-! ### `Dsa.X86_64.Generation.BackendCorrect`, which only this module used -/

section

/-! # Functional correctness for the existing hash and primality backends -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashCode.lean`, which only this module imported.
section

/-! # Existing hash variants supply the generator's instruction and stack checks -/

public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64

theorem generationSafe_of_noSp {c : Prog isa} (hs : NoSp c)
    (hm : c.allInstrs (fun i => !loadsMxcsr i) = true) : generationSafe c := by
  have sp := VG.Proof.RsaOaep.X86_64.SpSafe.of_noSp hs
  apply generationSafe_of_allInstrs
  rw [Code.allInstrs_eq]
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
    omega_using [hd]
  update := by
    change v.H.updC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.updSp]
    have hd := v.ok.updDepth
    omega_using [hd]
  finish := by
    change v.H.finC.x86_64Depth ≤ 120
    rw [x86_64Depth_noSp v.ok.finSp]
    have hd := v.ok.finDepth
    omega_using [hd]

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerDepth.lean`, which only this module imported.
section

/-! # Search controllers inherit their bodies’ stack bounds -/

public section
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

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ControllerSafety.lean`, which only this module imported.
section

/-! # Bounded seed, prime, and generator controllers inherit their bodies' safety -/

public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem pSearch_safe {body : Prog isa} (hb : generationSafe body) (limit stride : Nat) :
    generationSafe (pSearch body limit stride) := by
  unfold generationSafe at hb ⊢
  simp only [pSearch, pSearchIteration, seqs, generationOk, hb]
  rfl

theorem tapeLoop_safe {body : Prog isa} (hb : generationSafe body) (slots : TapeSlots) (width : Nat) :
    generationSafe (tapeLoop slots width body) := by
  unfold generationSafe at hb ⊢
  simp only [tapeLoop, tapeIteration, generationOk, hb]
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


end


-- separate module: its proofs build in parallel with the constant-time ones, `RefillCT`

/-! # The refillable-tape search with the hash and Miller–Rabin backends, on x86-64

For one width, `Refill.code` (`Impl/Dsa/X86_64/Generation/Refill.lean`) uses
at most 568 octets of stack, writes `rsp` only in its frames and calls, and
never loads `mxcsr`, given the same of its hashes, multiplications and
probable-prime test (as `BackendCorrect.lean`'s `entry_depth` and
`entry_safe` for the finite search). With `RefillCorrect.lean`'s
`refill_correct` and its constant time (`RefillCTObligation`, which the
constant-time proof discharges), it is `Verified` against
`Refill.contract`; then, as `Widths.lean` does for
`vg_dsa_generate_parameters`, each width's function with the one hash it
uses (SHA-1 for width 128, SHA-256 for 256 and 384), and the search over all
three (`searchCode`), forwarded to by `ParameterSearch.widths`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.RefillBackend
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.X86_64.Generation.Refill
open VG.Proof.Dsa.X86_64.Generation VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-! ## Depth -/

theorem window_depth (pLen : Nat) : generationDepth (window pLen) := by
  exact (show 0 ≤ 128 by decide)

theorem windowShort_depth (pLen : Nat) : generationDepth (windowShort pLen) := by
  exact (show 0 ≤ 128 by decide)

theorem finish_depth (pLen : Nat) : generationDepth (finish pLen) := by
  exact (show 0 ≤ 128 by decide)

theorem refillAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul)))
    (pLen qLen : Nat) :
    callerDepth (refillAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have finish : callerDepth (finishDomain (checkName := checkName) sq mul pLen qLen) :=
    callerDepth.of ((show generationDepth (pack pLen qLen) by exact (show 0 ≤ 128 by decide)).seq
      (validate_depth (checkName := checkName) sq mul hc pLen qLen))
  exact ((callerDepth.of (generationDepth.block _)).seq (subgroup_depth h1 h256 prime hp qLen)).seq
    (onSuccess_depth ((primeSearch_depth h1 h256 prime hp pLen qLen).seq
      (onSuccess_depth ((callerDepth.of (window_depth pLen)).seq
        ((generatorSearch_depth sq mul hs hm pLen).seq
          ((callerDepth.of (generationDepth.block _)).seq
            ((callerDepth.of (windowShort_depth pLen)).seq (onSuccess_depth finish))))))))

theorem controller_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul)))
    (pLen qLen : Nat) :
    callerDepth (controller (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have ha := refillAttempt_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc pLen qLen
  have b : ∀ is : List Instr, callerDepth (.block is) := fun is => callerDepth.of (generationDepth.block is)
  exact (b _).seq (((b _).ite ((b _).seq ((b _).ite ((b _).seq (ha.seq ((b _).seq ((b _).ite (b _) _)))) _)) _).seq
    (b _))

theorem code_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (hp : callerDepth prime)
    (hc : generationDepth (.call checkName (VG.Impl.Dsa.X86_64.Generate.checkParameters sq mul)))
    (pLen qLen : Nat) :
    (Refill.code (checkName := checkName) H1 H256 sq mul prime pLen qLen).x86_64Depth ≤ 568 := by
  have body : callerDepth (Refill.body (checkName := checkName) H1 H256 sq mul prime pLen qLen) :=
    (callerDepth.of (generationDepth.block _)).seq
      ((controller_depth (checkName := checkName) h1 h256 sq mul prime hs hm hp hc pLen qLen).seq
        (callerDepth.of (finish_depth pLen)))
  unfold callerDepth at body
  simp only [Refill.code, Code.x86_64Depth, Instr.frameBytes, Nat.zero_max, Nat.max_zero, frameBytes]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right body 296) 32) 48

/-! ## Instructions -/

theorem safe_frame {body : Prog isa} (h : generationSafe body) (bytes : Nat) :
    generationSafe (.frame (.alloc bytes) body (.free bytes)) := by
  change ((true && _) && true) = true
  rw [h]; rfl

theorem refillAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime)
    (pLen qLen : Nat) :
    generationSafe (refillAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have finish : generationSafe (finishDomain (checkName := checkName) sq mul pLen qLen) :=
    (show generationSafe (pack pLen qLen) from rfl).seq (validate_safe (checkName := checkName) sq mul hs hm pLen qLen)
  exact ((show generationSafe (.block (seedArguments qLen)) from rfl).seq
    (subgroup_safe h1 h256 prime hp qLen)).seq
    (onSuccess_safe ((primeSearch_safe h1 h256 prime hp pLen qLen).seq
      (onSuccess_safe ((show generationSafe (window pLen) from rfl).seq
        ((generatorSearch_safe sq mul hs hm pLen).seq
          ((show generationSafe (.block windowConsumed) from rfl).seq
            ((show generationSafe (windowShort pLen) from rfl).seq (onSuccess_safe finish))))))))

theorem code_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (prime : Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (hp : generationSafe prime)
    (pLen qLen : Nat) :
    generationSafe (Refill.code (checkName := checkName) H1 H256 sq mul prime pLen qLen) := by
  have ha := refillAttempt_safe (checkName := checkName) h1 h256 sq mul prime hs hm hp pLen qLen
  have it : generationSafe (iteration (refillAttempt (checkName := checkName) H1 H256 sq mul prime pLen qLen) qLen) :=
    (show generationSafe (.block [.mov .rax (.mem (sp 128)), .store (ctl 3) .rax, .mov .rcx (.mem (ctl 2)),
        .alu .test .rcx (.reg .rcx)]) from rfl).seq
      (((show generationSafe (.block (stackStatus 2)) from rfl).ite
        ((show generationSafe (.block [.mov .rcx (.mem (sp 120)), .alu .sub .rcx (.reg .rax),
            .alu .cmp .rcx (.imm (BitVec.ofNat 32 qLen))]) from rfl).seq
          ((show generationSafe (.block (stackStatus 0)) from rfl).ite
            ((show generationSafe (.block (seedStart qLen)) from rfl).seq (ha.seq
              ((show generationSafe (.block tapeStatus) from rfl).seq
                ((show generationSafe (.block rejected) from rfl).ite
                  (show generationSafe (.block []) from rfl) _)))) _)) _).seq
        (show generationSafe (.block tapeStatus) from rfl))
  have body : generationSafe (Refill.body (checkName := checkName) H1 H256 sq mul prime pLen qLen) :=
    (show generationSafe (.block (entryHeader pLen qLen ++ entryDerived)) from rfl).seq
      ((it.loop _).seq (show generationSafe (finish pLen) from rfl))
  exact safe_frame ((show generationSafe (.block saveRegisters) from rfl).seq
    ((safe_frame (safe_frame body frameBytes) 32).seq (show generationSafe (.block restoreRegisters) from rfl))) 48

/-! ## With the hash and Miller–Rabin backends -/

/-- The multiplications generation's own arithmetic uses (`SharedChecker.arith`). -/
abbrev arith : RoundImpl := VG.Proof.Variants.MillerRabin.X86_64.Base.variant

/-- `Refill.code` for width `pBytes`, with the hashes `G1` and `G256` and
Miller–Rabin `v`. -/
abbrev backendCode (G1 G256 : Stream) (v : RoundImpl) (pBytes : Nat) : Prog isa :=
  Refill.code (checkName := checkName) G1 G256 arith.inlineMont.toS.mm arith.inlineMont.mm
    (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run pBytes (Spec.Dsa.generationQLen pBytes)

theorem backend_safe (v1 v256 : MdHash) (v : RoundImpl) (pBytes : Nat) :
    generationSafe (backendCode (checkName := checkName) v1.H.stream v256.H.stream v pBytes) :=
  code_safe (checkName := checkName) (hashCode_safe v1) (hashCode_safe v256) _ _ _
    (generationSafe_of_allInstrs (arith.inlineSafe _ _ _))
    (fun o a b => generationSafe_of_allInstrs (arith.inlineSafe o a b)) ((ProbablePrime.testCode_safe v).call _) _ _

theorem backend_depth (v1 v256 : MdHash) (v : RoundImpl) (pBytes : Nat) :
    (backendCode (checkName := checkName) v1.H.stream v256.H.stream v pBytes).x86_64Depth ≤ 568 :=
  code_depth (checkName := checkName) (hashCode_depth v1) (hashCode_depth v256) _ _ _
    (inlineMul_depth arith _ _ _) (inlineMul_depth arith) (by
      have := (ProbablePrime.primeTest v).depth
      have : ProbablePrime.stack = 184 := rfl
      change (ProbablePrime.primeTest v).code.x86_64Depth + 8 ≤ 192
      omega_arith) (by
      have h := checkParameters_depth_bound arith.inlineMont.toS.mm arith.inlineMont.mm
        (n := 0) (by rw [VG.Proof.Bignum.X86_64.Mont.toS, arith.inlineDepth])
        (fun o a b => by rw [arith.inlineDepth])
      change (VG.Impl.Dsa.X86_64.Generate.checkParameters arith.inlineMont.toS.mm arith.inlineMont.mm).x86_64Depth + 8 ≤ 128
      omega_using [h]) _ _

/-! ## Verified -/

/-- The constant time of `Refill.code` for every backend, which the
constant-time proof (`RefillCT*.lean`) proves. -/
def RefillCTObligation : Prop :=
  ∀ (checkName : String) (H : GenerationHashes) (M : VG.Proof.Bignum.X86_64.Mont)
    (Sq : VG.Proof.Bignum.X86_64.MontS) (T : PrimeTest) (pBytes : Nat),
    (pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) →
    ConstantTime isa (Refill.contract pBytes abi 568).pre (Refill.contract pBytes abi 568).pub
      (Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes
        (Spec.Dsa.generationQLen pBytes))

theorem refill_verified (ct : RefillCTObligation) (H : GenerationHashes) (M : VG.Proof.Bignum.X86_64.Mont)
    (Sq : VG.Proof.Bignum.X86_64.MontS) (T : PrimeTest) (pBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384)
    (safe : generationSafe (Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes
      (Spec.Dsa.generationQLen pBytes)))
    (depth : (Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes
      (Spec.Dsa.generationQLen pBytes)).x86_64Depth ≤ 568) :
    Verified target (Refill.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) (Refill.contract pBytes abi 568) :=
  ⟨Refill.refill_correct (checkName := checkName) H M Sq T
      (by
        intro _ _ _ hm hin seed hlen hseed h1 _ h16 hu
        exact refillAttempt_ok H M Sq T hm hin seed hlen hseed h1 h16 hu)
      pBytes _ rfl safe.sp depth safe.mx,
    ct checkName H M Sq T pBytes hp,
    RefillWidths.refill_sat (S := 504) hp (by decide)⟩

theorem backend_verified (ct : RefillCTObligation) (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") (pBytes : Nat)
    (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) :
    Verified target (backendCode (checkName := checkName) v1.H.stream v256.H.stream v pBytes)
      (Refill.contract pBytes abi 568) :=
  refill_verified (checkName := checkName) ct (generationHashes v1 v256 h1 h256) arith.inlineMont
    arith.inlineMont.toS (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v) pBytes hp
    (backend_safe v1 v256 v pBytes) (backend_depth v1 v256 v pBytes)

/-! ## One hash for each width -/

/-- Only a proof witness: `sha1_verified` and `sha256_verified` show it does
not occur in the code. -/
private def sha1Witness : MdHash := VG.Proof.Pbkdf2.Md.X86_64.Sha1.variant .scalar
private def sha256Witness : MdHash := VG.Proof.Variants.MdHash.X86_64.Sha256.variant

theorem sha1_verified (ct : RefillCTObligation) (h : MdHash) (v : RoundImpl) (hh : h.mgf.G.rust = "sha1") :
    Verified target (backendCode (checkName := checkName) h.H.stream h.H.stream v 128)
      (Refill.contract 128 abi 568) :=
  backend_verified (checkName := checkName) ct h sha256Witness v hh rfl 128 (.inl rfl)

theorem sha256_verified (ct : RefillCTObligation) (h : MdHash) (v : RoundImpl) (hh : h.mgf.G.rust = "sha256")
    (pBytes : Nat) (hp : pBytes = 256 ∨ pBytes = 384) :
    Verified target (backendCode (checkName := checkName) h.H.stream h.H.stream v pBytes)
      (Refill.contract pBytes abi 568) := by
  rcases hp with rfl | rfl
  · exact backend_verified (checkName := checkName) ct sha1Witness h v rfl hh 256 (.inr (.inl rfl))
  · exact backend_verified (checkName := checkName) ct sha1Witness h v rfl hh 384 (.inr (.inr rfl))

theorem single_safe (h : MdHash) (v : RoundImpl) (pBytes : Nat) :
    (backendCode (checkName := checkName) h.H.stream h.H.stream v pBytes).all (fun i => !isa.writesSp i) = true :=
  (backend_safe h h v pBytes).sp

theorem single_depth (h : MdHash) (v : RoundImpl) (pBytes : Nat) :
    (backendCode (checkName := checkName) h.H.stream h.H.stream v pBytes).x86_64Depth ≤ 568 :=
  backend_depth h h v pBytes

/-! ## The instances the registration binds -/

/-- The function for width `p`, with the hash `h` and Miller–Rabin `v`. -/
def body (h : MdHash) (v : RoundImpl) (p : Nat) : Prog isa :=
  backendCode (checkName := SharedChecker.name) h.H.stream h.H.stream v p

/-- The name the function for width `p` is emitted as, its hash tagged `tag`. -/
def name (tag : String) (h : MdHash) (v : RoundImpl) (p : Nat) : String :=
  s!"vg_dsa_parameter_search_{8 * p}" ++ qualifiedName "" [(tag, h.suffix), ("mr", v.suffix)]

/-- `vg_dsa_parameter_search` with the hashes `v1` (width 128) and `v256`
(256 and 384) and Miller–Rabin `v`. -/
def searchCode (v1 v256 : MdHash) (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.ParameterSearch.widths (name "sha1" v1 v 128) (name "sha256" v256 v 256)
    (name "sha256" v256 v 384) (body v1 v 128) (body v256 v 256) (body v256 v 384)

theorem searchCode_verified (ct : RefillCTObligation) (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (searchCode v1 v256 v) (Spec.Dsa.parameterSearchContract abi 632) :=
  RefillWidths.refillWidths_verified 568 (by decide)
    (sha1_verified ct v1 v h1) (sha256_verified ct v256 v h256 256 (.inl rfl))
    (sha256_verified ct v256 v h256 384 (.inr rfl))
    (single_safe v1 v 128) (single_safe v256 v 256) (single_safe v256 v 384)
    (single_depth v1 v 128) (single_depth v256 v 256) (single_depth v256 v 384)

theorem searchCode_spSafe (v1 v256 : MdHash) (v : RoundImpl) :
    (searchCode v1 v256 v).all (fun i => !isa.writesSp i) = true :=
  RefillWidths.refillWidths_spSafe (single_safe v1 v 128) (single_safe v256 v 256) (single_safe v256 v 384)

end VG.Proof.Dsa.X86_64.Generation.RefillBackend
