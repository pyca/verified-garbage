module

public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SharedChecker
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerDepth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PowerSafety
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashVariants
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
    (arith.inlineSafe _ _ _) arith.inlineSafe ((ProbablePrime.testCode_safe v).call _) _ _

theorem backend_depth (v1 v256 : MdHash) (v : RoundImpl) (pBytes : Nat) :
    (backendCode (checkName := checkName) v1.H.stream v256.H.stream v pBytes).x86_64Depth ≤ 568 :=
  code_depth (checkName := checkName) (hashCode_depth v1) (hashCode_depth v256) _ _ _
    (inlineMul_depth arith _ _ _) (inlineMul_depth arith) (by
      have := (ProbablePrime.primeTest v).depth
      have : ProbablePrime.stack = 184 := rfl
      change (ProbablePrime.primeTest v).code.x86_64Depth + 8 ≤ 192
      omega) (by
      have h := checkParameters_depth_bound arith.inlineMont.toS.mm arith.inlineMont.mm
        (n := 0) (by rw [VG.Proof.Bignum.X86_64.Mont.toS, arith.inlineDepth])
        (fun o a b => by rw [arith.inlineDepth])
      change (VG.Impl.Dsa.X86_64.Generate.checkParameters arith.inlineMont.toS.mm arith.inlineMont.mm).x86_64Depth + 8 ≤ 128
      omega) _ _

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
  s!"vg_dsa_parameter_search_{8 * p}" ++ Emit.qualifiedName "" [(tag, h.suffix), ("mr", v.suffix)]

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
