module

public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Spec.Dsa.Generate
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
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Call
import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillAttempt
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
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.CT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Body
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes

/-! ### `Dsa.X86_64.ProbablePrime.Verified`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.RoundCode`, which this module and modules that import it used -/

section

/-! # Instruction safety and stack use of the shared Miller–Rabin backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem roundCode_safe (v : RoundImpl) : generationSafe (Kernel.called v).run := by
  exact (show generationSafe (.block Impl.MillerRabin.X86_64.Caller.save) from rfl).seq
    ((generationSafe.call_of v.ctl v.spSafe v.name).seq
      (show generationSafe (.block Impl.MillerRabin.X86_64.Caller.restore) from rfl))

/-- The call of the round never touches MXCSR. -/
theorem roundCode_noMx (v : RoundImpl) : (Kernel.called v).run.allInstrs (fun i => !touchesMxcsr i) = true := by
  simp only [Kernel.called, VG.Impl.MillerRabin.X86_64.Caller.call, Code.allInstrs, v.noMx,
    Bool.true_and]
  decide

theorem roundCode_depth (v : RoundImpl) : generationDepth (Kernel.called v).run := by
  change max 0 (max (v.code.x86_64Depth + 8) 0) ≤ 128
  simp only [Nat.zero_max, Nat.max_zero]
  have hd := v.depth
  change v.code.x86_64Depth ≤ 120 at hd
  omega_using [hd]

theorem inlineMul_depth (v : RoundImpl) (o a b : Nat) : generationDepth (v.inlineMont.mm o a b) := by
  unfold generationDepth
  rw [v.inlineDepth]
  exact Nat.zero_le _

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.ProbablePrime.Correct`, which only this module used -/

section

/-! # The probable-prime test meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Proof.MillerRabin.X86_64

/-- No byte of `ws` but those of the test's scratch ranges is in a region the test changes. -/
theorem keeps_of_frame {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {m : Mem}
    (hf : Frame (changed bits s) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .rdi) (s.gpr .rsi).toNat (layout bits).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := hout (witness, len bits) (by simp [layout])
  have h2 := hout (arithmetic, arithmeticBytes) (by simp [layout])
  have hc : (wsRegion s).Contains (s.gpr .rdi + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  apply hf
  intro r hr hx
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · have hd := Offset.disjoint (s.gpr .rdi) (d := i) (n := 1) (e := arithmetic) (k := arithmeticBytes)
      (by simp only at h2; omega_using [h2]) (by omega_using [hi, hw]) (by have : arithmetic + arithmeticBytes ≤ 2 ^ 64 := (by decide); omega_using [this])
    exact hd _ (Region.contains_self _ _) hx
  · have hd := Offset.disjoint (s.gpr .rdi) (d := i) (n := 1) (e := witness) (k := len bits)
      (by simp only at h1; omega_using [h1]) (by omega_using [hi, hw])
      (by have : witness + 384 ≤ 2 ^ 64 := (by decide); have := hlen; omega_arith)
    exact hd _ (Region.contains_self _ _) hx
  · exact (A.stackWs.sub_left (below_frame_sub s)) _ hx hc
  · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
    simp only [off, BitVec.add_zero] at hs
    exact A.stackWs _ (hs _ hx) hc
  · exact A.wsUsed _ hc hx

theorem correct (M : Mont) (K : Kernel)
    (ctl : ctlOk (code M.mm K.run) = true) (s : State) (pre : contract.pre s) :
    ∃ trace t, Exec isa (code M.mm K.run) s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨hb, A⟩ := primeABI_of pre
  have hwl : witness + len (s.gpr .r9).toNat ≤ domainCheck := by
    rcases hb with h | h | h | h | h <;> rw [h] <;> decide
  have hl : 56 ≤ (s.gpr .rsp).toNat := by have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower; omega_using [this]
  obtain ⟨trace, f, he, hsp, hpost⟩ := alloc_frame_ok (bytes := 56) (by decide) hl
    (Q := fun f => f.gpr .rsp = s.gpr .rsp ∧ BodyPost (s.gpr .r9).toNat s f)
    (WP.mono (body_ok M K hb A) fun t ⟨h1, h2, _, hp⟩ => ⟨h1, h2, freeState_rsp h1, by
      obtain ⟨hr, hu, hm, hg⟩ := hp
      exact ⟨hr, hu, hm, fun r hr' => by
        have : r ≠ .rsp := by revert r; decide
        simp only [freeState, State.setReg, this, ite_false]
        exact hg r hr'⟩⟩)
  obtain ⟨hrax, hused, hframe, hgpr⟩ := hpost
  refine ⟨trace, f, he, ⟨?_, ?_, VG.X86_64.Exec.ctl ctl he⟩, ?_⟩
  · intro r hr
    by_cases h : r = .rsp
    · subst h; exact hsp
    · exact hgpr r (by revert r; decide)
  · apply hframe.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact A.retWs.sub_right (ws_sub A (by decide))
    · exact A.retWs.sub_right (ws_sub A hwl)
    · exact (Offset.base_disjoint_below _ (by decide)).sub_right (below_frame_sub s)
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      exact (Offset.base_disjoint_below _ (by decide)).sub_right hs
    · exact A.retUsed
  · sig_post [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
      argRegs]
    refine ⟨?_, keeps_of_frame hb A hframe, fun b rest h => ?_⟩
    · rw [hrax]
      have st : ∀ o : Option (Bool × Spec.RsaKeyGen.Rand),
          (BitVec.setWidth 32 (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status o))).toNat =
            Proof.Dsa.ProbablePrime.status o := by
        intro o
        rcases o with _ | ⟨_ | _, _⟩ <;> rfl
      exact st _
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
      rw [show s.gpr .r8 + BitVec.ofNat 64 0 = s.gpr .r8 from BitVec.add_zero _, hused b rest h]

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.ProbablePrime.Satisfiable`, which only this module used -/

section

/-! # A state meets the probable-prime test's precondition

An all-ones candidate of 160 bits at its offset of a working space of 5120
words, and an empty tape. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Dsa.X86_64.ProbablePrime

def satBase : Addr := 0x100000

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - (satBase + BitVec.ofNat 64 (candidate bits))).toNat < bits / 8 then 0xFF#8 else 0

def satState (bits : Nat) : State where
  gpr r := match r with
    | .rdi => 0x100000 | .rsi => 5120 | .rdx => 0x200000 | .rcx => 0
    | .r8 => 0x300000 | .r9 => BitVec.ofNat 64 bits | .rsp => 0x400000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory bits
  rd := [⟨0x200000, 0⟩]
  wr := [⟨0x100000, 40960⟩, ⟨0x300000, 8⟩]

theorem foldl_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, foldl_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega_using [pos]⟩
    grind

theorem sat_candidate {bits : Nat} (hb : Supported bits) :
    candidateOf bits (satState bits) = 2 ^ bits - 1 := by
  have hl : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits)) (bits / 8) =
      List.replicate (bits / 8) 0xFF#8 := by
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl, hi])]
    exact ite_eq_left hi
  change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (satMemory bits) (satBase + BitVec.ofNat 64 (candidate bits))
    (bits / 8)) = _
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [foldl_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide]

theorem sat_odd {bits : Nat} (hb : Supported bits) : candidateOf bits (satState bits) % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega_using []
  have := Nat.two_pow_pos bits
  omega_arith

theorem sat_length {bits : Nat} (hb : Supported bits) :
    Spec.Dsa.bitLength (candidateOf bits (satState bits)) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [low])).mpr ⟨by omega_using [half], by omega_using [half, pos]⟩

theorem satisfiable : ∃ s, contract.pre s := by
  refine ⟨satState 160, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd (bits := 160) (Or.inl rfl)
    | exact sat_length (bits := 160) (Or.inl rfl)
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.Generation.PrimeSafety`, which only this module used -/

section

/-! # The probable-prime policy inherits instruction safety from shared arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem primeSetup_safe (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) : generationSafe (primeSetup mul) := by
  unfold generationSafe at hm ⊢
  simp only [primeSetup, primeR2, Impl.Dsa.X86_64.Arithmetic.constants,
    Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants,
    R2Words.choice, R2Words.fast, R2Words.old, VG.Impl.Bignum.X86_64.Public.R2Squares.run,
    VG.Impl.Bignum.X86_64.Public.R2Squares.init, VG.Impl.Bignum.X86_64.Public.R2Squares.next, seqs, generationOk, hm]
  rfl

theorem millerRabin_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) :
    generationSafe (millerRabin mul round) := by
  unfold generationSafe at hm hr ⊢
  simp only [millerRabin, primeIteration, drawRound, sampleRound,
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRound, seqs, generationOk, hm, hr]
  rfl

theorem probablePrime_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) :
    generationSafe (probablePrime mul round) := by
  exact (show generationSafe (seqs Impl.RsaKeyGen.X86_64.Candidate.trial) by
    unfold generationSafe; decide +kernel).seq
    (((primeSetup_safe mul hm).seq (millerRabin_safe mul round hm hr)).ite
      (show generationSafe (.block [.mov32 .rax (.imm 3), .store (hdr Impl.RsaKeyGen.X86_64.Candidate.kStat) .rax]) from rfl) _)

theorem primeBytes_noMx (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !touchesMxcsr i) = true)
    (hr : round.allInstrs (fun i => !touchesMxcsr i) = true) :
    (primeBytes mul round).allInstrs (fun i => !touchesMxcsr i) = true := by
  simp only [primeBytes, loadPadded, probablePrime, primeSetup, primeR2, Impl.Dsa.X86_64.Arithmetic.constants,
    Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants,
    R2Words.choice, R2Words.fast, R2Words.old, VG.Impl.Bignum.X86_64.Public.R2Squares.run,
    VG.Impl.Bignum.X86_64.Public.R2Squares.init, VG.Impl.Bignum.X86_64.Public.R2Squares.next,
    millerRabin, primeIteration, drawRound, sampleRound, Impl.Ffdh.X86_64.ParameterCandidate.witnessRound,
    seqs, Code.allInstrs, Bool.and_eq_true, hm, hr, and_true, true_and]
  and_intros <;> lit_decide

theorem primeBytes_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) :
    generationSafe (primeBytes mul round) :=
  (show generationSafe (loadPadded 0 20 18) from rfl).seq (probablePrime_safe mul round hm hr)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PrimeDepth`, which only this module used -/

section

/-! # The probable-prime policy inherits stack bounds from shared arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem primeSetup_depth (mul : Nat → Nat → Nat → Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) : generationDepth (primeSetup mul) := by
  unfold generationDepth at hm ⊢
  simp only [primeSetup, primeR2, Impl.Dsa.X86_64.Arithmetic.constants,
    Impl.Ffdh.X86_64.ParameterCandidate.prepareConstants,
    R2Words.choice, R2Words.fast, R2Words.old, VG.Impl.Bignum.X86_64.Public.R2Squares.run,
    VG.Impl.Bignum.X86_64.Public.R2Squares.init, VG.Impl.Bignum.X86_64.Public.R2Squares.next, seqs, Code.x86_64Depth, Nat.max_le]
  and_intros
  all_goals first | exact hr | apply hm | exact (show 0 ≤ 128 by decide)

theorem millerRabin_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (millerRabin mul round) := by
  unfold generationDepth at hm hr ⊢
  simp only [millerRabin, primeIteration, drawRound, sampleRound,
    Impl.Ffdh.X86_64.ParameterCandidate.witnessRound, seqs, Code.x86_64Depth, Nat.max_le]
  and_intros
  all_goals first | exact hr | apply hm | exact (show 0 ≤ 128 by decide)

theorem probablePrime_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (probablePrime mul round) := by
  exact (show generationDepth (seqs Impl.RsaKeyGen.X86_64.Candidate.trial) by
    unfold generationDepth; decide +kernel).seq
    (((primeSetup_depth mul hm).seq (millerRabin_depth mul round hm hr)).ite
      (show generationDepth (.block [.mov32 .rax (.imm 3), .store (hdr Impl.RsaKeyGen.X86_64.Candidate.kStat) .rax]) by exact (show 0 ≤ 128 by decide)) _)

theorem primeBytes_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    generationDepth (primeBytes mul round) :=
  (show generationDepth (loadPadded 0 20 18) by exact (show 0 ≤ 128 by decide)).seq (probablePrime_depth mul round hm hr)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # `vg_dsa_probable_prime` on x86-64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Safety.lean`, which only this module imported.
section

/-! # The probable-prime test neither loads MXCSR nor writes `rsp` but in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Impl.Dsa.X86_64.ProbablePrime
open VG.Proof.Dsa.X86_64.Generation (generationSafe generationDepth)

theorem code_safe (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationSafe (mul o a b)) (hr : generationSafe round) :
    generationSafe (code mul round) := by
  have hs : generationSafe setup := rfl
  have hb := hs.seq ((VG.Proof.Dsa.X86_64.Generation.primeBytes_safe mul round hm hr).seq
    ((show generationSafe (.block exit) from rfl).seq (show generationSafe (.block restoreRegisters) from rfl)))
  have hb' : generationSafe (.seq setup
      (Impl.Bignum.X86_64.seqs [Impl.Dsa.X86_64.Generation.primeBytes mul round,
        .block exit, .block restoreRegisters])) := hb
  unfold generationSafe at hb'
  change ((true && _) && true) = true
  rw [hb']; rfl

theorem code_noMx (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, (mul o a b).allInstrs (fun i => !touchesMxcsr i) = true)
    (hr : round.allInstrs (fun i => !touchesMxcsr i) = true) :
    (code mul round).allInstrs (fun i => !touchesMxcsr i) = true := by
  simp only [code, Impl.Bignum.X86_64.seqs, Code.allInstrs,
    VG.Proof.Dsa.X86_64.Generation.primeBytes_noMx mul round hm hr, Bool.true_and]
  lit_decide

theorem code_depth (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (hm : ∀ o a b, generationDepth (mul o a b)) (hr : generationDepth round) :
    (code mul round).x86_64Depth ≤ 184 := by
  have hp := VG.Proof.Dsa.X86_64.Generation.primeBytes_depth mul round hm hr
  unfold generationDepth at hp
  simp only [code, setup, Impl.Bignum.X86_64.seqs, sizedWorkspace, Code.x86_64Depth, Instr.frameBytes,
    Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right hp 56

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.ProbablePrime.code v.inlineMont.mm (Kernel.called v).run

theorem testCode_safe (v : RoundImpl) :
    VG.Proof.Dsa.X86_64.Generation.generationSafe (testCode v) :=
  code_safe _ _ (fun o a b => VG.Proof.Dsa.X86_64.Generation.generationSafe_of_allInstrs (v.inlineSafe o a b)) (VG.Proof.Dsa.X86_64.Generation.roundCode_safe v)

theorem verified (v : RoundImpl) : Verified target (testCode v) contract :=
  ⟨correct v.inlineMont (Kernel.called v) (testCode_safe v).mx, code_ct _ _, satisfiable⟩

/-- The test with the round implementation `v`, as parameter generation
calls it. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.X86_64.Generation.PrimeTest where
  name := "vg_dsa_probable_prime" ++ v.suffix
  code := testCode v
  verified := verified v
  safe := testCode_safe v
  noMx := code_noMx _ _ v.inlineNoMx (VG.Proof.Dsa.X86_64.Generation.roundCode_noMx v)
  depth := code_depth _ _ (VG.Proof.Dsa.X86_64.Generation.inlineMul_depth v)
    (VG.Proof.Dsa.X86_64.Generation.roundCode_depth v)

end VG.Proof.Dsa.X86_64.ProbablePrime

end

end

/-! ### `Dsa.X86_64.Generation.HashVariants`, which only this module used -/

section

/-! # Select the SHA-1 and SHA-256 stream implementations for DSA generation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Pbkdf2.Md.X86_64

theorem sha1_of_name (v : MdHash) (h : v.mgf.G.rust = "sha1") : v.mgf.G = Spec.Mgf1.sha1 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem sha256_of_name (v : MdHash) (h : v.mgf.G.rust = "sha256") : v.mgf.G = Spec.Mgf1.sha256 := by
  have hm := v.mgf.mem
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm
  all_goals rw [hm] at h
  all_goals first | exact hm | contradiction

theorem hashCode_size (v : MdHash) (x : List (BitVec 8)) : (v.mgf.G.hash x).length = v.H.D := by
  rw [v.mgf.hash, v.ok.hash, List.length_take, MdStream.Md.hash, v.ok.md.digest_length]
  exact Nat.min_eq_left v.ok.hDN

def generationHashes (v1 v256 : MdHash) (h1 : v1.mgf.G.rust = "sha1")
    (h256 : v256.mgf.G.rust = "sha256") : GenerationHashes where
  sha1 := v1.H.stream
  sha256 := v256.H.stream
  h1 := v1.ok.stream
  h256 := v256.ok.stream
  hash1 x := by rw [← sha1_of_name v1 h1]; exact v1.mgf.hash x
  hash256 x := by rw [← sha256_of_name v256 h256]; exact v256.mgf.hash x
  size1 x := by rw [← sha1_of_name v1 h1]; exact hashCode_size v1 x
  size256 x := by rw [← sha256_of_name v256 h256]; exact hashCode_size v256 x
  width1 := by
    change v1.H.D = 20
    rw [← v1.mgf.len, sha1_of_name v1 h1]
    rfl
  width256 := by
    change v256.H.D = 32
    rw [← v256.mgf.len, sha256_of_name v256 h256]
    rfl

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.PowerDepth`, which only this module used -/

section

/-! # Stack bound for public generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem generatorPower_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) :
    generationDepth (generatorPower sq mul) := by
  unfold generationDepth at hs hm ⊢
  unfold generatorPower Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN Crt.toEnt Crt.copyArr R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- one pass: a `rw` for each node of the code read the whole goal again
  simp only [generation_depth_seqs, Code.x86_64Depth, List.foldr_append, List.foldr_cons, List.foldr_nil,
    Nat.max_le]
  and_intros
  all_goals first | exact hs | apply hm | exact (show 0 ≤ 128 by decide)

theorem generatorPowerFresh_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    generationDepth (generatorPowerFresh sq mul len) :=
  (show generationDepth (generatorModulus len) by exact (show 0 ≤ 128 by decide)).seq (generatorPower_depth sq mul hs hm)

theorem generatorStep_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationDepth sq) (hm : ∀ o a b, generationDepth (mul o a b)) (len : Nat) :
    generationDepth (generatorStep sq mul len) := by
  have test : generationDepth (.block [.alu .test .rax (.reg .rax)]) := by exact (show 0 ≤ 128 by decide)
  have retry : generationDepth (.block (stackStatus 3)) := by exact (show 0 ≤ 128 by decide)
  have success : generationDepth (.block (stackStatus 1)) := by exact (show 0 ≤ 128 by decide)
  have run := (show generationDepth (.block generatorInput) by exact (show 0 ≤ 128 by decide)).seq
    (generatorPowerFresh_depth sq mul hs hm len)
  exact (show generationDepth (generatorRangeFromFrame len false) by exact (show 0 ≤ 128 by decide)).seq
    (test.seq (retry.ite (run.seq
      ((show generationDepth (generatorRangeFromFrame len true) by exact (show 0 ≤ 128 by decide)).seq
        (test.seq (retry.ite success .e)))) .e))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ValidateDepth`, which only this module used -/

section

/-! # Stack bound for the final domain validator -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64


variable {checkName : String}

theorem checkParameters_depth_bound (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    {n : Nat} (hs : sq.x86_64Depth ≤ n) (hm : ∀ o a b, (mul o a b).x86_64Depth ≤ n) :
    (Generate.checkParameters sq mul).x86_64Depth ≤ n := by
  unfold Generate.checkParameters Checks.signingKey Checks.publicPrefix Core.reduce
    Arithmetic.reduce Arithmetic.reduceSetup Arithmetic.reduceByte Arithmetic.reduceStep
    Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN Crt.toEnt Crt.copyArr R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- one pass: a `rw` for each node of the code read the whole goal again
  simp only [generation_depth_seqs, Code.x86_64Depth, List.foldr_append, List.foldr_cons, List.foldr_nil,
    Nat.max_le]
  and_intros
  all_goals first | exact hs | apply hm | exact (Nat.zero_le n)

theorem validate_depth (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hc : generationDepth (.call checkName (Generate.checkParameters sq mul))) (pLen qLen : Nat) :
    generationDepth (validate (checkName := checkName) sq mul pLen qLen) := by
  exact ((generationDepth.block _).seq hc).seq
    ((generationDepth.block _).seq ((generationDepth.block _).ite (generationDepth.block _) .e))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.CandidateDepth`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.HashDepth`, which this module and modules that import it used -/

section

/-! # Seed hashing fits the reserved stack below the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

structure HashDepth (H : Stream) : Prop where
  init : H.initC.x86_64Depth ≤ 120
  update : H.updC.x86_64Depth ≤ 120
  finish : H.finC.x86_64Depth ≤ 120

theorem hashLabel_depth {H : Stream} (h : HashDepth H) (o : Nat) :
    generationDepth (Impl.RsaOaep.X86_64.hashLabel H o) := by
  simp only [generationDepth, Impl.RsaOaep.X86_64.hashLabel, Impl.Mgf1.X86_64.seqs,
    Code.x86_64Depth, Nat.max_le]
  exact ⟨by decide, Nat.add_le_add_right h.init 8, by decide,
    Nat.add_le_add_right h.update 8, by decide, Nat.add_le_add_right h.finish 8⟩

private theorem seedAddUnrolled_depth (n : Nat) : generationDepth (seedAddUnrolled n) := by
  induction n with
  | zero => exact generationDepth.block _
  | succ n ih => exact (generationDepth.block _).seq ih

theorem seedAdd_depth (n : Nat) : generationDepth (seedAdd n) := by
  unfold seedAdd
  split
  · exact seedAddUnrolled_depth n
  · unfold seedAddTail
    split <;> exact Nat.zero_le _

theorem seedHashAt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256) (len : Nat) :
    generationDepth (seedHashAt H1 H256 len) := by
  unfold seedHashAt
  split <;> first | exact hashLabel_depth h1 _ | exact hashLabel_depth h256 _

theorem pHashOne_depth {H : Stream} (h : HashDepth H) (len count j : Nat) :
    generationDepth (pHashOne H len count j) :=
  ((generationDepth.block _).seq ((seedAdd_depth len).seq (hashLabel_depth h _))).seq
    ((generationDepth.block _).seq (by unfold generationDepth; decide +kernel))

theorem pHashPrefix_depth {H : Stream} (h : HashDepth H) (len count k : Nat) :
    generationDepth (pHashPrefix H len count k) := by
  induction k with
  | zero => exact generationDepth.block _
  | succ k ih => exact ih.seq (pHashOne_depth h len count k)

theorem pHashes_depth {H : Stream} (h : HashDepth H) (len count : Nat) :
    generationDepth (pHashes H len count) := pHashPrefix_depth h len count (count + 1)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Stack bounds for subgroup candidates and prime search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem primeCall_depth (prime : Prog isa) (hp : callerDepth prime) (bits : Nat) :
    callerDepth (primeCall prime bits) := by
  unfold callerDepth at hp ⊢
  simp only [primeCall, primeCallResult, primeCallStatus, Code.x86_64Depth, Nat.max_le, Nat.zero_le,
    and_true, true_and]
  exact hp

theorem qCandidate_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256) (len : Nat) :
    generationDepth (qCandidate H1 H256 len) := by
  exact (seedHashAt_depth h1 h256 len).seq ((show generationDepth (.block qArgs) by exact (show 0 ≤ 128 by decide)).seq
    (show generationDepth Impl.Ffdh.X86_64.ParameterCandidate.shape by exact (show 0 ≤ 128 by decide)))

theorem subgroup_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (len : Nat) :
    callerDepth (subgroup H1 H256 prime len) :=
  (callerDepth.of (qCandidate_depth h1 h256 len)).seq (primeCall_depth prime hp _)

theorem pConstruct_depth {H : Stream} (h : HashDepth H) (pLen qLen : Nat) :
    generationDepth (pConstruct H pLen qLen) := by
  exact ((pHashes_depth h _ _).seq (show generationDepth (pShape qLen _ pLen) by exact (show 0 ≤ 128 by decide))).seq
    ((show generationDepth (.block workspaceBase) by exact (show 0 ≤ 128 by decide)).seq
      ((show generationDepth (workspace (pLen / 8)) by exact (show 0 ≤ 128 by decide)).seq
        (show generationDepth (candidateFromFrame pLen qLen) by exact (show 0 ≤ 128 by decide))))

theorem pTest_depth (prime : Prog isa) (hp : callerDepth prime) (pLen : Nat) :
    callerDepth (pTest prime pLen) := by
  unfold pTest
  exact (callerDepth.of (generationDepth.block _)).seq
    ((callerDepth.of (generationDepth.block _)).ite (primeCall_depth prime hp _) _)

theorem pAttempt_depth {H1 H256 : Stream} (h1 : HashDepth H1) (h256 : HashDepth H256)
    (prime : Prog isa) (hp : callerDepth prime) (pLen qLen : Nat) :
    callerDepth (pAttempt H1 H256 prime pLen qLen) := by
  have hh : HashDepth (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (callerDepth.of (generationDepth.block _)).seq
    (((callerDepth.of (pConstruct_depth hh pLen qLen)).seq (pTest_depth prime hp pLen)).seq
      (callerDepth.of (generationDepth.block _)))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ValidateSafety`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.PowerSafety`, which this module and modules that import it used -/

section

/-! # Public generator exponentiation preserves stack and MXCSR control state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64

theorem generatorPower_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) :
    generationSafe (generatorPower sq mul) := by
  unfold generationSafe at hs hm ⊢
  unfold generatorPower Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- one pass: a `rw` for each node of the code read the whole goal again
  simp only [generationOk_seqs, generationOk, List.all_append, List.all_cons, hs, hm]
  rfl

theorem generatorPowerFresh_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorPowerFresh sq mul len) :=
  (show generationSafe (generatorModulus len) from rfl).seq (generatorPower_safe sq mul hs hm)

theorem generatorStep_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (len : Nat) :
    generationSafe (generatorStep sq mul len) := by
  have test : generationSafe (.block [.alu .test .rax (.reg .rax)]) := rfl
  have retry : generationSafe (.block (stackStatus 3)) := rfl
  have success : generationSafe (.block (stackStatus 1)) := rfl
  have run := (show generationSafe (.block generatorInput) from rfl).seq
    (generatorPowerFresh_safe sq mul hs hm len)
  exact (show generationSafe (generatorRangeFromFrame len false) from rfl).seq
    (test.seq (retry.ite (run.seq
      ((show generationSafe (generatorRangeFromFrame len true) from rfl).seq
        (test.seq (retry.ite success .e)))) .e))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The final domain validator preserves stack and MXCSR control state -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Rsa.X86_64


variable {checkName : String}

theorem checkParameters_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) :
    generationSafe (Generate.checkParameters sq mul) := by
  unfold generationSafe at hs hm ⊢
  unfold Generate.checkParameters Checks.signingKey Checks.publicPrefix Core.reduce
    Arithmetic.reduce Arithmetic.reduceSetup Arithmetic.reduceByte Arithmetic.reduceStep
    Core.publicPow PublicPower.power PublicPower.powerCore
    PublicPower.encodedPower PublicPower.expLoop PublicPower.byte PublicPower.window
    PublicPower.squares PublicPower.squaresInit PublicPower.squaresNext
    PublicPower.applyWindow Arithmetic.encodePower Arithmetic.constants
    Crt.tabBuild Crt.tabBuildN R2Words.choice R2Words.fast R2Words.old VG.Impl.Bignum.X86_64.Public.R2Squares.run
    VG.Impl.Bignum.X86_64.Public.R2Squares.init VG.Impl.Bignum.X86_64.Public.R2Squares.next
  -- one pass: a `rw` for each node of the code read the whole goal again
  simp only [generationOk_seqs, generationOk, List.all_append, List.all_cons, hs, hm]
  rfl

theorem validate_safe (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa)
    (hs : generationSafe sq) (hm : ∀ o a b, generationSafe (mul o a b)) (pLen qLen : Nat) :
    generationSafe (validate (checkName := checkName) sq mul pLen qLen) := by
  unfold validate
  refine .seq (.seq ?_ ((checkParameters_safe sq mul hs hm).call checkName)) (.seq ?_ ?_)
  all_goals rfl

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.CandidateSafety`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.HashSafety`, which this module and modules that import it used -/

section

/-! # Instruction safety of every seed hash and wrapped-seed contribution -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

structure HashSafety (H : Stream) : Prop where
  init : generationSafe H.initC
  update : generationSafe H.updC
  finish : generationSafe H.finC

theorem hashLabel_safe {H : Stream} (h : HashSafety H) (o : Nat) :
    generationSafe (Impl.RsaOaep.X86_64.hashLabel H o) := by
  unfold Impl.RsaOaep.X86_64.hashLabel Impl.Mgf1.X86_64.seqs
  repeat' apply generationSafe.seq
  all_goals first | exact h.init.call _ | exact h.update.call _ | exact h.finish.call _ | rfl

private theorem seedAddUnrolled_safe (n : Nat) : generationSafe (seedAddUnrolled n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (show generationSafe (.block (seedAddByte n)) from rfl).seq ih

theorem seedAdd_safe (n : Nat) : generationSafe (seedAdd n) := by
  unfold seedAdd
  split
  · exact seedAddUnrolled_safe n
  · unfold seedAddTail
    split <;> rfl

theorem seedHashAt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256) (len : Nat) :
    generationSafe (seedHashAt H1 H256 len) := by
  unfold seedHashAt
  split <;> first | exact hashLabel_safe h1 _ | exact hashLabel_safe h256 _

theorem pHashOne_safe {H : Stream} (h : HashSafety H) (len count j : Nat) :
    generationSafe (pHashOne H len count j) := by
  exact ((show generationSafe (.block (seedInputArgs j)) from rfl).seq
    ((seedAdd_safe len).seq (hashLabel_safe h _))).seq
    ((show generationSafe (.block (hashCopyArgs len count j)) from rfl).seq (by unfold generationSafe; decide +kernel))

theorem pHashPrefix_safe {H : Stream} (h : HashSafety H) (len count k : Nat) :
    generationSafe (pHashPrefix H len count k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih.seq (pHashOne_safe h len count k)

theorem pHashes_safe {H : Stream} (h : HashSafety H) (len count : Nat) :
    generationSafe (pHashes H len count) := pHashPrefix_safe h len count (count + 1)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Instruction safety of subgroup candidates and bounded prime search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem primeCall_safe (prime : Prog isa) (hp : generationSafe prime) (bits : Nat) :
    generationSafe (primeCall prime bits) :=
  (show generationSafe (.block (primeCallArgs bits)) from rfl).seq
    (hp.seq (show generationSafe primeCallResult from rfl))

theorem qCandidate_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256) (len : Nat) :
    generationSafe (qCandidate H1 H256 len) := by
  exact (seedHashAt_safe h1 h256 len).seq ((show generationSafe (.block qArgs) from rfl).seq
    (show generationSafe Impl.Ffdh.X86_64.ParameterCandidate.shape from rfl))

theorem subgroup_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (len : Nat) :
    generationSafe (subgroup H1 H256 prime len) :=
  (qCandidate_safe h1 h256 len).seq (primeCall_safe prime hp _)

theorem pConstruct_safe {H : Stream} (h : HashSafety H) (pLen qLen : Nat) :
    generationSafe (pConstruct H pLen qLen) := by
  exact ((pHashes_safe h _ _).seq (show generationSafe (pShape qLen _ pLen) from rfl)).seq
    ((show generationSafe (.block workspaceBase) from rfl).seq
      ((show generationSafe (workspace (pLen / 8)) from rfl).seq
        (show generationSafe (candidateFromFrame pLen qLen) from rfl)))

theorem pTest_safe (prime : Prog isa) (hp : generationSafe prime) (pLen : Nat) :
    generationSafe (pTest prime pLen) := by
  unfold pTest
  apply generationSafe.seq (show generationSafe (.block candidateWidth) from rfl)
  exact generationSafe.ite (show generationSafe (.block (stackStatus 3)) from rfl) (primeCall_safe prime hp _) _

theorem pAttempt_safe {H1 H256 : Stream} (h1 : HashSafety H1) (h256 : HashSafety H256)
    (prime : Prog isa) (hp : generationSafe prime) (pLen qLen : Nat) :
    generationSafe (pAttempt H1 H256 prime pLen qLen) := by
  have hh : HashSafety (if qLen = 20 then H1 else H256) := by split <;> with_reducible assumption
  exact (show generationSafe (.block pAttemptArgs) from rfl).seq
    (((pConstruct_safe hh pLen qLen).seq (pTest_safe prime hp pLen)).seq
      (show generationSafe (.block searchReturn) from rfl))

end VG.Proof.Dsa.X86_64.Generation

end

end

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
