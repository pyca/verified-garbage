module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.CT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundCode
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeSafety
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CodeDepth
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Body
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

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
  depth := code_depth _ _ (VG.Proof.Dsa.X86_64.Generation.inlineMul_depth v)
    (VG.Proof.Dsa.X86_64.Generation.roundCode_depth v)

end VG.Proof.Dsa.X86_64.ProbablePrime
