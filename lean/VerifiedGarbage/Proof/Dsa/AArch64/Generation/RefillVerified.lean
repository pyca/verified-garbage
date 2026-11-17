module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Body
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.CT
public import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Params
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeTest
import VerifiedGarbage.Proof.Dsa.AArch64.ProbablePrime.Depth
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.Verified
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillCT
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.ProbablePrime.Verified`, which only this module used -/

section

/-! ### `Dsa.AArch64.ProbablePrime.Correct`, which only this module used -/

section

/-! # The probable-prime test meets its contract's functional part -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Proof.Dsa.AArch64.Generation (allocState freeState alloc_frame_ok)

/-- No byte of `ws` but those of the test's scratch ranges is in a region the test changes. -/
theorem keeps_of_frame {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {m : Mem}
    (hf : Frame (changed bits s) s.mem m) :
    Proof.Dsa.ModPow.Keeps (s.gpr .x0) (s.gpr .x1).toNat (layout bits).scratch s.mem m := by
  intro i hi hout
  have hw := A.wsBound
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have h1 := hout (witness, len bits) (by simp [layout])
  have h2 := hout (arithmetic, arithmeticBytes) (by simp [layout])
  have hc : (wsRegion s).Contains (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hw])
  apply hf
  intro r hr hx
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := arithmetic) (k := arithmeticBytes)
      (by simp only at h2; omega_using [h2]) (by omega_using [hi, hw]) (by have : arithmetic + arithmeticBytes ≤ 2 ^ 64 := (by decide); omega_using [this])
    exact hd _ (Region.contains_self _ _) hx
  · have hd := Offset.disjoint (s.gpr .x0) (d := i) (n := 1) (e := witness) (k := len bits)
      (by simp only at h1; omega_using [h1]) (by omega_using [hi, hw])
      (by have : witness + 384 ≤ 2 ^ 64 := (by decide); have := hlen; omega_arith)
    exact hd _ (Region.contains_self _ _) hx
  · exact (A.stackWs.sub_left (frame_sub s)) _ hx hc
  · exact A.wsUsed _ hc hx

theorem correct (M : Mont) (K : VG.Proof.Dsa.AArch64.Generation.PublicKernel) {bits : Nat} (hb : Supported bits) (s : State)
    (pre : (contract bits).pre s) :
    ∃ trace t, Exec isa (code bits M.mm K.run) s trace t ∧ abiPreserved s t ∧ (contract bits).post s t := by
  have A := primeABI_of pre
  obtain ⟨trace, t, he, hpre, hpost⟩ := alloc_frame_ok (bytes := 272) (by decide) A.stackLower
    (Q := fun t => abiPreserved s t ∧ BodyPost bits s t)
    (WP.mono (body_ok M K hb A) fun t ⟨hsp, _, _, hp⟩ m u f => ⟨⟨hp.2.2.2.1, by
        change t.sp + BitVec.ofNat 64 272 = s.sp
        rw [hsp]; exact BitVec.sub_add_cancel .., hp.2.2.2.2⟩, by
      -- The frame's bytes are lost; `used` is apart from them.
      unfold BodyPost at hp ⊢
      refine ⟨hp.1, fun b rest hr => ?_, hp.2.2.1.trans (f.sub fun R hR => ⟨⟨frameBase s, 272⟩, by simp [changed],
        by obtain rfl := List.mem_singleton.mp hR; exact fun _ h => h⟩), hp.2.2.2.1, hp.2.2.2.2⟩
      exact (f.readW (r := ⟨s.gpr .x4, 8⟩) (Region.contains_self _ _)
        (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact A.stackUsed.symm.sub_right (frame_sub s))
        (by decide)).trans (hp.2.1 b rest hr)⟩)
  obtain ⟨hx0, hused, hframe, _, _⟩ := hpost
  refine ⟨trace, t, he, hpre, ?_⟩
  sig_post [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, keeps_of_frame hb A hframe, fun b rest h => ?_⟩
  · rw [hx0]
    have st : ∀ o : Option (Bool × Spec.RsaKeyGen.Rand),
        (BitVec.setWidth 32 (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status o))).toNat =
          Proof.Dsa.ProbablePrime.status o := by
      intro o
      rcases o with _ | ⟨_ | _, _⟩ <;> rfl
    exact st _
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    rw [show s.gpr .x4 + BitVec.ofNat 64 0 = s.gpr .x4 from BitVec.add_zero _, hused b rest h]

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.ProbablePrime.Satisfiable`, which only this module used -/

section

/-! # A state meets the probable-prime test's precondition

An all-ones candidate of `bits` bits at its offset of a working space of 5120
words, and an empty tape. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Impl.Dsa.AArch64.ProbablePrime

def satBase : Addr := 0x100000

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - (satBase + BitVec.ofNat 64 (candidate bits))).toNat < bits / 8 then 0xFF#8 else 0

def satState (bits : Nat) : State where
  gpr r := match r with
    | .x0 => 0x100000 | .x1 => 5120 | .x2 => 0x200000 | .x3 => 0
    | .x4 => 0x300000 | _ => 0
  sp := 0x400000
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

theorem satisfiable {bits : Nat} (hb : Supported bits) : ∃ s, (contract bits).pre s := by
  refine ⟨satState bits, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact sat_odd hb
    | exact sat_length hb
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end


/-! # `vg_dsa_probable_prime_{bits}` on AArch64 is verified

For each Miller–Rabin round implementation: the test multiplies with the
round's inlined arithmetic and calls the shared round. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.ProbablePrime
open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The test's code with the round implementation `v`. -/
abbrev testCode (v : RoundImpl) (bits : Nat) : Prog isa :=
  Impl.Dsa.AArch64.ProbablePrime.code bits v.mont.mm (VG.Proof.Dsa.AArch64.Generation.publicKernel v).run

theorem verified (v : RoundImpl) {bits : Nat} (hb : Supported bits) :
    Verified target (testCode v bits) (contract bits) :=
  ⟨correct v.mont (VG.Proof.Dsa.AArch64.Generation.publicKernel v) hb, code_ct v.mont (VG.Proof.Dsa.AArch64.Generation.publicKernel v) hb, satisfiable hb⟩

/-- Its frames: its own 272 bytes. -/
theorem testCode_depth (v : RoundImpl) (bits : Nat) : 16 * (testCode v bits).aarch64Depth ≤ stack := by
  have h := aarch64Depth_of_noFrames _ (test_noFrames v bits)
  simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Code.aarch64Depth, h,
    AArch64.Instr.frameUnits]
  decide

/-- The tests with the round implementation `v`, as parameter generation
calls them. -/
def primeTest (v : RoundImpl) : VG.Proof.Dsa.AArch64.Generation.PrimeTest where
  name bits := s!"vg_dsa_probable_prime_{(Impl.Dsa.AArch64.ProbablePrime.layout bits).bits}" ++ v.suffix
  code := testCode v
  verified _ hb := verified v hb
  depth := testCode_depth v
  noDit _ hb := by
    have h := test_noDit v hb
    simp only [testCode, Impl.Dsa.AArch64.ProbablePrime.code, Impl.Bignum.AArch64.seqs, Code.all, h]
    rfl

end VG.Proof.Dsa.AArch64.ProbablePrime

end

end

/-! ### `Dsa.AArch64.Generation.HashVariants`, which only this module used -/

section

/-! # Select the SHA-1 and SHA-256 stream implementations for DSA generation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

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
  exact Nat.min_eq_left v.ok.sizes.DN

def generationHashes (v1 v256 : MdHash) (h1 : v1.mgf.G.rust = "sha1")
    (h256 : v256.mgf.G.rust = "sha256") : GenerationHashes where
  sha1 := v1.H
  sha256 := v256.H
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

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # `vg_dsa_parameter_search` on AArch64, verified

`refill_correct` and `refill_ct` for the hash backends and Miller–Rabin
variants, and a state that meets the contract's precondition; and the pairs
of a SHA-1 and a SHA-256 implementation that the search is emitted for
(`hashPairs`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.MillerRabin.AArch64 VG.Proof.Dsa.AArch64.Generation

/-- `state`'s words `[0, 128, 32769 · 128, 0]` at `0x4000`. -/
def satMem : Mem :=
  Mem.writeW (Mem.writeW (fun _ => 0) (0x4008 : Addr) (128 : BitVec 64)) (0x4010 : Addr)
    (BitVec.ofNat 64 (Spec.Dsa.parameterEntropy 128))

/-- A search for width 128 with an empty tape. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 276 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x10000 | .x6 => 9216
    | .x7 => 0x4000 | _ => 0
  sp := 0x1000000000000
  mem := satMem
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 276⟩, ⟨0x2000, 8⟩, ⟨0x10000, 73728⟩, ⟨0x4000, 32⟩]

theorem refill_satisfiable : ∃ s, (Spec.Dsa.parameterSearchContract abi 768).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel

theorem backend_verified (v1 v256 : MdHash) (v : RoundImpl)
    (h1 : v1.mgf.G.rust = "sha1") (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (Impl.Dsa.AArch64.Generation.code v1.H v256.H (Generator.generatorStage v).run
      (ProbablePrime.primeTest v).run)
      (Spec.Dsa.parameterSearchContract abi 768) :=
  ⟨refill_correct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_ct (generationHashes v1 v256 h1 h256) (Generator.generatorStage v) (ProbablePrime.primeTest v),
    refill_satisfiable⟩

/-- A SHA-1 and a SHA-256 implementation, as the parameter search takes
them, and that they are SHA-1 and SHA-256. -/
structure Hashes where
  sha1 : MdHash
  sha256 : MdHash
  h1 : sha1.mgf.G.rust = "sha1"
  h256 : sha256.mgf.G.rust = "sha256"

open VG.Proof.Variants.MdHash.AArch64 (sha1Variants sha256Variants)

theorem sha1Variants_rust : ∀ v ∈ sha1Variants, v.mgf.G.rust = "sha1" := by
  intro v hv
  simp only [sha1Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

theorem sha256Variants_rust : ∀ v ∈ sha256Variants, v.mgf.G.rust = "sha256" := by
  intro v hv
  simp only [sha256Variants, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

/-- The pairs the parameter search is emitted for, best first: a SHA-1 and
a SHA-256 implementation for the same CPUs (both baselines or both SHA-2
extensions). Either other pair needs the features of one of these, which
runs both hashes with them. -/
def hashPairs : List Hashes :=
  sha1Variants.attach.flatMap fun ⟨v1, h1⟩ => sha256Variants.attach.filterMap fun ⟨v256, h256⟩ =>
    if v1.suffix == v256.suffix then some ⟨v1, v256, sha1Variants_rust v1 h1, sha256Variants_rust v256 h256⟩
    else none

end VG.Proof.Dsa.AArch64.Generation.Refill
