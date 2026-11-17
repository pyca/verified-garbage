module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.PX
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.CT
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.TaintRel
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Verified

/-! ### `Dsa.PPC64LE.Gen.HashInst`, which only this module used -/

section

/-! # DSA parameter generation on PPC64LE: SHA-1 and SHA-256

The two hash functions of parameter generation (`Impl.Dsa.PPC64LE.Generation.sha1`,
`sha256`) as `HashOk`: the parameters of the streaming code (SHA-1's own;
for SHA-256, whose streaming code is its own, `sha256Params`), their
compression functions' proofs, and the hash of a message of fewer than 56
bytes as the compression of its one padded block (`hash_blk`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A message of fewer than 56 bytes pads to one block, `blk`. -/
theorem hash_blk {N : Nat} (md : MdStream.Md 64 N 8) (iv : md.HV) {msg : List Byte} (h : msg.length < 56) :
    md.hash iv msg = md.digest (md.compress iv (md.parse fun t => (blk md msg).getD t 0)) := by
  have hp : md.pad msg = blk md msg := by
    simp only [MdStream.Md.pad, blk, Nat.mod_eq_of_lt (show msg.length < 64 by omega_using [h])]
    rw [show (2 * 64 - 8 - 1 - msg.length) % 64 = 55 - msg.length by omega_using [h]]
  have hl : (blk md msg).length = 64 := by
    simp only [blk, List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      md.lenBytes_length]
    omega_using [h]
  rw [MdStream.Md.hash, hp, hl, Nat.div_self (by decide), MdStream.Md.compressList_one]

/-- SHA-256's compression function as the streaming code's callee. -/
def sha256Params : VG.Impl.MdStream.PPC64LE.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := VG.Impl.MdStream.PPC64LE.len64 88 true
  out := VG.Impl.MdStream.PPC64LE.out32 8 true

theorem sha256_callee : VG.Proof.MdStream.PPC64LE.CalleeOk (P := sha256Params) Proof.Sha256.md
    Impl.Sha256.PPC64LE.compress :=
  ⟨Proof.Sha256.PPC64LE.compress_verified.1, by decide +kernel⟩

def sha1Ok : HashOk sha1 where
  P := Impl.Sha1.PPC64LE.Stream.params
  md := Proof.Sha1.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := by decide
  hso0 := by decide
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha1.PPC64LE.Stream.callee
  ct := Proof.Sha1.PPC64LE.compress_verified.2.1
  H0 := Spec.Sha1.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha1] using hj)]
    simp [sha1]
  digest := Proof.Sha1.digest_eq
  H := Spec.Sha1.hash
  hash msg h := (Proof.Sha1.hash_eq msg).trans (hash_blk _ _ h)
  cert1 L := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block (ivStore sha1.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])), by kernel_rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 5 true ++ [.subi .r28 .r28 dst])), by kernel_rfl⟩

def sha256Ok : HashOk sha256 where
  P := sha256Params
  md := Proof.Sha256.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := by decide
  hso0 := by decide
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := sha256_callee
  ct := Proof.Sha256.PPC64LE.compress_verified.2.1
  H0 := Spec.Sha256.H0
  iv m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    rw [h j (by simpa [sha256] using hj)]
    simp [sha256]
  digest := Proof.Sha256.digest_eq
  H := Spec.Sha256.hash
  hash msg h := (Proof.Sha256.hash_eq msg).trans (hash_blk _ _ h)
  cert1 L := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block (ivStore sha256.iv ++ [scr .r26 sState, scr .r27 (wB L), scr .r4 sMsg])), by kernel_rfl⟩
  cert3 dst := ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r26])
    (.block ([.addi .r28 .r28 dst] ++ VG.Impl.MdStream.PPC64LE.out32 8 true ++ [.subi .r28 .r28 dst])), by kernel_rfl⟩

theorem sha1_length (bs : List Byte) : (Spec.Sha1.hash bs).length = 20 := by
  rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _

theorem sha256_length (bs : List Byte) : (Spec.Sha256.hash bs).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

end VG.Proof.Dsa.PPC64LE.Gen

end

end

/-! ### `Dsa.PPC64LE.Prime.Satisfiable`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.Prime.Verified`, which only this module used -/

section

/-!
# DSA's probable-prime test on PPC64LE: verified

`correct`: the contract's postcondition (with the table, `abi.withConsts`),
from `code_ok`. `constantTime`: from `code_ct`, the contract's public data
(the arguments, the stack pointer, the candidate, the tape's octets and the
table's address) giving the same `PD` in both runs. `satisfiable`: an
all-ones candidate and an empty tape. `verified`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two)

/-- The contract, with the table. -/
abbrev contract (bits : Nat) : Contract isa :=
  Proof.Dsa.ProbablePrime.contract (layout bits) (abi.withConsts K) 176

theorem pre_of {bits : Nat} {s : State} (hs : (contract bits).pre s) : CIn bits s ∧ ConstsOk K 176 s := by
  unfold contract Proof.Dsa.ProbablePrime.contract at hs
  obtain ⟨hp, hk⟩ := pre_consts.mp hs
  exact ⟨CIn.ofStrip (cin_of_pre bits _ hp), hk⟩

theorem correct (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) (s : State) (hs : (contract bits).pre s) :
    ∃ t s', Exec isa (code bits Ri.name Ri.code) s t s' ∧ abiPreserved s s' ∧ (contract bits).post s s' := by
  obtain ⟨h, hk⟩ := pre_of hs
  obtain ⟨t, s', he, hc⟩ := code_ok Ri hb h hk
  refine ⟨t, s', he, hc.abi, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  refine post_consts.mpr ?_
  sig_post [Proof.Dsa.ProbablePrime.sig, abi, argRegs]
  refine ⟨?_, hc.keeps, hc.used⟩
  rw [hc.r3, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := status_le (res bits s)
  simp only [res, cand, tape] at this ⊢
  omega_using [this]

theorem constantTime (Ri : RoundImpl) {bits : Nat} (hb : Bits bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub (code bits Ri.name Ri.code) := by
  refine RelCT.constantTime ((code_ct Ri hb).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ?_) fun _ _ h => h)
  obtain ⟨c₁, k₁⟩ := pre_of h₁
  obtain ⟨c₂, k₂⟩ := pre_of h₂
  unfold contract Proof.Dsa.ProbablePrime.contract at hp
  obtain ⟨hp, hsy⟩ := pub_consts.mp hp
  sig_pub [Proof.Dsa.ProbablePrime.sig, abi, argRegs] at hp
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7⟩ := hp
  obtain ⟨hc, ht⟩ := List.cons.inj hl
  have ht' : tape s₁ = tape s₂ :=
    (List.map_inj_right fun _ _ e => BitVec.eq_of_toNat_eq e).mp ht
  refine ⟨⟨s₁.gpr .r3, s₁.gpr .r4, s₁.gpr .r5, s₁.gpr .r6, s₁.gpr .r7, s₁.sp, s₁.syms VG.Impl.RsaKeyGen.TrialTable32.symbol,
    cand bits s₁, tape s₁⟩, ⟨hb, c₁, k₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨hb, c₂, k₂, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, hsp.symm, (hsy _ List.mem_cons_self).symm, hc.symm,
      ht'.symm⟩⟩

end VG.Proof.Dsa.PPC64LE.Prime

end

end


/-!
# DSA's probable-prime test on PPC64LE: a state meets the precondition

An all-ones candidate of `bits` bits at the start of a working space of
2000 words, an empty tape, and the table at `0x30000`. `verified`: with
`correct` and `constantTime`, the test is verified.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The witness's memory. -/
def satMemory (bits : Nat) : Mem := fun a =>
  if (a - 0x10000#64).toNat < bits / 8 then 0xFF#8
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

/-- The witness. -/
def satState (bits : Nat) : State where
  gpr r := if r = .r3 then 0x10000 else if r = .r4 then 2000 else if r = .r5 then 0x5000 else
    if r = .r7 then 0x2000 else 0
  lr := 0
  sp := 0x20000
  mem := satMemory bits
  rd := [⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 16000⟩, ⟨0x2000, 8⟩]
  unknowns _ := 0
  syms _ := 0x30000

theorem os2ip_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, os2ip_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    have pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega_using [pos]⟩
    grind

theorem sat_candidate {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 = 2 ^ bits - 1 := by
  have hs := shape_of hb
  have hl := hs.hlen8
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bytes : Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 (layout bits).candidate)
      ((layout bits).bits / 8) = List.replicate (bits / 8) 0xFF#8 := by
    change Spec.Rsa.bytesAt (satMemory bits) (0x10000#64 + BitVec.ofNat 64 0) (bits / 8) = _
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [ite_eq_left (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hi])]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [os2ip_ones, Nat.zero_mul, Nat.zero_add]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by rw [← hs.hlen]; omega_using [hl]]

theorem sat_odd {bits : Nat} (hb : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64 % 2 = 1 := by
  rw [sat_candidate hb]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide, Nat.pow_succ]; omega_using []
  have := Nat.two_pow_pos bits
  omega_arith

theorem sat_length {bits : Nat} (hb : Bits bits) :
    Spec.Dsa.bitLength (Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) 0x10000#64) = bits := by
  rw [sat_candidate hb]
  have low : 1 ≤ bits := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  have pos := Nat.two_pow_pos (bits - 1)
  exact (VG.Proof.Dsa.bitLength_iff_bounds (by omega_using [low])).mpr ⟨by omega_using [half], by omega_using [half, pos]⟩

theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

theorem sat_table {bits : Nat} (hb : Bits bits) :
    Abi.constsHeld (satMemory bits) (fun _ => 0x30000#64) VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  have fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length]; decide
  have small : i < 1024 := by rw [VG.Proof.RsaKeyGen.TrialTable32.packed_length] at index; exact index
  have h384 : bits / 8 ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine Eq.trans (Mem.readW_congr (m := satMemory bits)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_)
    (constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index)
  intro j hj
  change (if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [small, h384, hj])]
  rfl

theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.TrialTable32.packed_length]

theorem satisfiable {bits : Nat} (hb : Bits bits) : ∃ s, (contract bits).pre s := by
  have hs := shape_of hb
  have hkw : keyOff + 8 * keyWords bits ≤ 16000 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨satState bits, ?_⟩
  unfold contract Proof.Dsa.ProbablePrime.contract
  refine pre_consts.mpr ⟨?_, ?_⟩
  · sig_pre [Proof.Dsa.ProbablePrime.sig, abi, argRegs, stripConsts]
    sig_and_intros
    all_goals first
      | exact sat_odd hb
      | exact sat_length hb
      | (show _ ≤ 8 * 2000; omega_using [hkw])
      | decide
      | exact Region.disjoint_of_sep (by decide +kernel)
  · refine ⟨?_, sat_table hb, ?_, ?_⟩
    · simp only [constRegs, packed_regions]; rfl
    · simp only [constRegs, packed_regions]
      simp only [List.forall_mem_singleton, satState, abi, List.forall_mem_cons, stackBelow]
      exact ⟨by decide, ⟨Region.disjoint_of_sep (by decide +kernel), Region.disjoint_of_sep (by decide +kernel)⟩,
        Region.disjoint_of_sep (by decide +kernel)⟩
    · simp only [constRegs, packed_regions, List.forall_mem_singleton, satState]
      decide

/-- `vg_dsa_probable_prime_{bits}`, calling the round `Ri`, is verified. -/
theorem verified (Ri : RoundImpl) (bits : Nat) (hb : Bits bits := by decide) :
    Verified target (code bits Ri.name Ri.code) (contract bits) :=
  ⟨correct Ri hb, constantTime Ri hb, satisfiable hb⟩

end VG.Proof.Dsa.PPC64LE.Prime

end

end


/-! # DSA parameter generation on PPC64LE: the three geometries

`geo pLen qLen G v ck`: the geometry of `(pLen, qLen)`, hashing with `G`,
testing with the probable-prime functions over the Miller–Rabin round `v`,
whose candidates are at the start of their working space, and checking the
domain with `ck`; `geoOk`: its proofs, for every call with those lengths;
`params_verified`: the three of them meet the contract of
`vg_dsa_parameter_search`, and `search_params` with `vg_dsa_check_parameters`
as the check.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The geometry of `(pLen, qLen)`, hashing with `G`, testing with the round
`v`, checking with `ck`. -/
def geo (pLen qLen : Nat) (G : Hash) (v : RoundImpl) (ck : Prog isa) : Geo where
  pLen := pLen
  qLen := qLen
  G := G
  qCand := 0
  qName := s!"vg_dsa_probable_prime_{(Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * qLen)).bits}" ++ v.suffix
  qCode := Impl.Dsa.PPC64LE.ProbablePrime.code (8 * qLen) v.name v.code
  pCand := 0
  pName := s!"vg_dsa_probable_prime_{(Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * pLen)).bits}" ++ v.suffix
  pCode := Impl.Dsa.PPC64LE.ProbablePrime.code (8 * pLen) v.name v.code
  checkName := "vg_dsa_check_parameters"
  checkCode := ck

/-- The test uses the stack of the round it calls. -/
theorem prime_stack (bits : Nat) (name : String) (rc : Prog isa) :
    sdepth (Impl.Dsa.PPC64LE.ProbablePrime.code bits name rc) ≤ sdepth rc := by
  have z : ∀ c, sdepth c = 0 → sdepth c ≤ sdepth rc := fun _ h => h ▸ Nat.zero_le _
  simp only [Impl.Dsa.PPC64LE.ProbablePrime.code, Impl.Dsa.PPC64LE.ProbablePrime.body,
    Impl.Dsa.PPC64LE.ProbablePrime.loadC, Impl.Dsa.PPC64LE.ProbablePrime.exit, sdepth,
    VG.Impl.MillerRabin.PPC64LE.Blinded.millerRabin, VG.Impl.MillerRabin.PPC64LE.Blinded.draw,
    VG.Impl.MillerRabin.PPC64LE.Blinded.round, VG.Impl.RsaKeyGen.PPC64LE.Trial.trial,
    VG.Impl.MillerRabin.PPC64LE.Search.roundCall, Nat.max_le, Nat.zero_le, and_true, true_and]
  exact ⟨z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide), z _ (by decide),
    Nat.le_refl _⟩

theorem primeOk (v : RoundImpl) (bits : Nat) (hb : VG.Proof.Dsa.PPC64LE.Prime.Bits bits := by decide) :
    PrimeOk (Impl.Dsa.PPC64LE.ProbablePrime.layout bits) (Impl.Dsa.PPC64LE.ProbablePrime.code bits v.name v.code) :=
  ⟨VG.Proof.Dsa.PPC64LE.Prime.verified v bits hb, (prime_stack bits v.name v.code).trans v.stack⟩

/-- A test's layout in the working space of the tests of a `pLen`-byte search. -/
theorem lay_ok (pL bits : Nat) (h : Impl.Dsa.PPC64LE.ProbablePrime.keyOff +
      8 * Impl.Dsa.PPC64LE.ProbablePrime.keyWords bits ≤ 8 * wWords pL)
    (hc : bits / 8 ≤ 8 * wWords pL) (h15 : wB pL < 2 ^ 15) :
    (Impl.Dsa.PPC64LE.ProbablePrime.layout bits).size ≤ 8 * wWords pL ∧
      (∀ r ∈ (Impl.Dsa.PPC64LE.ProbablePrime.layout bits).scratch, r.1 + r.2 ≤ 8 * wWords pL) ∧
      (Impl.Dsa.PPC64LE.ProbablePrime.layout bits).candidate +
        (Impl.Dsa.PPC64LE.ProbablePrime.layout bits).bits / 8 ≤ 8 * wWords pL ∧
      wB pL + (Impl.Dsa.PPC64LE.ProbablePrime.layout bits).candidate < 2 ^ 15 := by
  simp only [Impl.Dsa.PPC64LE.ProbablePrime.layout, List.mem_singleton, forall_eq,
    Impl.Dsa.PPC64LE.ProbablePrime.saveOff, Impl.Dsa.PPC64LE.ProbablePrime.keyOff] at h ⊢
  omega_using [h, hc, h15]

/-- A geometry's proofs, from its facts that do not depend on the call. -/
theorem genOk {g : Geo} {HO : HashOk g.G} {pL qL : Nat} {G : GP} (hex : ∃ σ, CIn 176 σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) (gp : g.pLen = pL) (gq : g.qLen = qL)
    (okq : PrimeOk (Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * qL)) g.qCode)
    (okp : PrimeOk (Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * pL)) g.pCode)
    (hqc : g.qCand = 0) (hpc : g.pCand = 0)
    (lq : Impl.Dsa.PPC64LE.ProbablePrime.keyOff + 8 * Impl.Dsa.PPC64LE.ProbablePrime.keyWords (8 * qL) ≤
      8 * wWords pL)
    (lp : Impl.Dsa.PPC64LE.ProbablePrime.keyOff + 8 * Impl.Dsa.PPC64LE.ProbablePrime.keyWords (8 * pL) ≤
      8 * wWords pL)
    (hcq : 8 * qL / 8 ≤ 8 * wWords pL) (hcp : 8 * pL / 8 ≤ 8 * wWords pL) (h15 : wB pL < 2 ^ 15)
    (gcert : CertC pL qL) (hck : CheckOk g.checkCode) (hk4 : 4 * g.G.k = qL)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * qL) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qL) bs).length = 8 * qL) :
    GenOk G g HO (Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * qL))
      (Impl.Dsa.PPC64LE.ProbablePrime.layout (8 * pL)) := by
  obtain ⟨σ, pre, rfl⟩ := hex
  subst hp hq
  obtain ⟨qs, qr, qf, q15⟩ := lay_ok _ _ lq hcq h15
  obtain ⟨ps, pr, pf, p15⟩ := lay_ok _ _ lp hcp h15
  exact {
    okq, okp, gcert, hck, hk4, hH, hlen
    qlay := ⟨rfl, hqc.symm, qs, qr, qf, q15⟩
    lay := ⟨rfl, hpc.symm, ps, pr, pf, p15⟩
    hlq := pre.lens
    hp := gp
    hq := gq
    hwl := by simp [mkG, Spec.Rsa.bytesAt]
    h64 := BitVec.isLt _
    hqL := rfl
    k0 := pre.seeds }

def geo1 (v : RoundImpl) (ck : Prog isa) : Geo := geo 128 20 sha1 v ck
def geo2 (v : RoundImpl) (ck : Prog isa) : Geo := geo 256 32 sha256 v ck
def geo3 (v : RoundImpl) (ck : Prog isa) : Geo := geo 384 32 sha256 v ck

theorem cert1 : CertC 128 20 := ⟨_, by taint_decide_rel, by rfl⟩
theorem cert2 : CertC 256 32 := ⟨_, by taint_decide_rel, by rfl⟩
theorem cert3 : CertC 384 32 := ⟨_, by taint_decide_rel, by rfl⟩

def geoOk1 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo1 v ck) 128 20 where
  HO := sha1Ok
  Lq := Impl.Dsa.PPC64LE.ProbablePrime.layout 160
  Lp := Impl.Dsa.PPC64LE.ProbablePrime.layout 1024
  ok _ hex hp hq := genOk hex hp hq rfl rfl (primeOk v 160) (primeOk v 1024) rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) cert1 hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha1.hash bs).length = _; rw [sha1_length])
  hlb := by exact (by decide : Proof.Sha1.md.lenBytes 20 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 20 / 256), BitVec.ofNat 8 (8 * 20 % 256)])

def geoOk2 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo2 v ck) 256 32 where
  HO := sha256Ok
  Lq := Impl.Dsa.PPC64LE.ProbablePrime.layout 256
  Lp := Impl.Dsa.PPC64LE.ProbablePrime.layout 2048
  ok _ hex hp hq := genOk hex hp hq rfl rfl (primeOk v 256) (primeOk v 2048) rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) cert2 hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length])
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])

def geoOk3 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo3 v ck) 384 32 where
  HO := sha256Ok
  Lq := Impl.Dsa.PPC64LE.ProbablePrime.layout 256
  Lp := Impl.Dsa.PPC64LE.ProbablePrime.layout 3072
  ok _ hex hp hq := genOk hex hp hq rfl rfl (primeOk v 256) (primeOk v 3072) rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) cert3 hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length])
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])

/-- `vg_dsa_parameter_search` over the round `v` and the check `ck` meets
its contract. -/
theorem params_verified (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) :
    Verified target (code (geo1 v ck) (geo2 v ck) (geo3 v ck))
      (Spec.Dsa.parameterSearchContract (abi.withConsts Impl.RsaKeyGen.TrialTable32.consts) 176) :=
  search_verified (geoOk1 v hck) (geoOk2 v hck) (geoOk3 v hck)

/-- `vg_dsa_check_parameters`, which uses no stack. -/
theorem checkOk : CheckOk Impl.Dsa.PPC64LE.Params.checkParameters :=
  ⟨Proof.Dsa.PPC64LE.checkParameters_verified, by decide⟩

/-- The geometries with `vg_dsa_check_parameters` as the check. -/
def gen1 (v : RoundImpl) : Geo := geo1 v Impl.Dsa.PPC64LE.Params.checkParameters
def gen2 (v : RoundImpl) : Geo := geo2 v Impl.Dsa.PPC64LE.Params.checkParameters
def gen3 (v : RoundImpl) : Geo := geo3 v Impl.Dsa.PPC64LE.Params.checkParameters

/-- `vg_dsa_parameter_search` over the round `v` meets its contract. -/
theorem search_params (v : RoundImpl) :
    Verified target (code (gen1 v) (gen2 v) (gen3 v))
      (Spec.Dsa.parameterSearchContract (abi.withConsts Impl.RsaKeyGen.TrialTable32.consts) 176) :=
  params_verified v checkOk

end VG.Proof.Dsa.PPC64LE.Gen
