module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Verified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Sha1.Arm.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
public import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.GPart
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.Arm
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Impl.Dsa.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! ### `Dsa.Arm.Gen.HashInst`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: SHA-1 and SHA-256

The two hash functions of parameter generation (`Impl.Dsa.Arm.Generation.sha1`,
`sha256`) as `HashOk`: their streaming instances, their compression
functions' proofs, and the hash of a message of fewer than 56 bytes as the
compression of its one padded block (`hash_blk`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation

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

def sha1Ok : HashOk sha1 where
  P := Impl.Sha1.Arm.Stream.params
  md := Proof.Sha1.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := rfl
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha1.Arm.Stream.callee
  ct := Proof.Sha1.Arm.compress_verified.2.1
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
  cert1 L := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
    (.block (scr 128 .r0 sState ++ ivStore sha1.iv ++ scr 128 .r1 sMsg ++ scr 128 .r3 sA)), by kernel_rfl⟩
  cert3 L dst := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
    (.block (scr 128 .r6 192 ++ VG.Impl.MdStream.Arm.out32 5 true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (128 / 4)))])),
    by kernel_rfl⟩

def sha256Ok : HashOk sha256 where
  P := Impl.Sha256.Arm.Stream.params
  md := Proof.Sha256.md
  hB := rfl
  hL := rfl
  hN := rfl
  hso := rfl
  hk := by decide
  hk0 := by decide
  ivLen := rfl
  callee := Proof.Sha256.Arm.Stream.callee
  ct := Proof.Sha256.Arm.compress_verified.2.1
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
  cert1 L := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
    (.block (scr 128 .r0 sState ++ ivStore sha256.iv ++ scr 128 .r1 sMsg ++ scr 128 .r3 sA)), by kernel_rfl⟩
  cert3 L dst := ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r8])
    (.block (scr 128 .r6 192 ++ VG.Impl.MdStream.Arm.out32 8 true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (128 / 4)))])),
    by kernel_rfl⟩

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Prime.Stack`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7: the stack it uses

The 32-byte allocation and the 56 bytes of registers pushed, then the round's
own stack (`code_stack`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Dsa.Arm.ProbablePrime
open VG.Impl.Rsa.Arm.Keys (seqs)
open VG.Arm.FrameStack (armStack)

theorem seqs_le {B : Nat} : ∀ l : List (Prog isa), (∀ c ∈ l, armStack c ≤ B) → armStack (seqs l) ≤ B
  | [], _ => Nat.zero_le _
  | [c], h => h c (by simp)
  | c :: d :: l, h => by
    simp only [seqs, armStack]
    exact Nat.max_le.mpr ⟨h c (by simp), seqs_le (d :: l) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem z_loadC : ∀ c ∈ loadC, armStack c = 0 := by decide
theorem z_trial : ∀ c ∈ VG.Impl.RsaKeyGen.Arm.Candidate.trial, armStack c = 0 := by decide
theorem z_exp : ∀ c ∈ VG.Impl.RsaKeyGen.Arm.Candidate.expSetup, armStack c = 0 := by decide
theorem z_wl : ∀ c ∈ witnessLoad ++ witnessFix, armStack c = 0 := by decide

theorem z_le {c : Prog isa} {B : Nat} (h : armStack c = 0) : armStack c ≤ B := h ▸ Nat.zero_le _

theorem body_stack (name : String) (round : Prog isa) : armStack (body name round) ≤ armStack round := by
  unfold body
  refine seqs_le _ fun c hc => ?_
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with (hc | hc) | rfl
  · exact z_le (z_loadC c hc)
  · exact z_le (z_trial c hc)
  refine Nat.max_le.mpr ⟨?_, Nat.zero_le _⟩
  unfold mrPart
  refine seqs_le _ fun c hc => ?_
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, false_or] at hc
  rcases hc with rfl | hc | rfl | rfl | rfl | rfl
  · exact z_le (by decide)
  · exact z_le (z_exp c hc)
  · exact z_le (by decide)
  · exact z_le (by decide)
  · unfold millerRabin mrBody
    simp only [armStack, seqs, Nat.zero_max, Nat.max_zero]
    refine seqs_le _ fun c hc => ?_
    simp only [List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · exact z_le (z_wl c (List.mem_append_left _ hc))
    · exact z_le (z_wl c (List.mem_append_right _ hc))
    · simp only [VG.Impl.RsaKeyGen.Arm.Candidate.mrCall, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact Nat.le_refl _
      · exact z_le (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact z_le (by decide)
      · exact z_le (by decide)
  · exact z_le (by decide)

theorem code_stack (name : String) (round : Prog isa) :
    armStack (code name round) ≤ 88 + armStack round := by
  have := body_stack name round
  simp only [Impl.Dsa.Arm.ProbablePrime.code, armStack, List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero]
  omega_using [this]

end VG.Proof.Dsa.Arm.Prime

end

end


/-! # DSA parameter generation on ARMv7: the three geometries

`geo pLen qLen G v`: the geometry of `(pLen, qLen)`, hashing with `G` and
testing with the probable-prime functions over the Miller–Rabin round `v`,
exponentiating with `vg_dsa_pow_{pLen/8}_{e}`; `geoOk`: its proofs, for
every call with those lengths; `params_verified`: the three of them meet
the contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Impl.Mont.Arm.Dynamic (modS baseS expS resS contextBytes)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)
open VG.Impl.Rsa.Arm.Keys (ptr)

variable {umaal : Bool}

/-- The geometry of `(pLen, qLen)`, hashing with `G`, testing with the round `v`
(`Impl.Dsa.Arm.Fn.geo`). -/
def geo (umaal : Bool) (pLen qLen : Nat) (G : Hash) (v : RoundImpl) : Geo :=
  Impl.Dsa.Arm.Fn.geo umaal pLen qLen G v.suffix v.code

theorem primeOk (v : RoundImpl) (bits : Nat) (hb : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes := by decide) :
    PrimeOk bits (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) :=
  ⟨VG.Proof.Dsa.Arm.Prime.prime_verified v,
    (VG.Proof.Dsa.Arm.Prime.code_stack v.name v.code).trans (by have := v.stack; omega_using [this]), hb⟩

theorem powOk (n e : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) (he : 0 < e := by decide)
    (hen : e ≤ 2 * n := by decide) (hs : FrameStack.armStack (Impl.Dsa.Arm.Pow.body umaal n e) ≤ 176 := by decide) :
    PowOk n e (Impl.Dsa.Arm.Pow.body umaal n e) :=
  ⟨Proof.Dsa.Arm.Pow.powArm_correct hn hn48 he hen, Proof.Dsa.Arm.Pow.powArm_ct n e hn hn48, hs⟩

/-- A geometry's proofs, from its facts that do not depend on the call. -/
theorem genOk {g : Geo} {HO : HashOk g.G} {n pL qL : Nat} {G : GP} (hex : ∃ σ, CIn σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) (okq : PrimeOk (8 * qL) g.qCode) (okp : PrimeOk (8 * pL) g.pCode)
    (certs : PArithCerts pL qL) (gcerts : GStepCerts g) (pow : PowOk n g.e g.powCode) (gp : g.pLen = pL)
    (gq : g.qLen = qL) (hk4 : 4 * g.G.k = qL) (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * qL) m)
    (hsize : keyOff + 8 * keyWords (8 * pL) ≤ wa pL) (hsizeq : keyOff + 8 * keyWords (8 * qL) ≤ wa pL)
    (hb8 : 8 * qL / 8 ≤ wa pL) (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qL) bs).length = 8 * qL)
    (hck : g.checkCode = VG.Impl.Dsa.Arm.Generate.checkParameters umaal) (hn : 8 * n = pL) (hpm : g.powMod = modS n)
    (hpb : g.powBase = baseS n) (hpe : g.powExp = expS n) (hpr : g.powRes = resS n)
    (hctx : contextBytes n ≤ wa pL) (he4 : 4 * g.e ≤ 8 * n) (he0 : 0 < g.e)
    (he : 8 * pL - 8 * qL + 1 ≤ 32 * g.e) : GenOk G g HO n := by
  obtain ⟨σ, pre, rfl⟩ := hex
  subst hp hq
  exact {
    okq, okp, certs, gcerts, pow, hk4, hH, hsize, hsizeq, hb8, hlen, hn, hpm, hpb, hpe, hpr, hctx, he4,
    he0, he
    hck := ⟨_, hck⟩
    hlq := pre.lens
    hp := gp
    hq := gq
    hwl := by simp [mkG, Spec.Rsa.bytesAt]
    h32 := BitVec.isLt _
    hqL := rfl
    k0 := pre.seeds }

theorem sha1_length (bs : List Byte) : (Spec.Sha1.hash bs).length = 20 := by
  rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _

theorem sha256_length (bs : List Byte) : (Spec.Sha256.hash bs).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

/-- The copies around the exponentiation, for `(pLen, n)`. -/
theorem gStepCerts {g : Geo} (pL n e : Nat) (hp : g.pLen = pL) (he : g.e = e) (hm : g.powMod = modS n)
    (hb : g.powBase = baseS n) (hx : g.powExp = expS n) (hr : g.powRes = resS n)
    (mod : Cert7 (copyN (scr pL .r0 (sA + modS n)) (ptr .r1 aP) pL))
    (base : Cert7 (copyN (scr pL .r0 (sA + baseS n)) (ptr .r1 aH) pL))
    (exp : Cert7 (copyN (scr pL .r0 (sA + expS n)) (ptr .r1 aE) (4 * e)))
    (res : Cert7 (copyN (ptr .r0 aG) (scr pL .r1 (sA + resS n)) pL))
    (st : Cert7 (storeBE pL aG sG pL)) : GStepCerts g := by
  rw [← hp, ← hm, ← hb, ← hx, ← hr, ← he] at *
  exact ⟨mod, base, exp, res, st⟩

def geo1 (umaal : Bool) (v : RoundImpl) : Geo := geo umaal 128 20 sha1 v
def geo2 (umaal : Bool) (v : RoundImpl) : Geo := geo umaal 256 32 sha256 v
def geo3 (umaal : Bool) (v : RoundImpl) : Geo := geo umaal 384 32 sha256 v

theorem certs1 (v : RoundImpl) : GStepCerts (geo1 umaal v) :=
  gStepCerts 128 16 28 rfl rfl rfl rfl rfl rfl
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 128 .r0 (sA + modS 16)) (ptr .r1 aP) 128), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 128 .r0 (sA + baseS 16)) (ptr .r1 aH) 128), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 128 .r0 (sA + expS 16)) (ptr .r1 aE) (4 * 28)), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (ptr .r0 aG) (scr 128 .r1 (sA + resS 16)) 128), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 128 aG sG 128), by kernel_rfl⟩

theorem certs2 (v : RoundImpl) : GStepCerts (geo2 umaal v) :=
  gStepCerts 256 32 57 rfl rfl rfl rfl rfl rfl
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 256 .r0 (sA + modS 32)) (ptr .r1 aP) 256), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 256 .r0 (sA + baseS 32)) (ptr .r1 aH) 256), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 256 .r0 (sA + expS 32)) (ptr .r1 aE) (4 * 57)), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (ptr .r0 aG) (scr 256 .r1 (sA + resS 32)) 256), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 256 aG sG 256), by kernel_rfl⟩

theorem certs3 (v : RoundImpl) : GStepCerts (geo3 umaal v) :=
  gStepCerts 384 48 89 rfl rfl rfl rfl rfl rfl
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 384 .r0 (sA + modS 48)) (ptr .r1 aP) 384), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 384 .r0 (sA + baseS 48)) (ptr .r1 aH) 384), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (scr 384 .r0 (sA + expS 48)) (ptr .r1 aE) (4 * 89)), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9])
      (copyN (ptr .r0 aG) (scr 384 .r1 (sA + resS 48)) 384), by kernel_rfl⟩
    ⟨VG.Taint.hintOfSize VG.Arm.taint 4096 (Taint.ofRegs [.r7, .r8, .r9]) (storeBE 384 aG sG 384), by kernel_rfl⟩

def geoOk1 (umaal : Bool) (v : RoundImpl) : GeoOk (geo1 umaal v) 128 20 where
  HO := sha1Ok
  n := 16
  ok _ hex hp hq := genOk hex hp hq (primeOk v 160) (primeOk v 1024) pArithCerts_128 (certs1 v) (powOk 16 28 (hs := by cases umaal <;> decide))
    rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide) (fun bs => by
      show 8 * (Spec.Sha1.hash bs).length = _; rw [sha1_length]) rfl rfl rfl rfl rfl rfl (by decide)
    (by exact (by decide : 4 * 28 ≤ 8 * 16)) (by exact (by decide : 0 < 28))
    (by exact (by decide : 8 * 128 - 8 * 20 + 1 ≤ 32 * 28))
  hlb := by exact (by decide : Proof.Sha1.md.lenBytes 20 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 20 / 256), BitVec.ofNat 8 (8 * 20 % 256)])

def geoOk2 (umaal : Bool) (v : RoundImpl) : GeoOk (geo2 umaal v) 256 32 where
  HO := sha256Ok
  n := 32
  ok _ hex hp hq := genOk hex hp hq (primeOk v 256) (primeOk v 2048) pArithCerts_256 (certs2 v) (powOk 32 57 (hs := by cases umaal <;> decide))
    rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length]) rfl rfl rfl rfl rfl rfl (by decide)
    (by exact (by decide : 4 * 57 ≤ 8 * 32)) (by exact (by decide : 0 < 57))
    (by exact (by decide : 8 * 256 - 8 * 32 + 1 ≤ 32 * 57))
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])

def geoOk3 (umaal : Bool) (v : RoundImpl) : GeoOk (geo3 umaal v) 384 32 where
  HO := sha256Ok
  n := 48
  ok _ hex hp hq := genOk hex hp hq (primeOk v 256) (primeOk v 3072) pArithCerts_384 (certs3 v) (powOk 48 89 (hs := by cases umaal <;> decide))
    rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length]) rfl rfl rfl rfl rfl rfl (by decide)
    (by exact (by decide : 4 * 89 ≤ 8 * 48)) (by exact (by decide : 0 < 89))
    (by exact (by decide : 8 * 384 - 8 * 32 + 1 ≤ 32 * 89))
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])

/-- The pairs the parameter search is emitted for, best first: the arithmetic and the
Miller–Rabin round for the same CPUs. Any other pair needs the features of one of these,
which runs both with them. -/
def searchPairs : List (Proof.Variants.DsaArithmetic.Arm.Variant × RoundImpl) :=
  Proof.Variants.DsaArithmetic.Arm.variants.flatMap fun a =>
    Proof.Variants.MillerRabin.Arm.variants.filterMap fun r => if a.suffix == r.suffix then some (a, r) else none

/-- `vg_dsa_parameter_search` over the round `v` meets its contract. -/
theorem search_params (v : RoundImpl) :
    Verified target (code (geo1 umaal v) (geo2 umaal v) (geo3 umaal v)) (Spec.Dsa.parameterSearchContract abi 304) :=
  search_verified (geoOk1 umaal v) (geoOk2 umaal v) (geoOk3 umaal v)

end VG.Proof.Dsa.Arm.Gen
