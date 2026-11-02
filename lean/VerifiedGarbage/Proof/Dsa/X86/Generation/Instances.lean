module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashInst
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Verified
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.StackUse
public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCT

/-! # The three geometries, for every SHA-1, SHA-256 and Miller–Rabin backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.Generation

/-- The geometry of `(pLen, qLen)`, hashing with `H` from `iv` and testing
with the probable-prime functions of the Miller–Rabin backend `v`. -/
def geo (pLen qLen : Nat) (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (v : RoundImpl) : Geo where
  pLen := pLen
  qLen := qLen
  e := (8 * pLen - 8 * qLen) / 32 + 1
  H := H
  iv := iv
  qName := s!"vg_dsa_probable_prime_{(Impl.Dsa.X86.ProbablePrime.layout (8 * qLen)).bits}" ++ v.suffix
  qCode := Impl.Dsa.X86.ProbablePrime.code (8 * qLen) montName montCode v.name v.code
  pName := s!"vg_dsa_probable_prime_{(Impl.Dsa.X86.ProbablePrime.layout (8 * pLen)).bits}" ++ v.suffix
  pCode := Impl.Dsa.X86.ProbablePrime.code (8 * pLen) montName montCode v.name v.code
  checkName := "vg_dsa_check_parameters"
  checkCode := Impl.Dsa.X86.Generate.checkParameters

theorem check_noSp : NoSp Impl.Dsa.X86.Generate.checkParameters := NoSp.of_all (by decide +kernel)

theorem check_stack : stackUse Impl.Dsa.X86.Generate.checkParameters ≤ 108 := by decide +kernel

/-- The geometry `(pLen, qLen)` is one the proofs support. -/
def geoOk {pLen qLen : Nat} {H : Impl.Pbkdf2.Md.X86.Hash} {iv : List (BitVec 32)} (v : RoundImpl)
    (hash : HashOk H iv) (lengths : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32))
    (N : H.N = qLen) (seedHash : ∀ m, hash.ok.hH.SH.H.hash m = Spec.Dsa.seedHash (8 * qLen) m)
    (qWide : 64 ≤ 8 * qLen := by decide) (qNarrow : 8 * qLen ≤ 4096 := by decide)
    (qWhole : 8 * qLen % 32 = 0 := by decide)
    (pWide : 64 ≤ 8 * pLen := by decide) (pNarrow : 8 * pLen ≤ 4096 := by decide)
    (pWhole : 8 * pLen % 32 = 0 := by decide)
    (prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (scr .ebx sState ++ ivStore iv ++
        Impl.Pbkdf2.Md.X86.storeW .ebx (H.N + qLen) (padBytes qLen) ((64 - qLen) / 4) ++
        [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))] ++ scr .ebp sHScr)) fun _ _ => True)
    (outCt : ∀ dst, RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (scr .ebx sState ++ scr .eax dst ++ H.out)) fun _ _ => True)
    (outNoSp : ∀ i ∈ H.out, Taint.clobbers i .esp = false) :
    GeoOk (geo pLen qLen H iv v) where
  lengths := lengths
  hash := hash
  N := N
  seedHash := seedHash
  e := rfl
  qv := ProbablePrime.verified VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack v.verified v.noSp
    v.stack (8 * qLen) qWide qNarrow qWhole
  qNoSp := ProbablePrime.code_noSp compact_noSp v.noSp _ _ _
  qStack := ProbablePrime.code_stack compact_stack v.stack _ _ _
  pv := ProbablePrime.verified VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack v.verified v.noSp
    v.stack (8 * pLen) pWide pNarrow pWhole
  pNoSp := ProbablePrime.code_noSp compact_noSp v.noSp _ _ _
  pStack := ProbablePrime.code_stack compact_stack v.stack _ _ _
  cv := Proof.Dsa.X86.checking_verified
  cNoSp := check_noSp
  cStack := check_stack
  prepCt := prepCt
  outCt := outCt
  outNoSp := outNoSp

/-- 1024/160, with SHA-1. -/
abbrev geo1 (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : Geo :=
  geo 128 20 (Proof.Pbkdf2.Md.X86.sha1M v1.stream v1.cmpN v1.cmpC) Spec.Sha1.H0.toList v

/-- 2048/256 or 3072/256, with SHA-256. -/
abbrev geo256 (pLen : Nat) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : Geo :=
  geo pLen 32 (Proof.Pbkdf2.Md.X86.sha256M v256.stream v256.cmpN v256.cmpC) Spec.Sha256.H0.toList v

theorem sha1_prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore Spec.Sha1.H0.toList ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (20 + 20) (padBytes 20) ((64 - 20) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 20))] : List Instr) ++ scr .ebp sHScr)) fun _ _ => True :=
  (erased_relCT _ _ (.block []) rfl rfl rfl (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha256_prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore Spec.Sha256.H0.toList ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (32 + 32) (padBytes 32) ((64 - 32) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 32))] : List Instr) ++ scr .ebp sHScr)) fun _ _ => True :=
  (erased_relCT _ _ (.block []) rfl rfl rfl (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha1_outCt (dst : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha1.X86.Stream.params.out)) fun _ _ => True :=
  (erased_relCT (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha1.X86.Stream.params.out))
    (.block (scr .ebx sState ++ scr .eax 0 ++ Impl.Sha1.X86.Stream.params.out)) (.block []) rfl rfl rfl
    (τ := τr [.esp, .edi]) (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha256_outCt (dst : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha256.X86.Stream.params.out)) fun _ _ => True :=
  (erased_relCT (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha256.X86.Stream.params.out))
    (.block (scr .ebx sState ++ scr .eax 0 ++ Impl.Sha256.X86.Stream.params.out)) (.block []) rfl rfl
    rfl (τ := τr [.esp, .edi]) (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha1_outNoSp : ∀ i ∈ Impl.Sha1.X86.Stream.params.out, Taint.clobbers i .esp = false := by decide

theorem sha256_outNoSp : ∀ i ∈ Impl.Sha256.X86.Stream.params.out, Taint.clobbers i .esp = false := by decide

def geo1Ok (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo1 v1 v) :=
  geoOk v (sha1_hashOk v1) (.inl ⟨rfl, rfl⟩) rfl (fun _ => rfl) (prepCt := sha1_prepCt) (outCt := sha1_outCt)
    (outNoSp := sha1_outNoSp)

def geo2Ok (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo256 256 v256 v) :=
  geoOk v (sha256_hashOk v256) (.inr (.inl ⟨rfl, rfl⟩)) rfl (fun _ => rfl) (prepCt := sha256_prepCt)
    (outCt := sha256_outCt) (outNoSp := sha256_outNoSp)

def geo3Ok (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo256 384 v256 v) :=
  geoOk v (sha256_hashOk v256) (.inr (.inr ⟨rfl, rfl⟩)) rfl (fun _ => rfl) (prepCt := sha256_prepCt)
    (outCt := sha256_outCt) (outNoSp := sha256_outNoSp)

end VG.Proof.Dsa.X86.Generation
