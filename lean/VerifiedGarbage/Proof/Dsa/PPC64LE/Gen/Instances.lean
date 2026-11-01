module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.HashInst
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Satisfiable
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Verified

/-! # DSA parameter generation on PPC64LE: the three geometries

`geo pLen qLen G v ck`: the geometry of `(pLen, qLen)`, hashing with `G`,
testing with the probable-prime functions over the Miller–Rabin round `v`,
whose candidates are at the start of their working space, and checking the
domain with `ck`; `geoOk`: its proofs, for every call with those lengths;
`params_verified`: the three of them meet the contract, and `generate_params`
with `vg_dsa_check_parameters` as the check.
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
  omega

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
    hsb := by simp [mkG, Spec.Rsa.bytesAt]
    hwl := by simp [mkG, Spec.Rsa.bytesAt]
    hhsb := by simp [mkG, Spec.Rsa.bytesAt]
    hmod := pre.hsMod
    h64 := BitVec.isLt _
    smod := pre.seedsMod
    s64 := BitVec.isLt _ }

def geo1 (v : RoundImpl) (ck : Prog isa) : Geo := geo 128 20 sha1 v ck
def geo2 (v : RoundImpl) (ck : Prog isa) : Geo := geo 256 32 sha256 v ck
def geo3 (v : RoundImpl) (ck : Prog isa) : Geo := geo 384 32 sha256 v ck

theorem cert1 : CertC 128 20 := ⟨_, by taint_decide⟩
theorem cert2 : CertC 256 32 := ⟨_, by taint_decide⟩
theorem cert3 : CertC 384 32 := ⟨_, by taint_decide⟩

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

/-- `vg_dsa_generate_parameters` over the round `v` and the check `ck` meets
its contract. -/
theorem params_verified (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) :
    Verified target (code (geo1 v ck) (geo2 v ck) (geo3 v ck))
      (Spec.Dsa.generateParametersContract (abi.withConsts Impl.RsaKeyGen.TrialTable32.consts) 176) :=
  generate_verified (geoOk1 v hck) (geoOk2 v hck) (geoOk3 v hck)

/-- `vg_dsa_check_parameters`, which uses no stack. -/
theorem checkOk : CheckOk Impl.Dsa.PPC64LE.Params.checkParameters :=
  ⟨Proof.Dsa.PPC64LE.checkParameters_verified, by decide⟩

/-- The geometries with `vg_dsa_check_parameters` as the check. -/
def gen1 (v : RoundImpl) : Geo := geo1 v Impl.Dsa.PPC64LE.Params.checkParameters
def gen2 (v : RoundImpl) : Geo := geo2 v Impl.Dsa.PPC64LE.Params.checkParameters
def gen3 (v : RoundImpl) : Geo := geo3 v Impl.Dsa.PPC64LE.Params.checkParameters

/-- `vg_dsa_generate_parameters` over the round `v` meets its contract. -/
theorem generate_params (v : RoundImpl) :
    Verified target (code (gen1 v) (gen2 v) (gen3 v))
      (Spec.Dsa.generateParametersContract (abi.withConsts Impl.RsaKeyGen.TrialTable32.consts) 176) :=
  params_verified v checkOk

end VG.Proof.Dsa.PPC64LE.Gen
