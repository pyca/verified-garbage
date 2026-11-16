module

public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Verified
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.Attempt
public import VerifiedGarbage.Proof.Dsa.RISCV64.PSearch.HashInst
public import VerifiedGarbage.Proof.Dsa.RISCV64.Prime.Verified
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsVerified
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Backend

/-! # DSA parameter search on RISC-V: the three widths

`geo pLen qLen G v ck`: the width `(pLen, qLen)`, hashing with `G`, testing
with the probable-prime functions over the Miller–Rabin round `v`, and
checking the domain with `ck`; `geoOk1`–`geoOk3`: their proofs, for every
call with those lengths; `params_verified`: `vg_dsa_parameter_search` over
them and `vg_dsa_check_parameters` meets its contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.PSearch
open VG VG.RISCV64
open VG.Impl.Dsa.RISCV64.ParameterSearch
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

/-- The width `(pLen, qLen)`, hashing with `G`, testing with the round `v`,
checking with `ck`. -/
def geo (pLen qLen : Nat) (G : Hash) (v : RoundImpl) (ck : Prog isa) : Geo where
  pLen := pLen
  qLen := qLen
  G := G
  qName := s!"vg_dsa_probable_prime_{8 * qLen}" ++ v.suffix
  qCode := Impl.Dsa.RISCV64.ProbablePrime.code (8 * qLen) v.name v.code
  pName := s!"vg_dsa_probable_prime_{8 * pLen}" ++ v.suffix
  pCode := Impl.Dsa.RISCV64.ProbablePrime.code (8 * pLen) v.name v.code
  checkName := "vg_dsa_check_parameters"
  checkCode := ck

theorem primeOk (v : RoundImpl) (bits : Nat) (hb : VG.Proof.Dsa.RISCV64.Prime.Bits bits := by decide) :
    PrimeOk (Impl.Dsa.RISCV64.ProbablePrime.layout bits) (Impl.Dsa.RISCV64.ProbablePrime.code bits v.name v.code) :=
  ⟨VG.Proof.Dsa.RISCV64.Prime.verified v bits hb, VG.Proof.Dsa.RISCV64.Prime.stack_le v bits⟩

/-- A test's layout in the working space of a `pLen`-byte search. -/
theorem primeLay_ok (pL bits : Nat)
    (h : Impl.Dsa.RISCV64.ProbablePrime.keyOff + 8 * Impl.Dsa.RISCV64.ProbablePrime.keyWords bits ≤ 256 * pL) :
    (Impl.Dsa.RISCV64.ProbablePrime.layout bits).size ≤ 256 * pL ∧
      ∀ r ∈ (Impl.Dsa.RISCV64.ProbablePrime.layout bits).scratch, r.1 + r.2 ≤ 256 * pL := by
  simp only [Impl.Dsa.RISCV64.ProbablePrime.layout, List.mem_singleton, forall_eq,
    Impl.Dsa.RISCV64.ProbablePrime.saveOff, Impl.Dsa.RISCV64.ProbablePrime.keyOff] at h ⊢
  omega

/-- `vg_dsa_check_parameters`, which uses no stack. -/
theorem checkOk : CheckOk Impl.Dsa.RISCV64.Params.checkParameters :=
  ⟨Proof.Dsa.RISCV64.checkParameters_verified, by decide⟩

/-- A width's attempt, from its facts that do not depend on the call. -/
theorem aOk {g : Geo} {HO : HashOk g.G} {pL qL : Nat} {G : GP} (hex : ∃ σ, CIn STK0 σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) (gp : g.pLen = pL) (gq : g.qLen = qL)
    (okq : PrimeOk (Impl.Dsa.RISCV64.ProbablePrime.layout (8 * qL)) g.qCode)
    (okp : PrimeOk (Impl.Dsa.RISCV64.ProbablePrime.layout (8 * pL)) g.pCode)
    (lq : Impl.Dsa.RISCV64.ProbablePrime.keyOff + 8 * Impl.Dsa.RISCV64.ProbablePrime.keyWords (8 * qL) ≤ 256 * pL)
    (lp : Impl.Dsa.RISCV64.ProbablePrime.keyOff + 8 * Impl.Dsa.RISCV64.ProbablePrime.keyWords (8 * pL) ≤ 256 * pL)
    (hck : CheckOk g.checkCode) (hk4 : 4 * g.G.k = qL)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * qL) m)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qL) bs).length = 8 * qL) :
    AOk G g HO (Impl.Dsa.RISCV64.ProbablePrime.layout (8 * qL)) (Impl.Dsa.RISCV64.ProbablePrime.layout (8 * pL)) := by
  obtain ⟨σ, pre, rfl⟩ := hex
  have hw := pre.lens
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hw
  subst hp hq
  obtain ⟨qs, qr⟩ := primeLay_ok _ _ lq
  obtain ⟨ps, pr⟩ := primeLay_ok _ _ lp
  exact {
    okq, okp, hck, hk4, hH, hlen
    qBits := rfl
    qCand := rfl
    qSize := qs
    qScr := qr
    lay := ⟨rfl, rfl, ps, pr⟩
    hw := by omega
    hp := gp
    hq := gq
    hwl := by simp [mkG, Spec.Rsa.bytesAt] }

def geo1 (v : RoundImpl) (ck : Prog isa) : Geo := geo 128 20 sha1 v ck
def geo2 (v : RoundImpl) (ck : Prog isa) : Geo := geo 256 32 sha256 v ck
def geo3 (v : RoundImpl) (ck : Prog isa) : Geo := geo 384 32 sha256 v ck

def geoOk1 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo1 v ck) 128 20 where
  HO := sha1Ok
  hgp := rfl
  hgq := rfl
  hq := by decide
  hlb := by exact (by decide : Proof.Sha1.md.lenBytes 20 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 20 / 256), BitVec.ofNat 8 (8 * 20 % 256)])
  att _ hex hp hq := attempt_ok (g := geo1 v ck) sha1Ok (aOk (g := geo1 v ck) (HO := sha1Ok) (pL := 128) (qL := 20)
    hex hp hq rfl rfl (primeOk v 160) (primeOk v 1024) (by decide)
    (by decide) hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha1.hash bs).length = _; rw [sha1_length]))

def geoOk2 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo2 v ck) 256 32 where
  HO := sha256Ok
  hgp := rfl
  hgq := rfl
  hq := by decide
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])
  att _ hex hp hq := attempt_ok (g := geo2 v ck) sha256Ok (aOk (g := geo2 v ck) (HO := sha256Ok) (pL := 256) (qL := 32)
    hex hp hq rfl rfl (primeOk v 256) (primeOk v 2048) (by decide)
    (by decide) hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length]))

def geoOk3 (v : RoundImpl) {ck : Prog isa} (hck : CheckOk ck) : GeoOk (geo3 v ck) 384 32 where
  HO := sha256Ok
  hgp := rfl
  hgq := rfl
  hq := by decide
  hlb := by exact (by decide : Proof.Sha256.md.lenBytes 32 =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * 32 / 256), BitVec.ofNat 8 (8 * 32 % 256)])
  att _ hex hp hq := attempt_ok (g := geo3 v ck) sha256Ok (aOk (g := geo3 v ck) (HO := sha256Ok) (pL := 384) (qL := 32)
    hex hp hq rfl rfl (primeOk v 256) (primeOk v 3072) (by decide)
    (by decide) hck rfl (fun _ => rfl) (fun bs => by
      show 8 * (Spec.Sha256.hash bs).length = _; rw [sha256_length]))

/-- The widths with `vg_dsa_check_parameters` as the check. -/
def gen1 (v : RoundImpl) : Geo := geo1 v Impl.Dsa.RISCV64.Params.checkParameters
def gen2 (v : RoundImpl) : Geo := geo2 v Impl.Dsa.RISCV64.Params.checkParameters
def gen3 (v : RoundImpl) : Geo := geo3 v Impl.Dsa.RISCV64.Params.checkParameters

/-- `vg_dsa_parameter_search` over the round `v` meets its contract. -/
theorem params_verified (v : RoundImpl) : Verified target (code (gen1 v) (gen2 v) (gen3 v)) searchK :=
  search_verified (geoOk1 v checkOk) (geoOk2 v checkOk) (geoOk3 v checkOk)

end VG.Proof.Dsa.RISCV64.PSearch
