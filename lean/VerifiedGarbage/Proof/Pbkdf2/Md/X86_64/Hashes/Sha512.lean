import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The SHA-512 family on x86-64, as Merkle–Damgård hash functions

SHA-384, SHA-512, SHA-512/224 and SHA-512/256, each with an implementation `v`
of their compression function (`Proof/Sha512/X86_64/Variant.lean`), as
variants of `MdHash` (`sha384 v`, …), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/X86_64/`): their streaming code is the generic Merkle–Damgård
code (`Stream.params`), shared by the four, which differ in their initial hash
value `iv` and the size `D` of their digest, the first `D` bytes of the final
hash value. The facts about the code HMAC and PBKDF2 add, which do not depend
on `v`, are checked once for each member (`coreOK`).

`stream v` are the streaming `update` and `finalize` made with `v`, which
the four share: SHA-512's variant (`sha512 v`) carries them, and
`Generic/MdHash/X86_64/Stream.lean` emits them from their `Api`s, named
with its suffix.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha512.X86_64 (Compress)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`, calling the
implementation `v` of the compression function, named with its suffix. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) (v : Compress) :
    Hash where
  P := Impl.Sha512.X86_64.Stream.params
  D := D
  W := I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := initN
  initC := Impl.Sha512.X86_64.Stream.init iv
  updN := Spec.Sha512.updateScratchApi.name ++ v.suffix
  finN := Spec.Sha512.finalizeScratchApi.name ++ v.suffix
  hmacInitN := I.initScratchApi.name ++ v.suffix
  hmacFinN := I.finalizeScratchApi.name ++ v.suffix
  iterN := I.iterateApi.name ++ v.suffix

/-- A member of the family without the functions it calls, the same for
every `v`. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Sha512.X86_64.Stream.params, D, 234, "", .block [], "", .block [], "", "", "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> refine {
      pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
        ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      hinit := {
        pro := ⟨?_, ?_⟩
        argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
        keys := ⟨?_, ?_⟩
        mid := ⟨?_, ?_⟩
        restore := ⟨?_, ?_⟩ }
      hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      pbkMx := ?_
      pbkSp := ?_
      hinitMx := ?_
      hinitSp := ?_
      hinitNs := ?_
      hinitD := ?_
      hfinMx := ?_
      hfinSp := ?_
      hfinNs := ?_
      hfinD := ?_
      hinitXD := ?_
      hfinXD := ?_
      pbkXD := ?_
      iterMx := ?_
      iterSp := ?_
      iterNs := ?_
      iterD := ?_
      updMx := ?_
      updNs := ?_
      updD := ?_
      finMx := ?_
      finNs := ?_
      finD := ?_
      fitI := ?_
      fitF := ?_
  }
  taint_decide_all

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

theorem callees {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (hiv : IVs iv)
    (v : Compress) : Callees (hash I D initN iv v) where
  cMx := v.mxcsr
  cSp := allInstrs_of_all v.spSafe
  cNs := by
    show v.callee.code.allInstrs _ = true
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  cD := v.ok.depth
  iMx := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iSp := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iNs := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  cXD := v.noStack
  iXD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} {v : Compress}
    (C : CoreOK (core (hash I D initN iv v))) (K : Callees (hash I D initN iv v))
    (hR : I.S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, I.S.H.hash m = (Proof.Sha512.md.hash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) : HashOK (hash I D initN iv v) where
  md := Proof.Sha512.md
  dims := Proof.Sha512.X86_64.Stream.dims
  shape := Proof.Sha512.X86_64.Stream.shape
  taints := Proof.Sha512.X86_64.Stream.taints
  comp := v.ok
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  SH := I.S
  iv := iv
  repr _ _ _ := by rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  hB := hB
  hS := hS
  hD := hDs
  hD0 := by show 0 < D; omega
  hDN := by show D ≤ 64; omega
  hD4 := by show D % 4 = 0; omega
  hN4 := by simp only [hash] <;> decide
  hDL := by show D + 16 + 4 ≤ 128; omega
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hso := by simp only [hash] <;> decide
  fits := by show 1328 + 48 + 64 + 128 ≤ 8 * I.scratch; omega
  hW := by show I.scratch ≤ 256; omega
  init := hR ▸ Proof.Sha512.X86_64.Stream.init_verified iv
  initDepth := by rw [K.iD]; decide
  initSp := nosp_of K.iNs
  updMx := Callees.updMx K C
  finMx := Callees.finMx K C
  updSp := Callees.updSp K C
  finSp := Callees.finSp K C
  updDepth := Callees.updD K C
  finDepth := Callees.finD K C

/-- The streaming `update` and `finalize` made with `v`, which the family
shares and which keep their working space in a frame of their own, and
`update_scratch` and `finalize_scratch`, which HMAC's, PBKDF2's and
Ed25519's code calls with theirs. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .r8 (Impl.Sha512.X86_64.Stream.update v.callee)
    contract := Spec.Sha512.updateContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe) },
  { api := Spec.Sha512.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 1384 .rcx (Impl.Sha512.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha512.finalizeContract X86_64.abi (8 + 1384)
    stack := 8 + 1384
    verified := Proof.Sha512.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe) },
  { api := Spec.Sha512.updateScratchApi
    code := Impl.Sha512.X86_64.Stream.update v.callee
    contract := Spec.Sha512.updateScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.updateScratch v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe },
  { api := Spec.Sha512.finalizeScratchApi
    code := Impl.Sha512.X86_64.Stream.finalize v.callee
    contract := Spec.Sha512.finalizeScratchContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.finalizeScratch v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe }]

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Spec.Hmac.sha384I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha384I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Spec.Hmac.sha384I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha384I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Spec.Hmac.sha384I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha384I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 48 234

theorem sha384_satP : ∃ s, (Spec.Hmac.sha384I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha384_satPF :
    ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha384I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384's functions, with the implementation `v` of the compression function. -/
abbrev sha384H (v : Compress) : Hash := hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384 v

theorem sha384K (v : Compress) : Callees (sha384H v) := callees (Or.inl rfl) v

/-- What the proofs know of SHA-384's functions. -/
def sha384OK (v : Compress) : HashOK (sha384H v) :=
  ok sha384_coreOK (sha384K v) rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha384 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 48 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 64 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512_224 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 28 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all

/-- RSASSA-PSS's taint checks of the pieces that depend on the hash function. -/
theorem pss_sha512_256 : Proof.RsaPss.X86_64.PssChecks Impl.Sha512.X86_64.Stream.params 32 := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  taint_decide_all


/-- SHA-384 with the implementation `v` of the compression function, which it
carries for the functions built on SHA-384 alone (`MdHash.sha384`). -/
def sha384 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  { MdHash.of (sha384OK v) sha384_coreOK (sha384K v) ⟨Spec.Mgf1.sha384, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha384 rfl rfl
      sha384_satI sha384_satF sha384_satT sha384_satP (by decide)
      (by
        unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
        exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
      (by
        unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
        exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel)
          (by rw [Curry.apply_const]; trivial))
      (by decide) sha384_satPF
      v.suffix v.features stream with
    sha384 := some v }

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Spec.Hmac.sha512I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Spec.Hmac.sha512I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Spec.Hmac.sha512I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 64 234

theorem sha512_satP : ∃ s, (Spec.Hmac.sha512I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_satPF :
    ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512's functions, with the implementation `v` of the compression function. -/
abbrev sha512H (v : Compress) : Hash := hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512 v

theorem sha512K (v : Compress) : Callees (sha512H v) := callees (Or.inr (Or.inl rfl)) v

/-- What the proofs know of SHA-512's functions. -/
def sha512OK (v : Compress) : HashOK (sha512H v) :=
  ok sha512_coreOK (sha512K v) rfl
    (fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr rfl))) rfl

/-- SHA-512 with the implementation `v` of the compression function, which it
carries for the functions built on SHA-512 alone (`MdHash.sha512`). -/
def sha512 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  { MdHash.of (sha512OK v) sha512_coreOK (sha512K v) ⟨Spec.Mgf1.sha512, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512 rfl rfl
      sha512_satI sha512_satF sha512_satT sha512_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_satPF
    v.suffix v.features stream with
    sha512 := some v }

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Spec.Hmac.sha512_224I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_224I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Spec.Hmac.sha512_224I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_224I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Spec.Hmac.sha512_224I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 28 234

theorem sha512_224_satP : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_224_satPF :
    ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512_224I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

/-- SHA-512/224 with the implementation `v` of the compression function. -/
def sha512_224 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v)) := sha512_224_coreOK
  have K : Callees (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v) := callees (Or.inr (Or.inr (Or.inl rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl) C K ⟨Spec.Mgf1.sha512_224, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_224 rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_224_satPF
    v.suffix v.features stream

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Spec.Hmac.sha512_256I.initScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.sha512_256I, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig, Spec.Hmac.initPre, Spec.Hmac.initPost,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Spec.Hmac.sha512_256I.finalizeScratchContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.sha512_256I, Spec.Hmac.finalizeScratchContract,
    Spec.Hmac.finalizeScratchSig, Spec.Hmac.finalizePost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Spec.Hmac.sha512_256I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 32 234

theorem sha512_256_satP : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2ScratchContract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_256_satPF :
    ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86_64.abi (24 + pbkdf2Frame Spec.Hmac.sha512_256I)).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, pbkdf2Frame, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs, pbkFrameSat, pbkSat] using pbkFrameSat

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with the implementation `v` of the compression function. -/
def sha512_256 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v)) := sha512_256_coreOK
  have K : Callees (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v) := callees (Or.inr (Or.inr (Or.inr rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl) C K ⟨Spec.Mgf1.sha512_256, by simp [mdHashes], fun _ => rfl, rfl⟩ pss_sha512_256 rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP (by decide)
    (by
      unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))
    (by
      unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
      exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))
    (by decide) sha512_256_satPF
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
