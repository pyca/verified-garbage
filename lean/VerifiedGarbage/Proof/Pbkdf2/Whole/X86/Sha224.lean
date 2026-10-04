import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-SHA-224 on x86 (32-bit), the whole derivation, for every backend

The generic proof (`CT.lean`) at SHA-224, for any of SHA-256's backends
(`Proof/Sha256/X86/Variants/Interface.lean`): SHA-224's streaming functions,
HMAC's `init` and `finalize` and PBKDF2's iteration made with the backend,
verified for any backend against the shared contracts
(`Proof.Sha256.X86.Variants.Backend.hmacInit224` and the others), as for
SHA-256 (`Sha256.lean`). The taint checks depend only on the sizes, so they
are evaluated once, for any backend (`sha224Shape`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-224 with the backend `v`, verified. -/
def sha224OKF (v : Backend) : FnsOK v.F224 where
  hH := Proof.Pbkdf2.Stream.X86.sha224OK v.stream
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified v.hmacInit224
  hf := .of_verified v.hmacFin224
  it := .of_verified v.iterate224
  hiSp := v.init224NoSp
  hfSp := v.finalize224NoSp
  itSp := v.iter224NoSp
  hiSU := v.init224Stack
  hfSU := v.finalize224Stack
  itSU := v.iter224Stack
  hWi := show 104 ≤ 104 by decide
  hWf := show 104 ≤ 104 by decide
  hWt := show 104 ≤ 104 by decide
  hWH := show 20 ≤ 104 by decide
  hW := show 104 ≤ 512 by decide
  hDB := show 28 ≤ 64 by decide
  hBS := show 64 ≤ 96 by decide
  fits := show 20 + 2 * 28 + 32 ≤ 4 * 96 by decide

/-- The sizes of `Backend.F224`, which are all the taint checks depend on:
`shapeOf` of every backend's `Backend.F224`, written out, so that the kernel
reduces each side to it field by field rather than comparing the backends'
functions. -/
def sha224Shape : Fns :=
  ⟨⟨64, 96, 28, 32, 20, "", .block [], "", .block [], "", .block []⟩, Spec.Hmac.sha224I.scratch, "", .block [], "",
    .block [], "", .block []⟩

theorem sha224Shape_checks : Checks sha224Shape := by
  refine {
    pro := ⟨?_, ?_⟩
    cmp := ⟨?_, ?_⟩
    hk1 := ⟨?_, ?_⟩
    hk3 := ⟨?_, ?_⟩
    hk5 := ⟨?_, ?_⟩
    hk7 := ⟨?_, ?_⟩
    short := ⟨?_, ?_⟩
    su1 := ⟨?_, ?_⟩
    su3 := ⟨?_, ?_⟩
    su4 := ⟨?_, ?_⟩
    init := ⟨?_, ?_⟩
    b1 := ⟨?_, ?_⟩
    b2 := ⟨?_, ?_⟩
    b4 := ⟨?_, ?_⟩
    b6 := ⟨?_, ?_⟩
    b7 := ⟨?_, ?_⟩
    tail := ⟨?_, ?_⟩
    restore := ⟨?_, ?_⟩ }
  taint_decide_all

theorem sha224_checks (v : Backend) : Checks v.F224 := checks_of_shape (F := v.F224) sha224Shape_checks

theorem sha224_sat : ∃ s, (Spec.Hmac.sha224I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-224 with the backend `v`, verified. -/
theorem sha224_verified (v : Backend) :
    Verified X86.target v.F224.pbkdf2 (Spec.Hmac.sha224I.pbkdf2ScratchContract X86.abi 76) :=
  verified (sha224OKF v) (sha224_checks v) rfl rfl sha224_sat

end VG.Proof.Pbkdf2.Whole.X86
