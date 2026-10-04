import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-SHA-256 on x86 (32-bit), the whole derivation, for every backend

The generic proof (`CT.lean`) at SHA-256, for any backend
(`Proof/Sha256/X86/Variants/Interface.lean`): its streaming functions,
HMAC's `init` and `finalize` and PBKDF2's iteration made with the backend,
verified for any backend against the shared contracts
(`Proof.Sha256.X86.Variants.Backend.hmacInit` and the others), as for the
other hash functions (`Instances.lean`). The taint checks depend only on the
sizes, so they are evaluated once, for any backend (`sha256Shape`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-256 with the backend `v`, verified. -/
def sha256OKF (v : Backend) : FnsOK v.F where
  hH := Proof.Pbkdf2.Stream.X86.sha256OK v.stream
  Wi := 104
  Wf := 104
  Wt := 104
  hi := .of_verified v.hmacInit
  hf := .of_verified v.hmacFin
  it := .of_verified v.iterate
  hiSp := v.initNoSp
  hfSp := v.finalizeNoSp
  itSp := v.iterNoSp
  hiSU := v.initStack
  hfSU := v.finalizeStack
  itSU := v.iterStack
  hWi := show 104 ≤ 104 by decide
  hWf := show 104 ≤ 104 by decide
  hWt := show 104 ≤ 104 by decide
  hWH := show 20 ≤ 104 by decide
  hW := show 104 ≤ 512 by decide
  hDB := show 32 ≤ 64 by decide
  hBS := show 64 ≤ 96 by decide
  fits := show 20 + 2 * 32 + 32 ≤ 4 * 96 by decide

/-- `F` without the names and code of the functions it calls: the code
between the calls depends on nothing else. -/
def shapeOf (F : Fns) : Fns :=
  ⟨⟨F.H.B, F.H.S, F.H.D, F.H.F, F.H.W, "", .block [], "", .block [], "", .block []⟩, F.W, "", .block [], "",
    .block [], "", .block []⟩

/-- The sizes of `Backend.F`, which are all the taint checks depend on:
`shapeOf` of every backend's `Backend.F`, written out, so that the kernel
reduces each side to it field by field rather than comparing the backends'
functions. -/
def sha256Shape : Fns :=
  ⟨⟨64, 96, 32, 32, 20, "", .block [], "", .block [], "", .block []⟩, Spec.Hmac.sha256I.scratch, "", .block [], "",
    .block [], "", .block []⟩

theorem sha256Shape_checks : Checks sha256Shape := by
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

theorem checks_of_shape {F : Fns} (h : Checks (shapeOf F)) : Checks F :=
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.su4, h.init, h.b1, h.b2, h.b4, h.b6, h.b7,
    h.tail, h.restore⟩

theorem sha256_checks (v : Backend) : Checks v.F := checks_of_shape (F := v.F) sha256Shape_checks

theorem sha256_sat : ∃ s, (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-256 with the backend `v`, verified. -/
theorem sha256_verified (v : Backend) :
    Verified X86.target v.F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76) :=
  verified (sha256OKF v) (sha256_checks v) rfl rfl sha256_sat

end VG.Proof.Pbkdf2.Whole.X86
