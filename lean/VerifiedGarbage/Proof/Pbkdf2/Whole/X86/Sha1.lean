import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# PBKDF2-HMAC-SHA-1 on x86 (32-bit), the whole derivation, for every backend

The generic proof (`CT.lean`) at SHA-1, for any backend
(`Proof/Sha1/X86/Variants/Interface.lean`): its streaming functions, HMAC's
`init` and `finalize` and PBKDF2's iteration made with the backend, verified
for any backend against the shared contracts
(`Proof.Sha1.X86.Variants.Backend.hmacInit` and the others), as for the other
hash functions (`Instances.lean`). The taint checks depend only on the sizes,
so they are evaluated once, for any backend (`sha1Shape`). `sha1_stack`
bounds the stack the code uses from what the backend proves of the functions
it calls.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Sha1.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-1 with the backend `v`, verified. -/
def sha1OKF (v : Backend) : FnsOK v.F where
  hH := Proof.Pbkdf2.Stream.X86.sha1OK v.stream
  Wi := 56
  Wf := 56
  Wt := 56
  hi := .of_verified v.hmacInit
  hf := .of_verified v.hmacFin
  it := .of_verified v.iterate
  hiSp := v.initNoSp
  hfSp := v.finalizeNoSp
  itSp := v.iterNoSp
  hiSU := v.initStack
  hfSU := v.finalizeStack
  itSU := v.iterStack
  hWi := show 56 ≤ 56 by decide
  hWf := show 56 ≤ 56 by decide
  hWt := show 56 ≤ 56 by decide
  hWH := show 20 ≤ 56 by decide
  hW := show 56 ≤ 512 by decide
  hDB := show 20 ≤ 64 by decide
  hBS := show 64 ≤ 84 by decide
  fits := show 20 + 2 * 20 + 20 ≤ 4 * 84 by decide

/-- The sizes of `Backend.F`, which are all the taint checks depend on:
`shapeOf` of every backend's `Backend.F`, written out, so that the kernel
reduces each side to it field by field rather than comparing the backends'
functions. -/
def sha1Shape : Fns :=
  ⟨⟨64, 84, 20, 20, 20, "", .block [], "", .block [], "", .block []⟩, Spec.Hmac.sha1I.scratch, "", .block [], "",
    .block [], "", .block []⟩

theorem sha1Shape_checks : Checks sha1Shape := by
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

theorem sha1_checks (v : Backend) : Checks v.F := checks_of_shape (F := v.F) sha1Shape_checks

theorem sha1_sat : ∃ s, (Spec.Hmac.sha1I.pbkdf2ScratchContract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2ScratchContract, Spec.Pbkdf2.pbkdf2ScratchContract,
    Spec.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 140

/-- `pbkdf2` for SHA-1 with the backend `v`, verified. -/
theorem sha1_verified (v : Backend) :
    Verified X86.target v.F.pbkdf2 (Spec.Hmac.sha1I.pbkdf2ScratchContract X86.abi 76) :=
  verified (sha1OKF v) (sha1_checks v) rfl rfl sha1_sat

/-- PBKDF2-HMAC-SHA1 made with the backend `v` uses at most 76 bytes of
stack. -/
theorem sha1_stack (v : Backend) : stackUse v.F.pbkdf2 ≤ 76 := by
  have := v.stream.updSU; have := v.stream.finSU; have := v.initStack; have := v.finalizeStack; have := v.iterStack
  have hi : stackUse Impl.Sha1.X86.Stream.init ≤ 20 := by lit_decide
  simp only [Impl.Pbkdf2.Whole.X86.Fns.pbkdf2, Impl.Pbkdf2.Whole.X86.Fns.key,
    Impl.Pbkdf2.Whole.X86.Fns.hashKey, Impl.Pbkdf2.Whole.X86.Fns.setup, Impl.Pbkdf2.Whole.X86.Fns.block,
    Impl.Pbkdf2.Whole.X86.Fns.outLen, Impl.Pbkdf2.Whole.X86.Fns.outLoop, Impl.Pbkdf2.Stream.X86.copy,
    Impl.Pbkdf2.Stream.X86.Hash.callInit, Backend.F, Proof.Sha1.X86.Variants.pbkdf2Fns,
    Proof.Sha1.X86.Variants.fns, Proof.Sha1.X86.Variants.hmacHash, Proof.Pbkdf2.Md.X86.sha1M,
    stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at *
  omega

end VG.Proof.Pbkdf2.Whole.X86
