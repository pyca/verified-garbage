module

public import VerifiedGarbage.Impl.Ed25519.X86.Recover
public import VerifiedGarbage.Impl.Ed25519.X86.FieldCheck

@[expose] public section

namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def recoverParity : List Instr :=
  [.mov .eax (.mem (sc 64)), .alu .and .eax (.imm 1), .alu .xor .eax (.reg .esi),
    .alu .test .eax (.reg .eax)]

def recoverSuccessOps : List FieldOp := [.const 2 1, .mul 3 0 1]
def recoverSuccess : List Instr := fieldCode recoverSuccessOps ++ [.mov .eax (.imm 1)]
def recoverInvalid : Prog isa := .block [.mov .eax (.imm 0)]
def recoverAdjustSign : Prog isa :=
  .seq (.block (freeze 64 ++ recoverParity))
    (.seq (.ite .e (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0]))) (.block recoverSuccess))
/-- `eax = 1` if `x = 0` and the sign bit `esi` is 1 (no point), and 0 otherwise. -/
def recoverZero : Prog isa :=
  .seq (.block (fieldZero 0)) (.ite .e (.block [.mov .eax (.reg .esi)]) (.block [.mov .eax (.imm 0)]))
def recoverSign : Prog isa :=
  .seq recoverZero (.seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne recoverInvalid recoverAdjustSign))
/-- `x` kept and `eax = 1` if `v x² = u`; `x` times `√-1` and `eax = 1` if `v x² = -u`; `eax = 0`
otherwise. -/
def recoverRoot : Prog isa :=
  .seq (.block (fieldEqual 11 6)) (.ite .e (.block [.mov .eax (.imm 1)])
    (.seq (.block (fieldEqual 11 12)) (.ite .e
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] ++ [.mov .eax (.imm 1)]))
      recoverInvalid)))
def recoverChecks : Prog isa :=
  .seq recoverRoot (.seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne recoverSign recoverInvalid))
def recoverPoint : Prog isa :=
  .seq recoverCandidate (.seq (.block [.mov .esi (.mem (sc 32))]) recoverChecks)

end VG.Impl.Ed25519.X86
