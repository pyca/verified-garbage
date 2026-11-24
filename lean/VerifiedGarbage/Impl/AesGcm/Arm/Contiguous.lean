module

public import VerifiedGarbage.Impl.AesGcm.Arm.FrameArgs

/-! # AES-GCM seal from a contiguous source into a caller-supplied destination -/

@[expose] public section
namespace VG.Impl.AesGcm.Arm.Contiguous

open VG.Arm

/-- Keep the one-shot argument layout for nonce processing and authentication.
The last private argument before the workspace holds the plaintext pointer. -/
def frameArgs : List Instr :=
  orderedFrameArgs 2592 6 fun slot => ([0, 1, 3, 4, 5, 2] : List Nat)[slot]!

def cryptArgs : List Instr := [.ldrSp .r4 20, .ldrSp .r5 12, .ldrSp .r6 8]

def body : Prog isa :=
  .seq (.block (oneEntry 24)) (.seq oneAad (.seq (.block cryptArgs)
    (.seq cryptTo (.seq (oneTag 0) (.seq (.block tagOut) (.block restore))))))

def sealContiguous : Prog isa :=
  .frame (.alloc 2592) (.seq (.block frameArgs) body) (.free 2592)

end VG.Impl.AesGcm.Arm.Contiguous
