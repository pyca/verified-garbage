module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Generate

/-! AAPCS64 entry with a 320-byte persistent frame and saved link register. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def entryHeader : List Instr :=
  [.strSp .x0 48, .strSp .x1 56, .strSp .x2 136, .strSp .x3 144, .strSp .x3 208,
   .strSp .x4 64, .strSp .x5 72, .strSp .x6 88, .strSp .x7 104]

def incomingSlots : List (Nat × Nat) := [(320, 112), (328, 120), (336, 40)]

def entryIncoming : List Instr := incomingSlots.flatMap fun (src, dst) => [.ldrSp .x3 src, .strSp .x3 dst]

def derivedSlots : List (Nat × Nat) :=
  [(24, VG.Impl.Dsa.Generation.Layout.wrappedSeed), (32, VG.Impl.Dsa.Generation.Layout.hashes),
   (96, VG.Impl.Dsa.Generation.Layout.hash)]

def entryDerived : List Instr :=
  (derivedSlots.flatMap fun (dst, offset) =>
    [.ldrSp .x3 40, movi .x4 offset, .add .x .x3 .x3 .x4, .strSp .x3 dst]) ++
  [movi .x3 0, .strSp .x3 128]

def dispatch (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) : Prog isa :=
  .seq (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128])
    (.ite (.zero .x .x4) (generate G1 G256 mul roundCode 128 20)
      (.seq (.block [.subImm .x .x4 .x3 256])
        (.ite (.zero .x .x4) (generate G1 G256 mul roundCode 256 32) (generate G1 G256 mul roundCode 384 32))))

def entryBody (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) : Prog isa :=
  .seq (.block [.strSp .x30 296])
    (.seq (.block (entryHeader ++ entryIncoming ++ entryDerived))
      (.seq (dispatch G1 G256 mul roundCode) (.block [.ldrSp .x30 296])))

def code (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) : Prog isa :=
  .frame (.alloc 320) (entryBody G1 G256 mul roundCode) (.free 320)

end VG.Impl.Dsa.AArch64.Generation
