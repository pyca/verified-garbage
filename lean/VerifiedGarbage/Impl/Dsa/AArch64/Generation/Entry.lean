module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Generate

/-! AAPCS64 entry with a 448-byte persistent frame and saved link register. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def entryHeader : List Instr :=
  [.strSp .x0 48, .strSp .x1 56, .strSp .x2 136, .strSp .x3 144, .strSp .x3 208,
   .strSp .x4 64, .strSp .x5 72, .strSp .x6 88, .strSp .x7 104]

def incomingSlots : List (Nat × Nat) := [(448, 112), (456, 120), (464, 40)]

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

def abiGprs : List (Reg × Nat) :=
  [⟨.x19, 304⟩, ⟨.x20, 312⟩, ⟨.x21, 320⟩, ⟨.x22, 328⟩, ⟨.x23, 336⟩, ⟨.x24, 344⟩, ⟨.x25, 352⟩, ⟨.x26, 360⟩, ⟨.x27, 368⟩, ⟨.x28, 376⟩]

def abiVectors : List (VReg × Nat) :=
  [⟨.v8, 384⟩, ⟨.v9, 392⟩, ⟨.v10, 400⟩, ⟨.v11, 408⟩, ⟨.v12, 416⟩, ⟨.v13, 424⟩, ⟨.v14, 432⟩, ⟨.v15, 440⟩]

def entrySave : List Instr :=
  (abiGprs.map fun (r, d) => .strSp r d) ++
    (abiVectors.flatMap fun (v, d) => [.umov .x .x9 v 0, .strSp .x9 d]) ++ [.strSp .x30 296]

def entryRestore : List Instr :=
  (abiVectors.flatMap fun (v, d) => [.ldrSp .x9 d, .vop (.ins .d2 v 0 .x9)]) ++
    (abiGprs.map fun (r, d) => .ldrSp r d) ++ [.ldrSp .x30 296]

def entryBody (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) : Prog isa :=
  .seq (.block entrySave)
    (.seq (.block (entryHeader ++ entryIncoming ++ entryDerived))
      (.seq (dispatch G1 G256 mul roundCode) (.block entryRestore)))

def code (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) : Prog isa :=
  .frame (.alloc 448) (entryBody G1 G256 mul roundCode) (.free 448)

end VG.Impl.Dsa.AArch64.Generation
