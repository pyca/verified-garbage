module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill

/-! # `vg_dsa_parameter_search` on AArch64

`vg_dsa_parameter_search(out = x0, out_len = x1, used = x2, rand = x3,
rand_len = x4, scratch = x5, scratch_len = x6, state = x7)`: a 480-byte
frame holding the attempts' words, the saved registers (from offset 296)
and the controller's words (`Refill.ctl`); the entry stores the arguments,
with `rand` as every tape of the attempts (the seeds', the witnesses' and,
empty, the generator's), and the search for the width in `state[1]` runs
(`dispatch`). -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- The arguments in the attempts' words and the controller's, and
`state[0]` and `state[1]` (the seeds left and the width). -/
def entryHeader : List Instr :=
  [.ldr .x .x8 .x7 0, .ldr .x .x9 .x7 8,
   .strSp .x0 48, .strSp .x1 56, .strSp .x3 64, .strSp .x4 72, .strSp .x3 88, .strSp .x3 112,
   .strSp .x4 120, .strSp .x5 40, .strSp .x9 136, movi .x3 0, .strSp .x3 80, .strSp .x3 104,
   .strSp .x2 (Refill.ctl 0), .strSp .x7 (Refill.ctl 1), .strSp .x8 (Refill.ctl 2)]

def derivedSlots : List (Nat × Nat) :=
  [(24, VG.Impl.Dsa.Generation.Layout.wrappedSeed), (32, VG.Impl.Dsa.Generation.Layout.hashes),
   (96, VG.Impl.Dsa.Generation.Layout.hash)]

def entryDerived : List Instr :=
  (derivedSlots.flatMap fun (dst, offset) =>
    [.ldrSp .x3 40, movi .x4 offset, .add .x .x3 .x3 .x4, .strSp .x3 dst]) ++
  [movi .x3 0, .strSp .x3 128]

/-- The search for the width in `W 17`. -/
def dispatch (G1 G256 : Hash) (gen : Nat → Prog isa) (prime : Nat → Prog isa) : Prog isa :=
  .seq (.block [.ldrSp .x3 136, .subImm .x .x4 .x3 128])
    (.ite (.zero .x .x4) (Refill.search G1 G256 gen prime 128 20)
      (.seq (.block [.subImm .x .x4 .x3 256])
        (.ite (.zero .x .x4) (Refill.search G1 G256 gen prime 256 32) (Refill.search G1 G256 gen prime 384 32))))

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

def entryBody (G1 G256 : Hash) (gen : Nat → Prog isa)
    (prime : Nat → Prog isa) : Prog isa :=
  .seq (.block entrySave)
    (.seq (.block (entryHeader ++ entryDerived))
      (.seq (dispatch G1 G256 gen prime) (.block entryRestore)))

def code (G1 G256 : Hash) (gen : Nat → Prog isa)
    (prime : Nat → Prog isa) : Prog isa :=
  .frame (.alloc Refill.frameBytes) (entryBody G1 G256 gen prime) (.free Refill.frameBytes)

end VG.Impl.Dsa.AArch64.Generation
