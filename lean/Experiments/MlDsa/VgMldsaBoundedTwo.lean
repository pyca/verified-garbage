import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (mov)
open VG.Impl.MlDsa.AArch64.Sample
namespace ExpBoundedTwo

def loop (eta : Nat) : Prog isa :=
 .loop (.seq (rbBody eta) (.block [.mul .x .x8 .x4 .x5])) (.nonzero .x .x8)

def choose : Prog isa := .seq (.block [.subImm .x .x9 .x27 2]) <|
 .ite (.zero .x .x9) (loop 2) (loop 4)

-- All rb constants depend only on public eta. Return the same count and
-- last rejected store as the original544-byte bounded sampler.
def parse (first : Bool) : Prog isa :=
 .seq (.block [.subImm .x .x9 .x27 2]) <|
 .ite (.zero .x .x9) (one 2) (one 4)
where
 one eta := .seq (.block ((rbSetup eta).drop 4 ++
   (if first then [.addImm .x .x2 .x25 840,mov .x3 .x26,.movz .x .x4 256 0]
    else [.addImm .x .x2 .x25 1112,.ldr .x .x4 .x25 2000,
      .movz .x .x6 256 0,.sub .x .x6 .x6 .x4,.lsl .x .x6 .x6 2,
      .add .x .x3 .x26 .x6]) ++ [.movz .x .x5 272 0])) (loop eta)

def extra (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
 .seq (.block [.str .x .x4 .x25 2000,mov .x0 .x25,
   .movz .x .x1 136 0,.movz .x .x2 136 0,.addImm .x .x3 .x25 1112,
   .movz .x .x4 272 0,.addImm .x .x5 .x25 200]) <|
 .seq (.call ("vg_keccak_squeeze_scratch"++c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c))
 (parse false)

def sampler (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
 .seq (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) <|
 .seq (spongeWith c 136 272) <| .seq (parse true) <|
 .seq (.ite (.zero .x .x4) (.block []) (extra c)) (.block (retZ++epi))
end ExpBoundedTwo

def main : IO Unit := do
 let sha3 : Impl.Sha3.AArch64.Callee := {
  name := "vg_keccak_f1600_sha3", code := Impl.Sha3.AArch64.Sha3.Vector.permute,
  suffix := "_sha3", pairedSha3 := true }
 for (name,c) in [("two",Impl.Sha3.AArch64.Callee.scalar),("two-sha3",sha3)] do
  IO.FS.writeFile ("/tmp/vg-mldsa-bounded-"++name++".body")
   (String.join ((printer.function (ExpBoundedTwo.sampler c)).map (Rust.line printer.call)))
