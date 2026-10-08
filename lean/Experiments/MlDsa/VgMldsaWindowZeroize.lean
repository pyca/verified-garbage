import VerifiedGarbage.Impl.Zeroize.AArch64
import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
open VG VG.AArch64
namespace WindowZeroize
-- x0 buffer, x1 arbitrary byte count; same exact tail as current implementation.
def zeroize (shift : Nat) (vector : Bool) : Prog isa :=
 let n := 2^shift
 .seq (.block ([.movz .x .x2 0 0,.lsr .x .x3 .x1 shift,
   .movz .x .x4 (BitVec.ofNat 16 (n-1)) 0,.logic .and .x .x1 .x1 .x4] ++
   if vector then [.vop (.dup .d2 .v0 .x2)] else [])) <|
 .seq (.ite (.zero .x .x3) (.block [])
   (.loop (.block ((List.range (n/(if vector then 16 else 8))).map (fun i =>
    if vector then .strq .v0 .x0 (16*i) else .str .x .x2 .x0 (8*i)) ++
    [.addImm .x .x0 .x0 n,.subImm .x .x3 .x3 1])) (.nonzero .x .x3))) <|
 .seq (.block [.lsr .x .x3 .x1 3,.movz .x .x4 7 0,.logic .and .x .x1 .x1 .x4]) <|
 .seq (Impl.Zeroize.AArch64.loop true) <|
 .seq (.block [.addImm .x .x3 .x1 0]) (Impl.Zeroize.AArch64.loop false)
end WindowZeroize

def main : IO Unit := do
 for (name,shift,vector) in [("neon64",6,true),("neon128",7,true),("gpr64",6,false)] do
  let code := printer.function (WindowZeroize.zeroize shift vector)
  IO.FS.writeFile ("/tmp/vg-window-zeroize-"++name++".body") (String.join (code.map (Rust.line printer.call)))
