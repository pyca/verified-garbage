import VerifiedGarbage.Impl.Camellia.X86_64.Sbox
import VerifiedGarbage.Proof.Camellia.SboxTable
import VerifiedGarbage.Proof.Framework.X86_64.Straight
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# The bitsliced Camellia S-box on x86-64

`sboxCode` only combines words bitwise, so it computes the same Boolean
function at each of the 64 bit positions: the kernel evaluates it once on
truth tables of the 256 inputs (`Bitslice.table`) and compares the result
with the specification's `SBOX1` on the same inputs. `sbox_ok` then gives,
at every bit position `p`, `SBOX1` of the byte formed by bit `p` of the
eight words.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Impl.Camellia.X86_64
open VG.Proof.Camellia

/-- The S-box's memory: its spill slots, at `r9`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map inT, slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (q j) == some (sbox1T j)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) Impl.Camellia.X86_64.sboxCode sboxEnv sboxPost = true := by
  decide +kernel

end VG.Proof.Camellia.X86_64
