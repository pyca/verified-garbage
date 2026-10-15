module

public import VerifiedGarbage.Impl.Dsa.X86.Entry

/-! # A fixed-width digest buffer avoids duplicating the arithmetic bodies

The caller allocates at least 16384 scratch bytes. The arithmetic body uses
15712 bytes; the following 32 bytes hold the selected digest prefix, padded
with leading zeros. Only this small copy is specialized by prefix length.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.DigestPad
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.Layout

def output : Nat := usedBytes

def byte (len j : Nat) : List Instr :=
  (if j < 32 - len then [.mov .eax (.imm 0)]
    else [.movzx8 .eax (at_ .esi (j - (32 - len)))]) ++
    [.store8 (sc (output + j)) .al]

def fill (len : Nat) : List Instr := (List.range 32).flatMap (byte len)

def prepare (len : Nat) : List Instr :=
  Core.pointer (.input .digest) ++ fill len ++
    Core.pointer (.local output) ++ [.store (sc (Layout.field .digest)) .esi]

def dispatch : Nat → Prog isa
  | 0 => .block (prepare 0)
  | n + 1 => .seq (.block [.mov .eax (.mem (sc (Layout.field .digestPrefixLen))),
      .alu .cmp .eax (.imm (BitVec.ofNat 32 (n + 1)))])
      (.ite .e (.block (prepare (n + 1))) (dispatch n))

end VG.Impl.Dsa.X86.DigestPad
