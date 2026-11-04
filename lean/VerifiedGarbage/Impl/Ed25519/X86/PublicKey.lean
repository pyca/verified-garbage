module

public import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe
public import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase

/-! Ed25519 public-key derivation from the seed's SHA-512 digest, including pruning, on x86.
The 256-byte frame holds outgoing cdecl arguments at 0, the scalar at 32,
and the digest at 192. The original arguments remain above the frame.
The base-point multiplication uses the caller's scratch buffer. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86.PublicKey
open VG.X86

def at_ (d : Nat) : MemOp := { base := .esp, disp := d }

def argument (j : Nat) : MemOp := at_ (260 + 4 * j)

def baseArgs : List Instr := Whole.setup 0 [.caller 0 0, .frame 32, .caller 2 0]

/-- Prune one word; the other words are copied unchanged. -/
def pruneWord (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (192 + 4 * k)))] ++
  (if k = 0 then [.alu .and .eax (.imm 0xfffffff8)] else []) ++
  (if k = 7 then [.alu .and .eax (.imm 0x3fffffff), .alu .or .eax (.imm 0x40000000)] else []) ++
  [.store (at_ (32 + 4 * k)) .eax]

def prune : List Instr := (List.range 8).flatMap pruneWord

def wipe : List Instr := Whole.zeroWords 8 56

def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

/-- The frame's body after `first`, which leaves the seed's SHA-512 digest at 192. -/
def bodyFrom (first : Prog isa) : Prog isa := .seq first (.seq (.block prune)
  (.seq (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) (.block wipe)))

/-- The digest's address, the second argument, in ECX. -/
def copyPtr : List Instr := [.mov .ecx (.mem (argument 1))]

/-- Word `k` of the 64 bytes at ECX copied to the frame's digest at 192. -/
def copyDigestWord (k : Nat) : List Instr :=
  [.mov .eax (.mem { base := .ecx, disp := 4 * k }), .store (at_ (192 + 4 * k)) .eax]

def copyDigestWords : List Instr := (List.range 16).flatMap copyDigestWord

/-- The seed's SHA-512 digest, the second argument, copied to 192. -/
def copyExpanded : Prog isa := .seq (.block copyPtr) (.block copyDigestWords)

/-- `vg_ed25519_public_key_expanded`: the public key of the seed whose SHA-512 digest is the
second argument (`publicKeyExpandedContract`). -/
def publicKeyExpanded : Prog isa :=
  .frame (.push (List.replicate 64 .eax)) (bodyFrom copyExpanded) (.pop .eax 64)

end VG.Impl.Ed25519.X86.PublicKey
