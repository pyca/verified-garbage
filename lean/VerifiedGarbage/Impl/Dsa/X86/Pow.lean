module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # Shared DSA modular exponentiation on IA-32

The caller loads the modulus, base and exponent into the existing Montgomery
workspace. Each width has one callable setup-and-exponentiation body.

The context's setup (`contextSeed`) leaves `2^(65 n) mod m` in slot 4, which
six Montgomery squarings raise to `R² mod m`, `R = 2^(64 n)`: the Montgomery
square of `2^(64 n + j)` is `2^(64 n + 2 j)`, so the doublings reach `65 n`
bits instead of `128 n`. Every Montgomery multiplication is
a call of `vg_rsa_mont_mul_at` (`mul`), whose own range is slots 1 to 3,
which only the setup uses: one is kept in slot 7, the product's, where the
encoding and the decoding need it.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Pow
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def slots : List (Reg × Nat) := [(.ebx, 8), (.esi, 12), (.ebp, 16), (.edi, 20)]

def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 4))] ++
    slots.map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

def restore : List Instr := slots.map fun (r, d) => .mov r (.mem (sc d))

/-- The callee's own range, `scratchBytes n` bytes: from slot 1, within slots
1 to 3 for `n ≥ 2`. -/
def calleeScratch (n : Nat) : Nat := slot n 1

/-- `[esp + d + 4 i] = v_i`, through `eax`. -/
def immStores : List Nat → Nat → List Instr
  | [], _ => []
  | v :: vs, d => .mov .eax (.imm (BitVec.ofNat 32 v)) :: .store (at_ .esp d) .eax :: immStores vs (d + 4)

/-- The arguments of `vg_rsa_mont_mul_at` for slots `o`, `a` and `b`, stored
into the frame at `esp`: `ws` (`edi`), the context's length in words, the
width, the offsets of the modulus, the inverse (the header's first word) and
the callee's range, and those of `o`, `a` and `b`. Only `eax` changes. -/
def mulArgs (n o a b : Nat) : List Instr :=
  .store (at_ .esp 0) .edi ::
    immStores [contextBytes n / 8, n, slot n 0, 0, calleeScratch n, slot n o, slot n a, slot n b] 4

/-- `[o] = [a] [b] R⁻¹ mod m` for slots `o`, `a` and `b`, by a call of
`vg_rsa_mont_mul_at` with its arguments in a frame of 36 bytes, which keeps
`ebx`, `esi`, `ebp` and `edi`. -/
def mul (n o a b : Nat) : Prog isa :=
  .frame (.alloc 36) (.seq (.block (mulArgs n o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody))
    (.free 36)

/-- `k` Montgomery squarings of slot 4. -/
def squarings (n : Nat) : Nat → Prog isa
  | 0 => .block []
  | k + 1 => .seq (squarings n k) (mul n 4 4 4)

/-- `R² mod m` in slot 4, from `2^(65 n) mod m`. -/
def setup (n : Nat) : Prog isa := .seq (contextSeed n (65 * n)) (squarings n 6)

/-- One in slot 7; the result `R mod m`, one in Montgomery form; the base
encoded. -/
def encode (n : Nat) : Prog isa :=
  .seq (one n (slot n 7)) (.seq (mul n 6 4 7) (mul n 5 5 4))

/-- An iteration: the result times the base where the exponent's low bit is
set, the base squared, the exponent shifted, the count decremented. -/
def step (n e : Nat) : Prog isa :=
  .seq (.block (exponentMask (slot n 8) 4)) <|
  .seq (mul n 7 6 5) <|
  .seq (selectProduct (contextMod n) (slot n 6) (slot n 7) 4) <|
  .seq (mul n 5 5 5) <|
  .seq (shiftDown e (slot n 8)) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- The result decoded: its product with one. -/
def finish (n : Nat) : Prog isa := .seq (one n (slot n 7)) (mul n 6 6 7)

def core (n e : Nat) : Prog isa :=
  .seq (setup n) <| .seq (encode n) <|
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * e)))]) <|
  .seq (.loop (step n e) .ne) (finish n)

def body (n e : Nat) : Prog isa :=
  .seq (.block save) (.seq (core n e) (.block restore))

def scratch (n : Nat) : List (Nat × Nat) := [(0, 64), (slot n 1, contextBytes n - slot n 1)]

def layout (n e : Nat) : Impl.Dsa.ModPow.Layout where
  n := n
  e := e
  modulus := slot n 0
  base := slot n 5
  exponent := slot n 8
  result := slot n 6
  scratch := scratch n
  size := contextBytes n

def name (n e : Nat) : String := s!"vg_dsa_pow_{(layout n e).n}_{(layout n e).e}"

/-- Pass the workspace and its length using cdecl's two stack arguments. -/
def call (n e : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))])
    (.frame (.push [.eax, .edi]) (.call (name n e) (body n e)) (.pop .eax 2))

end VG.Impl.Dsa.X86.Pow
