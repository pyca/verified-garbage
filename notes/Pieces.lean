import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.TCB.X86_64.Print
open VG VG.X86_64 VG.Impl.X25519.X86_64
partial def dump : Prog isa → StateM Nat (List String)
  | .block is => pure (is.flatMap Instr.asm)
  | .seq a b => do return (← dump a) ++ (← dump b)
  | .loop b c => do
      let n ← get; set (n+1)
      let x ← dump b
      return [s!".Lx{n}:"] ++ x ++ [s!"j{c.name} .Lx{n}"]
  | .call n _ => pure [s!"call {n}"]
  | .ite .. => pure ["ud2"]
  | .frame .. => pure ["ud2"]
  | .icall .. => pure ["ud2"]
def fn (n : String) (p : Prog isa) (k : Nat) : String :=
  let (l, _) := (dump p).run (1000 * k)
  s!".globl {n}\n.p2align 5\n{n}:\n" ++ "\n".intercalate l ++ "\nret\n"

def pieces (F : Field) : List (String × List Instr) :=
  let s (i : Nat) := 32 * i
  [("A", addCmov (s 7) X2 Z2), ("B", subCmov (s 8) X2 Z2), ("C", addCmov (s 9) X3 Z3), ("D", subCmov (s 10) X3 Z3),
   ("UV", bitsDiffer 2 ++ choose2 (s 11) (s 7) (s 9) (s 12) (s 8) (s 10)),
   ("P", F.mul (s 13) (s 10) (s 7)), ("Q", F.mul (s 14) (s 9) (s 8)), ("AA", F.sqr (s 15) (s 11)), ("BB", F.sqr (s 16) (s 12)),
   ("s", addCmov (s 18) (s 13) (s 14)), ("d", subCmov (s 19) (s 13) (s 14)), ("E", subCmov (s 21) (s 15) (s 16)),
   ("x2", F.mul X2 (s 15) (s 16)), ("w", F.a24add (s 22) (s 15) (s 21)), ("dd", F.sqr (s 23) (s 19)),
   ("z2", F.mul Z2 (s 21) (s 22)), ("x3", F.sqr X3 (s 18)), ("z3", F.mul Z3 X1 (s 23))]
def main : IO Unit := do
  IO.println "@inv"
  IO.println (fn "vg_gf25519_r64_invert" invertFn 1)
  for (n, F, p) in [("base", baseline, x25519), ("adx", adx, x25519Adx)] do
    IO.println s!"@whole {n}"
    IO.println (fn s!"x_{n}" p (if n == "base" then 2 else 3))
    for (m, is) in pieces F do
      IO.println s!"@{n} {m}"
      IO.println ("\n".intercalate (is.flatMap Instr.asm))
