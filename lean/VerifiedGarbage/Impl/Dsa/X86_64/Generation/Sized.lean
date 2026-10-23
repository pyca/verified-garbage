module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry

/-! # Share the complete generation body by its public modulus width

Retain the dispatch instructions while omitting the bodies which the
restricted helper's width precondition rules out. This preserves the
executed instruction trace inside a helper.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation.Sized
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Mgf1.X86_64 (sp)

def dispatch (pBytes : Nat) (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp 136)), .alu .cmp .rax (.imm 128)])
    (.ite .e (if pBytes = 128 then generate G1 G256 sq mul round 128 20 else .block [])
      (.seq (.block [.alu .cmp .rax (.imm 256)])
        (.ite .e (if pBytes = 256 then generate G1 G256 sq mul round 256 32 else .block [])
          (if pBytes = 384 then generate G1 G256 sq mul round 384 32 else .block []))))

def entryBody (pBytes : Nat) (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq (.block (entryHeader ++ entryIncoming ++ entryDerived)) (dispatch pBytes G1 G256 sq mul round)

def code (pBytes : Nat) (G1 G256 : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .frame (.alloc 48)
    (.seq (.block saveRegisters)
      (.seq (.frame (.alloc 296) (entryBody pBytes G1 G256 sq mul round) (.free 296))
        (.block restoreRegisters))) (.free 48)

/-- Only the selected hash survives the statically pruned size branches. -/
def single (pBytes : Nat) (G : Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  code pBytes G G sq mul round

end VG.Impl.Dsa.X86_64.Generation.Sized
