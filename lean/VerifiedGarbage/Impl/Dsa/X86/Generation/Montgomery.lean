module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Spec.Rsa.MontMul

/-! Calls of the shared optimized Montgomery kernel in the parent workspace. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def montgomeryBytes : Nat := 14720
def montgomeryScratch : Nat := 8192

def montgomeryWord (n o a b : Nat) : Nat → BitVec 32
  | 1 => BitVec.ofNat 32 (montgomeryBytes / 8)
  | 2 => BitVec.ofNat 32 n
  | 3 => BitVec.ofNat 32 (Dynamic.slot n 0)
  | 4 => 0
  | 5 => BitVec.ofNat 32 montgomeryScratch
  | 6 => BitVec.ofNat 32 (Dynamic.slot n o)
  | 7 => BitVec.ofNat 32 (Dynamic.slot n a)
  | _ => BitVec.ofNat 32 (Dynamic.slot n b)

def montgomeryStores (values : Nat → BitVec 32) (first : Nat) : Nat → List Instr
  | 0 => []
  | count + 1 => [.mov .eax (.imm (values first)), .store (at_ .esp (4 * first)) .eax] ++
      montgomeryStores values (first + 1) count

def montgomeryArgs (n o a b : Nat) : List Instr :=
  .store (at_ .esp 0) .edi :: montgomeryStores (montgomeryWord n o a b) 1 8

/-- Equal input offsets select the kernel's optimized symmetric square. -/
def montgomery (n o a b : Nat) : Prog isa :=
  .frame (.alloc 36)
    (.seq (.block (montgomeryArgs n o a b))
      (.call Spec.Rsa.MontMul.mulApi.name Rt.body)) (.free 36)

end VG.Impl.Dsa.X86.Generation
