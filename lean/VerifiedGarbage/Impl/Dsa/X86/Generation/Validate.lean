module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Pack

/-! # A separate outgoing frame keeps domain-check arguments away from search state -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def validateArgs (plen qlen : Nat) : List Instr :=
  bufferPointer .esi VG.Impl.Dsa.Generation.Layout.packed ++
  bufferPointer .edi VG.Impl.Dsa.Generation.Layout.domainCheck ++
  [.mov .ebx (.imm (BitVec.ofNat 32 (2 * plen + qlen))),
   .mov .ecx (.imm (BitVec.ofNat 32 plen)), .mov .edx (.imm (BitVec.ofNat 32 qlen)),
   .mov .ebp (.imm (BitVec.ofNat 32 (16 * plen)))]

def validateReg : Nat → Reg
  | 0 => .esi
  | 1 => .ebx
  | 2 => .ecx
  | 3 => .edx
  | 4 => .edi
  | _ => .ebp

def validateOutgoing : List Instr :=
  (List.range 6).map fun i => .store (at_ .esp (4 * i)) (validateReg i)

def validate (name : String) (check : Prog isa) (plen qlen : Nat) : Prog isa :=
  .seq (.block (validateArgs plen qlen))
    (.seq (.frame (.alloc 24) (.seq (.block validateOutgoing) (.call name check)) (.free 24))
      (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .e (.block (frameStatus 3)) (.block (frameStatus 1)))))

def finishDomain (name : String) (check : Prog isa) (plen qlen : Nat) : Prog isa :=
  .seq (pack plen qlen) (validate name check plen qlen)
end VG.Impl.Dsa.X86.Generation
