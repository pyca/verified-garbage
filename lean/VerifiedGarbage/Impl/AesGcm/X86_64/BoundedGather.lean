module
public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather

/-! Feed up to two gather descriptors to the bounded seal; longer scatter lists use the streaming pieces. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86_64.DirectGather
open VG.X86_64

def descriptorHead : List Instr := [.mov .rax (.mem (at_ .rsp 8))]
def descriptorData : List Instr :=
  [.mov .rbx (.mem (at_ .rax 0)), .mov .r10 (.mem (at_ .rax 8)),
   .mov .rcx (.mem (at_ .rsp 16)),.alu .cmp .rcx (imm 2)]

def gatherArgs : Prog isa := .seq (.block descriptorHead) (.seq (.block descriptorData)
  (.ite .e (.block [.mov .r11 (.mem (at_ .rax 16))]) (.block [.mov .r11 (.reg .rbx)])))

def boundedGather : Prog isa := .seq gatherArgs (.call Short.bounded.name Short.bounded.code)

/-- One descriptor is eligible at any supported length. Two descriptors use the
bounded kernel from 17 bytes, when the streaming setup stops winning. -/
def countTest : List Instr :=
  [.mov .rax (.mem (at_ .r15 lenO)), .alu .cmp .rax (imm 17),
   .mov32 .rcx (imm 2), .alu .sbb .rcx (imm 0),
   .mov .rax (.mem (at_ .rsp 16)), .alu .sub .rax (imm 1),
   .alu .cmp .rax (.reg .rcx), .alu .sbb .rax (.reg .rax)]

def withBounded (fallback : Prog isa) : Prog isa :=
  .seq (.seq (Short.condWith true) (.ite .e (.block []) (.block countTest))) (.ite .e fallback boundedGather)

def preparedBounded (c : Callees) (ctr toFn : Fn) : Prog isa :=
  framed (dispatch (withBounded (quick toFn)) (withBounded (general c ctr (some toFn))))

namespace AlignedWipe
open VG.Impl.Scrub.X86_64

/-- True selects the aligned interior cursor. False selects a fixed frame boundary. -/
abbrev Loc := Bool × Nat
def locReg (l : Loc) : Reg := if l.1 then .r11 else .rsp
def emitStore (l : Loc) : Instr := .vmovdquStore .l256 {base := locReg l, disp := (l.2 : Int)} .xmm0
def locs : List Loc :=
  [(false, 0)] ++ (List.range 82).map (fun i => (true, 32 * i)) ++ [(false, 2624), (false, 2632)]
def setup : List Instr :=
  [.mov .r11 (.reg .rsp), .alu .add .r11 (.imm 32), .alu .and .r11 (.imm (-32))]
def code := setup ++ locs.map emitStore ++ [zeroR .r11]
def save8 : List Instr := [.store {base := .rsp} .r11]
def wipeWhole : Prog isa :=
  .frame (.alloc 8) (.seq (.block save8) (.frame (.alloc 2664) (.block code) (.free 2664))) (.free 8)
abbrev preCode := xregs.map (zeroX .evex) ++ clearHigh .evex ++ [Reg.r11].map zeroR
abbrev postRegs := scratchRegs.erase .r11
abbrev postCode := retFix 0 ++ postRegs.map zeroR
def tail : Prog isa := .seq (.block preCode) (.seq (mxFix .avx) (.seq wipeWhole (.block postCode)))
def scrub (body : Prog isa) : Prog isa := .seq body tail
end AlignedWipe

/-- Use the bounded record routine only on the variant providing its AVX-512 instructions. -/
def directSeal48 (baseLv lv : Impl.Scrub.X86_64.VecLevel) (short : Bool)
    (c : Callees) (ctr : Fn) (blocks : Option Fn) : Prog isa :=
  match blocks with
  | some b =>
    if short = true ∧ lv = .evex then
      AlignedWipe.scrub (Impl.Gcm.X86_64.Flag.onFlag 48 (preparedBounded c ctr b) (plain c ctr))
    else directPrepared lv 48 c ctr b
  | none => directBase baseLv c ctr

end VG.Impl.AesGcm.X86_64.DirectGather
