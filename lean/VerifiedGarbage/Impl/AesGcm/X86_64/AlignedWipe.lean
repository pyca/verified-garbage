module
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! The complete stack wipe for the two AVX-512 seal entries. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86_64.DirectGather.AlignedWipe
open VG.X86_64
inductive Frame where
  | gather
  | contiguous

def Frame.count : Frame → Nat
  | .gather => 82
  | .contiguous => 81

/-- The outer eight bytes and the inner frame keep the existing scrub permissions. -/
def Frame.inner (f : Frame) := 32 * f.count + 40
def Frame.bytes (f : Frame) := f.inner + 8

open VG.Impl.Scrub.X86_64

/-- True selects the aligned interior cursor. False selects a fixed frame boundary. -/
abbrev Loc := Bool × Nat
def locReg (l : Loc) : Reg := if l.1 then .r11 else .rsp
def emitStore (l : Loc) : Instr := .vmovdquStore .l256 {base := locReg l, disp := (l.2 : Int)} .xmm0
def locs (f : Frame) : List Loc :=
  [(false, 0)] ++ (List.range f.count).map (fun i => (true, 32 * i)) ++ [(false, 32 * f.count), (false, f.inner - 32)]
def setup : List Instr :=
  [.mov .r11 (.reg .rsp), .alu .add .r11 (.imm 32), .alu .and .r11 (.imm (-32))]
def code (f : Frame) := setup ++ (locs f).map emitStore ++ [zeroR .r11]
def save8 : List Instr := [.store {base := .rsp} .r11]
def wipeWhole (f : Frame) : Prog isa :=
  .frame (.alloc 8) (.seq (.block save8) (.frame (.alloc f.inner) (.block (code f)) (.free f.inner))) (.free 8)
abbrev preCode := xregs.map (zeroX .evex) ++ clearHigh .evex ++ [Reg.r11].map zeroR
abbrev postRegs := scratchRegs.erase .r11
abbrev postCode := retFix 0 ++ postRegs.map zeroR
def tail (f : Frame) : Prog isa := .seq (.block preCode) (.seq (mxFix .avx) (.seq (wipeWhole f) (.block postCode)))
def scrub (f : Frame) (body : Prog isa) : Prog isa := .seq body (tail f)
end VG.Impl.AesGcm.X86_64.DirectGather.AlignedWipe
