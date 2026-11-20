module

public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# The registers code writes (AArch64)

A function generic over the implementations of the functions it calls
clears, before returning, the registers its code may write, the functions it
calls included: `Clear.of` reads them off the code, so that the function as
emitted (`scrubAll W rb (Clear.of c) c`) is a definition here, whatever the
implementation. These are definitions on instructions and code only; that
code keeps every other register is `Clear.of_keeps`
(`Proof/Framework/AArch64/ScrubAll.lean`).
-/

@[expose] public section

namespace VG.AArch64

/-- The register an instruction writes, if it writes exactly one (a frame's
pop writes its register); none for `ldp`, which writes two (`dsts`). -/
def dstOf : Instr → Option Reg
  | .adds _ d .. | .adcs _ d .. | .subs _ d .. | .sbcs _ d .. | .adc _ d .. | .sbc _ d .. | .csel _ d .. | .umulh d .. | .umaddl d .. | .umull d .. | .adrSym d _ => some d
  | .add _ d .. | .sub _ d .. | .addImm _ d .. | .subImm _ d .. | .logic _ _ d .. | .logicRor _ _ d .. | .bicRor _ d .. | .ror _ d .. | .extr _ d ..
  | .lsr _ d .. | .lsl _ d .. | .madd _ d .. | .mul _ d .. | .rev32 d _ | .rev d _ | .clz _ d _ | .rbit _ d _ | .movz _ d ..
  | .addSp d _ | .movk _ d .. | .ldr _ d .. | .ldrb d .. | .ldrSp d _ | .pop d | .umov _ d .. | .mrsDit d => some d
  | .ldrTbl _ d .. => some d
  | .cselc _ d .. | .csneg _ d .. => some d
  | .str .. | .strb .. | .strSp .. | .alloc _ | .free _ | .push _ | .vop _ | .ldrq .. | .ldrqTbl .. | .strq .. | .tst .. | .ccmp ..
  | .ldp .. | .stp .. | .align _ | .blr _ | .msrDitImm _ | .barrier _ => none

/-- The general-purpose registers instruction `i` writes. -/
def dsts (i : Instr) : List Reg :=
  match i with
  | .ldp t1 t2 _ _ => [t1, t2]
  | _ => (dstOf i).toList

/-- Whether instruction `i` writes the general-purpose register `r`, one of
`dsts i`. The lemmas about the registers code keeps are stated with it (or
`dsts`), not with `dstOf`, which names only an instruction's single
destination. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .ldp t1 t2 _ _ => r == t1 || r == t2
  | _ => dstOf i == some r

/-- The registers a call changes: the link register, and the
intra-procedure-call scratch registers, which a linker veneer may change. -/
def linkRegs : List Reg := [.x16, .x17, .x30]

/-- Destination of an AdvSIMD instruction. -/
def VOp.dst : VOp → VReg
  | .mov d .. | .movi0 d | .dup _ d .. | .ins _ d .. | .dupS d .. => d
  | .logic _ d .. | .not d .. | .add _ d .. | .sub _ d .. | .shift _ _ d .. => d
  | .cmp _ _ d .. | .addv _ d _ | .uaddlv _ d _ => d
  | .ext d .. | .rev _ d .. | .perm _ _ d .. | .tbl d .. => d
  | .dupE _ d .. | .insE _ d .. | .cmeq _ d .. | .bsel _ d .. | .tblN _ _ d .. => d
  | .umull _ d .. | .umlal _ d .. | .mul d .. | .mla d .. | .mls d .. => d
  | .umullH _ d .. | .umlalH _ d .. => d
  | .sqdmulh d .. | .umin d .. | .mulH _ d .. | .mulHE _ d .. | .pmull _ d .. | .pmull8 _ d .. => d
  | .aese d .. | .aesd d .. | .aesmc d .. | .aesimc d .. => d
  | .sha1 _ d .. | .sha1h d .. | .sha1su0 d .. | .sha1su1 d .. => d
  | .sha256h d .. | .sha256h2 d .. | .sha256su0 d .. | .sha256su1 d .. => d
  | .sha512h d .. | .sha512h2 d .. | .sha512su0 d .. | .sha512su1 d .. => d
  | .sm4e d .. | .sm4ekey d .. => d
  | .sm3ss1 d .. | .sm3tt _ d .. | .sm3partw1 d .. | .sm3partw2 d .. => d
  | .eor3 d .. | .bcax d .. | .rax1 d .. | .xar d .. | .xarS d .. => d

/-- The vector register an instruction writes, if any. -/
def vdstOf : Instr → Option VReg
  | .vop op => some op.dst
  | .ldrq d .. | .ldrqTbl d .. => some d
  | _ => none

end VG.AArch64

namespace VG.Impl.Residue.AArch64

open VG.AArch64

/-- The instructions of code (the pushes and pops of its frames included)
and of the functions it calls: `VG.instrs`, for this module. -/
def codeInstrs : Prog isa → List Instr
  | .block is => is
  | .seq a b => codeInstrs a ++ codeInstrs b
  | .ite _ t e => codeInstrs t ++ codeInstrs e
  | .loop b _ => codeInstrs b
  | .call _ b => codeInstrs b
  | .frame i b j => i :: codeInstrs b ++ [j]
  | .icall i _ b n => i :: codeInstrs b ++ codeInstrs n

/-- Whether code calls no function and has no frame: `Code.noCalls`, for
this module. -/
def codeNoCalls : Prog isa → Bool
  | .block _ => true
  | .seq a b => codeNoCalls a && codeNoCalls b
  | .ite _ t e => codeNoCalls t && codeNoCalls e
  | .loop b _ => codeNoCalls b
  | .call _ _ => false
  | .frame .. => false
  | .icall .. => false

/-- What the tail after `c` clears: the general-purpose registers of
`allGprs` that an instruction of `c` (callees included) may write, and the
link registers if `c` calls; the vector registers of `allVecs` and of
`hiVecs` that one may write. -/
def Clear.of (c : Prog isa) : Clear where
  gprs := allGprs.filter fun q => (codeInstrs c).any (fun i => clobbers i q) || (!codeNoCalls c && linkRegs.contains q)
  vecs := allVecs.filter fun w => (codeInstrs c).any fun i => vdstOf i == some w
  his := hiVecs.filter fun w => (codeInstrs c).any fun i => vdstOf i == some w

end VG.Impl.Residue.AArch64
