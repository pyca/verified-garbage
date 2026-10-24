module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Spec.Ffdh.VettedGroups

/-! Public exact-domain recognition. Unrecognized groups retain the full scalar bound.
The shared policy accepts a missing q or exactly (p-1)/2, never merely a matching width. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached.Policy
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

structure Group where
 len : Nat
 bits : Nat
 prime : Nat
 deriving DecidableEq

def groups : List Group :=
 [⟨256,225,Spec.Ffdh.modp2048Prime⟩,⟨256,225,Spec.Ffdh.ffdhe2048Prime⟩,
  ⟨384,275,Spec.Ffdh.modp3072Prime⟩,⟨384,275,Spec.Ffdh.ffdhe3072Prime⟩,
  ⟨512,325,Spec.Ffdh.modp4096Prime⟩,⟨512,325,Spec.Ffdh.ffdhe4096Prime⟩,
  ⟨768,375,Spec.Ffdh.modp6144Prime⟩,⟨768,375,Spec.Ffdh.ffdhe6144Prime⟩,
  ⟨1024,400,Spec.Ffdh.modp8192Prime⟩,⟨1024,400,Spec.Ffdh.ffdhe8192Prime⟩]

def Group.domain (g : Group) : List Byte :=
 Spec.Rsa.i2osp g.prime g.len ++ Spec.Rsa.i2osp 2 g.len ++
 Spec.Rsa.i2osp ((g.prime-1)/2) g.len

/-- Pure reference view of the recognizer's exact public byte comparisons. -/
def recognizeList : List Group → Nat → List Byte → Nat
 | [],_,_=>0
 | g::gs,k,dom=>if g.len=k ∧ dom=g.domain.take dom.length then g.bits else recognizeList gs k dom

def wordBytes (n : Nat) : List Byte := (List.range 4).map fun i => BitVec.ofNat 8 (n / 2^(8*i))
def Group.bytes (g : Group) : List Byte := wordBytes g.len ++ wordBytes g.bits ++ g.domain
def tableBytes : List Byte := groups.flatMap Group.bytes
def tableWord (i : Nat) : BitVec 64 :=
 (show Mem from fun a : Addr => tableBytes.getD a.toNat 0).readW (BitVec.ofNat 64 (8*i)) 64
def tableWords : List (BitVec 64) := (List.range (tableBytes.length/8)).map tableWord

def tableSym : String := "VG_FFDH_VETTED_GROUPS_A64"
def tableConsts : List (String × List (BitVec 64)) := [(tableSym,tableWords)]

/-- x1 points to p or q, and x2 is p_len. Scan only public bytes. -/
def boundSource : List Instr :=
 [ldh .x1 sDom,ldh .x2 sLen,ldh .x3 sDL,.lsl .x .x4 .x2 1,.subs .x .x3 .x3 .x4,
  .add .x .x4 .x1 .x4,.cselc .x .x1 .x1 .x4 .eq]

def scanStep : List Instr :=
 [.ldrb .x3 .x1 0,.addImm .x .x1 .x1 1,.subImm .x .x2 .x2 1]
def countStep : List Instr := [.addImm .x .x10 .x10 1,.lsr .x .x3 .x3 1]

def boundBits : Prog isa := .seq (.block (boundSource ++ [movi .x10 0]))
 (.seq (.loop (.block scanStep) (.zero .x .x3))
 (.seq (.block [.lsl .x .x2 .x2 3])
 (.seq (.loop (.block countStep) (.nonzero .x .x3))
 (.block [.add .x .x10 .x10 .x2,sth .x10 sBits]))))

-- Only public input addresses and fixed domain lengths control these loops.
def compareBody : List Instr := [.ldrb .x8 .x1 0,.ldrb .x9 .x2 0,.logic .eor .x .x8 .x8 .x9,
 .logic .orr .x .x11 .x11 .x8,.addImm .x .x1 .x1 1,.addImm .x .x2 .x2 1]

def compare : Prog isa := .seq (.block [ldh .x1 sDom,ldh .x5 sDL,mov .x2 .x4,movi .x11 0])
 (countLoop .x5 compareBody)

/-- The current record's cap is selected only after an exact comparison. -/
def matched : List Instr :=
 [ldh .x10 sBits,.subs .x .x9 .x10 .x6,.csel .x .x10 .x6 .x10,sth .x10 sBits,movi .x7 1]

def recordHead : List Instr := [.ldr .w .x5 .x4 0,
 .ldr .w .x6 .x4 4,.addImm .x .x4 .x4 8,ldh .x3 sLen,.sub .x .x3 .x3 .x5]

def recordTail : List Instr := [.subImm .x .x2 .x4 8,.ldr .w .x5 .x2 0,
 .lsl .x .x3 .x5 1,.add .x .x3 .x3 .x5,.add .x .x4 .x4 .x3,.subImm .x .x7 .x7 1]

def recordChoice : Prog isa :=
 .ite (.zero .x .x3) (.seq compare (.ite (.zero .x .x11) (.block matched) (.block []))) (.block [])

def record : Prog isa := .seq (.block recordHead) (.seq recordChoice (.block recordTail))

def recognize : Prog isa := .seq boundBits
 (.seq (.block [.adrSym .x4 tableSym,movi .x7 10]) (.loop record (.nonzero .x .x7)))

def rowStep : List Instr := [.subImm .x .x12 .x12 5,.addImm .x .x13 .x13 1,
 movi .x14 5,.subs .x .x14 .x12 .x14,.lsr .x .x14 .x14 63]

/-- Positive public bits to ceil(bits/8), ceil(bits/5), stored in header/context. -/
def metadataHead : List Instr := [ldh .x10 sBits,.addImm .x .x11 .x10 7,.lsr .x .x11 .x11 3,
 sth .x11 sBytes,.addImm .x .x12 .x10 4,movi .x13 0]

def metadataTail : List Instr := [sth .x13 sRows,ldh .x8 sCtx,
 st .x10 .x8 0,st .x11 .x8 8,st .x13 .x8 16]

def metadata : Prog isa := .seq (.block metadataHead)
 (.seq (.loop (.block rowStep) (.zero .x .x14)) (.block metadataTail))

end VG.Impl.Ffdh.AArch64.Cached.Policy
