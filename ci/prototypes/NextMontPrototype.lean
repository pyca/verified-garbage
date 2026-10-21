import VerifiedGarbage.Impl.Weierstrass.X86.Inv
import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Impl.Mont.X86.Rt.Square
namespace NextMont
-- UNPROVEN screening only. Printed by the existing ISA printer.
def prodAt (j : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ecx (4*j))),
   .mov .edx (.mem (at_ .ebp (if j=0 then 0 else 2^32-4*j))), .mul .edx] ++ accum

def products (u : Nat) : List Instr := (List.range u).flatMap prodAt

def redUnrollCore (u : Nat) : Prog isa := seqs [
  .block [.alu .sub .ebx (.imm (BitVec.ofNat 32 (4*(u-1)))), .alu .cmp .ecx (.reg .ebx)],
  .ite .b (.loop (.block (products u ++ [
    .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))),
    .alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u))), .alu .cmp .ecx (.reg .ebx)])) .b) (.block []),
  .block [.alu .add .ebx (.imm (BitVec.ofNat 32 (4*(u-1)))), .alu .cmp .ecx (.reg .ebx)],
  .ite .b redLoop (.block [])]

def redUnroll (u : Nat) : Prog isa := .seq
 (.block [.alu .cmp .ebx (.imm (BitVec.ofNat 32 (4*(u-1))))])
 (.iteCold .b redLoop (redUnrollCore u))

def crossUnroll (u : Nat) : Prog isa := seqs [
  .block [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .ecx),
    .alu .cmp .eax (.imm (BitVec.ofNat 32 (8*(u-1)+1)))],
  .ite .ae (seqs [
    .block [.shift .shr .eax 1, .alu .add .eax (.reg .ecx),
      .alu .sub .eax (.imm (BitVec.ofNat 32 (4*(u-1)))), .mov .ebx (.reg .eax)],
    .loop (.block (products u ++ [
      .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))),
      .alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u))), .alu .cmp .ecx (.reg .ebx)])) .b]) (.block []),
  .block [.alu .cmp .ecx (.reg .ebp)], .ite .b pairLoop (.block [])]

def tune (u : Nat) : Prog isa → Prog isa
 | .loop (.block xs) c =>
   if xs = prod ++ [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebp)]
   then crossUnroll u
   else if xs = prod ++ [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebx)]
   then redUnroll u else .loop (.block xs) c
 | .seq a b => .seq (tune u a) (tune u b)
 | .ite c a b => .ite c (tune u a) (tune u b)
 | .loop a c => .loop (tune u a) c
 | .frame a b c => .frame a (tune u b) c
 | a => a

def generalInput : Prog isa := seqs [
 .block (lenTimes .ebx 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .ebx)]),
 .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
 .block (ptr .ecx argA .eax ++ [.alu .add .ecx (.reg .edx)] ++ ptr .ebp argB .eax ++
   [.alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .mov .eax (.reg .esi),
    .alu .add .eax (.imm 4), .alu .cmp .eax (.reg .ebx)]),
 .ite .b (.block [.mov .ebx (.reg .eax)]) (.block []),
 .block [.mov .eax (.mem argWs), .alu .add .ebx (.reg .eax), .mov .eax (.mem argA),
   .alu .add .ebx (.reg .eax), .alu .cmp .ecx (.reg .ebx)],
 .ite .b redLoop (.block [])]

def genColumn : Prog isa := seqs [
 .block [.xop (.bin .pxor .xmm0 .xmm0), .xop (.bin .pxor .xmm1 .xmm1)],
 .seq (.block (lenTimes .eax 1 ++ [.alu .sub .eax (.imm 4), .alu .cmp .esi (.reg .eax)]))
   (.ite .b generalInput (.block [])),
 .block carryIn, reduction,
 .block ([.xop (.bin .movdqa .xmm3 .xmm0), .xop (.shift .psrlq .xmm3 32),
   .xop (.bin .paddq .xmm3 .xmm1), .alu .add .esi (.imm 4)] ++ lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)])]

def general : Prog isa := seqs [.block save,
 .block [.mov .esi (.imm 0), .xop (.bin .pxor .xmm3 .xmm3), .mov .eax (.imm (-1)), .xop (.movd .xmm7 .eax)],
 .loop genColumn .ne,
 .block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 52), .alu .add .ebp (.reg .esi),
   .movqStore (at_ .ebp 0) .xmm3] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]),
 subM, .block mask, select, .block restoreRegs]

def combined (u : Nat) : Prog isa := .seq
 (.block [.mov .eax (.mem argA), .mov .edx (.mem argB), .alu .cmp .eax (.reg .edx)])
 (.ite .e (tune u square) (tune u general))

def printFn (name : String) (p : Prog isa) (callee : String := "proto_mont0") : String :=
 ".globl "++name++"\n.p2align 6\n"++name++":\n"++
 "\n".intercalate ((printer.function p).map fun l => match l with
 | .text s => s | .call n => "call "++(if n = "proto_gcd_C" then n else callee) | .sym .. => "ERROR")++"\n"
end NextMont

namespace ScalarCombaProto
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
-- ESI:EBX:EDI hold low, middle, high of a 96-bit accumulator.
-- Public column/end and the incoming carry use the existing scratch header.
def seqs := VG.Impl.Mont.X86.Rt.Square.seqs

def accum : List Instr := [.alu .add .esi (.reg .eax), .alu .adc .ebx (.reg .edx), .alu .adc .edi (.imm 0)]
def prodAt (j : Nat) : List Instr := [
 .mov .eax (.mem (at_ .ecx (4*j))),
 .mov .edx (.mem (at_ .ebp (if j=0 then 0 else 2^32-4*j))), .mul .edx] ++ accum

def sPtr (d t : Reg) : List Instr := ptr d argS t

def getEnd : List Instr := sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 0))]

def crossLoop (u : Nat) : Prog isa := seqs [
 .block [.mov .eax (.reg .ebp), .alu .sub .eax (.reg .ecx),
   .alu .cmp .eax (.imm (BitVec.ofNat 32 (8*u)))],
 .ite .ae (.loop (.block ((List.range u).flatMap prodAt ++ [
   .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))), .alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u))),
   .mov .eax (.reg .ebp), .alu .sub .eax (.reg .ecx),
   .alu .cmp .eax (.imm (BitVec.ofNat 32 (8*u)))])) .ae) (.block []),
 .block [.alu .cmp .ecx (.reg .ebp)],
 .ite .b (.loop (.block (prodAt 0 ++ [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4),
    .alu .cmp .ecx (.reg .ebp)])) .b) (.block [])]

def redLoop (u : Nat) : Prog isa := seqs [
 .block (getEnd ++ [.alu .sub .eax (.reg .ecx), .alu .cmp .eax (.imm (BitVec.ofNat 32 (4*u)))]),
 .ite .ae (.loop (.block ((List.range u).flatMap prodAt ++ [
   .alu .add .ecx (.imm (BitVec.ofNat 32 (4*u))), .alu .sub .ebp (.imm (BitVec.ofNat 32 (4*u)))] ++
   getEnd ++ [.alu .sub .eax (.reg .ecx), .alu .cmp .eax (.imm (BitVec.ofNat 32 (4*u)))])) .ae) (.block []),
 .block (getEnd ++ [.alu .cmp .ecx (.reg .eax)]),
 .ite .b (.loop (.block (prodAt 0 ++ [.alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4)] ++
    getEnd ++ [.alu .cmp .ecx (.reg .eax)])) .b) (.block [])]

def cross (u : Nat) : Prog isa := seqs [
 .block (sPtr .edi .eax ++ [.mov .esi (.mem (at_ .edi 4))] ++ lenTimes .eax 1 ++
   [.alu .sub .eax (.imm 4), .alu .cmp .esi (.reg .eax)]),
 .ite .b (seqs [
   .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
   .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
   .block ([.mov .ecx (.mem argWs), .mov .eax (.mem argA), .alu .add .ecx (.reg .eax),
     .mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx), .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
     .mov .esi (.imm 0), .mov .ebx (.imm 0), .mov .edi (.imm 0)]),
   crossLoop u,
   .block ([.alu .add .esi (.reg .esi), .alu .adc .ebx (.reg .ebx), .alu .adc .edi (.reg .edi)] ++
     sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 4)), .alu .and .eax (.imm 4)]),
   .ite .e (.block (sPtr .edx .eax ++ [.mov .eax (.mem (at_ .edx 4)), .shift .shr .eax 1,
     .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA),
     .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ accum)) (.block [])])
   (.block [.mov .esi (.imm 0), .mov .ebx (.imm 0), .mov .edi (.imm 0)]),
 .block (sPtr .edx .eax ++ [.alu .add .esi (.mem (at_ .edx 8)),
   .alu .adc .ebx (.mem (at_ .edx 12)), .alu .adc .edi (.imm 0)])]

def reduce (u : Nat) : Prog isa := seqs [
 .block (sPtr .ecx .eax ++ [.mov .ebp (.mem (at_ .ecx 4))] ++ lenTimes .eax 0 ++
   [.mov .edx (.reg .ebp), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
 .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
 .block [.alu .cmp .ebp (.reg .eax)],
 .ite .b (.block [.mov .eax (.reg .ebp)]) (.block []),
 .block [.alu .add .eax (.reg .ecx), .alu .add .eax (.imm 52), .store (at_ .ecx 0) .eax,
   .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
   .alu .sub .ebp (.reg .edx), .mov .eax (.mem argWs), .alu .add .ebp (.reg .eax),
   .mov .eax (.mem argM), .alu .add .ebp (.reg .eax)],
 redLoop u,
 .block (sPtr .ecx .eax ++ [.mov .ebp (.mem (at_ .ecx 4))] ++ lenTimes .eax 0 ++ [.alu .cmp .ebp (.reg .eax)]),
 .ite .b (.block [
   .mov .eax (.reg .esi), .mov .edx (.mem (at_ .ecx 16)), .mul .edx,
   .mov .edx (.reg .ecx), .alu .add .edx (.imm 52), .alu .add .edx (.reg .ebp), .store (at_ .edx 0) .eax,
   .mov .ebp (.mem argM), .mov .edx (.mem argWs), .alu .add .ebp (.reg .edx),
   .mov .edx (.mem (at_ .ebp 0)), .mul .edx,
   .alu .add .esi (.reg .eax), .alu .adc .ebx (.reg .edx), .alu .adc .edi (.imm 0)])
   (.block [.mov .edx (.reg .ecx), .alu .add .edx (.imm 52), .alu .add .edx (.reg .ebp), .store (at_ .edx 0) .esi]),
 .block (sPtr .ecx .eax ++ [.store (at_ .ecx 8) .ebx, .store (at_ .ecx 12) .edi,
   .mov .eax (.mem (at_ .ecx 4)), .alu .add .eax (.imm 4), .store (at_ .ecx 4) .eax] ++
   lenTimes .edx 1 ++ [.alu .cmp .eax (.reg .edx)])]

def square (u : Nat) : Prog isa := seqs [
 .block (save ++ ptr .edx argInv .eax ++ [.mov .eax (.mem (at_ .edx 0)), .store (at_ .edi 16) .eax,
   .mov .eax (.imm 0), .store (at_ .edi 4) .eax, .store (at_ .edi 8) .eax, .store (at_ .edi 12) .eax]),
 .loop (.seq (cross u) (reduce u)) .ne,
 .block (sPtr .edi .eax ++ lenTimes .ebp 1 ++ [.alu .add .ebp (.reg .edi), .alu .add .ebp (.imm 52),
   .mov .eax (.mem (at_ .edi 8)), .store (at_ .ebp 0) .eax,
   .mov .eax (.mem (at_ .edi 12)), .store (at_ .ebp 4) .eax] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)]),
 subM, .block mask, select, .block restoreRegs]

def dispatch (u : Nat) : Prog isa := .seq
 (.block [.mov .eax (.mem argA), .mov .edx (.mem argB), .alu .cmp .eax (.reg .edx)])
 (.ite .e (square u) VG.Impl.Mont.X86.Rt.scalarBody)
end ScalarCombaProto

namespace KeyCheckMontProto
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.KeyCheck

def mulArgs (full : Bool) (o a b : Nat) : List Instr :=
 let L := VG.Impl.Rsa.X86.KeyCheckRt.lay full
 let F : Lay := { L with len := L.len+9, ws := L.ws+9 }
 let off (i j : Nat) := arrPtr F .eax j .edx ++
   [.alu .sub .eax (.reg .edi), .store (at_ .esp (4*i)) .eax]
 [.mov .eax (.mem (argOp (L.ws+1+9))), .store (at_ .esp 4) .eax, .store (at_ .esp 0) .edi] ++
 bytesB F .eax ++ [.shift .shr .eax 3, .store (at_ .esp 8) .eax] ++
 off 3 aY ++ [.mov .eax (.imm 124), .store (at_ .esp 16) .eax] ++ off 5 aT ++
 off 6 o ++ off 7 a ++ off 8 b

def mmul (full : Bool) (o a b : Nat) : Prog isa :=
 .frame (.alloc 36) (.seq (.block (mulArgs full o a b))
   (.call Spec.Rsa.MontMul.mulApi.name VG.Impl.Mont.X86.Rt.body)) (.free 36)

def qiCheck (full : Bool) : Prog isa :=
 let L := VG.Impl.Rsa.X86.KeyCheckRt.lay full
 VG.Impl.Rsa.X86.Keys.seqs [
   sel L aX aZ aQI sF,
   copy L aY aP, .block (orOne L aY),
   .block (arrPtr L .eax aY .edx ++ [.mov .ebx (.mem (at_ .eax 0))] ++
     VG.Impl.Mont.X86.Dynamic.inverse ++ [.store (sc 124) .eax]),
   mmul full aA aQ aX,
   copy L aVD aY, .block (clrLow L aVD),
   mmul full aVR aVD aVD,
   eqS L sF aA aVR aW, .block acc]

def crtChecks (full : Bool) : Prog isa :=
 let L := VG.Impl.Rsa.X86.KeyCheckRt.lay full
 VG.Impl.Rsa.X86.Keys.seqs (VG.Impl.Rsa.X86.KeyCheckRt.eqA full aVQ aQ ++
   VG.Impl.Rsa.X86.KeyCheckRt.eqA full aVR aZ ++
   [copy L aM1 aP, .block (clrLow L aM1), copy L aM2 aQ, .block (clrLow L aM2)] ++
   VG.Impl.Rsa.X86.KeyCheckRt.ltA full aDP aM1 ++
   VG.Impl.Rsa.X86.KeyCheckRt.mulA full aE aDP aM1 cnt33 ++
   VG.Impl.Rsa.X86.KeyCheckRt.eqA full aA aOne ++
   VG.Impl.Rsa.X86.KeyCheckRt.ltA full aDQ aM2 ++
   VG.Impl.Rsa.X86.KeyCheckRt.mulA full aE aDQ aM2 cnt33 ++
   VG.Impl.Rsa.X86.KeyCheckRt.eqA full aA aOne ++
   VG.Impl.Rsa.X86.KeyCheckRt.ltA full aQI aP ++ [qiCheck full])

def crtBody (full : Bool) : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [
 VG.Impl.Rsa.X86.KeyCheckRt.start full, VG.Impl.Rsa.X86.KeyCheckRt.division full, crtChecks full]

def sized (full : Bool) : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [VG.Impl.Rsa.X86.KeyCheckRt.loads full,
 (if full then VG.Impl.Rsa.X86.Keys.seqs [crtBody full,
   VG.Impl.Rsa.X86.KeyCheckRt.dChecks1 full, VG.Impl.Rsa.X86.KeyCheckRt.division full,
   VG.Impl.Rsa.X86.KeyCheckRt.dChecks2 full, VG.Impl.Rsa.X86.KeyCheckRt.division full,
   VG.Impl.Rsa.X86.KeyCheckRt.dChecks3 full] else crtBody full),
 .block [.mov .eax (.mem (sc sMask))]]

def code (full : Bool) : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [
 .block (entry full),
 .seq (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 0)) (.block modulusCheck))
   (.ite .e
     (.seq (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) exponentCheck)
       (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure (sized full)))) failure),
 .block VG.Impl.Bignum.X86.PublicFn.restore]
end KeyCheckMontProto

namespace BatchCrtProto
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD)

def batchCall : Prog isa :=
 let L := VG.Impl.Rsa.X86.CrtValuesRt.lay
 let F : Lay := { L with len := L.len+4, ws := L.ws+4 }
 .frame (.alloc 16) (.seq (.block (
   [.store (at_ .esp 0) .edi] ++ bytesB F .eax ++ [.shift .shr .eax 2, .store (at_ .esp 4) .eax,
    .mov .eax (.mem (argOp 13)), .store (at_ .esp 8) .eax,
    .mov .eax (.mem (argOp 15)), .store (at_ .esp 12) .eax]))
   (.call "proto_inv_C" (.block []))) (.free 16)

def checks : Prog isa :=
 let L := VG.Impl.Rsa.X86.CrtValuesRt.lay
 VG.Impl.Rsa.X86.Keys.seqs ([
  eqS L sE1 aDQ aQ aT1, eqS L sE2 aDR aZero aT1] ++ VG.Impl.Rsa.X86.CrtValuesRt.invSetup ++ [
  batchCall, eqS L sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy L aDQ aD, copy L aDD aP, .block (clrLow L aDD)])

def code : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [
 .block VG.Impl.Rsa.X86.CrtValues.entry,
 .seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 6))
  (.seq (.block modulusCheck) (.ite .e
   (VG.Impl.Rsa.X86.Keys.seqs [VG.Impl.Rsa.X86.CrtValuesRt.loads,
    VG.Impl.Rsa.X86.CrtValuesRt.firstDiv, checks,
    VG.Impl.Rsa.X86.CrtValuesRt.div aDR2, VG.Impl.Rsa.X86.CrtValuesRt.divQ,
    VG.Impl.Rsa.X86.CrtValuesRt.stores]) VG.Impl.Rsa.X86.CrtValues.failure)),
 .block VG.Impl.Bignum.X86.PublicFn.restore]
end BatchCrtProto

namespace IsaBatchGcdProto
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt

def off (n j : Nat) := 160+j*(4*n+8)
def seqs := VG.Impl.Rsa.X86.Keys.seqs

def init (n : Nat) : List Instr :=
 let F:=off n 4; let G:=off n 5; let M:=off n 8; let X:=off n 0; let T:=off n 13; let W:=off n 3
 VG.Impl.Weierstrass.X86.copy n F M ++ zeros (F+4*n) 1 ++
 [.mov .eax (.mem (sc X)), .alu .and .eax (.imm 1), .alu .xor .eax (.imm 1),
  .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax)] ++ maskCopy n T M ++
 (List.range n).flatMap (fun j => [.mov .eax (.mem (sc (X+4*j))),
   .alu (if j=0 then .add else .adc) .eax (.mem (sc (T+4*j))), .store (sc (G+4*j)) .eax]) ++
 [.mov .eax (.imm 0),.alu .adc .eax (.imm 0),.store (sc (G+4*n)) .eax,
 .mov .eax (.imm 1),.store (sc W) .eax]

def start (n : Nat) : List Instr :=
 let W:=off n 3
 VG.Impl.Weierstrass.X86.copy 1 (W+4) (off n 4) ++ VG.Impl.Weierstrass.X86.copy 1 (W+8) (off n 5) ++
 zeros (W+12) 4 ++ [.mov .eax (.imm 1),.store (sc (W+12)) .eax,.store (sc (W+24)) .eax]

def update (n : Nat) : List Instr :=
 let F:=off n 4; let G:=off n 5; let T:=off n 11; let U:=off n 13; let W:=off n 3
 linear (W+12) (W+16) T F G U (n+1) (n-1) ++ shr30 (off n 6) T (n+1) ++
 linear (W+20) (W+24) T F G U (n+1) (n-1) ++ shr30 (off n 7) T (n+1) ++
 VG.Impl.Weierstrass.X86.copy (n+1) F (off n 6) ++ VG.Impl.Weierstrass.X86.copy (n+1) G (off n 7)

def finish (n : Nat) : List Instr :=
 let F:=off n 4; let O:=off n 1; let T:=off n 13
 maskOf (F+4*n) ++ maskCopy n T F ++
 -- Negating through two's complement, including a carry from the low word.
 [.mov .ebx (.reg .ecx),.alu .and .ebx (.imm 1)] ++
 (List.range n).flatMap (fun j =>
  [.mov .eax (.mem (sc (F+4*j))),.alu .xor .eax (.reg .ecx),.store (sc (T+4*j)) .eax]) ++
 [.mov .eax (.imm 0),.alu .sub .eax (.reg .ebx)] ++
 (List.range n).flatMap (fun j =>
  [.mov .eax (.mem (sc (T+4*j))),.alu .adc .eax (.imm 0),.store (sc (O+4*j)) .eax])

def body (n : Nat) : Prog isa := seqs [
 .block (init n ++ [.mov .esi (.imm (BitVec.ofNat 32 (3*(n+1))))]),
 .loop (.seq (.frame (.push [.esi])
   (seqs [.block (start n),wordSteps (off n 3) 30,.block (update n)]) (.pop .esi 1))
   (.block [.alu .sub .esi (.imm 1),.alu .cmp .esi (.imm 0)])) .ne,
 .block (finish n)]

def choose (len : Nat) (k : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem (argOp 5)), .alu .cmp .eax (.imm (BitVec.ofNat 32 len))])
 (.ite .e (body k) fallback)
def code : Prog isa := choose 256 66 (choose 384 98 (choose 512 130
  (VG.Impl.Rsa.X86.KeyRt.gcd VG.Impl.Rsa.X86.RecoverRt.nar)))
end IsaBatchGcdProto

namespace BatchGcdProto
open VG VG.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.Keys (seqs)
def gcdCall : Prog isa :=
 let F : Lay := { nar with len := nar.len+2, ws := nar.ws+2 }
 .frame (.alloc 8) (.seq (.block (
   [.store (at_ .esp 0) .edi] ++ bytesB F .eax ++ [.shift .shr .eax 2, .store (at_ .esp 4) .eax]))
   (.call "proto_gcd_C" (.block []))) (.free 8)
def newFactors : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [gcdSet,gcdCall,divSet,div nar VG.Impl.Rsa.X86.Recover.aQ VG.Impl.Rsa.X86.Recover.aRm VG.Impl.Rsa.X86.Recover.aDv VG.Impl.Rsa.X86.Recover.aDt,order]
def newFin : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [finY,newFactors,stores]
def newRest : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [halving,mont,candLoop,newFin]
def newFused : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [fusedPrepare,mont,fusedLoop,newFin]
def newSelected : Prog isa := .seq (.block recoveryChoice) (.iteCold .b newRest newFused)
def newSized : Prog isa := .seq numbers (.ite .e newSelected VG.Impl.Rsa.X86.Recover.failure)
def newBody : Prog isa := .seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.seq (.block VG.Impl.Bignum.X86.modulusCheck) (.ite .e newSized VG.Impl.Rsa.X86.Recover.failure))
def code : Prog isa := .seq (.block VG.Impl.Rsa.X86.Recover.entry) (.seq newBody (.block VG.Impl.Bignum.X86.PublicFn.restore))
end BatchGcdProto

def replaceGcd : Prog isa → Prog isa
 | .call n b => if n="proto_gcd_C" then IsaBatchGcdProto.code else .call n b
 | .seq a b => .seq (replaceGcd a) (replaceGcd b)
 | .ite c a b => .ite c (replaceGcd a) (replaceGcd b)
 | .loop a c => .loop (replaceGcd a) c
 | .frame a b c => if a = .alloc 8 then IsaBatchGcdProto.code else .frame a (replaceGcd b) c
 | a => a

namespace FastDoubleProto
open VG VG.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.Recover (mXm mX aN aZ mAcc sCand)
open VG.Impl.Rsa.X86.Keys (sC)
def twice : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [
 VG.Impl.Rsa.X86.KeyRt.chain nar .adc mXm mX mX false,sub3 nar mAcc mXm aN,
 .block [.store (sc sC) .ebx],sel nar mXm mAcc mXm sC]
def multiply : Prog isa := .seq
 (.block [.mov .eax (.mem (sc sCand)),.alu .cmp .eax (.imm 0)])
 (.ite .e twice fusedMultiply)
def tune : Prog isa → Prog isa
 | .seq (.block xs) b =>
   if xs = [.mov .eax (.mem (sc sCand)), .alu .sub .eax (.imm 14)] then multiply
   else .seq (.block xs) (tune b)
 | .seq a b => .seq (tune a) (tune b)
 | .ite c a b => .ite c (tune a) (tune b)
 | .loop a c => .loop (tune a) c
 | .frame a b c => .frame a (tune b) c
 | a => a
end FastDoubleProto

namespace FastR2Proto
open VG VG.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.Recover (mR2 aOne aZ aN mAcc mBase mXm)
open VG.Impl.Rsa.X86.Keys (seqs)
def rMinus (t j : Nat) : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [
 copy nar mR2 aZ,
 .block (arrPtr nar .eax mR2 .edx ++ [.alu .add .eax (.reg .edx),.alu .sub .eax (.imm 16),
   .mov .ecx (.imm 1),.store (at_ .eax 0) .ecx]),
 sub3 nar mR2 mR2 aN,
 VG.Impl.Rsa.X86.Keys.seqs ((List.range t).flatMap fun _ => addMod nar mR2 mR2 mR2 aN aZ mAcc),
 .block [.mov .esi (.imm (BitVec.ofNat 32 j))],
 .loop (.seq (mmul mR2 mR2 mR2) (.block [.alu .sub .esi (.imm 1),.alu .cmp .esi (.imm 0)])) .ne]
def choose (len t j : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem (argOp 5)),.alu .cmp .eax (.imm (BitVec.ofNat 32 len))])
 (.ite .e (rMinus t j) fallback)
def setup : Prog isa := choose 256 1 11 (choose 384 3 10 (choose 512 1 12 setupR2))
def mont : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [sub3 nar aZ aN aN,copy nar aOne aZ,
 .block (setOne nar aOne),copy nar mBase aN,.block setupInverse,setup,copy nar mXm aOne,
 mmul mXm mXm mR2,montTail]
def fused : Prog isa := VG.Impl.Rsa.X86.Keys.seqs [fusedPrepare,mont,fusedLoop,BatchGcdProto.newFin]
def selected : Prog isa := .seq (.block recoveryChoice) (.iteCold .b BatchGcdProto.newRest fused)
def sized : Prog isa := .seq numbers (.ite .e selected VG.Impl.Rsa.X86.Recover.failure)
def body : Prog isa := .seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4))
 (.seq (.block VG.Impl.Bignum.X86.modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))
def code : Prog isa := .seq (.block VG.Impl.Rsa.X86.Recover.entry)
 (.seq body (.block VG.Impl.Bignum.X86.PublicFn.restore))
end FastR2Proto

def main : IO Unit := do
 let modes := [VG.Impl.Mont.X86.Rt.body, NextMont.tune 2 VG.Impl.Mont.X86.Rt.body,
   NextMont.tune 4 VG.Impl.Mont.X86.Rt.body, NextMont.tune 8 VG.Impl.Mont.X86.Rt.body,
   NextMont.combined 4, NextMont.combined 8,
   ScalarCombaProto.dispatch 2, ScalarCombaProto.dispatch 4, ScalarCombaProto.dispatch 8, ScalarCombaProto.dispatch 16]
 let codes := (modes.zipIdx).map fun (p,i) =>
   NextMont.printFn ("proto_mont"++toString i) p ++
   NextMont.printFn ("proto_recover"++toString i) VG.Impl.Rsa.X86.RecoverRt.code ("proto_mont"++toString i)
 IO.FS.writeFile "/workspace/scratch/openssl/next-generated.S" (
   ".intel_syntax noprefix\n.text\n"++String.join codes++
   NextMont.printFn "proto_recover10" BatchGcdProto.code "proto_mont7" ++
   NextMont.printFn "proto_recover11" BatchGcdProto.code "proto_mont8" ++
   NextMont.printFn "proto_recover12" (replaceGcd BatchGcdProto.code) "proto_mont7" ++
   NextMont.printFn "proto_recover13" (replaceGcd BatchGcdProto.code) "proto_mont8" ++
   NextMont.printFn "proto_recover14" (FastDoubleProto.tune (replaceGcd BatchGcdProto.code)) "proto_mont7" ++
   NextMont.printFn "proto_recover15" (FastDoubleProto.tune (replaceGcd BatchGcdProto.code)) "proto_mont8" ++
   NextMont.printFn "proto_recover16" (FastDoubleProto.tune (replaceGcd FastR2Proto.code)) "proto_mont7" ++
   NextMont.printFn "proto_recover17" (FastDoubleProto.tune (replaceGcd FastR2Proto.code)) "proto_mont8" ++
   NextMont.printFn "proto_check0" (VG.Impl.Rsa.X86.KeyCheckRt.code false) ++
   NextMont.printFn "proto_check1" (KeyCheckMontProto.code false) ++
   NextMont.printFn "proto_crt0" VG.Impl.Rsa.X86.CrtValuesRt.code ++
   NextMont.printFn "proto_crt2" BatchCrtProto.code "proto_inv_C" ++
   NextMont.printFn "proto_crt3" BatchCrtProto.code "proto_inv_active_C" ++
   ".section .note.GNU-stack,\"\",@progbits\n")
