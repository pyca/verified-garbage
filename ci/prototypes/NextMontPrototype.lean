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
 | .text s => s | .call _ => "call "++callee | .sym .. => "ERROR")++"\n"
end NextMont

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

def main : IO Unit := do
 let modes := [VG.Impl.Mont.X86.Rt.body, NextMont.tune 2 VG.Impl.Mont.X86.Rt.body,
   NextMont.tune 4 VG.Impl.Mont.X86.Rt.body, NextMont.tune 8 VG.Impl.Mont.X86.Rt.body,
   NextMont.combined 4, NextMont.combined 8]
 let codes := (modes.zipIdx).map fun (p,i) =>
   NextMont.printFn ("proto_mont"++toString i) p ++
   NextMont.printFn ("proto_recover"++toString i) VG.Impl.Rsa.X86.RecoverRt.code ("proto_mont"++toString i)
 IO.FS.writeFile "/workspace/scratch/openssl/next-generated.S" (
   ".intel_syntax noprefix\n.text\n"++String.join codes++
   NextMont.printFn "proto_check0" (VG.Impl.Rsa.X86.KeyCheckRt.code false) ++
   NextMont.printFn "proto_check1" (KeyCheckMontProto.code false) ++
   NextMont.printFn "proto_crt0" VG.Impl.Rsa.X86.CrtValuesRt.code ++
   ".section .note.GNU-stack,\"\",@progbits\n")
