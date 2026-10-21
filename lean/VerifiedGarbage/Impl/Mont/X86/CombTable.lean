module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-! Shared five-tooth comb table operations over the x86 Montgomery workspace. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def seq (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- Direct table selection is used only for public exponents. -/
def publicSelect (n tab dst : Nat) : Prog isa := seq [
  .block [.mov .eax (.mem (sc windowOffset)), .mov .edx (imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (imm tab),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (imm (2*n))],
  .loop (.block [.mov .eax (.mem (at_ .ecx 0)), .store (at_ .ebp dst) .eax,
    .alu .add .ecx (imm 4), .alu .add .ebp (imm 4), .alu .sub .ebx (imm 1)]) .ne]

/-- Fixed-address masked table scan, accumulating each output word in a
register. Masks are computed once per window, without secret indexing. -/
def wordSelectBody (n tab dst : Nat) (entries : Nat) : Prog isa :=
  seq [
    .block ((List.range entries).flatMap fun j => windowMask j ++ [.store (at_ .esp (4*j)) .ecx]),
    .block [.mov .ebp (.reg .edi)],
    .loop (.block ([.mov .ebx (imm 0)] ++ (List.range entries).flatMap (fun j => [
      .mov .eax (.mem (at_ .ebp (entry n tab j))), .alu .and .eax (.mem (at_ .esp (4*j))),
      .alu .or .ebx (.reg .eax)]) ++ [
      .store (at_ .ebp dst) .ebx, .alu .add .ebp (imm 4),
      .mov .eax (.reg .edi), .alu .add .eax (imm (8*n)), .alu .cmp .ebp (.reg .eax)])) .ne]

def wordSelect (n tab dst : Nat) (entries : Nat := 16) : Prog isa :=
  .frame (.alloc (4*entries)) (wordSelectBody n tab dst entries) (.free (4*entries))

def copyToComb (n tab src : Nat) : Prog isa := seq [
  .block [.mov .eax (.reg .esi), .mov .edx (imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (imm tab),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (imm (2*n))],
  .loop (.block [.mov .eax (.mem (at_ .ebp src)), .store (at_ .ecx 0) .eax,
    .alu .add .ecx (imm 4), .alu .add .ebp (imm 4), .alu .sub .ebx (imm 1)]) .ne]

def combBuild (n e context : Nat) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let tab := context + 16*n
  seq [copyWords n (slot n 0) context, copyWords n (slot n 4) (context+8*n),
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 4) (slot n 3),
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 4),
    copyWords n (slot n 6) tab, copyWords n (slot n 5) (entry n tab 1),
    .block [.mov .eax (imm 1), .store (sc 28) .eax],
    .loop (seq [
      .block [.mov .esi (imm d)],
      .loop (.seq (Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 5) (slot n 5) (slot n 5))
        (.block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)])) .ne,
      .block [.mov .esi (.mem (sc 28)), .alu .add .esi (.reg .esi), .store (sc 28) .esi],
      copyToComb n tab (slot n 5), .block [.alu .cmp .esi (imm 16)]]) .ne,
    .block [.mov .esi (imm 1)],
    .loop (seq [
      .block [.mov .eax (imm 0), .alu .sub .eax (.reg .esi), .alu .and .eax (.reg .esi),
        .store (sc 28) .eax, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax), .store (sc windowOffset) .edx],
      publicSelect n tab (slot n 6),
      .block [.mov .eax (.mem (sc 28)), .store (sc windowOffset) .eax],
      publicSelect n tab (slot n 5),
      Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 6) (slot n 5),
      copyToComb n tab (slot n 7), .block [.alu .add .esi (imm 1), .alu .cmp .esi (imm 32)]]) .ne]


end VG.Impl.Mont.X86.Comb
