module

public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Ffdh.VettedGroups
import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Impl.Bignum.Arm.CompareBytes

/-! Exact vetted-domain recognition with one shared table and one comparison loop. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.VettedGroups
open VG VG.Arm

structure Group where
  len : Nat
  bits : Nat
  prime : Nat
  deriving DecidableEq

def groups : List Group :=
  [⟨256, 225, Spec.Ffdh.modp2048Prime⟩, ⟨256, 225, Spec.Ffdh.ffdhe2048Prime⟩,
   ⟨384, 275, Spec.Ffdh.modp3072Prime⟩, ⟨384, 275, Spec.Ffdh.ffdhe3072Prime⟩,
   ⟨512, 325, Spec.Ffdh.modp4096Prime⟩, ⟨512, 325, Spec.Ffdh.ffdhe4096Prime⟩,
   ⟨768, 375, Spec.Ffdh.modp6144Prime⟩, ⟨768, 375, Spec.Ffdh.ffdhe6144Prime⟩,
   ⟨1024, 400, Spec.Ffdh.modp8192Prime⟩, ⟨1024, 400, Spec.Ffdh.ffdhe8192Prime⟩]

def Group.domain (g : Group) : List Byte :=
  Spec.Rsa.i2osp g.prime g.len ++ Spec.Rsa.i2osp 2 g.len ++
    Spec.Rsa.i2osp ((g.prime - 1) / 2) g.len

/-- A pure view of the exact byte comparisons performed by the scan. -/
def recognize : List Group → Nat → List Byte → Nat
  | [], _, _ => 0
  | g :: gs, k, dom =>
    if g.len = k ∧ dom = g.domain.take dom.length then g.bits else recognize gs k dom

def wordBytes (x : Nat) : List Byte :=
  (List.range 4).map fun i => BitVec.ofNat 8 (x / 2 ^ (8 * i))

def Group.bytes (g : Group) : List Byte := wordBytes g.len ++ wordBytes g.bits ++ g.domain

def tableBytes : List Byte := groups.flatMap Group.bytes

def tableWord (i : Nat) : BitVec 64 :=
  (show Mem from fun a : Addr => tableBytes.getD a.toNat 0).readW (BitVec.ofNat 64 (8 * i)) 64

def tableWords : List (BitVec 64) := (List.range (tableBytes.length / 8)).map tableWord

def tableSym : String := "VG_FFDH_VETTED_GROUPS"
def tableConsts : List (String × List (BitVec 64)) := [(tableSym, tableWords)]

/-- The table pointer advances over each record once. The existing RSA
byte comparator preserves the public outer-loop registers. -/
def header : List Instr :=
  [.ldr .r5 .r4 0, .ldr .r11 .r4 4, .dp .add .r4 .r4 (.imm 8),
   .cmp .r5 (.reg .r6), .dp .add .r5 .r5 (.shifted .r5 .lsl 1), .mov .r2 (.imm 1)]

def compareArgs : List Instr :=
  [.mov .r0 (.reg .r9), .mov .r1 (.reg .r4), .mov .lr (.reg .r10), .mov .r2 (.imm 0)]

def compare : Prog isa := .seq (.block compareArgs) VG.Impl.Bignum.Arm.compareBytes

def matched : List Instr := [.mov .r7 (.imm 0)]
def next : List Instr :=
  [.mov .r11 (.imm 0), .dp .add .r4 .r4 (.reg .r5), .subs .r7 .r7 (.imm 1)]

def finish : Prog isa :=
  .seq (.block [.cmp .r2 (.imm 0)])
    (.seq (.ite .eq (.block matched) (.block next)) (.block [.cmp .r7 (.imm 0)]))

def step : Prog isa :=
  .seq (.block header) (.seq (.ite .eq compare (.block [])) finish)

def loop : Prog isa := .loop step .ne

/-- Return the vetted cap in r11, zero when no complete domain matches.
The workspace pointer r0 is restored and memory is unchanged. -/
def entry : List Instr :=
  [.mov .r8 (.reg .r0), .ldrSp .r9 24, .ldrSp .r10 28,
    .ldrSp .r6 32, .adrSym .r4 tableSym, .mov .r7 (.imm 10)]

def code : Prog isa := .seq (.block entry) (.seq loop (.block [.mov .r0 (.reg .r8)]))

end VG.Impl.Ffdh.Arm.VettedGroups
