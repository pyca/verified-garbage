module

public import VerifiedGarbage.Spec.Ffdh.VettedGroups
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.Artifact

/-! Architecture-independent exact encodings of the ten reviewed MODP/FFDHE groups.
The little-endian record headers are internal public-table data; p/g/q use big-endian octets. -/
@[expose] public section
namespace VG.Impl.Ffdh.VettedGroups
open VG

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

end VG.Impl.Ffdh.VettedGroups
