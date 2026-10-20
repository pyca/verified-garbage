module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash

/-! # Public addresses and lengths for each streaming-hash call -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Pbkdf2.Stream.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

structure HashPublic where
  input : BitVec 32
  output : BitVec 32
  scratch : BitVec 32
  sp : BitVec 32

structure HashAt {H : Hash} (K : HashOK H) (len : Nat) (p : HashPublic) (s : State) : Prop where
  resources : HashResources K p.input p.output p.scratch len s
  esp : s.gpr .esp = p.sp
  esi : s.gpr .esi = p.input
  edi : s.gpr .edi = p.output
  ebp : s.gpr .ebp = p.scratch

def HashBaseAt {H : Hash} (K : HashOK H) (len : Nat) (p : HashPublic) (s : State) : Prop :=
  HashAt K len p s ∧ s.gpr .ebx = p.scratch + 512#32

def HashUpdateAt {H : Hash} (K : HashOK H) (len : Nat) (p : HashPublic) (s : State) : Prop :=
  HashBaseAt K len p s ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = BitVec.ofNat 32 len ∧ s.gpr .edx = p.input

def HashFinalAt {H : Hash} (K : HashOK H) (len : Nat) (p : HashPublic) (s : State) : Prop :=
  HashBaseAt K len p s ∧ s.gpr .eax = BitVec.ofNat 32 len ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = p.output

theorem HashAt.keep {H : Hash} {K : HashOK H} {len : Nat} {p : HashPublic} {s t : State} {rs : List Reg}
    (R : HashAt K len p s) (K' : Keeps rs s t) (sp : .esp ∉ rs) (si : .esi ∉ rs) (di : .edi ∉ rs) (bp : .ebp ∉ rs) :
    HashAt K len p t :=
  ⟨R.resources.keeps K' sp, (K'.1 _ sp).trans R.esp, (K'.1 _ si).trans R.esi,
    (K'.1 _ di).trans R.edi, (K'.1 _ bp).trans R.ebp⟩

theorem HashAt.after {H : Hash} {K : HashOK H} {len : Nat} {p : HashPublic} {s t : State} {rs : List Region}
    (R : HashAt K len p s) (A : After s rs t) : HashAt K len p t :=
  R.keep (hash_after_keeps A) (by decide) (by decide) (by decide) (by decide)
end VG.Proof.Dsa.X86.Generation
