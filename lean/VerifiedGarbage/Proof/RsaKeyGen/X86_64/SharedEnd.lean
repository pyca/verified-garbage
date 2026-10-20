module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KEnd

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.KMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Candidate finalization with the shared callee's private stack -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MlKem.X86_64

structure SharedKEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr)
    (k st u : Nat) (outv : Option Nat) : Prop where
  rax : t.gpr .rax = BitVec.ofNat 64 st
  used : t.mem.readW up 64 = BitVec.ofNat 64 u
  out : outBytes t.mem op k = match outv with
    | some c => Spec.Rsa.i2osp c k
    | none => outBytes s.mem op k
  saved : ∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)
  frame : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x →
    (∀ b < 8, x ≠ up + BitVec.ofNat 64 b) → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep mmRegs s t

theorem KEnd.shared {s t : State} {B sp : Addr} {Z : Nat} {op up : Addr}
    {k st u : Nat} {outv : Option Nat} (h : KEnd s t B Z op up k st u outv) :
    SharedKEnd s t B sp Z op up k st u outv :=
  ⟨h.rax, h.used, h.out, h.saved, fun x _ hx hu ho => h.frame x hx hu ho, h.keep⟩

theorem SharedKEnd.trans_pre {s₀ s t : State} {B sp : Addr} {Z : Nat} {op up : Addr}
    {k st u : Nat} {outv : Option Nat}
    (h : SharedKEnd s t B sp Z op up k st u outv)
    (hlo : ∀ i < 6, word s.mem B (8 * i) = word s₀.mem B (8 * i))
    (hhi : ∀ x, ¬(below sp 128).Contains x 1 → Z ≤ ofs B x → s.mem x = s₀.mem x)
    (hout : ∀ j < k, s.mem (op + BitVec.ofNat 64 j) = s₀.mem (op + BitVec.ofNat 64 j))
    (hk : Keep mmRegs s₀ s) : SharedKEnd s₀ t B sp Z op up k st u outv := by
  refine ⟨h.rax, h.used, ?_, fun i hi => (h.saved i hi).trans (hlo i hi),
    fun x he hx hu ho => (h.frame x he hx hu ho).trans (hhi x he hx),
    (hk.trans h.keep).mono (by decide)⟩
  rw [h.out]
  cases outv
  · exact List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  · rfl

def SharedCandEnd (s t : State) (B sp : Addr) (Z : Nat) (op up : Addr) (k : Nat) (r : List Byte) :
    Option (Spec.RsaKeyGen.Candidate × List Byte) → Prop
  | none => SharedKEnd s t B sp Z op up k 0 0 none
  | some (.prime c, rest) => SharedKEnd s t B sp Z op up k 1 (r.length - rest.length) (some c)
  | some (.close, rest) => SharedKEnd s t B sp Z op up k 2 (r.length - rest.length) none
  | some (.rejected, rest) => SharedKEnd s t B sp Z op up k 3 (r.length - rest.length) none

theorem sharedFinUsed_end {s sX : State} {B sp : Addr} {Z : Nat} {op up : Addr} {k st u : Nat}
    (hs : Scr sX B Z) (hdi : sX.gpr .rdi = B) (h8 : 8 * 32 ≤ Z) (hst : st < 2 ^ 31)
    (hu : word sX.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hU : word sX.mem B (8 * kUsedP) = up) (ho : OutUp sX B Z op up k)
    (hlo : ∀ i < 6, word sX.mem B (8 * i) = word s.mem B (8 * i))
    (hhi : InScr B Z s.mem sX.mem) (kk : Keep mmRegs s sX) :
    WP isa (finUsed st) sX fun t => SharedKEnd s t B sp Z op up k st u none :=
  WP.mono (finUsed_end hs hdi h8 hst hu hU ho hlo hhi kk) fun _ h => h.shared

end VG.Proof.RsaKeyGen.X86_64
