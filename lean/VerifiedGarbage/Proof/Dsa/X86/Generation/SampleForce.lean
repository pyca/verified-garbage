module
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Bytes
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ForceWitness
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleExternal
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLoad
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory

/-! # Force and reload an out-of-range witness while retaining the prepared context -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Generation

theorem sampleForce_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (C : Context n m base size s) (hp : s.gpr .esi = p)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0) (fit : p.toNat + len ≤ 2 ^ 32)
    (read4 : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (off (p.setWidth 64) d) 4)
    (read1 : ∀ i < len, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (p.setWidth 64) i) 1)
    (apart : Region.Disjoint ⟨p.setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (.seq (.block (forceWitness len)) (loadComponent len n (slot n 5))) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 5) n = Spec.Dsa.decodeBE
        (VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len)) ∧
      Frame [⟨p.setWidth 64, len⟩, ⟨off base (slot n 5), 8 * n⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (forceWitness_ok (by omega) hp fit read1 write) fun a ⟨bytes, Oa, Ka⟩ => ?_)
  have Ca := sampleExternal_context C Ka (by decide) (by decide) Oa apart.symm
  have pa : a.gpr .esi = p := (Ka.1 _ (by decide)).trans hp
  refine WP.mono (sampleLoad_ok Ca h4 hlen hw4 (by rw [pa]; exact fit)
    (fun d hd => by rw [pa, Ka.2.1, Ka.2.2]; exact read4 d hd)
    (by rw [pa]; exact apart)) fun t ⟨Ct, value, Ot, Kt⟩ => ?_
  refine ⟨Ct, by rw [value, pa, bytes], ?_, (Ka.mono (by decide)).trans Kt⟩
  have bound : slot n 5 + 8 * n ≤ 2 ^ 64 := by
    have := VG.Proof.Mont.X86.Dynamic.slot_bound (n := n) (i := 5) (by decide)
    have := C.size_le
    have := C.scr.nowrap
    unfold stride at *
    omega
  exact (Oa.mono (by intro r hr; simp_all)).trans ((sampleOutside_frame Ot bound).mono (by intro r hr; simp_all))
end VG.Proof.Dsa.X86.Generation
