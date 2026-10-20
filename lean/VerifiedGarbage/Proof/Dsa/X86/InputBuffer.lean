module

public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.RunBytes

/-! # Constructing caller-buffer invariants from ABI-owned byte ranges -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem inputBuffer {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {ptr : BitVec 32} {regs : List Reg}
    (K : Keeps regs s t) (hp : pointerValue base t p = ptr)
    (hf : ptr.toNat + len ≤ 2 ^ 32)
    (hr : ∀ d k, d + k ≤ len → InRegions (s.rd ++ s.wr) (ptr.setWidth 64 + BitVec.ofNat 64 d) k)
    (ha : Region.Disjoint ⟨ptr.setWidth 64, len⟩ ⟨base, size⟩)
    (room : Pow.Room (t.gpr .esp) base size)
    (stack : Region.Disjoint ⟨ptr.setWidth 64, len⟩ (callStack (t.gpr .esp))) : CallerBuffer t base size p len := by
  refine ⟨room, by rw [hp]; exact hf, ?_, by rw [hp]; exact ha, by rw [hp]; exact stack⟩
  intro d k hd
  rw [hp, K.2.1, K.2.2]
  exact hr d k hd

theorem inputBytes_keep {s t : State} {base : Addr} {size len : Nat} {p : Pointer} {ptr : BitVec 32}
    (O : Outside base 0 size s.mem t.mem) (hp : pointerValue base t p = ptr)
    (hlen : len ≤ 2 ^ 64) (hsize : size ≤ 2 ^ 64)
    (ha : Region.Disjoint ⟨ptr.setWidth 64, len⟩ ⟨base, size⟩) :
    Spec.Rsa.bytesAt t.mem ((pointerValue base t p).setWidth 64) len = Spec.Rsa.bytesAt s.mem (ptr.setWidth 64) len := by
  rw [hp]
  apply outs_bytes (ranges := [(0, size)]) (Outs.of_outside O (by simp)) hlen
  · intro pair hpair
    have H : pair = (0, size) := List.mem_singleton.mp hpair
    subst pair
    simpa only [Nat.zero_add] using hsize
  · intro pair hpair
    have H : pair = (0, size) := List.mem_singleton.mp hpair
    subst pair
    simpa only [off, BitVec.add_zero] using ha

end VG.Proof.Dsa.X86
