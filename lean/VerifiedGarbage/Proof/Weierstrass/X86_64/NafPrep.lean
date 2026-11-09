module
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafSubtract

import VerifiedGarbage.Proof.Weierstrass.X86_64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-! The public scalar recoder, its byte stores and bounded 257-step loop. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.X25519.X86_64

/-- What recoding a scalar of `n` words clobbers: the scalar's registers too. -/
def nafPrepClobN (n : Nat) : List Reg := [.rax,.rbx,.rcx,.rdx]++Naf.sregs n

theorem notin_sregs {n : Nat} {r : Reg} (h : r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi]) :
    r∉Naf.sregs n :=
  fun hm => h (List.mem_of_mem_take hm)

/-- Clobbering registers outside the scalar's keeps its value. -/
theorem nafValN_keep {n : Nat} {rs : List Reg} {s t : State} (hk : ∀ r,r∉rs → t.gpr r=s.gpr r)
    (hd : ∀ r∈[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi],r∉rs) : nafValN n t=nafValN n s :=
  regsVal_congr fun r hr => hk r (hd r (List.mem_of_mem_take hr))

theorem notin_clobN {n : Nat} {r : Reg} (h₁ : r∉[Reg.rax,.rbx,.rcx,.rdx])
    (h₂ : r∉[Reg.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15,.rbp,.rsi]) : r∉nafPrepClobN n := fun h => by
  rcases List.mem_append.mp h with h|h
  · exact h₁ h
  · exact notin_sregs h₂ h

theorem mem_clobN {n : Nat} {r : Reg} {pre : List Reg} (hpre : ∀ q∈pre,q∈[Reg.rax,.rbx,.rcx,.rdx])
    (h : r∈pre++Naf.sregs n) : r∈nafPrepClobN n := by
  rcases List.mem_append.mp h with h|h
  · exact List.mem_append_left _ (hpre r h)
  · exact List.mem_append_right _ h

end VG.Proof.Weierstrass.X86_64
