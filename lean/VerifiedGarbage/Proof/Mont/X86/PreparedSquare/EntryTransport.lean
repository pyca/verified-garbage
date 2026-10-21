module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Correct
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.TCB.Artifact

/-! # Volatile-register dispatch preserves the prepared call inputs -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem argument_transport {s t : State} (mem : t.mem = s.mem) (sp : t.gpr .esp = s.gpr .esp) (i : Nat) :
    arg t i = arg s i := by simp only [arg, argAddr, mem, sp]

theorem entry_transport {s t : State} (A : Compact.Entry s)
    (mem : t.mem = s.mem) (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Compact.Entry t := by
  have args := argument_transport mem sp
  have addr (i : Nat) : argAddr t i = argAddr s i := by simp only [argAddr, sp]
  have ws : Compact.wsOf t = Compact.wsOf s := by simp only [Compact.wsOf, args]
  have len : Compact.lenOf t = Compact.lenOf s := by simp only [Compact.lenOf, args]
  constructor
  · simpa only [sp] using A.stackFit
  · simpa only [sp] using A.stackBound
  · simpa only [rd, addr] using A.rd
  · simpa only [wr, ws, len] using A.wr
  · simpa only [args, len] using A.bound
  · simpa only [sp, ws, len] using A.savedSeparate
  · simpa only [sp, addr] using A.savedArgsSeparate
  · simpa only [ws, len, addr] using A.argSeparate
  · simpa only [sp, ws, len] using A.returnSeparate
  · simpa only [mem, ws, args] using A.layout
  · simpa only [args] using A.output
  · simpa only [args] using A.left
  · simpa only [args] using A.right
  · simpa only [mem, ws] using A.inverse
  · simpa only [mem, ws, args] using A.rightLt

theorem result_transport {s t : State} (mem : t.mem = s.mem) (sp : t.gpr .esp = s.gpr .esp) (m : Mem) :
    Compact.Result t m ↔ Compact.Result s m := by
  have args := argument_transport mem sp
  unfold Compact.Result Compact.wsOf
  simp only [args, mem]

theorem abi_transport {s t u : State} (K : Keeps [.eax, .edx] s t) (mem : t.mem = s.mem)
    (H : abiPreserved t u) : abiPreserved s u := by
  refine ⟨?_, ?_⟩
  · intro r hr
    exact (H.1 r hr).trans (K.1 r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
  · rw [← K.1 .esp (by decide), ← mem]
    exact H.2

theorem pre_transport {s t : State} (H : (Spec.Rsa.Mont.mulContract abi 16).pre s)
    (mem : t.mem = s.mem) (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    (Spec.Rsa.Mont.mulContract abi 16).pre t := by
  have args := argument_transport mem sp
  have addr (i : Nat) : argAddr t i = argAddr s i := by simp only [argAddr, sp]
  sig_pre [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow] at H
  sig_pre [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argSlots, argVal, argBytes, stackBelow]
  simpa only [mem, sp, rd, wr, args, addr] using H

theorem pub_transport {s t u v : State} (H : (Spec.Rsa.Mont.mulContract abi 16).pub s t)
    (sm : u.mem = s.mem) (ss : u.gpr .esp = s.gpr .esp)
    (tm : v.mem = t.mem) (ts : v.gpr .esp = t.gpr .esp) :
    (Spec.Rsa.Mont.mulContract abi 16).pub u v := by
  have sa := argument_transport sm ss
  have ta := argument_transport tm ts
  sig_pub [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argSlots, argVal, argBytes] at H
  sig_pub [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, abi, argSlots, argVal, argBytes]
  simpa only [sm, ss, tm, ts, sa, ta] using H

end VG.Proof.Mont.X86.PreparedSquare
