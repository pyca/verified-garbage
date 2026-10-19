module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPair
public import VerifiedGarbage.Proof.Bignum.X86.PublicMask

/-! # Releasing the masked result has no input-dependent branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

theorem precomputedWriteResult_relCT (base : Addr) (bytes len n : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputedPair base bytes len args) (PublicFn.writeResult n) (fun _ _ => True) := by
  have Tail : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset)), .alu .and .eax (.imm 1)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (storeArguments_relCT 0 1 (args 0) (args 1))
    (VG.RelCT.seq (storeBE_relCT (slot n 7)) Tail)).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc,
      (H.left.stack 1 (by decide)).readSrc, (H.right.stack 1 (by decide)).readSrc⟩
  · exact fun _ _ h => h

theorem precomputedExportResult_trace {base : Addr} {bytes len n : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : PrecomputedPair base bytes len args s t) (hn : 0 < n) (space : size n ≤ bytes)
    (a b : Bool)
    (Ms : s.mem.readW (off base 144) 32 = if a then BitVec.allOnes 32 else 0)
    (Mt : t.mem.readW (off base 144) 32 = if b then BitVec.allOnes 32 else 0)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (PublicFn.exportResult n) s tr sf) (F : Exec isa (PublicFn.exportResult n) t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have A : VG.X86.Taint.Agree (workspaceTaint false) s t :=
        agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.agree.rf.1 _ (by decide))
      have T1 := (maskResult_relCT n _ _ _ _ _ _ A E1 F1).1
      obtain ⟨_, _, Os, Ks⟩ := wp_result (PublicContext.maskResult_ok H.left.scratch hn space a rfl Ms) E1
      obtain ⟨_, _, Ot, Kt⟩ := wp_result (PublicContext.maskResult_ok H.right.scratch hn space b rfl Mt) F1
      have sz := PublicContext.size_eq n
      have Next := H.keep Ks Kt (by decide) (by decide)
        (Os.mono (by omega) (by omega)) (Ot.mono (by omega) (by omega))
      have T2 := (precomputedWriteResult_relCT base bytes len n args _ _ _ _ _ _ Next E2 F2).1
      rw [T1, T2]

end VG.Proof.Bignum.X86
