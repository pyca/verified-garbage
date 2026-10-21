module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvTimeBody
import VerifiedGarbage.Proof.Rsa.X86.InvTimeCheck
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeCompare
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.TimeCheck

/-! # Constant-time public dispatch and the verified inverse fallback -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

 theorem qChoice_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' w n : Nat} {sp : BitVec 32} {fallback : Prog isa}
    (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (width : kw len=w) (pb : (args 9).toNat≤4*n)
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n))).isSome=true)
    (other : RelCT isa (Pair args base size len P Q P' Q' sp) fallback (fun _ _ => True)) :
    RelCT isa (Pair args base size len P Q P' Q' sp)
      (.seq (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 11)),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*n+1)))])
        (.ite .b (VG.Impl.Rsa.X86.InvBatch.body w n) fallback)) (fun _ _ => True) := by
  refine RelCT.seq (compare_relCT (i:=11) (by decide) (by omega) (compare11_check _)) ?_
  refine RelCT.ite (fun s t h => by change s.cf=t.cf; rw [h.1.cf,h.2.cf]) ?_ ?_
  · exact (inverseBody_trace hn nl hw he width pb check).mono
      (fun _ _ h => ⟨⟨h.1.1.input,h.1.1.pub⟩,⟨h.1.2.input,h.1.2.pub⟩⟩) (fun _ _ _ => trivial)
  · exact other.mono (fun _ _ h => ⟨⟨h.1.1.input,h.1.1.pub⟩,⟨h.1.2.input,h.1.2.pub⟩⟩) (fun _ _ _ => trivial)

 theorem pChoice_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' w n : Nat} {sp : BitVec 32} {fallback : Prog isa}
    (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (width : kw len=w)
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n))).isSome=true)
    (other : RelCT isa (Pair args base size len P Q P' Q' sp) fallback (fun _ _ => True)) :
    RelCT isa (Pair args base size len P Q P' Q' sp)
      (.seq (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 9)),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*n+1)))])
        (.ite .b (.seq (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp 11)),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*n+1)))])
          (.ite .b (VG.Impl.Rsa.X86.InvBatch.body w n) fallback)) fallback)) (fun _ _ => True) := by
  refine RelCT.seq (compare_relCT (i:=9) (by decide) (by omega) (compare9_check _)) ?_
  refine RelCT.ite (fun s t h => by change s.cf=t.cf; rw [h.1.cf,h.2.cf]) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨hs,ht⟩,yes⟩ es et
    have pb : (args 9).toNat≤4*n := by
      change s.cf=some true at yes
      rw [hs.cf] at yes
      have := of_decide_eq_true (Option.some.inj yes)
      omega
    exact qChoice_relCT hn nl hw he width pb check other _ _ _ _ _ _
      ⟨⟨hs.input,hs.pub⟩,⟨ht.input,ht.pub⟩⟩ es et
  · exact other.mono (fun _ _ h => ⟨⟨h.1.1.input,h.1.1.pub⟩,⟨h.1.2.input,h.1.2.pub⟩⟩) (fun _ _ _ => trivial)

 theorem choose_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' desired w n : Nat} {sp : BitVec 32} {fallback : Prog isa}
    (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (small : desired<2^32) (widthChoice : kw desired=w)
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n))).isSome=true)
    (other : RelCT isa (Pair args base size len P Q P' Q' sp) fallback (fun _ _ => True)) :
    RelCT isa (Pair args base size len P Q P' Q' sp) (VG.Impl.Rsa.X86.InvBatch.choose desired w n fallback) (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.InvBatch.choose
  refine RelCT.seq (compare_relCT (i:=7) (by decide) small (compare7_check _)) ?_
  refine RelCT.ite (fun s t h => by change s.zf=t.zf; rw [h.1.zf,h.2.zf]) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨hs,ht⟩,yes⟩ es et
    have e : args 7=BitVec.ofNat 32 desired := by
      change s.zf=some true at yes
      rw [hs.zf] at yes
      exact of_decide_eq_true (Option.some.inj yes)
    have width := publicWidth hs.input
    rw [e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,widthChoice] at width
    exact pChoice_relCT hn nl hw he width.symm check other _ _ _ _ _ _
      ⟨⟨hs.input,hs.pub⟩,⟨ht.input,ht.pub⟩⟩ es et
  · exact other.mono (fun _ _ h => ⟨⟨h.1.1.input,h.1.1.pub⟩,⟨h.1.2.input,h.1.2.pub⟩⟩) (fun _ _ _ => trivial)

 theorem dispatch_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' : Nat} {sp : BitVec 32} :
    RelCT isa (Pair args base size len P Q P' Q' sp) VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice VG.Impl.Rsa.X86.InvBatch.dispatch
  refine choose_relCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) InvBatch.body64_check
    (choose_relCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) InvBatch.body96_check
      (choose_relCT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) InvBatch.body128_check ?_))
  exact (RelCT.taint (A:=taint) τ (fun _ _ h => agree h.1.1.ws.ws.workspace h.2.1.ws.ws.workspace h.1.2 h.2.2) fallback_check).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86.InvTiming
