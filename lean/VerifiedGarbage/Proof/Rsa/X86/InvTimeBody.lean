module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.InvTimeCompare
public import VerifiedGarbage.Proof.Rsa.X86.WorkspaceTaint
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.TimeCheck
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Body

/-! # The trace of a selected fixed-width inversion kernel -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

 omit rsaBatchLaw in
 theorem activeModulus {args : Nat → BitVec 32} {base : Addr} {size len P Q w n : Nat} {s : State}
    (h : InvInput args base size len P Q s) (hn : 16≤n) (hw : w=2*n) (width : kw len=w)
    (pb : (args 9).toNat≤4*n) :
    val32 s.mem base (VG.Impl.Rsa.X86.InvBatch.offset w 8) n=inverseM P := by
  have offeq : VG.Impl.Rsa.X86.InvBatch.offset w 8=VG.Proof.Rsa.X86.Keys.arr (kw len) VG.Impl.Rsa.X86.Keys.aM := by
    rw [width]
    dsimp only [VG.Impl.Rsa.X86.InvBatch.offset,VG.Proof.Rsa.X86.Keys.arr,VG.Proof.Rsa.X86.Keys.S,VG.Impl.Rsa.X86.Keys.aM,VG.Impl.Rsa.X86.Keys.hdr]
    omega
  rw [offeq]
  have pc : inverseM P<2^(32*n) := odd_modulus_bound (by omega) (prime_bound h.gate.pBound pb)
  rw [prefix_eq (w:=kw len) (by omega) (by change VG.Proof.Rsa.X86.Keys.num s.mem base (kw len) VG.Impl.Rsa.X86.Keys.aM<_; rw [h.m]; exact pc)]
  exact h.m

 theorem inverseBody_trace {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' w n : Nat} {sp : BitVec 32}
    (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (width : kw len=w)
    (pb : (args 9).toNat≤4*n)
    (check : (VG.Taint.check taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n)
      (VG.Taint.hintOf taint (WorkspaceTaint.dom (VG.Impl.Rsa.X86.InvBatch.offset w 15)) (VG.Impl.Rsa.X86.InvBatch.body w n))).isSome=true) :
    RelCT isa (Pair args base size len P Q P' Q' sp) (VG.Impl.Rsa.X86.InvBatch.body w n) (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨⟨hs,ps⟩,⟨ht,pt⟩⟩ es et
  have ws := hs.ws.ws.workspace
  have wt := ht.ws.ws.workspace
  have hz : VG.Impl.Rsa.X86.InvBatch.offset w 15≤size := by
    have fits := hs.ws.ws.fits
    rw [width] at fits
    dsimp only [VG.Impl.Rsa.X86.InvBatch.offset,VG.Proof.Rsa.X86.Keys.arr,VG.Proof.Rsa.X86.Keys.S,
      VG.Impl.Rsa.X86.Keys.hdr,VG.Impl.Rsa.X86.CrtValues.nArr] at *
    omega
  have sm := activeModulus hs hn hw width pb
  have tm := activeModulus ht hn hw width pb
  have so : val32 s.mem base (VG.Impl.Rsa.X86.InvBatch.offset w 8) n%2=1 := by rw [sm]; unfold inverseM; omega
  have oddT : val32 t.mem base (VG.Impl.Rsa.X86.InvBatch.offset w 8) n%2=1 := by rw [tm]; unfold inverseM; omega
  refine ⟨WorkspaceTaint.trace_eq ws wt hz (ps.stack.trans pt.stack.symm) check ?_ ?_ es et,trivial⟩
  · exact WP.mono (InvBatch.body_ok (WorkspaceTaint.view_scr ws) hn nl hw he hz rfl rfl so) fun _ _ => trivial
  · exact WP.mono (InvBatch.body_ok (WorkspaceTaint.view_scr wt) hn nl hw he hz rfl rfl oddT) fun _ _ => trivial

end VG.Proof.Rsa.X86.InvTiming
