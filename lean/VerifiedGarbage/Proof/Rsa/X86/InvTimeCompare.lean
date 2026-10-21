module

public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import VerifiedGarbage.Proof.Rsa.X86.InvChoice
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base

/-! # Relating public length comparisons in the inverse dispatcher -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

 def Pair (args : Nat → BitVec 32) (base : Addr) (size len P Q P' Q' : Nat) (sp : BitVec 32) (s t : State) : Prop :=
  (InvInput args base size len P Q s ∧ Public args base size sp s) ∧
  (InvInput args base size len P' Q' t ∧ Public args base size sp t)
 structure Compared (args : Nat → BitVec 32) (base : Addr) (size len P Q i limit : Nat) (sp : BitVec 32) (s : State) : Prop where
  input : InvInput args base size len P Q s
  pub : Public args base size sp s
  zf : s.zf=some (decide (args i=BitVec.ofNat 32 limit))
  cf : s.cf=some (decide ((args i).toNat<limit))

 theorem compare_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q i limit : Nat} {sp : BitVec 32} {s : State}
    (h : InvInput args base size len P Q s) (p : Public args base size sp s) (hi : i<16) (small : limit<2^32) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]) s
      (Compared args base size len P Q i limit sp) := by
  refine WP.mono (invCompare_ok h (p.arguments i hi) small) fun t ⟨ht,K,mem,zf,cf⟩ => ?_
  refine ⟨ht,p.keep K (by decide) ?_,zf,cf⟩
  rw [mem]; exact Outside.refl _ _ _ _

 theorem compare_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' i limit : Nat} {sp : BitVec 32}
    (hi : i<16) (small : limit<2^32)
    (check : (VG.Taint.check taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))])
      (VG.Taint.hintOf taint τ (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]))).isSome=true) :
    RelCT isa (Pair args base size len P Q P' Q' sp)
      (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))])
      (fun s t => Compared args base size len P Q i limit sp s ∧ Compared args base size len P' Q' i limit sp t) := by
  have trace : RelCT isa (Pair args base size len P Q P' Q' sp)
      (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp i)),.alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]) (fun _ _ => True) :=
    (RelCT.taint (A:=taint) τ (fun s t h => agree h.1.1.ws.ws.workspace h.2.1.ws.ws.workspace h.1.2 h.2.2) check).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  exact (trace.wp (F₁:=Compared args base size len P Q i limit sp) (F₂:=Compared args base size len P' Q' i limit sp)
    (fun _ _ h => ⟨compare_ok h.1.1 h.1.2 hi small,compare_ok h.2.1 h.2.2 hi small⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

 theorem publicWidth {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) : kw (args 7).toNat=kw len := by
  obtain ⟨a,al,aw,arg⟩ := h.ws.lenArg
  have e : BitVec.ofNat 32 a=args 7 := Option.some.inj (arg.readSrc.symm.trans h.gate.nArg.readSrc)
  rw [←e,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact aw

end VG.Proof.Rsa.X86.InvTiming
