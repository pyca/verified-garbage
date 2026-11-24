module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedTiming
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64

/-! # Constant-time absorption and padding with the prepared GHASH table -/

public section
namespace VG.Proof.AesGcm.RISCV64
open VG VG.RISCV64 VG.Impl.Gcm.RISCV64.Prepared
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

open VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (blockAt)
open VG.Proof.Gather.RISCV64 (rel_ite)

private theorem freshMid {V : Reg → BitVec 64} {sp D : Addr} {yo n : Nat}
    {H : Spec.Gcm.Block} {x : List Byte} {s : State} (h : AbsIn V sp yo H x D n s)
    (empty : x.length%16=0) : AbsMid V sp yo H x D n s.mem 0 s :=
  ⟨h.env,by omega,by rw [h.s4,BitVec.add_zero],by rw [h.s5,Nat.sub_zero],h.data,h.hH,
    fun ha => by simpa [Spec.Aes.bytesAt] using ha,.inr (by omega),Frame.refl _ _⟩

private theorem skipFill {s : State} {yo : Nat} (zero : s.gpr .s6=0) :
    WP isa (absorbFillWith preparedInvocation yo) s (·=s) := by
  refine WP.ite true (by simp [RISCV64.eval,zero]) (fun _ => WP.block_nil rfl) (fun h => by contradiction)

theorem preparedAbsorb_rel {bk c st w sp D : Addr} {rs : List Region} {s t : State} {yo n : Nat}
    (lay : Lay c st w) (y : yo=0 ∨ yo=16)
    (l : AbsI c st w sp yo D n 0 s) (r : AbsI c st w sp yo D n 0 t)
    (a : HashScope (c+BitVec.ofNat 64 240) bk rs s) (b : HashScope (c+BitVec.ofNat 64 240) bk rs t) :
    RelCT isa (Eq2 s t) (absorbWith preparedInvocation yo) TT := by
  obtain ⟨V,H,X,vc,vs,vw,empty,h⟩ := l
  obtain ⟨W,H',X',wc,ws,ww,empty',j⟩ := r
  have spin := h.env.sp.trans j.env.sp.symm
  have skip : RelCT isa (Eq2 s t) (.block []) TT := preparedSkip_rel
  refine rel_ite (eval_zero h.s5 h.data.lt) (eval_zero j.s5 j.data.lt) (fun _ => skip) fun _ => ?_
  have zero : s.gpr .s6=0 := by simpa [empty] using h.s6
  have zero' : t.gpr .s6=0 := by simpa [empty'] using j.s6
  refine rel_seq (rel_ite (b:=true) (by simp [RISCV64.eval,zero]) (by simp [RISCV64.eval,zero'])
    (fun _ => skip) (fun bad => by contradiction)) (skipFill zero) (skipFill zero') fun x z ex ez => ?_
  subst x z
  have hx := freshMid h empty
  have hz := freshMid j empty'
  have act : HashAction preparedInvocation (c+BitVec.ofNat 64 240) s := FramedHashAction.now a.action
  have act' : HashAction preparedInvocation (c+BitVec.ofNat 64 240) t := FramedHashAction.now b.action
  rw [←vc] at act
  rw [←wc] at act'
  refine rel_seq (preparedWhole_rel y ⟨V,H,X,s.mem,vc,vs,vw,empty,hx⟩
    ⟨W,H',X',t.mem,wc,ws,ww,empty',hz⟩ a b)
    (whole_ok_with (lay.v vc vs vw) y hx rfl act) (whole_ok_with (lay.v wc ws ww) y hz rfl act')
    fun u v ⟨i,ei,hu,_⟩ ⟨k,ek,hv,_⟩ => ?_
  subst i k
  exact RelCT.mono (absorbTail_ct (c:=c) (st:=st) (w:=w) (sp:=sp) (yo:=yo) (D:=D) (n:=n) (q:=0)
    (j:=0+16*((n-0)/16))) (fun i j ⟨hi,hj⟩ => by
      subst i j;exact ⟨⟨V,H,X,s.mem,vc,vs,vw,empty,hu⟩,⟨W,H',X',t.mem,wc,ws,ww,empty',hv⟩⟩)
    fun _ _ _ => trivial

end VG.Proof.AesGcm.RISCV64
