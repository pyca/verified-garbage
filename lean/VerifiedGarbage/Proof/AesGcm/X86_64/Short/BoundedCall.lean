module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedCT
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short

/-! Outline the common bounded seal without changing either public caller's stack contract. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.Short
open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block)

private theorem bounded_inline_ok : (Code.call bounded.name bounded.code).InlineOk = true := by decide +kernel

theorem bounded_call_ok {k : Nat} {o s : State} {Ctx W SP Np A D : Addr} {nl n al R : Nat} {H J : Block}
    {aad input : List Byte} (C : OneCtx o k Ctx W SP Np A D nl al n) (rsp : s.gpr .rsp = SP)
    (clear : Clear (hole SP) s) (run : WP isa bounded.code s (SealPostFrom o Ctx W SP D n R al H J aad input)) :
    WP isa (.call bounded.name bounded.code) s (SealPostFrom o Ctx W SP D n R al H J aad input) := by
  have cs : Clear (hole (s.gpr .rsp)) s := rsp.symm ▸ clear
  refine WP.mono (WP.of_inline bounded_inline_ok cs run) ?_
  rintro _ ⟨b,hv,u,rfl,_,env,rd,wr,saved,frame,dataEq,tag⟩
  rw [rsp]
  have hf : Frame [hole SP] b.mem (b.patch (hole SP) hv u).mem :=
    fun x hx => State.patch_mem (hx _ (List.mem_singleton_self _))
  have sub : (hole SP).Sub (below SP 24) := below_sub (by decide : 8 ≤ 24) (by decide)
  have dW := C.t_w.symm.sub_right sub
  have dD := C.t_d.symm.sub_right sub
  have bytesD := bytesAt_frame hf (p:=D) (n:=n) (fun r hr => List.mem_singleton.mp hr ▸ dD) (Nat.le_of_lt C.data.ok.lt)
  have bytesW := bytesAt_frame hf (p:=W) (n:=16) (fun r hr => List.mem_singleton.mp hr ▸
    dW.sub_left (Region.sub_prefix (by decide))) (by decide)
  refine ⟨env.keep (fun _ _ => rfl) rfl rfl,rd,wr,saved.frame hf (fun r hr =>
    List.mem_singleton.mp hr ▸ dW.sub_left (Lay.wSub (by decide))),frame.trans (hf.sub ?_),bytesD.trans dataEq,?_⟩
  · intro r hr
    exact ⟨_,by simp,List.mem_singleton.mp hr ▸ sub⟩
  · rw [bytesD,bytesW]; exact tag

/-- The only additional address leaked by the shared call is the caller's public stack slot. -/
theorem bounded_call_rel {P : State → State → Prop}
    (clear : ∀ a b, P a b → Clear (hole (a.gpr .rsp)) a ∧ Clear (hole (b.gpr .rsp)) b)
    (rsp : ∀ a b, P a b → a.gpr .rsp = b.gpr .rsp)
    (runs : ∀ a b, P a b → WP isa bounded.code a (fun _ => True) ∧ WP isa bounded.code b (fun _ => True))
    (ct : RelCT isa P bounded.code (fun _ _ => True)) :
    RelCT isa P (.call bounded.name bounded.code) (fun _ _ => True) := by
  intro a b ta tb u v h ea eb
  obtain ⟨⟨la,sa,ra,_⟩,⟨lb,sb,rb,_⟩⟩ := runs a b h
  obtain ⟨cl,cl'⟩ := clear a b h
  obtain ⟨_,_,_,exa,_,liftA⟩ := Exec.of_inline bounded_inline_ok ra cl
  obtain ⟨_,_,_,exb,_,liftB⟩ := Exec.of_inline bounded_inline_ok rb cl'
  obtain ⟨rfl,_⟩ := Exec.det ea exa
  obtain ⟨rfl,_⟩ := Exec.det eb exb
  have eq := (ct _ _ _ _ _ _ h ra rb).1
  rw [eq,rsp a b h] at liftA
  exact ⟨liftA.unique liftB,trivial⟩

end VG.Proof.AesGcm.X86_64.Short
