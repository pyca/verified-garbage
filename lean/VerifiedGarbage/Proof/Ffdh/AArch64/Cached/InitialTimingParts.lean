module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInitial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ConstTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Fixed-index stores, field initialization, and generator loading have public traces. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def fieldWs (p : Parameters) : Ws := ⟨p.B,p.Z,p.w⟩

theorem fieldPowerInit_ct (M : Mont) : RelCT isa (Two FieldInitial)
 (.seq (const 7 1) (M.mm 6 4 7)) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=fun p s =>GoodW (fieldWs p) s)
  (two_map fieldWs (fun p s h =>⟨p.mi,h.good,p.room⟩) (const_ct 7 1 (by decide) (by taint_decide) (by taint_decide))) ?_)
  (two_map fieldWs (fun _ _ h =>h) (M.ct (by simp [MmUse,Public.aY,Public.aR2,Public.aOne])))
 intro p s h
 exact WP.mono (const_ok h.good p.room (by have :=p.positive;omega) p.width (by decide : 7<8) (by decide : 1<2^16))
  (fun _ ⟨good,_,_,_⟩ =>⟨p.mi,good,p.room⟩)

def LiteralReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ word s.mem p.B (8*sCtx)=p.ctx

theorem storeLiteral_ct {a d : Nat} (array : a<8) (small : d<2^16)
 {hc hd : VG.Taint.Hint VG.AArch64.Taint.T}
 (head : (taint.check (Taint.ofRegs []) (.block [movi .x3 d]) hc).isSome=true)
 (tail : (taint.check (Taint.ofRegs [.x0,.x3]) (.block (entryPtr++[ldh .x16 (sArr a)])) hd).isSome=true) :
 RelCT isa (Two LiteralReady) (.seq (.block [movi .x3 d]) (storeEntry a)) (fun _ _ =>True) := by
 refine RelCT.seq (two_piece (Ψ:=fun p s =>EntryReady (p,d) s) [] (fun _ _ _ _ _ r hr =>by simp at hr) head ?_)
  (two_map (fun p =>(p,d)) (fun _ _ h =>h) (storeEntry_ct a array tail))
 rintro p s ⟨good,ctx⟩
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 d ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [movi_nat small]
 · rintro t ⟨⟨digit,mem⟩,rest⟩
   exact ⟨⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,mem ▸ ctx,digit⟩

structure GeneratorPublic where
 p : Parameters
 dom : Addr

structure GeneratorReady (q : GeneratorPublic) (s : State) : Prop where
 good : Good s q.p.B q.p.Z q.p.w q.p.mi
 domain : word s.mem q.p.B (8*sDom)=q.dom
 length : word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k

theorem generatorLoad_ct : RelCT isa (Two GeneratorReady)
 (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) (fun _ _ =>True) := by
 refine RelCT.seq (two_piece (Ψ:=fun q s =>LoadReady (⟨fieldWs q.p,q.dom+BitVec.ofNat 64 q.p.k,q.p.k⟩ : LoadPublic) s) [.x0]
  (fun q s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r;exact hs.good.x0.trans ht.good.x0.symm) (by taint_decide) ?_)
  (two_map (fun q =>(⟨fieldWs q.p,q.dom+BitVec.ofNat 64 q.p.k,q.p.k⟩ : LoadPublic)) (fun _ _ h =>h)
   (load_ct (by decide : 1<8) (by taint_decide)))
 intro q s h
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
  t.gpr .x1=q.dom+BitVec.ofNat 64 q.p.k ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [h.good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read h.good q.p.room (show sDom<32 by decide),header_read h.good q.p.room (show sLen<32 by decide),h.domain,h.length]
 · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
   exact ⟨⟨q.p.mi,⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,q.p.room⟩,ptr,len⟩

end VG.Proof.Ffdh.AArch64.Cached
