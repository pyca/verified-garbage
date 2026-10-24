module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorSource
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Load g, immediately after p in the validated domain encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generatorLoad_ok {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (good : Good s p.B p.Z p.w p.mi) (source : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s)
 (words : p.w=(p.k+7)/8) (positive : 0<p.k) (size : p.k<2^31)
 (domain : word s.mem p.B (8*sDom)=dom) (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k) :
 WP isa (.seq (.block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2]) (load 1)) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.B (slot p.w 1) p.w=p.G ∧
 Arrays p.B p.w [1] s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun u =>u.gpr .x1=dom+BitVec.ofNat 64 p.k ∧
  u.gpr .x2=BitVec.ofNat 64 p.k ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read good p.room (show sDom<32 by decide),header_read good p.room (show sLen<32 by decide),domain,length]
 · rintro u ⟨⟨ptr,count,mem⟩,rest⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩
   have src := source.after_inscr (fun x _ => by rw [mem]) rest
   refine WP.mono (loadArray_ok goodU p.room words positive size (by decide : 1<8) src.source src.length ptr count) ?_
   rintro t ⟨goodT,value,frame,keep⟩
   rw [mem] at frame
   exact ⟨goodT,value.trans source.value,frame,(rest.trans keep).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
