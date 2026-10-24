module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ContextBuild
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadEntry
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StoreEntry
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Public subset indices load and store canonical context entries. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem productLoad_ok {s : State} {p : Parameters} {j : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j) (inside : j<32) :
 WP isa Precompute.productLoad s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.B (slot p.w 1) p.w=wv s.mem p.ctx (entryOffset p.w j) p.w ∧
 Arrays p.B p.w [1] s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.productLoad
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 j ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sJ<32 by decide),header_read good p.room (show sJ<32 by decide),index]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (loadEntry_ok goodU p.room (by have := p.positive;omega) p.width (by decide : 1<8)
    (memU ▸ context) indexU
    (fun i hi => (space.after restU).entry_read inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,restT⟩
   rw [memU] at value frame
   exact ⟨goodT,value,frame,(restU.trans restT).mono (by simp [mmRegs])⟩

theorem productStore_ok {s : State} {p : Parameters} {j d : Nat}
 (good : Good s p.B p.Z p.w p.mi) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx)
 (index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j) (basis : word s.mem p.B (8*sD)=BitVec.ofNat 64 d)
 (inside : j+d<32) :
 WP isa Precompute.productStore s fun t =>
 Good t p.B p.Z p.w p.mi ∧ wv t.mem p.ctx (entryOffset p.w (j+d)) p.w=wv s.mem p.B (slot p.w 6) p.w ∧
 Outside p.ctx (entryOffset p.w (j+d)) (8*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 unfold Precompute.productStore
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun u =>u.gpr .x3=BitVec.ofNat 64 (j+d) ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
    header_read good p.room (show sJ<32 by decide),header_read good p.room (show sD<32 by decide),index,basis,←BitVec.ofNat_add]
 · rintro u ⟨⟨indexU,memU⟩,restU⟩
   have goodU : Good u p.B p.Z p.w p.mi :=
    ⟨good.scr.congr restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,memU ▸ good.hdr⟩
   refine WP.mono (storeEntry_ok goodU p.room (by have := p.positive;omega) p.width (by decide : 6<8)
    (memU ▸ context) indexU (entry_fit p inside)
    (fun i hi => (space.after restU).entry_write inside hi)
    (fun i hi => space.entry_outside inside hi)) ?_
   rintro t ⟨goodT,value,frame,unchanged,restT⟩
   rw [memU] at value frame unchanged
   exact ⟨goodT,value,frame,unchanged,(restU.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
