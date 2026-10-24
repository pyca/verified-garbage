module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.FieldFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyToContext
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Store p and R² after the three canonical metadata words. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem storePrefix_ok {s : State} {p : Parameters} (h : FieldInitial p s) (space : ContextSpace p s)
 (context : word s.mem p.B (8*sCtx)=p.ctx) :
 WP isa Precompute.storePrefix s fun t =>
 FieldInitial p t ∧ wv t.mem p.ctx 24 p.w=p.P ∧
 wv t.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P ∧
 Outside p.ctx 24 (16*p.w) s.mem t.mem ∧
 (∀ x,ofs p.B x<p.Z→t.mem x=s.mem x) ∧ Keep mmRegs s t := by
 unfold Precompute.storePrefix
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x12,.x16,.x17] (Q:=fun a =>a.gpr .x16=off p.B (slot p.w 0) ∧
  a.gpr .x17=off p.ctx 24 ∧ a.gpr .x12=BitVec.ofNat 64 p.w ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [h.good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
    header_read h.good p.room (show sCtx<32 by decide),header_read h.good p.room (show sArr 0<32 by decide),
    header_read h.good p.room (show sW<32 by decide),context,h.good.hdr.harr 0 (by decide),h.good.hdr.hw]
 · rintro a ⟨⟨srcA,dstA,countA,memA⟩,restA⟩
   have goodA : Good a p.B p.Z p.w p.mi :=
    ⟨h.good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans h.good.x0,memA ▸ h.good.hdr⟩
   rw [WP.seq_iff]
   refine WP.mono (copyToContext_ok goodA (space.after restA) (by decide : 0<8) (by omega : 3+p.w≤3+34*p.w)
    srcA dstA countA) ?_
   rintro b ⟨goodB,valueB,frameB,sameB,pointerB,restB⟩
   have sameBS (x : Addr) (hx : ofs p.B x<p.Z) : b.mem x=s.mem x := by rw [sameB x hx,memA]
   have fieldB := h.after_workspace goodB sameBS
   have spaceB := (space.after restA).after restB
   have firstValue : wv b.mem p.ctx 24 p.w=p.P := by rw [valueB,memA];exact h.modulus
   rw [WP.seq_iff]
   refine WP.mono (WP.keep [.x12,.x16] (Q:=fun c =>c.gpr .x16=off p.B (slot p.w 4) ∧
    c.gpr .x12=BitVec.ofNat 64 p.w ∧ c.mem=b.mem) ?_ rfl rfl rfl) ?_
   · brun [goodB.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
      header_read goodB p.room (show sArr 4<32 by decide),header_read goodB p.room (show sW<32 by decide),
      goodB.hdr.harr 4 (by decide),goodB.hdr.hw]
   · rintro c ⟨⟨srcC,countC,memC⟩,restC⟩
     have goodC : Good c p.B p.Z p.w p.mi :=
      ⟨goodB.scr.congr restC.wr,(restC.gpr .x0 (by decide)).trans goodB.x0,memC ▸ goodB.hdr⟩
     refine WP.mono (copyToContext_ok goodC (spaceB.after restC) (by decide : 4<8) (by omega : 3+p.w+p.w≤3+34*p.w)
      srcC ((restC.gpr .x17 (by decide)).trans pointerB) countC) ?_
     rintro t ⟨goodT,valueT,frameT,sameT,_,restT⟩
     have sameTS (x : Addr) (hx : ofs p.B x<p.Z) : t.mem x=s.mem x := by
      rw [sameT x hx,memC]
      exact sameBS x hx
     have fieldT := h.after_workspace goodT sameTS
     have secondValue : wv t.mem p.ctx (24+8*p.w) p.w=2^(128*p.w)%p.P := by
      have rhs : wv c.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P := by rw [memC];exact fieldB.r2
      simpa only [Nat.mul_add] using valueT.trans rhs
     have frameTC : Outside p.ctx (24+8*p.w) (8*p.w) c.mem t.mem := by
      simpa only [Nat.mul_add] using frameT
     have firstT : wv t.mem p.ctx 24 p.w=p.P := by
      rw [frameTC.wv (Or.inl (by omega)) (by have := p.width;omega),memC]
      exact firstValue
     have frameBS : Outside p.ctx 24 (8*p.w) s.mem b.mem := by rw [←memA];exact frameB
     have frameTS : Outside p.ctx 24 (16*p.w) s.mem t.mem := by
      intro x hx
      rw [frameTC x (by omega),memC]
      exact frameBS x (by omega)
     exact ⟨fieldT,firstT,secondValue,frameTS,sameTS,
      (((restA.trans restB).trans restC).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
