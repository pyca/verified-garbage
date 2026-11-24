module

-- separate module: Keep the functional short/long composition independent of its trace proof.

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskPayload
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt

/-! # A shared contiguous RISC-V seal payload for either layout and every length -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Gcm (Block blockAt gctr inc32 toBytes ghashFrom ghash blocks ofBytes zeros padLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (padded lensBlock Absorbed)

structure PayloadIn (V : Reg → BitVec 64) (sp X D : Addr) (R : Nat) (H : Block) (a : List Byte) (s : State) : Prop where
  env : Env V sp s
  src : s.gpr .s4=X
  dst : s.gpr .s8=D
  len : s.gpr .s5=V .s11
  delta : V .s9=D-X
  read : DataOk (V .s1) (V .s0) s X (V .s11).toNat
  write : DataW (V .s2) (V .s1) (V .s0) s D (V .s11).toNat
  buffers : Alias true X D (V .s11).toNat
  roundsReg : V .s3=BitVec.ofNat 64 R
  rounds : R=10 ∨ R=12 ∨ R=14
  keys : BkIn (V .s7) (V .s2) (V .s1) (V .s0) sp R s.mem X D (V .s11).toNat s
  h : blockAt s.mem (V .s2+BitVec.ofNat 64 240)=H
  aadLen : (V .s10).toNat=a.length
  aad : Absorbed s.mem (V .s1+BitVec.ofNat 64 16) (V .s1+BitVec.ofNat 64 32) H (a++zeros (padLen a.length))
  slot : s.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D
  counter : blockAt s.mem (V .s1+BitVec.ofNat 64 48)=inc32 (blockAt s.mem (V .s1))

abbrev payloadFrame (st w D sp : Addr) (n : Nat) :=
  dataFrame st w D n ++ crFrame st w D n ++ otFrame st w 0 sp

structure PayloadOut (V : Reg → BitVec 64) (sp X D : Addr) (R : Nat) (H : Block) (a : List Byte) (s t : State) : Prop where
  env : Env V sp t
  data : bytesAt t.mem D (V .s11).toNat = gctr (ciphOf s.mem (V .s2) R) (inc32 (blockAt s.mem (V .s1))) (bytesAt s.mem X (V .s11).toNat)
  tag : bytesAt t.mem (V .s0) 16=toBytes (ghashFrom H (ghash H (blocks (padded a (bytesAt t.mem D (V .s11).toNat))))
      [ofBytes (lensBlock a.length (V .s11).toNat)] ^^^ ciphOf s.mem (V .s2) R (blockAt s.mem (V .s1)))
  frame : Frame (payloadFrame (V .s1) (V .s0) D sp (V .s11).toNat) s.mem t.mem

theorem PayloadIn.start {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {H : Block} {a : List Byte} {s : State}
    (p : PayloadIn V sp X D R H a s) :
    CrMid true V sp R (inc32 (blockAt s.mem (V .s1))) 0 X D (V .s11).toNat s.mem 0 s := by
  refine ⟨p.env,by omega,by simpa using p.src,by simpa using p.len,p.roundsReg,p.rounds,p.write,p.read,p.buffers,
      fun _ => p.delta,fun e => e,fun _ => ?_,rfl,.inr rfl,Frame.refl _ _⟩
  simp [bytesAt,Proof.Gcm.xorKs]

theorem PayloadIn.crypt {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {H : Block} {a : List Byte} {s : State}
    (p : PayloadIn V sp X D R H a s) (L : Lay (V .s2) (V .s1) (V .s0)) :
    WP isa (.seq (cryptWholeB true true) (cryptTailB true true)) s fun u =>
      CrOut true V sp R (inc32 (blockAt s.mem (V .s1))) 0 X D (V .s11).toNat s.mem u ∧ u.rd=s.rd ∧ u.wr=s.wr := by
  apply WP.seq
  refine WP.mono (WP.with_rdwr' (cryptWholeB_ok L p.start rfl fun _ => p.keys)) fun t ⟨⟨_,_,mt,lt⟩,rd,wr⟩ => ?_
  refine WP.mono (WP.with_rdwr' (cryptTailB_ok (bs := true) L mt lt (mt.ciph L) (fun _ => p.keys.of_eq rd wr))) fun _ ⟨out,rd',wr'⟩ =>
    ⟨out,rd'.trans rd,wr'.trans wr⟩

private theorem long_wp {invoke : Prog isa} {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {H : Block}
    {a : List Byte} {s : State} (L : Lay (V .s2) (V .s1) (V .s0)) (p : PayloadIn V sp X D R H a s)
    (exec : FramedHashAction invoke (V .s2+BitVec.ofNat 64 240) (sealWrites (V .s1) (V .s0) D sp (V .s11).toNat) s) :
    WP isa (VG.Impl.AesGcm.RISCV64.Contiguous.longPayloadWith invoke) s (PayloadOut V sp X D R H a s) := by
  let j := blockAt s.mem (V .s1)
  apply WP.seq
  refine WP.mono (WP.seq_iff.mp (p.crypt L)) fun _ run => WP.seq (WP.mono run fun u ⟨out,ru,wu⟩ => ?_)
  have su := out.env.sp.trans p.env.sp.symm
  have ct := out.out (Proof.Gcm.ctr_zero s.mem _ (V .s1+BitVec.ofNat 64 64) (ciphOf s.mem (V .s2) R) p.counter)
  rw [← Proof.Gcm.gctr_eq] at ct
  have ctx := ctx_crFrame L p.write
  have hh := (blockAt_frame out.frame (fun r hr => (ctx r hr).sub_left (Lay.ctxSub (d := 240) (by decide)))).trans p.h
  have ab := p.aad.congr (blockAt_frame out.frame (stp_crFrame L p.write (by decide)))
    (bytesAt_frame out.frame (stp_crFrame L p.write (by omega)) (by omega))
  have sl := (slot_keep out.frame (slot_crFrame L p.write (d := dataO) (by decide))).trans p.slot
  have bk := p.keys.frame p.rounds out.frame p.keys.crFrame ctx ru wu
  refine WP.mono (oneTagB_ok_with (bs := true) (o := 0) L (.inl rfl) out.env p.roundsReg p.rounds hh p.aadLen ab
    (p.write.ok.of_eq ru wu su) sl (fun _ => bk) (FramedHashAction.narrow
      (FramedHashAction.after exec ⟨ru,wu,su⟩ (out.frame.sub crypt_sealSub)) j0_sealSub)) fun v ot => ?_
  have data : bytesAt v.mem D (V .s11).toNat=bytesAt u.mem D (V .s11).toNat := bytesAt_frame ot.frame (fun r hr => by
    simp only [otFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact p.write.ok.st.sub_right (Region.sub_prefix (by decide))
    · exact p.write.ok.w.sub_right (Lay.wSub (by decide))
    · exact p.write.ok.w.sub_right (Lay.wSub (by decide))
    · exact p.write.ok.w.sub_right (Lay.wSub (by decide))
    · simpa only [p.env.sp] using p.write.ok.sk) (by have := (V .s11).isLt; omega)
  refine ⟨ot.env,data.trans ct,?_,?_⟩
  · have tag := ot.out
    rw [show V .s0+BitVec.ofNat 64 0=V .s0 from BitVec.add_zero _,length_bytesAt,ciph_frame out.frame ctx p.rounds,
      blockAt_frame out.frame (by simpa using stp_crFrame L p.write (d := 0) (k := 16) (by decide)),←data] at tag
    exact tag
  · exact (out.frame.mono (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr))).trans
      (ot.frame.mono (fun r hr => List.mem_append_right _ hr))

theorem payload_wp {invoke : Prog isa} {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {H : Block}
    {a : List Byte} {s : State} (L : Lay (V .s2) (V .s1) (V .s0)) (p : PayloadIn V sp X D R H a s) (cut : s.gpr .t0=241)
    (exec : FramedHashAction invoke (V .s2+BitVec.ofNat 64 240) (sealWrites (V .s1) (V .s0) D sp (V .s11).toNat) s) :
    WP isa (.ite (.ltu .s5 .t0) (VG.Impl.AesGcm.RISCV64.Contiguous.shortPayloadWith invoke) (VG.Impl.AesGcm.RISCV64.Contiguous.longPayloadWith invoke))
      s (PayloadOut V sp X D R H a s) := by
  have ev : isa.eval (.ltu .s5 .t0) s=some (decide ((V .s11).toNat<241)) := by
    change some (decide (s.gpr .s5 < s.gpr .t0))=_
    rw [p.len,cut]; rfl
  apply WP.ite _ ev
  · intro h
    have small : (V .s11).toNat≤240 := by have := of_decide_eq_true h; omega
    refine WP.mono (shortPayload_wp p.env L p.src p.dst p.len small p.read p.write p.buffers p.roundsReg p.rounds p.keys
      p.h p.aadLen p.aad p.slot exec) fun t ⟨et,ct,tag,f⟩ => ⟨et,ct,by rw [ct];exact tag,?_⟩
    exact f.mono (fun r hr => (List.mem_append.mp hr).elim
      (fun x => List.mem_append_left _ (List.mem_append_left _ x)) (List.mem_append_right _))
  · intro _; exact long_wp L p exec

end VG.Proof.AesGcm.RISCV64.Contiguous
