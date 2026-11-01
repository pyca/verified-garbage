module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Arguments
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: use the block helper's postcondition in the shared seal finisher.
/-! # Whole-block split seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SealFused


theorem whole_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp S : Addr} {count R : Nat} {s : State}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (lay : Call.Layout V sp S count s) (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    WP isa Impl.AesGcm.PPC64LE.SealSplit.whole s
      (WholeOutWith V sp R (Call.argsState s).mem
        (Input.blocks (Call.argsState s).mem S (V .r27) (V .r23).toNat count)) := by
  refine WP.seq (WP.mono (Call.args_ok s (by rw [he.sp]; exact lay.slotWrite)) fun a ha => ?_)
  subst a
  refine WP.mono (Call.ok (Call.args_config L he hd lay hR hv)) fun t ht => ?_
  obtain ⟨h3,h4,h5,h6,h7,h8,h9,h10,_⟩ := Call.args_values he lay
  have hc : count/16<2^64 := by have := lay.bound; have := (V .r23).isLt; omega
  have hn : (V .r23).toNat/16<2^64 := by have := (V .r23).isLt; omega
  have hr : R<2^64 := by rcases hv with h | h | h <;> omega
  have hd' := ht.ciphertext
  have hb := ht.counter
  have hy := ht.hash
  simp only [h3,h4,h5,h6,h7,h8,h9,h10,hR,toNat64 hc,toNat64 hn,toNat64 hr] at hd' hb hy
  refine ⟨(Call.args_env he lay).of_saved ht.saved ht.sp ht.rd ht.wr,hd',hb,hy,?_⟩
  have hf := ht.frame
  rw [(Call.args_regions he lay).2] at hf
  exact hf


theorem input_length (m : Mem) (S D : Addr) (total count : Nat) (hc : count≤total) :
    (Input.blocks m S D total count).length=total/16 := by
  simp only [Input.blocks,List.length_append,List.length_drop,Proof.Gcm.length_blocksAt]
  omega


theorem whole_done {V : Reg → BitVec 64} {sp : Addr} {R count : Nat} {S : Addr} {a : List Byte}
    {s t : State}
    (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hc : count≤(V .r23).toNat) (hv : R=10 ∨ R=12 ∨ R=14)
    (hw : WholeOutWith V sp R s.mem (Input.blocks s.mem S (V .r27) (V .r23).toNat count) t)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WholeDone V sp R a s.mem
      ((Input.blocks s.mem S (V .r27) (V .r23).toNat count).flatMap Spec.Gcm.toBytes)
      (Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16)) t := by
  have hh := Proof.Gcm.ctr_blocks (ks := V .r30+64) (input_length _ _ _ _ _ hc) hw.data hw.counter
  rw [Proof.Gcm.gctr_eq] at hh
  refine ⟨hw.env,?_,hh.1,hh.2,?_,hw.cipher L hd hv,hw.hashKey L hd,hw.j0 L hd,hw.rest hd,
    hw.frame.sub (whole_body_sub V)⟩
  · rw [Proof.Gcm.length_flatMap_toBytes,input_length _ _ _ _ _ hc]
  · exact hw.absorbed hab (by
      rw [List.length_append,Proof.Gcm.length_zeros]
      exact Proof.Gcm.length_pad_mod _)

end VG.Proof.AesGcm.PPC64LE.SealSplit
