module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FastFinish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdSplit
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block

/-! # Complete singleton matrix sampling and restoration of its caller -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem VG.Spec.MlKem VG.Impl.MlKem.AArch64

def lastCode (sb ss a k off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a a k))
  (.seq Impl.MlKem.AArch64.Paired.squeeze
   (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts)
    (.seq (Impl.MlKem.AArch64.Paired.reject 400 off .x22 w16)
     (.seq (.ite (.zero .x .x22) (fullSampleCode sb ss off a k w16) (.block []))
      (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i)))))))

theorem lastSample_eq (L : KemLay) (kg : Bool) (w16 : Bool) :
    Impl.MlKem.AArch64.Paired.lastSample L kg w16 =
      lastCode (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
        (L.k*L.k-1) L.k ((if kg then KG.AH else KEM.AH)+1024*(L.k*L.k-1)) w16 := by
  simp only [Impl.MlKem.AArch64.Paired.lastSample,fullSample_eq,lastCode,seqs]

structure LastPostW (w16 : Bool) (B : List Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep pairRegs s t
 frame : Frame (fullWrites p out) s.mem t.mem
 coeffs : CoeffsUpToW w16 t.mem out (sampleAfter [] (xofByte B) 280).length (Sample.cvW w16 (sampleAfter [] (xofByte B) 280)) (fun _=>0)
 reduced : ReducedW (cw w16) t.mem out
 result : ((sampleAfter [] (xofByte B) 280).length=256 ∧ sampleNTT 280 B=some (polyAtW (cw w16) t.mem out)) ∨
   ((sampleAfter [] (xofByte B) 280).length≠256 ∧ sampleNTT 280 B=none)
 status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] (xofByte B) 280).length=256 then 1 else 0)

structure LastReadyW (w16 : Bool) (B : List Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep pairWorkingRegs s t
 frame : Frame (fullWrites p out) s.mem t.mem
 saved : Noise.Saved p s t.mem
 ptr : t.gpr .x19=p
 coeffs : CoeffsUpToW w16 t.mem out (sampleAfter [] (xofByte B) 280).length (Sample.cvW w16 (sampleAfter [] (xofByte B) 280)) (fun _=>0)
 reduced : ReducedW (cw w16) t.mem out
 status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] (xofByte B) 280).length=256 then 1 else 0)

theorem lastCode_ok {w16 : Bool} {s : State} {p seed out table : Addr} {sb ss a k off : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p) (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (hseedOut : (Region.mk seed 32).Disjoint (polyRegion out))
    (ctx : SingleContext p out table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE"=table)
    (hstatus : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (lastCode sb ss a k off w16) s (LastPostW w16 (seedBytes s.mem seed a k) p out s) := by
  have combined := WP.mono_syms (lastStart_ok (w16 := w16) (a := a) (k := k) (by omega) hsb h8 hoff hk hk256 hp hseed hout hin hsep ctx ht)
    (R := fun u => WP isa (.seq (.ite (.zero .x .x22) (fullSampleCode sb ss off a k w16) (.block []))
      (.block (Impl.MlKem.AArch64.Paired.saved.zipIdx.reverse.map fun (r,i)=>.ldr .x r .x19 (1800+8*i)))) u
      (LastPostW w16 (seedBytes s.mem seed a k) p out s))
    (fun u hu sy => by
      have seedEq : seedBytes u.mem seed a k=seedBytes s.mem seed a k := by
        unfold seedBytes
        rw [bytesAt_frame hu.frame (by
          intro r hr; simp only [fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl; exact hsep; exact hseedOut) (by decide : 32≤2^64)]
      have branch : WP isa (.ite (.zero .x .x22) (fullSampleCode sb ss off a k w16) (.block [])) u
          (LastReadyW w16 (seedBytes s.mem seed a k) p out s) := by
        refine WP.ite (u.gpr .x22 == 0) (eval_zero _ _) (fun _ => ?_) (fun hz => ?_)
        · refine WP.mono (fullSampleCode_ok hss hsb h8 hoff hk hk256 hu.ptr
            (by rw [hu.keep.get .x28]; exact hp) (by rw [hu.keep.get .x28]; exact hseed)
            (by rw [hu.keep.get .x28]; exact hout)
            (by rw [hu.keep.rd,hu.keep.wr]; exact hin) hu.context.scratch hu.context.output
            hsep ctx.apart hu.saved (by rw [sy,ht]; exact hu.context.artifact)
            (by rw [sy,ht]; exact hu.context.readable) (by rw [sy,ht]; exact ctx.tableScratch)
            (by rw [sy,ht]; exact ctx.tableOut)) fun t h => ?_
          refine ⟨(hu.keep.trans h.keep).mono (by decide),hu.frame.trans h.frame,h.saved,h.ptr,?_,h.reduced,?_⟩
          · rw [←seedEq]; exact h.coeffs
          · rw [h.status,hu.keep.get .x24,seedEq]
        · have full : (sampleAfter [] (xofByte (seedBytes s.mem seed a k)) 168).length=256 := by
            by_contra hh
            have he : u.gpr .x22=0 := BitVec.eq_of_toNat_eq (by rw [hu.flag,ite_eq_right hh]; rfl)
            rw [he] at hz; contradiction
          have eqFull := sampleAfter_full full 280 (by decide : 168≤280)
          have cc := full_coeffs hu.coeffs full
          apply wp_nil
          refine ⟨hu.keep.mono (by decide),hu.frame,hu.saved,hu.ptr,?_,Sample.reduced_of_coeffs cc,?_⟩
          · rw [eqFull]; exact cc
          · rw [eqFull,ite_eq_left full,hu.keep.get .x24]
            rcases hstatus with h | h <;> rw [h] <;> rfl
      refine WP.seq (WP.mono branch fun t h => ?_)
      refine WP.mono (restore_ok h.keep h.ptr h.saved (by rw [h.keep.wr]; exact ctx.scratch)) fun v ⟨kv,mv,v24⟩ => ?_
      have coeffs : CoeffsUpToW w16 v.mem out (sampleAfter [] (xofByte (seedBytes s.mem seed a k)) 280).length
          (Sample.cvW w16 (sampleAfter [] (xofByte (seedBytes s.mem seed a k)) 280)) (fun _=>0) := by rw [mv]; exact h.coeffs
      exact ⟨kv,by rw [mv]; exact h.frame,coeffs,by rw [mv]; exact h.reduced,coeffs_sample_result coeffs,v24.trans h.status⟩)
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu =>
    WP.seq (WP.mono (WP.seq_iff.mp hu) fun v hv =>
      WP.seq (WP.mono (WP.seq_iff.mp hv) fun w hw => WP.seq hw)))

end VG.Proof.MlKem.AArch64.Paired
