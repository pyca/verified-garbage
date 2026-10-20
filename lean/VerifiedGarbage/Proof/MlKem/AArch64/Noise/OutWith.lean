module
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Proof.MlKem.Mem16
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

def outCodeWith (nttAt : Nat→Nat→Prog isa) (off ns buf : Nat) (tr : Bool) :
    Prog isa :=
 seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off),
   Impl.MlKem.AArch64.Noise.cbdCall,if tr then nttAt off ns else .block []]

theorem out_okWith {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (nttAt : Nat→Nat→Prog isa) (hoff : off<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩)
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (hn : ∀v, Kept [⟨f,1024⟩,⟨w,1024⟩] s v → v.syms=s.syms →
   PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) →
   WP isa (nttAt off ns) v fun t=> Kept [⟨f,1024⟩,⟨w,1024⟩] v t ∧
     PolyIsW (cw true) t.mem f (ntt (samplePolyCBD 2 (bytesAt s.mem b 128)))) :
 WP isa (outCodeWith nttAt off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 have sample : WP isa (.seq (.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off))
     (Impl.MlKem.AArch64.Noise.cbdCall)) s fun v=>Kept [⟨f,1024⟩,⟨w,1024⟩] s v ∧
       PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) := by
  refine WP.seq (wp_addImm hbuf fun a ha ea=>wp_ptrTo' (by decide) hoff fun u hu eu=>?_)
  have ou : Only [.x0,.x1] s u := (ha.trans hu).mono (by simp)
  have ku : Kept [⟨f,1024⟩,⟨w,1024⟩] s u := Kept.of_keep ou.keep ou.mem (by decide)
  exact cbdW_call (by rw [hu.get .x0 (by decide),ea]; exact hb)
    (by rw [eu,ha.get .x28 (by decide)]; exact hf) hbf
    (by rw [ou.rd,ou.wr]; exact hc)
    (by rw [ou.wr]; intro a n ⟨r,hr,ha⟩; exact hcw a n ⟨r,by simp at hr; simp [hr],ha⟩)
    (fun v kv pv=>⟨ku.trans (kv.mono (by simp)),by simpa only [ou.mem] using pv⟩)
 apply WP.assoc
 refine WP.seq (WP.mono_syms sample fun v ⟨kv,pv⟩ sv=>?_)
 cases transform
 · exact wp_nil ⟨kv,pv⟩
 · exact WP.mono (hn v kv sv pv) fun t ⟨kt,pt⟩=>⟨kv.trans kt,pt⟩
end VG.Proof.MlKem.AArch64.Noise
