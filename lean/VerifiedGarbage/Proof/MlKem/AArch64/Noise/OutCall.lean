module
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Spec.MlKem.Poly

import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # CBD sampling and optional transform of one paired PRF output -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem out_ok {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
    (hoff : off < 65536) (hns : ns < 65536) (hbuf : buf < 4096)
    (hb : s.gpr .x19 + BitVec.ofNat 64 buf = b)
    (hf : s.gpr .x28 + BitVec.ofNat 64 off = f)
    (hw : s.gpr .x28 + BitVec.ofNat 64 ns = w)
    (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩)
    (hfw : (Region.mk f 1024).Disjoint ⟨w,1024⟩)
    (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
    (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr) :
    WP isa (seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr) ++ ptrTo .x1 .x28 off),
      .call "vg_mlkem_cbd2" cbd2,
      if transform then .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns))
        (.call "vg_mlkem_ntt" Ntt16.ntt) else .block []]) s fun t =>
      Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
      PolyIs t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
        else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
  simp only [seqs]
  refine WP.seq (wp_addImm hbuf fun a ha ea =>
    wp_ptrTo' (by decide) hoff fun u hu eu => ?_)
  have ou : Only [.x0,.x1] s u := (ha.trans hu).mono (by simp)
  have ku : Kept [⟨f,1024⟩,⟨w,1024⟩] s u := Kept.of_keep ou.keep ou.mem (by decide)
  refine WP.seq (cbd2_call (by rw [hu.get .x0 (by decide),ea]; exact hb)
    (by rw [eu,ha.get .x28 (by decide)]; exact hf) hbf
    (by rw [ou.rd,ou.wr]; exact hc)
    (by rw [ou.wr]; intro a n ⟨r,hr,ha⟩; exact hcw a n ⟨r, by simp at hr; simp [hr],ha⟩) fun v kv pv => ?_)
  have kv' : Kept [⟨f,1024⟩,⟨w,1024⟩] s v := ku.trans (kv.mono (by simp))
  have pv' : PolyIs v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) := by
    simpa only [ou.mem] using pv
  cases transform
  · exact wp_nil ⟨kv',pv'⟩
  · refine WP.seq (wp_ptrTo (by decide) hoff fun a ha ea =>
      wp_ptrTo' (by decide) hns fun z hz ez => ?_)
    have oz : Only [.x0,.x1] v z := (ha.trans hz).mono (by simp)
    have kz : Kept [⟨f,1024⟩,⟨w,1024⟩] s z :=
      kv'.trans (Kept.of_keep oz.keep oz.mem (by decide))
    refine ntt_call (by rw [hz.get .x0 (by decide),ea,kv'.cs .x28 (by decide) (by decide)]; exact hf)
      (by rw [ez,ha.get .x28 (by decide),kv'.cs .x28 (by decide) (by decide)]; exact hw)
      hfw (by rw [oz.mem]; exact pv'.1)
      (by rw [oz.wr,kv'.wr]; exact hcw) fun t kt pt => ?_
    refine ⟨kz.trans kt,?_⟩
    simpa only [oz.mem,pv'.2,ite_true] using pt

end VG.Proof.MlKem.AArch64.Noise
