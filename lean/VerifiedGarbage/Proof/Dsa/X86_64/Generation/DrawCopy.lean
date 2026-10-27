module
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.DrawCopy
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DrawArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PreparedFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Copy a complete draw and advance its tape cursor in verified code -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem drawCopy_ok {s : State} {B rp op : Addr} {Z w N drawBytes used : Nat} {mi : BitVec 64} {bs : List Byte}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hlen : 2 ≤ bs.length) (hld : bs.length ≤ drawBytes) (hmax : drawBytes ≤ 1024)
    (hrp : word s.mem B (8 * kRand) = rp) (hop : word s.mem B (8 * kOut) = op)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (hdl : word s.mem B (8 * kLen) = BitVec.ofNat 64 drawBytes)
    (hll : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length)
    (hsrc : Src s B Z (off rp (used + (drawBytes - bs.length))) bs)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hout : Region.Disjoint ⟨B, Z⟩ ⟨op, bs.length⟩)
    (hsep : ∀ i < bs.length, ∀ j < bs.length,
      off (off rp (used + (drawBytes - bs.length))) i ≠ off op j) :
    WP isa Impl.Dsa.X86_64.Generation.drawCopy s fun t =>
      ModulusReady t B Z w mi N ∧ Spec.Rsa.bytesAt t.mem op bs.length = bs ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + drawBytes) ∧
      WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega_arith
  unfold Impl.Dsa.X86_64.Generation.drawCopy
  simp only [seqs]
  refine WP.seq (WP.mono (drawCopyArgs_ok h.good hd.z hld hrp hop hus hdl hll)
    fun u ⟨h15, hsi, hdi, hcx, hdx, hmu, ku⟩ => ?_)
  have hfu : Frm B [(8 * kUsed, 8)] s.mem u.mem := by
    rw [hmu]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kUsed) (by decide)) (by simp)
  have hsrcu := hsrc.congrK (fun x hx => hfu x (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    right; change 208 ≤ ofs B x; omega_arith)) ku
  have hwu : ∀ i < bs.length, InRegions u.wr (off op i) 1 := fun i hi => by rw [ku.2.2]; exact hwr i hi
  have hbu : ∀ i < bs.length, u.mem (off (off rp (used + (drawBytes - bs.length))) i) = bs.getD i 0 := by
    intro i hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] using hsrcu.val i hi
  refine WP.seq (WP.mono (copyBytes_ok ⟨hlen, by omega_arith⟩ hsi hdi hcx hdx hsrcu.rd hwu hbu hsep)
    fun v ⟨hbv, hfv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = v.mem) (by
    xrun [(kv.gpr (by decide) : v.gpr .r15 = u.gpr .r15).trans h15]) rfl)
    fun t ⟨⟨hdit, hmt⟩, kt⟩ => ?_
  have k := (ku.trans kv).trans kt
  have hfvt : WorkFrame B [] [⟨op, bs.length⟩] u.mem t.mem := by
    intro x hx _
    rw [hmt]
    apply hfv
    intro i hi he
    subst x
    apply hx ⟨op, bs.length⟩ (by simp)
    apply (Region.contains_self op bs.length).byte
    simp only [off, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64)]
    exact hi
  have hft : WorkFrame B [(8 * kUsed, 8)] [⟨op, bs.length⟩] s.mem t.mem :=
    hfu.work.trans (hfvt.mono (by simp))
  have hex : ∀ r ∈ [⟨op, bs.length⟩], Region.Disjoint ⟨B, Z⟩ r := by simpa using hout
  refine ⟨ready_of_work h hd hft hex k.2.2 hdit (by simp; decide) (by rng_disj) (by rng_disj),
    by rw [hmt]; exact hbv, ?_, hft, ?_⟩
  · rw [hfvt.word_eq (by simp) (by change 208 ≤ Z; omega_arith) h.good.scr.nowrap hex,
      hmu, word_writeW_self]
  · refine ⟨fun r hr => ?_, k.2⟩
    by_cases he : r = .rdi
    · subst r; exact hdit.trans h.good.rdi.symm
    · exact k.gpr (by cases r <;> simp_all [mmRegs])

end VG.Proof.Dsa.X86_64.Generation
