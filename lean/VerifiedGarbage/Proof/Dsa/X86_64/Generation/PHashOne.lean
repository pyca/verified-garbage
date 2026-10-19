module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Offset

/-! # Construct and store one p-candidate hash contribution in assembly -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pHashOne_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op hp dp : Addr} {len offset count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hd : G.D = len) (hcount : count ≤ 11) (hj : j ≤ count)
    (hc : offset + j < 2 ^ 32) (hdp : off hp ((count - j) * len) = dp)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hhp : W 4 = hp) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hwd : ∀ i < len, InRegions s.wr (off dp i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) (hdbuf : HashBufferSeparate F S dp len) :
    WP isa (Impl.Dsa.X86_64.Generation.pHashOne G len count j) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem dp len =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.X86_64.Generation.pHashOne
  refine WP.seq (WP.mono (pSeedHash_ok hG hHh hsize (by omega) (by omega) hc L R A hrp hop hoff hrd hwr hsep hbuf)
    fun u ⟨Lu, rdu, wru, csu, hfu, ⟨V', Ru⟩, hb⟩ => ?_)
  refine WP.seq (WP.mono (hashCopyArgs_ok hlen hcount Lu Ru hhp) fun v ⟨hsi, hdi, hcx, hdx, hm, kv⟩ => ?_)
  rw [hdp] at hdi
  let digest := Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j)))
  have hdl : digest.length = len := (hsize _).trans hd
  have hread : ∀ i < digest.length, InRegions (v.rd ++ v.wr) (off (off S oDig) i) 1 := by
    intro i hi
    rw [hdl] at hi
    rw [kv.2.1, kv.2.2, off_off]
    exact Lu.sld8 (by dsimp only [oDig, oRsa]; omega)
  have hbytes : ∀ i < digest.length, v.mem (off (off S oDig) i) = digest.getD i 0 := by
    intro i hi
    rw [hdl] at hi
    rw [hm]
    change _ = (Hs.hash _).getD i 0
    rw [← hb, hd]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hcopy := copyDigest_ok (by rw [hdl]; exact hlen) hsi hdi
    (by rw [hdl]; exact hcx) (by rw [hdl]; exact hdx) hread
    (fun i hi => by rw [kv.2.2, wru]; exact hwd i (hdl ▸ hi)) hbytes
    (by
      intro i hi k hk
      rw [hdl] at hi hk
      rw [off_off]
      exact Ne.symm (hdbuf.scratch k hk (oDig + i) (by dsimp only [oDig, oRsa]; omega)))
  rw [hdl] at hcopy
  refine WP.mono hcopy fun t ⟨hout, hf, kt⟩ => ?_
  have Rv : Rep v.mem F S V' W := hm ▸ Ru
  have Rt := rep_of_external_write Rv hdbuf hf
  have Lv := Lu.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  refine ⟨lay_of_rep Lv Rv Rt rfl (kt.gpr (by decide)) kt.2.2,
    kt.2.1.trans (kv.2.1.trans rdu), kt.2.2.trans (kv.2.2.trans wru), ?_, ?_, ⟨V', Rt⟩, hout⟩
  · intro r hr
    rw [keep_cs' kt (cs_disj _ (by decide)) r hr,
      keep_cs' kv (cs_disj _ (by decide)) r hr, csu r hr]
  · have hft : Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] u.mem t.mem := by
      intro a ha
      rw [hf a (fun i hi => fun he => ha ⟨dp, len⟩ (by simp) (he ▸
        Offset.contains_base dp (by omega) (by omega))), hm]
    exact (hfu.mono (by simp)).trans hft

end VG.Proof.Dsa.X86_64.Generation
