module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSeedHash
import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Construct and store one p-candidate hash contribution in assembly -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pHashOne_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
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
    WP isa (Impl.Dsa.AArch64.Generation.pHashOne G len count j) s fun t =>
      Lay t F S ∧ Step F S [⟨dp, len⟩, ⟨op, len⟩] s t ∧
      Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem dp len =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.AArch64.Generation.pHashOne
  refine WP.seq (WP.mono (pSeedHash_ok hG hHh hsize (by omega) (by omega) hc L R A hrp hop hoff hrd hwr hsep hbuf)
    fun u ⟨Lu, step, hfu, ⟨V', Ru⟩, hb⟩ => ?_)
  refine WP.seq (WP.mono (hashCopyArgs_ok hlen hcount Lu Ru hhp) fun v ⟨hsi, hdi, hcx, hm, kv⟩ => ?_)
  rw [hdp] at hdi
  let digest := Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j)))
  have hdl : digest.length = len := (hsize _).trans hd
  have hread : ∀ i < digest.length, InRegions (v.rd ++ v.wr) (off (off S oDig) i) 1 := by
    intro i hi
    rw [hdl] at hi
    rw [kv.rd, kv.wr, off_off]
    exact Lu.sld (o := oDig + i) (n := 1) (by dsimp only [oDig, oRsa]; omega)
  have hbytes : ∀ i < digest.length, v.mem (off (off S oDig) i) = digest.getD i 0 := by
    intro i hi
    rw [hdl] at hi
    rw [hm]
    change _ = (Hs.hash _).getD i 0
    rw [← hb, hd]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hcopy := random_copyRest_ok hsi hdi (by rw [hdl]; exact hcx)
    (by rw [hdl]; rcases hlen with rfl | rfl <;> omega) hread
    (fun i hi => by rw [kv.wr, step.wr]; exact hwd i (hdl ▸ hi))
    (by
      intro i hi k hk
      rw [hdl] at hi hk
      change off (off S oDig) i ≠ off dp k
      rw [off_off]
      exact Ne.symm (hdbuf.scratch k hk (oDig + i) (by dsimp only [oDig, oRsa]; omega)))
  rw [hdl] at hcopy
  refine WP.mono hcopy fun t ⟨hout, hf, kt⟩ => ?_
  have Rv : Rep v.mem F S V' W := hm ▸ Ru
  have Rt := rep_of_external_write Rv hdbuf hf
  have Lv := Lu.congr kv.sp kv.wr (by rw [hm])
  have hft : Frame [⟨dp, len⟩, ⟨op, len⟩, ⟨S, oRsa⟩, retR F] u.mem t.mem := by
    intro a ha
    rw [hf a (fun i hi => fun he => ha ⟨dp, len⟩ (by simp) (he ▸
      Offset.contains_base dp (by omega) (by omega))), hm]
  have hfinal := (hfu.mono (by simp)).trans hft
  have k := kv.trans kt
  refine ⟨lay_of_rep Lv Rv Rt rfl kt.sp kt.wr,
    ⟨k.rd.trans step.rd, k.wr.trans step.wr, k.sp.trans step.sp, ?_,
      (fun r hr => (k.vcs r hr).trans (step.vec r hr)), hfinal.mono (by simp)⟩,
    hfinal, ⟨V', Rt⟩, ?_⟩
  · intro r hr h30
    rw [k.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | decide | exact (h30 rfl).elim)]
    exact step.cs r hr h30
  · apply List.ext_getElem
    · rw [VG.Proof.Bignum.bytesAt_length, hdl]
    · intro i hi hi'
      have hil : i < len := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (dp + BitVec.ofNat 64 i) = digest[i]'(by rw [hdl]; exact hil)
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < digest.length from hdl ▸ hil), Option.getD_some] using
        (hout i hil).trans (hbytes i (hdl ▸ hil))

end VG.Proof.Dsa.AArch64.Generation
