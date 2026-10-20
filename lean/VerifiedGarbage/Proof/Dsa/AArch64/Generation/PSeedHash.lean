module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Label
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! Each contribution hashes the original seed plus its wrapped public offset. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pSeedHash_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op : Addr} {len offset j : Nat}
    (hlen : len < 4096) (hj : j < 4096) (hc : offset + j < 2 ^ 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) :
    WP isa (Impl.Dsa.AArch64.Generation.pSeedHash G len j) s fun t =>
      Lay t F S ∧ Step F S [⟨op, len⟩] s t ∧
      Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem (off S oDig) G.D =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.AArch64.Generation.pSeedHash
  refine WP.seq (WP.mono (seedInputArgs_ok hj L R hrp hop hoff) fun u ⟨hu1, hu2, hu0, hm, ku⟩ => ?_)
  let bs := Spec.Rsa.bytesAt s.mem rp len
  have hbl : bs.length = len := VG.Proof.Bignum.bytesAt_length _ _ _
  have hread : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [ku.rd, ku.wr]
    exact hrd i (hbl ▸ hi)
  have hwrite : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
    intro i hi
    rw [ku.wr]
    exact hwr i (hbl ▸ hi)
  have hbytes : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hbl] at hi
    rw [hm]
    simp [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hseed := seedAdd_ok bs (hbl ▸ hlen) hc hu1 hu2 hu0 hread hwrite hbytes
    (fun i hi k hk => hsep i (hbl ▸ hi) k (hbl ▸ hk))
  rw [hbl] at hseed
  refine WP.seq (WP.mono hseed fun v ⟨hv, hf, kv⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Rv := rep_of_external_write Ru hbuf hf
  have Lu := L.congr ku.sp ku.wr (by rw [hm])
  have Lv := lay_of_rep Lu Ru Rv rfl kv.sp kv.wr
  have Av := A.congr (kv.rd.trans ku.rd) (kv.wr.trans ku.wr) rfl rfl
  refine WP.mono (hash_bytes_frame hG hHh hsize Lv Rv Av)
    fun t ⟨Lt, step, hft, V', Rt, _, hb⟩ => ?_
  have hfs : Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem v.mem := by
    intro a ha
    rw [hf a (fun i hi => fun he => ha ⟨op, len⟩ (by simp) (he ▸
      Offset.contains_base op (by omega) (by omega))), hm]
  have hfinal := hfs.trans (hft.mono (by simp))
  have k := ku.trans kv
  refine ⟨Lt, ⟨step.rd.trans k.rd, step.wr.trans k.wr, step.sp.trans k.sp, ?_,
    (fun r hr => (step.vec r hr).trans (k.vcs r hr)), hfinal.mono (by simp)⟩, hfinal, ⟨V', Rt⟩, ?_⟩
  · intro r hr h30
    rw [step.cs r hr h30]
    exact k.gpr r (by cases r <;> simp_all [preserved])
  · rw [hb, hv]

end VG.Proof.Dsa.AArch64.Generation
