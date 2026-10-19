module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PHashArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Label
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Hash one wrapped seed while preserving the frame and external tapes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pSeedHash_ok {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {Hs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (Hs.hash bytes).length = G.D)
    {s : State} {F S rp op : Addr} {len offset j : Nat}
    (hlen : len < 2 ^ 31) (hj : j < 2 ^ 31) (hc : offset + j < 2 ^ 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W op len)
    (hrp : W 1 = rp) (hop : W 3 = op) (hoff : W 2 = BitVec.ofNat 64 offset)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < len, ∀ k < len, off rp i ≠ off op k)
    (hbuf : HashBufferSeparate F S op len) :
    WP isa (Impl.Dsa.X86_64.Generation.pSeedHash G len j) s fun t =>
      Lay t F S ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem t.mem ∧
      (∃ V', Rep t.mem F S V' W) ∧
      Spec.Rsa.bytesAt t.mem (off S oDig) G.D =
        Hs.hash (Spec.Dsa.encodeBE len (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem rp len) + (offset + j))) := by
  unfold Impl.Dsa.X86_64.Generation.pSeedHash
  refine WP.seq (WP.mono (seedInputArgs_ok hj L R hrp hop hoff) fun u ⟨hsi, hdi, hax, hm, ku⟩ => ?_)
  let bs := Spec.Rsa.bytesAt s.mem rp len
  have hbl : bs.length = len := bytesAt_length _ _ _
  have hread : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [ku.2.1, ku.2.2]
    exact hrd i (hbl ▸ hi)
  have hwrite : ∀ i < bs.length, InRegions u.wr (off op i) 1 := by
    intro i hi
    rw [ku.2.2]
    exact hwr i (hbl ▸ hi)
  have hbytes : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hbl] at hi
    rw [hm]
    simp [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  have hseed := seedAdd_ok bs (hbl ▸ hlen) hc hsi hdi hax hread hwrite hbytes
    (fun i hi k hk => hsep i (hbl ▸ hi) k (hbl ▸ hk))
  rw [hbl] at hseed
  refine WP.seq (WP.mono hseed fun v ⟨hv, hf, kv⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Rv := rep_of_external_write Ru hbuf hf
  have Lu := L.congr (ku.gpr (by decide)) ku.2.2 (by rw [hm])
  have Lv := lay_of_rep Lu Ru Rv rfl (kv.gpr (by decide)) kv.2.2
  have Av := A.congr (kv.2.1.trans ku.2.1) (kv.2.2.trans ku.2.2) rfl rfl
  refine WP.mono (hash_bytes_frame hG hHh hsize Lv Rv Av)
    fun t ⟨Lt, rd, wr, cs, hft, V', Rt, _, hb⟩ => ?_
  refine ⟨Lt, rd.trans (kv.2.1.trans ku.2.1), wr.trans (kv.2.2.trans ku.2.2), ?_, ?_, ⟨V', Rt⟩, ?_⟩
  · intro r hr
    rw [cs r hr, keep_cs' kv (cs_disj _ (by decide)) r hr,
      keep_cs' ku (cs_disj _ (by decide)) r hr]
  · have hfs : Frame [⟨op, len⟩, ⟨S, oRsa⟩, retR F] s.mem v.mem := by
      intro a ha
      rw [hf a (fun i hi => fun he => ha ⟨op, len⟩ (by simp) (he ▸
        Offset.contains_base op (by omega) (by omega))), hm]
    exact hfs.trans (hft.mono (by simp))
  · rw [hb, hv]

end VG.Proof.Dsa.X86_64.Generation
