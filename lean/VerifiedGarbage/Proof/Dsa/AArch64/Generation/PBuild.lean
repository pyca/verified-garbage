module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashPlan

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashSequence
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! # Hash and shape the complete unreduced p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64

theorem pBuild_ok {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p H 0 s)
    {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j)
    (hbuf : HashBufferSeparate p.F p.S op plen) (q : Nat) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.AArch64.Generation.pShape p.len p.count plen)) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      Lay t p.F p.S ∧ (∃ V, Rep t.mem p.F p.S V p.W) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      Step p.F p.S [⟨op, plen⟩, ⟨p.output, (p.count + 1) * p.len⟩, ⟨p.wrapped, p.len⟩] s t ∧
      Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
  refine WP.seq (WP.mono (pHashes_ok hG hHh hsize hd hs)
    fun u ⟨hu, su, hfu⟩ => ?_)
  refine WP.mono (pShape_ok hu hl hlmax hroom hcount hhash hseedsize hop
    (fun i hi => su.wr ▸ hout i hi) hsep q) fun t ⟨hx, hb, hf, hk⟩ => ?_
  obtain ⟨V, R⟩ := hu.rep
  have Rt := rep_of_external_write R hbuf hf
  have hframe : Frame (⟨op, plen⟩ :: p.changed) s.mem t.mem := by
    intro a ha
    rw [hf a (fun i hi he => ha ⟨op, plen⟩ (by simp) (he ▸
      Offset.contains_base op (by omega) (by omega)))]
    exact hfu a (fun r hr => ha r (List.mem_cons_of_mem _ hr))
  refine ⟨hx, hb, lay_of_rep hu.layout R Rt rfl hk.sp hk.wr,
    ⟨V, Rt⟩, hk.rd.trans su.rd, hk.wr.trans su.wr,
    ⟨hk.rd.trans su.rd, hk.wr.trans su.wr, hk.sp.trans su.sp, ?_,
      (fun r hr => (hk.vcs r hr).trans (su.vec r hr)),
      hframe.mono (by simp [HashPlan.changed])⟩, hframe⟩
  intro r hr h30
  rw [hk.gpr r (by cases r <;> simp_all [preserved])]
  exact su.cs r hr h30

end VG.Proof.Dsa.AArch64.Generation
