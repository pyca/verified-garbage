module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native subgroup-candidate construction from a seed

The composition hashes the seed, selects SHA-1 or SHA-256 by its public
width, and shapes the digest. Its output is the exact fixed-width encoding
of the specification's q candidate.
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem qCandidate_ok {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Pbkdf2.Md.X86_64.Calls.StreamOK G1) (h256 : Pbkdf2.Md.X86_64.Calls.StreamOK G256)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32)
    {s : State} {F S rp op : Addr} {len : Nat} (hlen : len = 20 ∨ len = 32)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (A : LabAt s F S W rp len) (hop : W 0 = op)
    (hout : ∀ i < len, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < len, ∀ j < len, off (off S oDig) i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.qCandidate G1 G256) s fun t =>
      Spec.Rsa.bytesAt t.mem op len =
        Spec.Dsa.encodeBE len (Spec.Dsa.qCandidate (8 * len) (Spec.Rsa.bytesAt s.mem rp len)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) := by
  unfold Impl.Dsa.X86_64.Generation.qCandidate
  refine WP.seq (WP.mono (seedHash_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 hlen L R A)
    fun u ⟨Lu, rdu, wru, csu, V', Ru, _, hb⟩ => ?_)
  refine WP.seq (WP.mono (qArgs_ok Lu Ru hop A.hll) fun v ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let seed := Spec.Rsa.bytesAt s.mem rp len
  have hhash : (Spec.Dsa.seedHash (8 * len) seed).length = len := by
    rw [← hb, bytesAt_length]
  have hn : 8 * len = 160 ∨ 8 * len = 256 := by omega
  have hread : ∀ i < (Spec.Dsa.seedHash (8 * len) seed).length,
      InRegions (v.rd ++ v.wr) (off (off S oDig) i) 1 := by
    intro i hi
    rw [hhash] at hi
    rw [hk.2.1, hk.2.2, off_off]
    exact Lu.sld8 (by unfold oDig oRsa; omega)
  have hbytes : ∀ i < (Spec.Dsa.seedHash (8 * len) seed).length,
      v.mem (off (off S oDig) i) = (Spec.Dsa.seedHash (8 * len) seed).getD i 0 := by
    intro i hi
    rw [hhash] at hi
    rw [hm, ← hb]
    simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi]
  refine WP.mono (qShape_ok hn (by rw [hhash]) hsi hdi (by rw [hhash]; exact hcx) hdx hread
    (fun i hi => by rw [hk.2.2, wru]; exact hout i (hhash ▸ hi)) hbytes
    (fun i hi j hj => hsep i (hhash ▸ hi) j (hhash ▸ hj))) fun t ⟨ho, _, kt⟩ => ?_
  refine ⟨by simpa only [hhash] using ho, kt.2.1.trans (hk.2.1.trans rdu),
    kt.2.2.trans (hk.2.2.trans wru), ?_⟩
  intro r hr
  have hr1 : r ∉ [.rax, .rdx, .r8, .r9, .r10, .r11, .rcx] := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr2 : r ∉ [.rdi, .rsi, .rcx, .rdx] := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact (kt.gpr hr1).trans ((hk.gpr hr2).trans (csu r hr))

end VG.Proof.Dsa.X86_64.Generation
