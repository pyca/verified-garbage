module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! # The shaped hash bytes are determined by the public seed and offset -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

def HashPlan.shapedValue (p : HashPlan) (H : Spec.Mgf1.Hash) (plen : Nat) : Nat :=
  Spec.Ffdh.candidateOf (8 * plen)
    (VG.Proof.Dsa.Generation.contributions (8 * p.len)
      (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1))

theorem hash_shaped_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat}
    (hl : 2 ≤ plen) (hroom : plen ≤ (p.count + 1) * p.len) :
    Spec.Ffdh.candidateOf (8 * plen) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem
      (off p.output ((p.count + 1) * p.len - plen)) plen)) = p.shapedValue H plen := by
  have hsuf := VG.Proof.Dsa.Generation.bytesAt_suffix_value s.mem p.output ((p.count + 1) * p.len - plen) plen
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, pow256_eq] at hsuf
  change Spec.Ffdh.candidateOf (8 * plen) (Spec.Dsa.decodeBE _) = _
  rw [← hsuf, VG.Proof.Dsa.Generation.candidateOf_mod_width (by omega) (Nat.le_refl _)]
  rfl

theorem pShape_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  obtain ⟨V, R⟩ := hs.rep
  unfold Impl.Dsa.X86_64.Generation.pShape
  refine WP.seq (WP.mono (pShapeArgs_ok hs.layout R hop p.output_slot p.size.2.2 hlmax)
    fun u ⟨hdi, hsi, hcx, hdx, hm, hk⟩ => ?_)
  let rp := off p.output ((p.count + 1) * p.len - plen)
  let bs := Spec.Rsa.bytesAt s.mem rp plen
  have hbl : bs.length = plen := by simp [bs, Spec.Rsa.bytesAt]
  have hrd : ∀ i < bs.length, InRegions (u.rd ++ u.wr) (off rp i) 1 := by
    intro i hi
    rw [hbl] at hi
    obtain ⟨r, hr, hc⟩ := hs.outputWrite ((p.count + 1) * p.len - plen + i) (by omega)
    refine ⟨r, ?_, ?_⟩
    · rw [hk.2.1, hk.2.2]; exact List.mem_append_right _ hr
    · simpa only [rp, off_off] using hc
  have hb : ∀ i < bs.length, u.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    rw [hm]
    simp only [bs, Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD]
    simp [show i < plen by omega]
  refine WP.mono (VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
    (by omega : 9 ≤ 8 * plen) (by omega) (by rw [hbl]; omega)
    hsi hdi (by rw [hbl]; exact hcx) hdx hrd
    (fun i hi => by rw [hk.2.2]; exact hout i (hbl ▸ hi)) hb
    (fun i hi j hj => hsep i (hbl ▸ hi) j (hbl ▸ hj)))
    fun t ⟨_, hx, _, _⟩ => ?_
  rw [hbl] at hx
  have value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen) = p.shapedValue H plen := by
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) = _
    rw [hx]
    exact hash_shaped_value hs hl hroom
  have encoded := VG.Proof.Dsa.encodeBE_decodeBE (Spec.Rsa.bytesAt t.mem op plen)
  rw [bytesAt_length, value] at encoded
  exact encoded.symm

end VG.Proof.Dsa.X86_64.Generation
