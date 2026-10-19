module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeArgs
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashShape
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! # The native hash-suffix shaper feeds exactly the specified reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem pShape_ok {p : HashPlan} {H : Spec.Mgf1.Hash} {s : State}
    (hs : HashState p H (p.count + 1) s) {plen : Nat} {op : Addr}
    (hl : 2 ≤ plen) (hlmax : plen ≤ 1024) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (8 * plen - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len)
    (hop : p.W 0 = op) (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) (q : Nat) :
    WP isa (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen) s fun t =>
      let x := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem op plen)
      x + 1 - x % (2 * q) = Spec.Dsa.pCandidate (8 * plen) (8 * p.len) q p.seed p.offset ∧
      (x % 2 = 1 ∧ 2 ^ (8 * plen - 1) ≤ x ∧ x < 2 ^ (8 * plen)) ∧
      (∀ a, (∀ i < plen, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rdi, .rsi, .rcx, .rdx, .rax, .r8, .r9, .r10, .r11] s t := by
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
    fun t ⟨_, hx, hf, kt⟩ => ?_
  dsimp only
  rw [hbl] at hx
  refine ⟨?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) + 1 -
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % (2 * q) = _
    rw [hx]
    exact hash_shaped_candidate hs (by omega) rfl hroom hcount hhash hsize q
  · change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) % 2 = 1 ∧
      2 ^ (8 * plen - 1) ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op plen) < 2 ^ (8 * plen)
    rw [hx]
    exact VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := 8 * plen) (by omega) _
  · intro a ha
    rw [hf a (fun i hi => ha i (hbl ▸ hi)), hm]

end VG.Proof.Dsa.X86_64.Generation
