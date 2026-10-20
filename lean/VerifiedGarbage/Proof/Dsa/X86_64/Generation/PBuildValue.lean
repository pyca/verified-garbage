module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PShapeValue
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PHash
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashSequence
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Exact public bytes produced by the complete p hash-and-shape stage -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem pBuild_value {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {H : Spec.Mgf1.Hash} (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = G.D)
    {p : HashPlan} (hd : G.D = p.len) {s : State} (hs : HashState p H 0 s)
    {plen : Nat} {op : Addr} (hl : 2 ≤ plen) (hlmax : plen ≤ 1024)
    (hroom : plen ≤ (p.count + 1) * p.len) (hop : p.W 0 = op)
    (hout : ∀ i < plen, InRegions s.wr (off op i) 1)
    (hsep : ∀ i < plen, ∀ j < plen,
      off (off p.output ((p.count + 1) * p.len - plen)) i ≠ off op j) :
    WP isa (.seq (Impl.Dsa.X86_64.Generation.pHashes G p.len p.count)
      (Impl.Dsa.X86_64.Generation.pShape p.len p.count plen)) s fun t =>
      Spec.Rsa.bytesAt t.mem op plen = Spec.Dsa.encodeBE plen (p.shapedValue H plen) := by
  refine WP.seq (WP.mono (pHashes_ok hG hmatch hsize hd hs)
    fun u ⟨hu, _, wr, _, _⟩ => ?_)
  exact pShape_value hu hl hlmax hroom hop (fun i hi => wr ▸ hout i hi) hsep

end VG.Proof.Dsa.X86_64.Generation
