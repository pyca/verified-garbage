module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSubgroupResultCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess

/-! # Status inspection preserves the seed phase inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MlKem.AArch64

theorem seedBefore_congr {qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedBefore qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedBefore qLen p t := by
  obtain ⟨⟨W, hW, h1, h16, h10⟩, seed, he⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h1, h16, h10⟩,
    seed.frame (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr,
    he⟩

theorem seedPrimeBefore_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeBefore pLen qLen p t :=
  ⟨seedBefore_congr h.1 hm hk, h.2.1, hm ▸ h.2.2⟩

theorem seedSubgroupAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedSubgroupAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedSubgroupAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  exact ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => seedPrimeBefore_congr (next ha) hm hk⟩

end VG.Proof.Dsa.AArch64.Generation
