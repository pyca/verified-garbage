module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroupResultCT

/-! # Status inspection preserves the seed phase inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MlKem.X86_64

theorem seedBefore_congr {n qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedBefore n qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedBefore n qLen p t := by
  obtain ⟨⟨W, hW, h1, h16, h10⟩, seed, hf, hw, he⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h1, h16, h10⟩,
    seed.frame (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2,
    hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, he⟩

theorem seedPrimeBefore_congr {n pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeBefore n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedPrimeBefore n pLen qLen p t :=
  ⟨seedBefore_congr h.1 hm hk, h.2.1, hm ▸ h.2.2⟩

theorem seedSubgroupAfter_congr {n pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedSubgroupAfter n pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.rax] s t) :
    SeedSubgroupAfter n pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  exact ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => seedPrimeBefore_congr (next ha) hm hk⟩

end VG.Proof.Dsa.X86_64.Generation
