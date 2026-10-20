module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.DispatchCTState
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.GenerateCT

/-! # Supported public parameter lengths select the verified SHA family -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem dispatch_ct (H : GenerationHashes) (F : KeyRandom.CheckCall.CheckFn) :
    RelCT isa (Two DispatchBefore) (dispatch H.sha1 H.sha256 F.name F.code) (fun _ _ => True) := by
  unfold dispatch
  refine RelCT.seq dispatch_check (two_ite (fun _ _ _ hs ht => hs.2.2.trans ht.2.2.symm) ?_ ?_)
  · apply two_map (fun P : SearchContextPlan => P) ?_
      (generate_ct H.h1 F 128 20 H.width1 H.final1 H.hash1 H.size1)
    intro P s h
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    rcases P.geometry.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨⟨h.1.1, hp⟩, hq⟩
    all_goals simp [hp] at hb
  · have tail : RelCT isa (Two DispatchLarge)
        (.seq (.block [.alu .cmp .eax (.imm 256)])
          (.ite .e (generate H.sha256 F.name F.code 256 32) (generate H.sha256 F.name F.code 384 32)))
        (fun _ _ => True) := by
      refine RelCT.seq dispatch_check256 (two_ite (fun _ _ _ hs ht => hs.1.2.2.trans ht.1.2.2.symm) ?_ ?_)
      · apply two_map (fun P : SearchContextPlan => P) ?_
          (generate_ct H.h256 F 256 32 H.width256 H.final256 H.hash256 H.size256)
        intro P s h
        have hb := Option.some.inj (h.1.1.2.2.symm.trans h.2)
        rcases P.geometry.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2 hp)
        · exact ⟨⟨h.1.1.1, hp⟩, hq⟩
        · simp [hp] at hb
      · apply two_map (fun P : SearchContextPlan => P) ?_
          (generate_ct H.h256 F 384 32 H.width256 H.final256 H.hash256 H.size256)
        intro P s h
        have hb := Option.some.inj (h.1.1.2.2.symm.trans h.2)
        rcases P.geometry.lengths with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact False.elim (h.1.2 hp)
        · simp [hp] at hb
        · exact ⟨⟨h.1.1.1, hp⟩, hq⟩
    apply two_map (fun P : SearchContextPlan => P) ?_ tail
    intro P s h
    refine ⟨h.1.1, h.1.2.1, fun hp => ?_⟩
    have hb := Option.some.inj (h.1.2.2.symm.trans h.2)
    simp [hp] at hb
end VG.Proof.Dsa.X86.Generation
