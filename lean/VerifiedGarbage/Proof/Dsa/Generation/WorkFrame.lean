module

public import VerifiedGarbage.Proof.Bignum.WorkFrame

/-! # Compose workspace changes and separate buffer or call-stack changes -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG VG.Proof.Bignum

theorem workFrame_append {B : Addr} {rs₁ rs₂ : List (Nat × Nat)} {ex₁ ex₂ : List Region}
    {m₁ m₂ m₃ : Mem} (h₁ : WorkFrame B rs₁ ex₁ m₁ m₂) (h₂ : WorkFrame B rs₂ ex₂ m₂ m₃) :
    WorkFrame B (rs₁ ++ rs₂) (ex₁ ++ ex₂) m₁ m₃ := by
  intro x hx hr
  exact (h₂ x (fun r h => hx r (List.mem_append_right _ h))
    (fun r h => hr r (List.mem_append_right _ h))).trans
      (h₁ x (fun r h => hx r (List.mem_append_left _ h))
        (fun r h => hr r (List.mem_append_left _ h)))

end VG.Proof.Dsa.Generation
