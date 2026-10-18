module

public import VerifiedGarbage.Proof.HashFns.X86_64.Witness
public import VerifiedGarbage.Proof.Framework.X86_64.CallMeetsC

/-!
# Functions meeting the streaming contracts, for a caller with tables (x86-64)

`Witness.init_meets`, … for the contract of a caller under
`abi.withConsts cs`: the witnesses' functions, which read no tables, meet the
streaming contracts under it too (`C.tableOf_one`), as they run the same
whatever the regions, and their contracts under `abi.withConsts cs` hold of
an entry exactly when the plain ones hold of it without the tables' regions
(`CallC.withConsts_pre_inv`).
-/

@[expose] public section

namespace VG.Proof.HashFns.X86_64.Witness.C

open VG VG.X86_64
open VG.X86_64.CallC (withConsts_withConsts withConsts_pre_inv withConsts_post_inv)

/-- `meets_of`, under `abi.withConsts cs`: from what the function does on the
entries of the plain contract (`hrun`), for a contract `K` whose
precondition under `abi.withConsts cs` is the plain one without the tables'
regions (`hinv`) and whose postcondition does not depend on the regions
(`hpost`). -/
theorem meets_of {K : Abi isa → Nat → Contract isa} {cs : List (String × List (BitVec 64))} {stack : Nat}
    {s : State} {a : Addr} {g : Arch → Mem} (h : s.funs a = some (memFn g))
    (hinv : ∀ s₁, (K (abi.withConsts cs) 8).pre s₁ →
      (K abi 8).pre (s₁.withRegions (s₁.rd.take (s₁.rd.length - cs.length)) s₁.wr))
    (hpost : ∀ s₁ s₂ (r w : List Region), (K abi 8).post (s₁.withRegions r w) (s₂.withRegions r w) →
      (K (abi.withConsts cs) 8).post s₁ s₂)
    (hrun : ∀ s₁, (K abi 8).pre s₁ → Frame s₁.wr s₁.mem (g s₁.arch) ∧
      (∀ r ∈ s₁.wr, r.Disjoint ⟨s₁.gpr .rsp, 8⟩) ∧ (K abi 8).post s₁ (s₁.withArch { s₁.arch with mem := g s₁.arch })) :
    FnMeets (abi.withConsts cs) K 8 stack s a := by
  have hk : (abi.withConsts cs).withConsts [] = abi.withConsts cs := by
    rw [withConsts_withConsts, List.nil_append]
  refine ⟨_, [], by simp only [isa, fnAt, h]; rfl, by simp only [fnConsts, h]; rfl, ?_, ?_, ?_⟩
  · cases cs <;>
      exact ⟨fun c hc => absurd hc List.not_mem_nil, fun t ht => absurd ht List.not_mem_nil⟩
  · intro s₁ _ _ hp
    rw [hk] at hp ⊢
    obtain ⟨hF, hd, hq⟩ := hrun _ (hinv s₁ hp)
    refine ⟨_, [], rfl, ⟨⟨fun r _ => rfl, ?_, rfl⟩, fun x hx _ => hF x hx⟩, hpost s₁ _ _ _ hq⟩
    exact hF.readW (r := ⟨s₁.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => (hd r hr).symm) (by decide)
  · intro _ _ t₁ t₂ _ _ _ _ _ _ _ _ _ h₁ h₂
    simp only [memFn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.2, ← h₂.2]

theorem init_meets {cs : List (String × List (BitVec 64))} {stack : Nat} {s : State} {a : Addr}
    (h : s.funs a = some sha1Init) :
    FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.initContract T A n) 8 stack s a :=
  meets_of h (fun _ hp => withConsts_pre_inv (sig := Spec.HashFns.initSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.initPost T) hp)
    (fun _ _ _ _ hq => withConsts_post_inv (sig := Spec.HashFns.initSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.initPost T) hq) init_run

theorem update_meets {cs : List (String × List (BitVec 64))} {stack : Nat} {s : State} {a : Addr}
    (h : s.funs a = some sha1Update) :
    FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.updateContract T A n) 8 stack s a :=
  meets_of h (fun _ hp => withConsts_pre_inv (sig := Spec.HashFns.updateSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.updatePost T) hp)
    (fun _ _ _ _ hq => withConsts_post_inv (sig := Spec.HashFns.updateSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.updatePost T) hq) update_run

theorem finalize_meets {cs : List (String × List (BitVec 64))} {stack : Nat} {s : State} {a : Addr}
    (h : s.funs a = some sha1Finalize) :
    FnMeets (abi.withConsts cs) (fun A n => Spec.HashFns.finalizeContract T A n) 8 stack s a :=
  meets_of h (fun _ hp => withConsts_pre_inv (sig := Spec.HashFns.finalizeSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.finalizePost T) hp)
    (fun _ _ _ _ hq => withConsts_post_inv (sig := Spec.HashFns.finalizeSig T)
      (pre := fun _ => Curry.const (fun _ => True) _) (post := Spec.HashFns.finalizePost T) hq) finalize_run

/-- `tableOf_one`, for a caller under `abi.withConsts cs`. -/
theorem tableOf_one {cs : List (String × List (BitVec 64))} {stack : Nat} {s : State} {p a₀ a₁ a₂ : Addr}
    (h₀ : s.funs a₀ = some sha1Init) (h₁ : s.funs a₁ = some sha1Update) (h₂ : s.funs a₂ = some sha1Finalize)
    (r₀ : s.mem.readW p 64 = a₀) (r₁ : s.mem.readW (p + 8) 64 = a₁) (r₂ : s.mem.readW (p + 16) 64 = a₂) :
    Spec.HashFns.tableOf 1 s.mem p (fun a K n => FnMeets (abi.withConsts cs) K n stack s a) := by
  simp only [Spec.HashFns.tableOf, streaming_one, Spec.HashFns.table, r₀, r₁, r₂]
  exact ⟨init_meets h₀, update_meets h₁, finalize_meets h₂⟩

end VG.Proof.HashFns.X86_64.Witness.C
