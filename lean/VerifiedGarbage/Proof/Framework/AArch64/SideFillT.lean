module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
public import VerifiedGarbage.Impl.Scrub.AArch64.WritesL

/-! # The cleanup of code that calls through tables, and of code with large frames, on AArch64

`verifiedScrubbedOfT` is `verifiedScrubbedOf` for code with indirect calls,
through the tables of functions its contract's ABI states
(`Abi.withTables`): the functions it may call are the tables'
(`tablesCall`), whose addresses are public. `verifiedScrubbedOfL` and
`verifiedScrubbedOfLT` are those for more than 4080 bytes of stack
(`scrubOfL`). What they need of code that calls through tables is in
`TableFill.lean`. -/

@[expose] public section

namespace VG.AArch64.Scrub

open VG VG.AArch64 VG.Impl.Scrub.AArch64

/-- `verifiedScrubbedOf` for `4080 < W < 8176` bytes of stack. -/
theorem verifiedScrubbedOfL {c : Prog isa} {k : Contract isa} {W rb : Nat} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 4080 < W ∧ W < 8176 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hs : sideAll (fun i => !i.writesDit) c = true) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOfL W rb c) k rb :=
  ⟨Verified.scrubAllL (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAllL (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd
      (Code.all_of_allInstrs (allInstrs_of_sideAll hs))
      (fun _ _ _ n hn => by rw [inames_of_noIcall (noIcall_of_sideAll hs)] at hn; cases hn) hrb, fun ty _ h => by cases ty <;> cases h⟩

/-- The functions `c` calls indirectly have the same addresses in two runs
its contract relates, when they are those of the tables of its ABI. -/
theorem syms_of_tablesCall {c : Prog isa} {k : Contract isa} {sig : Sig} {ts : List (String × List FnTable)}
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (abi.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true) :
    ∀ s₁ s₂, k.pub s₁ s₂ → ∀ n ∈ inames c, s₁.syms n = s₂.syms n := by
  intro s₁ s₂ hp n hn
  have := List.all_eq_true.mp ht n hn
  simp only [decide_eq_true_eq] at this
  exact tables_pub_syms (hpub s₁ s₂ hp) n this

/-- `verifiedScrubbedOf` for code that calls through the tables `ts` of its
contract's ABI (`hpub`, by `contract_pub`). -/
theorem verifiedScrubbedOfT {c : Prog isa} {k : Contract isa} {W rb : Nat} {sig : Sig}
    {ts : List (String × List FnTable)} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (abi.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOf W rb c) k rb :=
  ⟨Verified.scrubAll (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCall hpub ht) hrb, fun ty _ h => by cases ty <;> cases h⟩

/-- `syms_of_tablesCall` for a contract whose ABI has the tables over any
ABI `A` (one with tables of constants, `Abi.withConsts`). -/
theorem syms_of_tablesCallA {A : Abi isa} {c : Prog isa} {k : Contract isa} {sig : Sig}
    {ts : List (String × List FnTable)}
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (A.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true) :
    ∀ s₁ s₂, k.pub s₁ s₂ → ∀ n ∈ inames c, s₁.syms n = s₂.syms n := by
  intro s₁ s₂ hp n hn
  have := List.all_eq_true.mp ht n hn
  simp only [decide_eq_true_eq] at this
  exact tables_pub_syms (hpub s₁ s₂ hp) n this

/-- `verifiedScrubbedOfT` for a contract whose ABI has the tables over any
ABI `A`: code that also reads tables of constants (ECDSA's comb). -/
theorem verifiedScrubbedOfTA {A : Abi isa} {c : Prog isa} {k : Contract isa} {W rb : Nat} {sig : Sig}
    {ts : List (String × List FnTable)} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (A.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOf W rb c) k rb :=
  ⟨Verified.scrubAll (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCallA hpub ht) hrb, fun ty _ h => by cases ty <;> cases h⟩

/-- `verifiedScrubbedOfT` for `4080 < W < 8176` bytes of stack. -/
theorem verifiedScrubbedOfLT {c : Prog isa} {k : Contract isa} {W rb : Nat} {sig : Sig}
    {ts : List (String × List FnTable)} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 4080 < W ∧ W < 8176 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (abi.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOfL W rb c) k rb :=
  ⟨Verified.scrubAllL (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAllL (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCall hpub ht) hrb, fun ty _ h => by cases ty <;> cases h⟩

end VG.AArch64.Scrub
