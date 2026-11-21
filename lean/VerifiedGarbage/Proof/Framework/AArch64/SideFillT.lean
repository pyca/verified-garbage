module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
public import VerifiedGarbage.Impl.Scrub.AArch64.WritesL

/-! # The cleanup of code that calls through tables, and of code with large frames, on AArch64

`verifiedScrubbedOfT` is `verifiedScrubbedOf` for code with indirect calls,
through the tables of functions its contract's ABI states
(`Abi.withTables`): the functions it may call are the tables'
(`tablesCall`), whose addresses are public. `verifiedScrubbedOfL` and
`verifiedScrubbedOfLT` are those for more than 4080 bytes of stack
(`scrubOfL`). `table_depth_of_fill2` is `side_depth_of_fill2` for code with
indirect calls: what the lemmas need of code that is closed code with its
holes filled by code without indirect calls. -/

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
      (fun _ _ _ n hn => by rw [inames_of_noIcall (noIcall_of_sideAll hs)] at hn; cases hn) hrb⟩

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
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCall hpub ht) hrb⟩

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
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCallA hpub ht) hrb⟩

/-- `verifiedScrubbedOfT` for `4080 < W < 8176` bytes of stack. -/
theorem verifiedScrubbedOfLT {c : Prog isa} {k : Contract isa} {W rb : Nat} {sig : Sig}
    {ts : List (String × List FnTable)} (hv : Verified target c k)
    (hok : ScrubAllOk k W rb) (hW : 4080 < W ∧ W < 8176 ∧ W % 16 = 0) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (abi.withTables sig ts).pub s₁ s₂) (ht : tablesCall c ts = true)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    VerifiedScrubbed target (scrubOfL W rb c) k rb :=
  ⟨Verified.scrubAllL (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAllL (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hd hdit (syms_of_tablesCall hpub ht) hrb⟩

/-- `Code.all` of code with its holes filled, from the code's and the
fillings'. -/
theorem all_fill2 {p : Instr → Bool} {a b e : Prog isa} (ha : a.all p = true) (hb : b.all p = true)
    (he : e.all p = true) : (Code.fill2 a b e).all p = true := by
  induction e with
  | block is => exact he
  | seq x y ihx ihy =>
    simp only [Code.fill2, Code.all, Bool.and_eq_true] at he ⊢
    exact ⟨ihx he.1, ihy he.2⟩
  | ite cd t e iht ihe =>
    simp only [Code.fill2, Code.all, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1, ihe he.2⟩
  | loop x cd ih => simp only [Code.fill2, Code.all] at he ⊢; exact ih he
  | call m body ih =>
    unfold Code.fill2
    split
    · exact ha
    · exact hb
    · simp only [Code.all] at he ⊢; exact ih he
  | frame i x j ih =>
    simp only [Code.fill2, Code.all, Bool.and_eq_true] at he ⊢
    exact ⟨⟨he.1.1, ih he.1.2⟩, he.2⟩
  | icall i m x y => exact he

/-- Filling holes with code without indirect calls leaves the functions
called indirectly. -/
theorem inames_fill2 {a b e : Prog isa} (ha : inames a = []) (hb : inames b = []) :
    inames (Code.fill2 a b e) = inames e := by
  induction e with
  | block is => rfl
  | seq x y ihx ihy => simp only [Code.fill2, inames, ihx, ihy]
  | ite cd t e iht ihe => simp only [Code.fill2, inames, iht, ihe]
  | loop x cd ih => simp only [Code.fill2, inames, ih]
  | call m body ih =>
    unfold Code.fill2
    split
    · simp only [ha, inames]
    · simp only [hb, inames, List.append_nil]
    · simp only [inames, ih]
  | frame i x j ih => simp only [Code.fill2, inames, ih]
  | icall i m x y => rfl

/-- What `verifiedScrubbedOfT` needs of code `c` that is the closed code `e`
with its two kinds of holes filled by `a` and `b`, code without indirect
calls: from the instructions, the indirect calls and the depth of `e`, which
the kernel evaluates once, and what is known of `a` and `b`. -/
theorem table_depth_of_fill2 {c e a b : Prog isa} {ts : List (String × List FnTable)} {da db d : Nat}
    (hc : c = Code.fill2 a b e)
    (ha : sideAll (fun i => !i.writesDit) a = true) (hda : a.aarch64Depth ≤ da)
    (hb : sideAll (fun i => !i.writesDit) b = true) (hdb : b.aarch64Depth ≤ db)
    (he : e.all (fun i => !i.writesDit) = true) (ht : tablesCall e ts = true)
    (hd : Code.aarch64Depth2 da db e ≤ d) :
    c.all (fun i => !i.writesDit) = true ∧ tablesCall c ts = true ∧ c.aarch64Depth ≤ d := by
  subst hc
  refine ⟨all_fill2 (Code.all_of_allInstrs (allInstrs_of_sideAll ha))
    (Code.all_of_allInstrs (allInstrs_of_sideAll hb)) he, ?_,
    Nat.le_trans (Code.aarch64Depth_fill2_le hda hdb e) hd⟩
  unfold tablesCall
  rw [inames_fill2 (inames_of_noIcall (noIcall_of_sideAll ha)) (inames_of_noIcall (noIcall_of_sideAll hb))]
  exact ht

end VG.AArch64.Scrub
