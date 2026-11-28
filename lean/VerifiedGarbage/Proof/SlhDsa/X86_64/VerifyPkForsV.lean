module

-- separate module: the calling convention of `forsPk`, which its constant-time proof builds on

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkForsMain
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmssV
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA on x86-64: `forsPk`'s calling-convention facts

`forsPk` never writes `rsp` itself (`forsPk_nosp`), never loads MXCSR but in
its callees (`forsPk_nm`), its depth of calls is one more than `thash4`'s
(`forsPk_depth`); from its precondition it runs to its postcondition,
keeping the calling convention (`forsPk_correct`), and a call of it does so
too (`forsPkcall_ok`); a state satisfies its precondition (`fsat_pre`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.SlhDsa

/-- A property of every instruction of `forsPk`, from those of `thash4` and
of its own blocks. -/
theorem forsPk_all {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (P : Instr → Bool)
    (hT : ∀ i ∈ instrs f.t4, P i = true)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p { f with t4 := .block [] }), P i = true) :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p f), P i = true := by
  intro i hi
  simp only [Impl.SlhDsa.X86_64.Verify.forsPk, Impl.SlhDsa.X86_64.Verify.forsGroup,
    Impl.SlhDsa.X86_64.Verify.forsLeaves, Impl.SlhDsa.X86_64.Verify.forsUp, Impl.SlhDsa.X86_64.Verify.forsUpLane,
    Impl.SlhDsa.X86_64.Fors.pkFors, Impl.SlhDsa.X86_64.thashCall, instrs, List.mem_append, List.not_mem_nil,
    or_false] at hi hB
  by_cases h₀ : i ∈ instrs f.t4
  · exact hT i h₀
  · simp only [h₀, or_false] at hi
    exact hB i hi

theorem forsPk_nosp {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hT : NoSp f.t4)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p { f with t4 := .block [] }), (!Taint.clobbers i .rsp) = true) :
    NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f) := fun i hi => by
  have := forsPk_all (p := p) (f := f) (fun i => !Taint.clobbers i .rsp) (fun i hi => by simp [hT i hi]) hB i hi
  simpa using this

theorem forsPk_nm {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hT : f.t4.allInstrs (fun i => !loadsMxcsr i) = true)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.forsPk p { f with t4 := .block [] }), (!loadsMxcsr i) = true) :
    (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  rw [Code.allInstrs_eq, List.all_eq_true] at hT
  exact forsPk_all _ hT hB

theorem forsPk_depth (p : Params) (f : Impl.SlhDsa.X86_64.Shake.Fns) :
    (Impl.SlhDsa.X86_64.Verify.forsPk p f).depth = f.t4.depth + 1 := by
  simp [Impl.SlhDsa.X86_64.Verify.forsPk, Impl.SlhDsa.X86_64.Verify.forsGroup,
    Impl.SlhDsa.X86_64.Verify.forsLeaves, Impl.SlhDsa.X86_64.Verify.forsUp, Impl.SlhDsa.X86_64.Verify.forsUpLane,
    Impl.SlhDsa.X86_64.Fors.pkFors, Impl.SlhDsa.X86_64.thashCall, Code.depth]

/-- The parameters `forsPk` is proved for: SHAKE, `n` of 16, 24 or 32 bytes,
`1 ≤ a ≤ 14`, `1 ≤ k ≤ 35`. -/
structure FPar (p : Params) : Prop where
  n : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  fam : p.family = .shake
  a1 : 1 ≤ p.a
  a : p.a ≤ 14
  k1 : 1 ≤ p.k
  k : p.k ≤ 35
  md : p.mdLen + 2 ≤ 64

/-- `forsPk`, from its precondition: an execution to its postcondition that
keeps the calling convention. -/
theorem forsPk_correct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : FPar p) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true) :
    ∀ s, (forsPkContract p stack).pre s → ∃ t s', Exec isa (Impl.SlhDsa.X86_64.Verify.forsPk p f) s t s' ∧
      abiPreserved s s' ∧ (forsPkContract p stack).post s s' := by
  intro s h
  obtain ⟨t, s', he, hcs, hpost⟩ := forsPk_ok T ht hp.n hp.fam hp.a1 hp.a hp.k1 hp.k hp.md hst hs63 h
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨hcs, ?_⟩, hpost⟩
  obtain ⟨R, ⟨pk, a, henv⟩, _⟩ := h
  have hn32 : p.n ≤ 32 := by omega_using [hp.n]
  have F := (hpost pk a henv).2.2
  refine F.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact R.ret_scr.sub_right (changes_sub_scr hn32 _ r hr)
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega

/-- A call of `forsPk`, given its precondition at the call's entry (narrowed
to the regions `rd` and `wr`). -/
theorem forsPkcall_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : FPar p) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (name : String) {s : State}
    {rd wr : List Region} (hpre : (forsPkContract p stack).pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .rsp) (8 * (T.code.depth + 2))]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧
        (forsPkContract p stack).post (s.callEntry.withRegions rd wr) s₂) →
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 → Q s') :
    WP isa (.call name (Impl.SlhDsa.X86_64.Verify.forsPk p f)) s Q := by
  have hd := T.depth_le
  exact WP.call_mx (forsPk_correct T ht hp hst hs63 hmx) hsp
    (by rw [forsPk_depth, ht]; omega_using [hd]) hpre hc hw fun s' h₁ h₂ h₃ h₄ _ h₆ h₇ =>
      hQ s' h₁ h₂ h₃ (by rw [forsPk_depth, ht] at h₄; exact h₄) h₆ h₇

/-! ## A state satisfying the precondition -/

open VG.Proof.SlhDsa.X86_64.Levels (lsp lS lAU lS_toNat lmem lsat_rc lbytes_zero)

/-- `forsPk`'s witness: `scratch` (with the round constants) and the
signature above the stack pointer `2^63`, the key pair 0. -/
def fsat (p : Params) : State where
  gpr r := match r with
    | .rdi => lS | .rsi => lAU | .rsp => lsp | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := lmem
  rd := [⟨lAU, p.forsSigLen⟩]
  wr := [⟨lS, scratchLen⟩, ⟨lS, 0⟩]

theorem fsat_pre {p : Params} (hn : p.n ≤ 32) (ha : p.a ≤ 14) (hk : p.k ≤ 35) {stack : Nat}
    (hs63 : stack < 2 ^ 63) : (forsPkContract p stack).pre (fsat p) := by
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have hx : p.forsSigLen ≤ 35 * 15 * 32 := by
    simp only [Params.forsSigLen]; exact Nat.mul_le_mul (Nat.mul_le_mul hk (by omega)) hn
  have eAU : lAU.toNat = 2 ^ 63 + 0x200000 := by decide
  have hAS : Region.Disjoint ⟨lAU, p.forsSigLen⟩ ⟨lS, scratchLen⟩ :=
    Offset.disjoint lsp (.inr (by rw [show scratchLen = 65536 from rfl]; omega)) (by omega)
      (by rw [show scratchLen = 65536 from rfl]; omega)
  refine ⟨⟨rfl, rfl, by show lS.toNat + scratchLen ≤ 2 ^ 64; rw [lS_toNat]; decide,
    by show lS.toNat + 0 ≤ 2 ^ 64; rw [lS_toNat]; decide, empty_disj _ _, fun r hr => ?_, fun r hr => ?_,
    ?_, (empty_disj _ _).symm, fun r hr => ?_, ?_, (empty_disj _ _).symm, fun r hr => ?_⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, lsat_rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk => ?_⟩, by show (0 : BitVec 64).toNat < 2 ^ 32; decide⟩
  all_goals first
    | (simp only [List.mem_singleton] at hr; subst hr)
    | skip
  · show lAU.toNat + p.forsSigLen ≤ 2 ^ 64; omega
  · exact hAS
  · exact (Offset.disjoint_base lsp (k := 8) (by omega) (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_base lsp (k := 8) (by omega) (by omega)).symm
  · exact (Offset.disjoint_below lsp (n := stack) (d := 0x100000) (k := scratchLen)
      (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_below lsp (n := stack) (d := 0x200000) (k := p.forsSigLen) (by omega)).symm
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))

end VG.Proof.SlhDsa.X86_64
