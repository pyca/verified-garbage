module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkXmss
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT

/-!
# SLH-DSA on x86-64: `xmssPk`'s calling-convention facts

`xmssPk` never writes `rsp` itself (`xmssPk_nosp`), never loads MXCSR but
in its callees (`xmssPk_nm`), its depth of calls is one more than
`thash4`'s (`xmssPk_depth`), and from its precondition it runs to its
postcondition, keeping the calling convention (`xmssPk_correct`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.SlhDsa

/-- A property of every instruction of `xmssPk`, from those of `thash4` and
of its own blocks. -/
theorem xmssPk_all {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (P : Instr → Bool)
    (hT : ∀ i ∈ instrs f.t4, P i = true)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.xmssPk p { f with t4 := .block [] }), P i = true) :
    ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.xmssPk p f), P i = true := by
  intro i hi
  simp only [Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.wotsPk, Impl.SlhDsa.X86_64.Verify.pathBody,
    Impl.SlhDsa.X86_64.thashCall, instrs, List.mem_append, List.not_mem_nil, or_false] at hi hB
  by_cases h₀ : i ∈ instrs f.t4
  · exact hT i h₀
  · simp only [h₀, or_false] at hi
    exact hB i hi

theorem xmssPk_nosp {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hT : NoSp f.t4)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.xmssPk p { f with t4 := .block [] }), (!Taint.clobbers i .rsp) = true) :
    NoSp (Impl.SlhDsa.X86_64.Verify.xmssPk p f) := fun i hi => by
  have := xmssPk_all (p := p) (f := f) (fun i => !Taint.clobbers i .rsp) (fun i hi => by simp [hT i hi]) hB i hi
  simpa using this

theorem xmssPk_nm {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (hT : f.t4.allInstrs (fun i => !loadsMxcsr i) = true)
    (hB : ∀ i ∈ instrs (Impl.SlhDsa.X86_64.Verify.xmssPk p { f with t4 := .block [] }), (!loadsMxcsr i) = true) :
    (Impl.SlhDsa.X86_64.Verify.xmssPk p f).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  rw [Code.allInstrs_eq, List.all_eq_true] at hT
  exact xmssPk_all _ hT hB

theorem xmssPk_depth (p : Params) (f : Impl.SlhDsa.X86_64.Shake.Fns) :
    (Impl.SlhDsa.X86_64.Verify.xmssPk p f).depth = f.t4.depth + 1 := by
  simp [Impl.SlhDsa.X86_64.Verify.xmssPk, Impl.SlhDsa.X86_64.Verify.chainGroup,
    Impl.SlhDsa.X86_64.Verify.stepBody, Impl.SlhDsa.X86_64.Verify.restoreLane, Impl.SlhDsa.X86_64.Verify.wotsPk,
    Impl.SlhDsa.X86_64.Verify.pathBody, Impl.SlhDsa.X86_64.thashCall, Code.depth]

/-- `xmssPk`, from its precondition: an execution to its postcondition that
keeps the calling convention. -/
theorem xmssPk_correct {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hw4 : p.lgw = 4)
    (hhp : 0 < p.hp) (hhp' : p.hp ≤ 32) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    (hmx : (Impl.SlhDsa.X86_64.Verify.xmssPk p f).allInstrs (fun i => !loadsMxcsr i) = true) :
    ∀ s, (xmssPkContract p stack).pre s → ∃ t s', Exec isa (Impl.SlhDsa.X86_64.Verify.xmssPk p f) s t s' ∧
      abiPreserved s s' ∧ (xmssPkContract p stack).post s s' := by
  intro s h
  obtain ⟨t, s', he, hcs, hpost⟩ := xmssPk_ok T ht hn hfam hw4 hhp hhp' hst hs63 h
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨hcs, ?_⟩, hpost⟩
  obtain ⟨R, ⟨pk, a, henv⟩, _⟩ := h
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have F := (hpost pk a henv).2.2
  refine F.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · exact R.ret_scr.sub_right (changes_sub_scr hn32 _ r hr)
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega

/-! ## A state satisfying the precondition -/

open VG.Proof.SlhDsa.X86_64.Levels (lsp lS lAU lS_toNat lmem lsat_rc lbytes_zero)

/-- `xmssPk`'s witness: `scratch` (with the round constants) and the
signature above the stack pointer `2^63`, the key pair 0. -/
def xsat (p : Params) : State where
  gpr r := match r with
    | .rdi => lS | .rdx => lAU | .rsp => lsp | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := lmem
  rd := [⟨lAU, p.xmssSigLen⟩]
  wr := [⟨lS, scratchLen⟩, ⟨lS, 0⟩]

theorem empty_disj (a : Addr) (R : Region) : Region.Disjoint ⟨a, 0⟩ R := fun x h _ => by
  simp only [Region.Contains] at h; omega

theorem xsat_pre {p : Params} (hn : p.n ≤ 32) (hl : p.len ≤ 128) (hh : p.hp ≤ 32) {stack : Nat}
    (hs63 : stack < 2 ^ 63) : (xmssPkContract p stack).pre (xsat p) := by
  have hLA : ∀ k, Layout.laneA k = 3296 + 128 * k := fun _ => rfl
  have hLB : ∀ k, Layout.laneB k = 3808 + 2208 * k := fun _ => rfl
  have hx : p.xmssSigLen ≤ 160 * 32 := by
    simp only [Params.xmssSigLen]; exact Nat.mul_le_mul (by omega) hn
  have eAU : lAU.toNat = 2 ^ 63 + 0x200000 := by decide
  have hAS : Region.Disjoint ⟨lAU, p.xmssSigLen⟩ ⟨lS, scratchLen⟩ :=
    Offset.disjoint lsp (.inr (by rw [show scratchLen = 65536 from rfl]; omega)) (by omega)
      (by rw [show scratchLen = 65536 from rfl]; omega)
  refine ⟨⟨rfl, rfl, by show lS.toNat + scratchLen ≤ 2 ^ 64; rw [lS_toNat]; decide,
    by show lS.toNat + 0 ≤ 2 ^ 64; rw [lS_toNat]; decide, empty_disj _ _, fun r hr => ?_, fun r hr => ?_,
    ?_, (empty_disj _ _).symm, fun r hr => ?_, ?_, (empty_disj _ _).symm, fun r hr => ?_⟩,
    ⟨List.replicate p.n 0, List.replicate 16 0, lsat_rc, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk => ?_⟩, by show (0 : BitVec 64).toNat < 2 ^ p.hp; exact Nat.two_pow_pos p.hp⟩
  all_goals first
    | (simp only [List.mem_singleton] at hr; subst hr)
    | skip
  · show lAU.toNat + p.xmssSigLen ≤ 2 ^ 64; omega
  · exact hAS
  · exact (Offset.disjoint_base lsp (k := 8) (by omega) (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_base lsp (k := 8) (by omega) (by omega)).symm
  · exact (Offset.disjoint_below lsp (n := stack) (d := 0x100000) (k := scratchLen)
      (by rw [show scratchLen = 65536 from rfl]; omega)).symm
  · exact (Offset.disjoint_below lsp (n := stack) (d := 0x200000) (k := p.xmssSigLen) (by omega)).symm
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))
  · exact (lbytes_zero (by rw [hLA]; omega) (by rw [hLA]; omega))
  · exact (lbytes_zero (by rw [hLB]; omega) (by rw [hLB]; omega))

end VG.Proof.SlhDsa.X86_64
