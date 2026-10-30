module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Framework.Omega

/-! # The trace of private CRT at a run-time width, from the components to the result

The components' import, the acceptance, the recombination and the output
are checked by the taint analysis, the powers and the coefficient related
by `power_relCT` and `coefficient_relCT` (`sized_relCT`), on states whose
permissions are narrowed to the output and the working space; the runs
from the states themselves leak the same traces (`sizedNarrow_relCT`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_narrow)
open VG.Proof.Bignum.X86.Crt (componentValue)

/-- The taint checks of `sized`. -/
structure SizedChecks : Prop where
  front : ACheck (Prog.chain [importComponents, validate] (.block []))
  init : ACheck (.block factorsInit)
  p : PowChecks 10 12 16
  swaps : ACheck (.seq (swap 10 11 (one .wide)) (.seq (swap 12 13 (one .wide)) (.seq (swap 16 17 (two .wide))
    (.block factorNext))))
  co : CoChecks
  back : ACheck (.seq recombine exportResult)

theorem sizedChecks : SizedChecks := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    (try dsimp only [MulCheck, ACheck]) <;> taint_decide

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

theorem front_run (R : Run (CrtExtra base bytes len args) base bytes len args sp s) :
    WP isa (Prog.chain [importComponents, validate] (.block [])) s fun u =>
      Run (CrtExtra base bytes len args) base bytes len args sp u ∧ ∃ m₀, Comps base len args m₀ u.mem :=
  front_ok R.1 fun _ hu _ c _ K => WP.block_nil ⟨⟨hu, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, _, c⟩

/-- The factors' loop with `n` of them left (`FacInv` after `2 - n` steps). -/
def LoopSt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (n : Nat) (t : State) : Prop :=
  1 ≤ n ∧ n ≤ 2 ∧ ∃ m₀ s₀, Comps base len args m₀ s₀.mem ∧ FacInv base bytes len args m₀ s₀ (2 - n) t

/-- Registers two states both keep from a third, one keeps from the other. -/
theorem Keeps.of_common {rs : List Reg} {s₀ t u : State} (K₁ : Keeps rs s₀ t) (K₂ : Keeps rs s₀ u) : Keeps rs t u :=
  ⟨fun r hr => (K₂.1 r hr).trans (K₁.1 r hr).symm, K₂.2.1.trans K₁.2.1.symm, K₂.2.2.trans K₁.2.2.symm⟩

/-- What a step of the factors' loop leaves: a run, ZF after the last factor, and the loop's state
otherwise. -/
abbrev LoopPost (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (n : Nat) (u : State) : Prop :=
  Run (CrtExtra base bytes len args) base bytes len args sp u ∧ (n = 1 ∨ n = 2) ∧
    u.zf = some (decide (n = 1)) ∧ (n = 2 → LoopSt base bytes len args 1 u)

theorem loopStep_ok {n : Nat} {t : State} (R : Run (CrtExtra base bytes len args) base bytes len args sp t)
    (L : LoopSt base bytes len args n t) : WP isa factorStep t (LoopPost base bytes len args sp n) := by
  obtain ⟨h1, h2, m₀, s₀, c, I⟩ := L
  refine WP.mono (facStep_ok c I.inp.crt.dpLen I.inp.crt.dqLen (by omega_arith) I) fun u ⟨I', Z⟩ => ?_
  have K := Keeps.of_common I.keeps I'.keeps
  refine ⟨⟨I'.inp, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by omega_arith, ?_, fun e => ?_⟩
  · rw [Z]; congr 1; apply decide_eq_decide.mpr; omega_arith
  · subst e; exact ⟨Nat.le_refl _, by decide, m₀, s₀, c, I'⟩

/-- The factors' loop, from runs with as many factors left. -/
theorem loop_relCT (hc : SizedChecks) (n : Nat) :
    RelCT isa (Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧ LoopSt base bytes len args n t)
      (.loop factorStep .ne) (Both (Run (CrtExtra base bytes len args) base bytes len args sp)) := by
  refine VG.RelCT.loop (M := isa) (fun n => Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧
    LoopSt base bytes len args n t) (fun n => ?_) n
  have tr : RelCT isa (Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧
      LoopSt base bytes len args n t) factorStep fun _ _ => True := by
    unfold factorStep
    refine VG.RelCT.seq ((power_relCT (Ex := CrtExtra base bytes len args) (base := base) (bytes := bytes) (len := len)
      (args := args) (sp := sp) hc.p (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).mono (fun s₁ s₂ h => ?_) fun _ _ h => h) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2)
      hc.swaps)
    obtain ⟨⟨R₁, _, _, _, _, _, I₁⟩, ⟨R₂, _, _, _, _, _, I₂⟩⟩ := h
    exact ⟨_, ⟨R₁, I₁.l₁⟩, ⟨R₂, I₂.l₁⟩⟩
  refine (tr.wp (F₁ := LoopPost base bytes len args sp n) (F₂ := LoopPost base bytes len args sp n)
    fun s₁ s₂ h => ⟨loopStep_ok h.1.1 h.1.2, loopStep_ok h.2.1 h.2.2⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨_, ⟨R₁, N₁, Z₁, L₁⟩, ⟨R₂, _, Z₂, L₂⟩⟩
  refine ⟨?_, fun _ => ⟨R₁, R₂⟩, fun e => ?_⟩
  · show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [Z₁, Z₂]
  · have e' : n ≠ 1 := fun h => by
      have : s₁.zf.map (!·) = some true := e
      rw [Z₁, h] at this; cases this
    have hn : n = 2 := by omega_arith
    exact ⟨1, by omega_arith, ⟨R₁, L₁ hn⟩, ⟨R₂, L₂ hn⟩⟩

theorem sized_relCT (sp : BitVec 32) :
    RelCT isa (Both (Run (CrtExtra base bytes len args) base bytes len args sp)) CrtRt.sized fun _ _ => True := by
  have hc := sizedChecks
  show RelCT isa _ (Prog.chain [importComponents, validate] (.seq (.block factorsInit) (.seq (.loop factorStep .ne)
    (.seq coefficient (.seq recombine exportResult))))) _
  refine VG.RelCT.chain (VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.front
    fun _ R => front_run R) ?_)
  refine VG.RelCT.seq (taint_both (F := fun u => Run (CrtExtra base bytes len args) base bytes len args sp u ∧
      LoopSt base bytes len args 2 u) (fun _ _ R₁ R₂ => R₁.1.agree R₂.1) _ hc.init fun t ⟨R, m₀, c⟩ =>
    WP.mono (factorsInit_ok R.1 c) fun u I => ⟨⟨I.inp, R.2.1.keep I.keeps, (I.keeps.1 _ (by decide)).trans R.2.2⟩,
      by decide, by decide, m₀, t, c, I⟩) ?_
  refine VG.RelCT.seq (loop_relCT hc 2) ?_
  refine VG.RelCT.seq (coefficient_relCT hc.co) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) hc.back

/-- The permissions of `sized`'s narrowed runs: everything readable, the output and the working space
writable. -/
abbrev narrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), len⟩, ⟨base, bytes⟩]

/-- What the runs of `sized` from the states themselves need: the inputs, a valid modulus, `esp`, and
the arguments apart from the output and the working space. -/
def SizedAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  RIn base bytes len args s ∧ s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩

theorem narrow_in (S : SizedAt base bytes len args sp s) :
    RIn base bytes len args (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨h, _, _, _, _⟩ := S
  have x := h.extra
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.room, h.top, h.need,
    h.hbase, h.hbytes, ⟨x.space, x.nLen, x.inLen, x.pShort, x.qShort, x.dpLen, x.dqLen, x.qiLen, x.outFit,
    ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, x.outApart, x.positive, x.bounded, x.fits,
    fun i hi => ?_, x.apart⟩⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := x.readable i hi
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem narrow_run (S : SizedAt base bytes len args sp s) :
    Run (CrtExtra base bytes len args) base bytes len args sp (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  refine ⟨narrow_in S, ⟨S.1.top, fun r hr => ?_⟩, S.2.1⟩
  simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact S.2.2.2.1
  · exact S.2.2.2.2

theorem sizedNarrow_relCT (sp : BitVec 32) :
    RelCT isa (Both (SizedAt base bytes len args sp)) CrtRt.sized fun _ _ => True := by
  refine relCT_narrow (Pn := Both (Run (CrtExtra base bytes len args) base bytes len args sp)) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (sized_relCT sp)
  have cov : ∀ {s : State}, SizedAt base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.crt.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, SizedAt base bytes len args sp s →
      ∃ F, WP isa CrtRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F :=
    fun S => ⟨_, sized_ok (narrow_in S) S.2.2.1⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    narrow_run S₁, narrow_run S₂⟩

end

end VG.Proof.Bignum.X86.CrtRt
