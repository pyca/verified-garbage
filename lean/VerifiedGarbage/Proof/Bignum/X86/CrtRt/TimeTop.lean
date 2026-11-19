module

public import VerifiedGarbage.Proof.Bignum.X86.CrtEntryTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Bignum.X86.CrtArgumentsEq`, which this module and modules that import it used -/

section

/-! # Private-call resources depend only on the eighteen cdecl arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

theorem Inputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : Inputs base bytes len args s) (eq : ∀ i < 18, args i = other i) :
    Inputs base bytes len other s := by
  have H0 := eq 0 (by decide)
  have H1 := eq 1 (by decide)
  have H3 := eq 3 (by decide)
  have H5 := eq 5 (by decide)
  have H7 := eq 7 (by decide)
  have H9 := eq 9 (by decide)
  have H11 := eq 11 (by decide)
  have H13 := eq 13 (by decide)
  have H15 := eq 15 (by decide)
  refine ⟨H.scratch, H.lower, H.upper, H.space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H.room, H.top⟩
  · intro i hi; rw [← eq i hi]; exact H.stack i hi
  · rw [← H1]; exact H.outLen
  · rw [← H3]; exact H.nLen
  · rw [← H5]; exact H.inLen
  · rw [← H7]; exact H.pShort
  · rw [← H9]; exact H.qShort
  · rw [← H11, ← H7]; exact H.dpLen
  · rw [← H13, ← H9]; exact H.dqLen
  · rw [← H15, ← H7]; exact H.qiLen
  · rw [← H0]; exact H.outFit
  · rw [← H0]; exact H.outWrite
  · rw [← H0]; exact H.outApart
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq (i + 1) bound]; exact H.positive i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq (i + 1) bound]; exact H.bounded i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega_using [bound]), ← eq (i + 1) bound]; exact H.fits i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega_using [bound]), ← eq (i + 1) bound]; exact H.readable i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega_using [bound]), ← eq (i + 1) bound]; exact H.apart i hi

end VG.Proof.Bignum.X86.Crt

end

end

/-! ### `Bignum.X86.CrtObservations`, which this module and modules that import it used -/

section

/-! # Extract the shared contract's public cdecl arguments and key bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem arguments {s t : State} (H : (Proof.Rsa.privateCrtContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 18, arg s i = arg t i := by
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulusBytes {s t : State} (H : (Proof.Rsa.privateCrtContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat := by
  have Leak : (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
    sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  exact (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak

end VG.Proof.Bignum.X86.Crt

end

end

/-! ### `Bignum.X86.CrtFailureTiming`, which this module and modules that import it used -/

section

/-! # Invalid public keys clear a public-length output with a fixed trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem failure_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) PublicFn.failure (fun _ _ => True) := by
  have Zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have Head := VG.RelCT.block_append (VG.RelCT.seq (loadArguments_relCT 0 1 (args 0) (args 1)) Zero)
  have Loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq Head Loop).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc,
      (H.left.stack 1 (by decide)).readSrc, (H.right.stack 1 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86.Crt

end

end

/-! ### `Bignum.X86.CrtModulusTiming`, which this module and modules that import it used -/

section

/-! # Loading and validating the public modulus preserves all call inputs -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem modulus_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (H : Inputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.modulusArgs) (.block modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nf := H.fits 2 (by decide)
  have nr := H.readable 2 (by decide)
  change (args 2).toNat + (args 3).toNat ≤ 2 ^ 32 at nf
  change InRegions (s.rd ++ s.wr) (byteAddr (args 2)) (args 3).toNat at nr
  rw [H.modulus_length] at nf nr
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    (H.stack 2 (by decide)).readSrc (by rw [← H.nLen]; exact (H.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.mono (modulusCheck_ok u H.lower H.upper (by rw [P]; exact nf)
    (by rw [P, K.2.1, K.2.2]; exact nr) C) fun t ⟨Z, Mt, Kt⟩ => ?_
  rw [P, M] at Z
  exact ⟨Z, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide))⟩

theorem modulus_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) (.seq (.block PublicFn.modulusArgs) (.block modulusCheck))
      (fun _ _ => True) := by
  have Check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block modulusCheck) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 2 3 (args 2) (args 3)) Check).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 2 (by decide)).readSrc, (H.right.stack 2 (by decide)).readSrc,
      (H.left.stack 3 (by decide)).readSrc, (H.right.stack 3 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86.Crt

end

end

/-! ### `Bignum.X86.CrtRt.TimeSized`, which only this module used -/

section

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
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
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
    u.zf = some (decide (n = 1)) ∧ (n = 2 → LoopSt base bytes len args 1 u) ∧
    (n = 1 → w32 u.mem base lenOff = (args 7).toNat)

theorem loopStep_ok {n : Nat} {t : State} (R : Run (CrtExtra base bytes len args) base bytes len args sp t)
    (L : LoopSt base bytes len args n t) : WP isa factorStep t (LoopPost base bytes len args sp n) := by
  obtain ⟨h1, h2, m₀, s₀, c, I⟩ := L
  refine WP.mono (facStep_ok c I.inp.crt.dpLen I.inp.crt.dqLen (by omega_arith) I (pc := none) trivial ⟨trivial, fun _ => trivial⟩) fun u ⟨I', Z⟩ => ?_
  have K := Keeps.of_common I.keeps I'.keeps
  refine ⟨⟨I'.inp, R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩, by omega_arith, ?_, fun e => ?_, fun e => ?_⟩
  · rw [Z]; congr 1; apply decide_eq_decide.mpr; omega_arith
  · subst e; exact ⟨Nat.le_refl _, by decide, m₀, s₀, c, I'⟩
  · subst e; exact I'.l₁

/-- The factors' loop, from runs with as many factors left. -/
theorem loop_relCT (hc : SizedChecks) (n : Nat) :
    RelCT isa (Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧ LoopSt base bytes len args n t)
      (.loop factorStep .ne) (Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧
        w32 t.mem base lenOff = (args 7).toNat) := by
  refine VG.RelCT.loop (M := isa) (fun n => Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧
    LoopSt base bytes len args n t) (fun n => ?_) n
  have tr : RelCT isa (Both fun t => Run (CrtExtra base bytes len args) base bytes len args sp t ∧
      LoopSt base bytes len args n t) factorStep fun _ _ => True := by
    unfold factorStep
    refine VG.RelCT.seq ((power_relCT (Ex := CrtExtra base bytes len args) (base := base) (bytes := bytes) (len := len)
      (args := args) (sp := sp) hc.p rhChecks.1 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).mono (fun s₁ s₂ h => ?_) fun _ _ h => h) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2)
      hc.swaps)
    obtain ⟨⟨R₁, _, _, _, _, _, I₁⟩, ⟨R₂, _, _, _, _, _, I₂⟩⟩ := h
    exact ⟨_, ⟨R₁, I₁.l₁⟩, ⟨R₂, I₂.l₁⟩⟩
  refine (tr.wp (F₁ := LoopPost base bytes len args sp n) (F₂ := LoopPost base bytes len args sp n)
    fun s₁ s₂ h => ⟨loopStep_ok h.1.1 h.1.2, loopStep_ok h.2.1 h.2.2⟩).mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨_, ⟨R₁, N₁, Z₁, L₁, W₁⟩, ⟨R₂, _, Z₂, L₂, W₂⟩⟩
  refine ⟨?_, fun x => ?_, fun e => ?_⟩
  · show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [Z₁, Z₂]
  · have n1 : n = 1 := by
      by_contra hn
      have hn2 : n = 2 := by omega_arith
      have : s₁.zf.map (!·) = some false := x
      rw [Z₁, hn2] at this; cases this
    exact ⟨⟨R₁, W₁ n1⟩, ⟨R₂, W₂ n1⟩⟩
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
  refine VG.RelCT.seq ((coefficient_relCT hc.co rhChecks.2.1 rhChecks.2.2).mono
    (fun _ _ h => ⟨_, ⟨h.1.1, h.1.2⟩, ⟨h.2.1, h.2.2⟩⟩) fun _ _ h => h) ?_
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

end

end

/-! # Private CRT RSA at a run-time width on i686 against its contract

The entry, the modulus's check, the failure and the return are the fixed
widths' (`Crt.entry_relCT`, `Crt.modulus_relCT`, `Crt.failure_relCT`,
`Crt.restore_relCT`), with `sized` related by `sizedNarrow_relCT` from what
each run keeps (`Side`): constant time but for the modulus
(`constantTime`), and with `correct`, `verified`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue Pair)
open VG.Proof.Dsa.X86 (argumentPointer wp_result)
open VG.Proof.Bignum.X86.PublicRt (setWidth_toNat)

/-- The contract's resources, and the output apart from the arguments. -/
structure TopABI (s : State) : Prop where
  abi : CrtABI s
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 72⟩

theorem topABI_of {s : State} (h : (Proof.Rsa.privateCrtContract abi 96).pre s) : TopABI s := by
  refine ⟨crtABI_of h, ?_⟩
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  with_reducible assumption

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What each run keeps from the entry on: its inputs, `esp`, and the arguments apart from the output and
the working space. -/
def Side (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  RIn base bytes len args s ∧ s.gpr .esp = sp ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩

theorem Side.keep {sp : BitVec 32} {s t : State} (S : Side base bytes len args sp s) {regs : List Reg}
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp' : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Side base bytes len args sp t :=
  ⟨S.1.keep K di sp' O, (K.1 _ sp').trans S.2.1, by rw [K.1 _ sp']; exact S.2.2.1,
    by rw [K.1 _ sp']; exact S.2.2.2⟩

theorem Side.pair {sp : BitVec 32} {s t : State} (S₁ : Side base bytes len args sp s)
    (S₂ : Side base bytes len args sp t) : Pair base bytes len args s t :=
  ⟨S₁.1.crt, S₂.1.crt, S₁.2.1.trans S₂.2.1.symm⟩

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => Side base bytes len args sp s ∧ Side base bytes len args sp t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      CrtRt.body (fun _ _ => True) := by
  let R := fun s t => (Side base bytes len args sp s ∧ Side base bytes len args sp t) ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧
      (b = true → Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true ∧
        Spec.Rsa.modulusValid (componentValue t.mem args 2) len = true)
  have Branch : RelCT isa R (.ite .e CrtRt.sized PublicFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨⟨⟨S₁, S₂⟩, b, Zs, _, V⟩, Z⟩ E F
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact sizedNarrow_relCT sp _ _ _ _ _ _ ⟨⟨S₁.1, S₁.2.1, (V B).1, S₁.2.2⟩,
        ⟨S₂.1, S₂.2.1, (V B).2, S₂.2.2⟩⟩ E F
    · exact (Crt.failure_relCT base bytes len args).mono (fun _ _ H => H.1.1.1.pair H.1.1.2) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨S₁, S₂, N⟩ E F
  have modulus : ∀ {m : Mem} {x : State}, Side base bytes len args sp x →
      componentValue m args 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) len) := by
    intro m x S
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) (args 3).toNat) = _
    rw [S.1.crt.modulus_length]
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (Crt.modulus_relCT base bytes len args _ _ _ _ _ _ (S₁.pair S₂) E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (Crt.modulus_ok S₁.1.crt) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (Crt.modulus_ok S₂.1.crt) F1
      have U₁ := S₁.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
      have U₂ := S₂.keep Kt (by decide) (by decide) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := ⟨⟨U₁, U₂⟩, _, Zs, by rw [N]; exact Zt, fun hb => ⟨?_, ?_⟩⟩
      · have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
        exact ⟨by rw [T1, T2], trivial⟩
      · rw [modulus U₁, Ms]; exact hb
      · rw [modulus U₂, Mt, ← N]; exact hb

end

/-- The arguments' bytes lie apart from the output and the working space. -/
theorem args_apart {s : State} (A : TopABI s) {r : Region}
    (hret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r) (hargs : Region.Disjoint ⟨argAddr s 0, 72⟩ r) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ r :=
  VG.X86.Taint.frame_disjoint (n := 72) (by have := A.abi.stackBound; omega_using [this]) hret hargs

theorem operation_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 18, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa CrtRt.code s tr sf) (F : Exec isa CrtRt.code t ur tf) : tr = ur := by
  have A0 := args 0 (by decide)
  have A1 := args 1 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A8 := args 16 (by decide)
  have A9 := args 17 (by decide)
  have hb : (arg s 16).toNat = (argumentPointer s 16).toNat := (setWidth_toNat _).symm
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (Crt.entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 16 < 18)).readSrc,
          (B.abi.stackArgument (by decide : 16 < 18)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (Crt.installed_ok A.abi) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (Crt.installed_ok B.abi) F1
      have Iv : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have need := need_le A.abi.lengths.1 A.abi.scratchLength
      have espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      have espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      have Su : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨In.ofInputs Is need hb rfl, espu, ?_, ?_⟩
        · rw [espu, ← A.abi.outLength]; exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      have Sv : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨In.ofInputs Iv need hb rfl, espv, ?_, ?_⟩
        · rw [espv]
          have D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          rw [← A.abi.outLength]; exact D
        · rw [espv]
          have D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      have Ns := scratch_bytes Os (by have := A.abi.lengths.2; omega_using []) (Is.apart 2 (by decide))
      have Nt := scratch_bytes Ov (by have := A.abi.lengths.2; omega_using []) (Iv.apart 2 (by decide))
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv, NN⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (body_ok Su.1) E2
          obtain ⟨_, Ktv⟩ := wp_result (body_ok Sv.1) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.pair Sv).agree.rf.1 _ (by decide))
          have T3 := (Crt.restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem constantTime : ConstantTime isa (Proof.Rsa.privateCrtContract abi 96).pre
    (Proof.Rsa.privateCrtContract abi 96).pub CrtRt.code := by
  intro s t tr ur sf tf S T H E F
  have Args := Crt.arguments H
  exact operation_trace (topABI_of S) (topABI_of T) Args.2 Args.1 (Crt.modulusBytes H) E F

/-- Disjoint minimum-length buffers with a runtime-rejected zero modulus. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 1
    else if a = 0x20025 then 80
    else if a = 0x20028 then 1
    else if a = 0x2002d then 96
    else if a = 0x20030 then 1
    else if a = 0x20035 then 112
    else if a = 0x20038 then 1
    else if a = 0x2003d then 128
    else if a = 0x20040 then 1
    else if a = 0x20045 then 144
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 64⟩, ⟨16384, 1⟩, ⟨20480, 1⟩, ⟨24576, 1⟩, ⟨28672, 1⟩, ⟨32768, 1⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 72⟩]

theorem satisfiable : ∃ s, (Proof.Rsa.privateCrtContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 24576 := by decide
  have a11 : arg satState 11 = 1 := by decide
  have a12 : arg satState 12 = 28672 := by decide
  have a13 : arg satState 13 = 1 := by decide
  have a14 : arg satState 14 = 32768 := by decide
  have a15 : arg satState 15 = 1 := by decide
  have a16 : arg satState 16 = 36864 := by decide
  have a17 : arg satState 17 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, satState, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using satState

theorem verified : Verified target CrtRt.code (Proof.Rsa.privateCrtContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Bignum.X86.CrtRt
