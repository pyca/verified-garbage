module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.AttemptTop
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
import VerifiedGarbage.Proof.Ffdh.X86.Cached.MetaCut
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.AttemptTop
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.CombCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.MetaCut
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.RelCTChain
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.ContextRows
meta import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-!
# `vg_ffdh_generate_key_cached` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status. The context is the
domain's (`generationPrecompute`), so runs with the same domain read the same
public width from it: the cut at that width (`metaCut_trace`) and the comb
(`comb_trace`) are related with its values, and the rest is
`vg_ffdh_generate_key`'s.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate

/-! ## The taint checks -/

theorem metaHead_check : ACheck (.block metaHead) := by dsimp only [ACheck]; taint_decide
theorem metaLoop_check : ACheck (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) := by
  dsimp only [ACheck]; taint_decide
theorem metaTail_check : ACheck (.block [.alu .sub .eax (.imm 1), .store (sc Impl.Ffdh.X86.tOff) .eax]) := by
  dsimp only [ACheck]; taint_decide
theorem pSetup_check : ACheck Impl.Ffdh.X86.pSetup := by dsimp only [ACheck]; taint_decide
theorem loadG_check : ACheck (load (.slot .wide 10) (one .wide) 4 5) := by dsimp only [ACheck]; taint_decide
theorem cutLoad_check : ACheck (.seq Impl.Ffdh.X86.GenerateKey.cut (.seq (load (.slot .wide 13) (one .wide) 0 1)
    (.block []))) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Generate.args)) (.block [])).isSome = true := by
  taint_decide

/-! ## The cut at the context's width -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run the cut starts from, with the context's width `bits`. -/
abbrev MW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (bits : Nat) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ CtxRd base bytes len args u ∧ w32 u.mem (ctxAddr args) 0 = bits ∧
    w32 u.mem (ctxAddr args) 8 = (bits + 7) / 8 ∧ args 3 = BitVec.ofNat 32 len

theorem metaCut_trace {bits : Nat} (hb1 : 1 ≤ bits) (hb : bits ≤ 8 * len) :
    RelCT isa (Both (MW Ex base bytes len args sp bits)) Generate.metaCut fun _ _ => True := by
  have hb8 : 1 ≤ bits + 8 - 8 * ((bits + 7) / 8) ∧ bits + 8 - 8 * ((bits + 7) / 8) ≤ 8 := by omega
  generalize hN : bits + 8 - 8 * ((bits + 7) / 8) = N at hb8
  unfold Generate.metaCut
  refine VG.RelCT.seq (taint_both (F := fun u => Run Ex base bytes len args sp u ∧
      u.gpr .edx = BitVec.ofNat 32 (N - 0)) (fun _ _ M₁ M₂ => M₁.1.agree M₂.1) _ metaHead_check fun x M =>
    WP.mono (metaHead_ok M.1.1 M.2.1 M.2.2.2.2 hb1 hb M.2.2.1 M.2.2.2.1) fun u ⟨S, _, _, e, _⟩ =>
      ⟨run_step M.1 S, by rw [e, hN, Nat.sub_zero]⟩) ?_
  refine VG.RelCT.seq (relCT_countLoop (N := N) (I := fun j u => Run Ex base bytes len args sp u ∧
      u.gpr .edx = BitVec.ofNat 32 (N - j)) (by omega) fun j hj => ?_) ?_
  · refine taint_both (fun _ _ M₁ M₂ => M₁.1.agree M₂.1) _ metaLoop_check fun x ⟨R, ed⟩ =>
      wp_addS rfl fun t₁ V₁ _ => wp_subZ rfl fun t₂ V₂ z₂ => WP.block_nil ⟨⟨?_, ?_⟩, ?_⟩
    · have K : Keeps [.eax, .edx] x t₂ := (V₁.keeps.mono (by decide)).widen V₂.keeps
      exact ⟨R.1.regs K (by rw [V₂.mem, V₁.mem]), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩
    · rw [V₂.gpr, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), Nat.sub_sub]
    · rw [z₂, V₁.other _ (by decide), ed, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
      by_cases e : j + 1 = N
      · simp [e, show N - j - 1 = 0 by omega]
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro c
        have := congrArg BitVec.toNat c
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        simp at this; omega
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.1.agree h.2.1) metaTail_check

end

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

/-- The context's width for the domain `D`. -/
abbrev cBits (len : Nat) (D : List Byte) : Nat := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len D)

/-- A run of the body, with the domain `D`, its context and the status `St`. -/
structure KAtC (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : KeyGen.Geo args base bytes len dlen sp u.rd u.wr
  dom : KeyGen.domOf u.mem args dlen = D
  st : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf len D)
    (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf len D) (Spec.Rsa.bytesAt u.mem (byteAddr (args 10)) len)) = St
  rd : CtxRd base bytes len args u
  stk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below sp 96)
  cx : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨byteAddr (args 0), len⟩
  dv : Spec.Ffdh.domainValid len D = true
  vals : CtxVals len args (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (cBits len D) u.mem

theorem KAtC.keep {x u : State} (A : KAtC Ex base bytes len dlen args sp D St x)
    (S : Step Ex base bytes len args x u) (m : u.mem = x.mem) : KAtC Ex base bytes len dlen args sp D St u := by
  refine ⟨run_step A.run S, ?_, by rw [m]; exact A.dom, by rw [m]; exact A.st, A.rd.keep S.keeps, A.stk, A.cx, A.dv,
    by rw [m]; exact A.vals⟩
  rw [S.keeps.2.1, S.keeps.2.2]; exact A.geo

/-- The context's values through a stage. -/
theorem KAtC.vals_step {x u : State} (A : KAtC Ex base bytes len dlen args sp D St x)
    (S : Step Ex base bytes len args x u) :
    CtxVals len args (Spec.Ffdh.domainOf len D).p (Spec.Ffdh.domainOf len D).g (cBits len D) u.mem := by
  have hn : ctxBytes len < 2 ^ 64 := by
    have := A.rd.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega
  have F := S.frame
  rw [A.run.2.2] at F
  exact A.vals.keep F (ctx_frameR A.rd A.stk (fR_fit A.run.1)) hn

/-- A run the front's stages after the first reach. -/
abbrev FW (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop :=
  ∃ x, KAtC Ex base bytes len dlen args sp D St x ∧ Step Ex base bytes len args x u

theorem FW.run {u : State} (W : FW Ex base bytes len dlen args sp D St u) : Run Ex base bytes len args sp u :=
  let ⟨_, A, S⟩ := W
  run_step A.run S

theorem prefix_trace (hD : Spec.Ffdh.domainValid len D = true) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St)) (Prog.chain (KeyGen.prefixWith Generate.metaCut)
      (.block [])) fun _ _ => True := by
  show RelCT isa _ (.seq Impl.Ffdh.X86.pSetup (.seq (load (.slot .wide 10) (one .wide) 4 5) (.seq Generate.metaCut
    (.seq Impl.Ffdh.X86.GenerateKey.cut (.seq (load (.slot .wide 13) (one .wide) 0 1) (.block [])))))) _
  refine VG.RelCT.seq (aRel (F := FW Ex base bytes len dlen args sp D St) (fun _ A => A.run) pSetup_check
    fun x A => ?_) ?_
  · have G := A.geo.dom
    have dl := G.dl
    have fit := G.fit
    have lw := G.lower
    exact WP.mono (pSetup_ok A.run.1 G.e3 (by omega_arith)
      (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega_arith) (by omega_arith)
          rwa [BitVec.add_zero] at this)
      (G.apart.sub_left (Region.sub_prefix (by omega_arith)))) fun u ⟨I, F, _, _, _, _, K⟩ => ⟨x, A, I, F, K⟩
  refine VG.RelCT.seq (aRel (F := FW Ex base bytes len dlen args sp D St) (fun _ W => W.run) loadG_check
    fun u ⟨x, A, S⟩ => ?_) ?_
  · have G := A.geo.dom
    have dl := G.dl
    have lw := G.lower
    exact WP.mono (loadComp_ok S.inp (G.keep ⟨rfl, rfl⟩ S.keeps) (k := 1) (j := 10) (by decide) (by omega_arith)
      (by decide)) fun t ⟨_, O, K⟩ => ⟨x, A, S.trans (Step.slot S.inp (by decide) O K)⟩
  refine VG.RelCT.seq (relCT_both (F := Run Ex base bytes len args sp)
    ((metaCut_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)
      (bits := cBits len D) ?_ ?_).mono (fun _ _ h => ?_) fun _ _ h => h) fun u M => ?_) ?_
  · exact (VG.Proof.Ffdh.ContextRows.genBits_facts hD).1
  · exact (VG.Proof.Ffdh.ContextRows.genBits_facts hD).2
  · obtain ⟨⟨x₁, A₁, S₁⟩, ⟨x₂, A₂, S₂⟩⟩ := h
    exact ⟨⟨run_step A₁.run S₁, A₁.rd.keep S₁.keeps, (A₁.vals_step S₁).w0, (A₁.vals_step S₁).w8, A₁.geo.dom.e3⟩,
      ⟨run_step A₂.run S₂, A₂.rd.keep S₂.keeps, (A₂.vals_step S₂).w0, (A₂.vals_step S₂).w8, A₂.geo.dom.e3⟩⟩
  · obtain ⟨x, A, S⟩ := M
    have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
    exact WP.mono (metaCut_ok S.inp (A.rd.keep S.keeps) A.geo.dom.e3 bf.1 bf.2 (A.vals_step S).w0
      (A.vals_step S).w8) fun t ⟨St, _⟩ => run_step (run_step A.run S) St
  exact aEnd (fun _ R => R) cutLoad_check

end

end VG.Proof.Ffdh.X86.Cached
