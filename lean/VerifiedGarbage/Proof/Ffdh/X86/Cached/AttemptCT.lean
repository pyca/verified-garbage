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


/-- The prefix's run, with the cut at the context's width. -/
theorem prefixC_ok (hD : Spec.Ffdh.domainValid len D = true) {x : State}
    (A : KAtC Ex base bytes len dlen args sp D St x) :
    WP isa (Prog.chain (KeyGen.prefixWith Generate.metaCut) (.block [])) x
      (KeyGen.PrefW Ex base bytes len dlen args x (Spec.Rsa.os2ip (Spec.Rsa.bytesAt x.mem (byteAddr (args 10)) len) %
        2 ^ cBits len D)) := by
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have lw := A.geo.dom.lower
  have sp' := A.run.2.2
  have wlt : len - VG.Proof.Ffdh.ScalarWidth.width (cBits len D) < len := by
    have := VG.Proof.Ffdh.ScalarWidth.width_pos (cBits len D); omega
  rw [← cut_vetted bf.2 (by omega)]
  exact KeyGen.prefixWith_ok A.run.1 A.geo.dom (by rw [sp']; exact A.geo.dom40) (by rw [sp']; exact A.geo.cut)
    A.geo.rWs (by rw [sp']; exact A.geo.r40) A.geo.domX wlt fun w Sw =>
      WP.mono (metaCut_ok Sw.inp (A.rd.keep Sw.keeps) A.geo.dom.e3 bf.1 bf.2 (A.vals_step Sw).w0
        (A.vals_step Sw).w8) fun t ⟨St', k, ld, tt⟩ => ⟨St', k.mono, ld, tt⟩

theorem front_trace (hD : Spec.Ffdh.domainValid len D = true) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St))
      (Prog.chain (KeyGen.mainFrontWith Generate.metaCut) (.block [])) fun _ _ => True := by
  show RelCT isa _ (Prog.chain (KeyGen.prefixWith Generate.metaCut) (.seq Impl.Ffdh.X86.CheckPrivate.bound
    (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := CheckPrivate.RG Ex base bytes len dlen args sp) (prefix_trace hD)
    fun x A => ?_) (VG.RelCT.seq CheckPrivate.bound_relCT (aEnd (fun _ h => h) CheckPrivate.mask_check))
  exact WP.mono (prefixC_ok hD A) fun u P => ⟨⟨P.inp, A.run.2.1.keep P.keeps, (P.keeps.1 _ (by decide)).trans A.run.2.2⟩,
    A.geo.dom.keep ⟨rfl, rfl⟩ P.keeps⟩

/-- A run the tail starts from: the comb's, and the tail's. -/
abbrev TC (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  KeyGen.TP Ex base bytes len dlen args sp u ∧ CS Ex base bytes len args sp (Spec.Ffdh.domainOf len D).p (cBits len D) u

/-- The front's runs: the tail's start, and the gate on the scalar, whether the status is 2. -/
theorem frontC_ok (hD : Spec.Ffdh.domainValid len D = true) (hm : KeyGen.modOk len D) {x : State}
    (A : KAtC Ex base bytes len dlen args sp D St x) :
    WP isa (Prog.chain (KeyGen.mainFrontWith Generate.metaCut) (.block [])) x fun u =>
      TC Ex base bytes len dlen args sp D u ∧ Gate u (St = 2) := by
  have G := A.geo.dom
  have dl := G.dl
  have lw := G.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have sm := (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := cBits len D)
    (Nat.le_trans bf.2 (by have := G.upper; omega_arith))).1
  refine WP.mono (KeyGen.frontWith_ok G (prefixC_ok hD A)) fun u F => ?_
  have sp' := A.run.2.2
  have Fu := F.frame
  rw [sp'] at Fu
  have hn : ctxBytes len < 2 ^ 64 := by
    have := A.rd.afit; have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega
  have Vu := A.vals.keep Fu (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact A.cx
    · exact ctx_frameR A.rd A.stk (fR_fit A.run.1) r hr) hn
  have spu : u.gpr .esp = sp := (F.keeps.1 _ (by decide)).trans sp'
  have pa : comp x.mem args len 0 = (Spec.Ffdh.domainOf len D).p := by rw [comp_p x.mem args h2]; rw [← A.dom]
  have mv : Spec.Rsa.modulusValid (Spec.Ffdh.domainOf len D).p len = true := hm
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  have p1 : 1 < (Spec.Ffdh.domainOf len D).p := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega_arith
  refine ⟨⟨⟨⟨F.inp, A.run.2.1.keep F.keeps, spu⟩, G.keep ⟨rfl, rfl⟩ F.keeps⟩, _, _,
    Nat.mod_lt _ (Nat.two_pow_pos _), F.inp, ⟨A.rd.keep F.keeps, by rw [spu]; exact A.stk, Vu.ents, F.v13, sm⟩,
    by rw [F.v9, pa]; exact safeM_of p1 mv.1.1.1, Vu.w16, A.run.2.1.keep F.keeps, spu⟩, F.gate.congr ?_⟩
  have hp : CheckPrivate.params x.mem args len dlen = Spec.Ffdh.domainOf len D := congrArg (Spec.Ffdh.domainOf len) A.dom
  rw [← A.st, KeyGen.keyStatus_two, hp]
  rfl

theorem main_trace (hD : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both fun x => KAtC Ex base bytes len dlen args sp D St x ∧ KeyGen.modOk len D) Generate.main
      fun _ _ => True := by
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts hD
  have hR0 := VG.Proof.Rsa.FixedBaseComb.rows_pos (bits := cBits len D) (Nat.lt_of_lt_of_le Nat.zero_lt_one bf.1)
  have hR : Spec.Rsa.FixedBaseComb.rows (cBits len D) ≤ 1639 :=
    (VG.Proof.Rsa.FixedBaseComb.rows_small (bits := cBits len D) (Nat.le_trans bf.2 ?_)).1
  rw [show Generate.main = Prog.chain (KeyGen.mainFrontWith Generate.metaCut)
    (.ite .e Impl.Ffdh.X86.GenerateKey.fail (KeyGen.tailWith Generate.comb)) from rfl]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := fun u => TC Ex base bytes len dlen args sp D u ∧ Gate u (St = 2))
    ((front_trace hD).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) fun x ⟨A, hm⟩ => frontC_ok hD hm A) ?_
  refine gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1.1) KeyGen.fail_check) ?_
  · refine KeyGen.tailWith_trace (Ex := Ex) (base := base) (bytes := bytes) (len := len) (dlen := dlen)
      (args := args) (sp := sp) (relCT_both ((comb_trace (P := (Spec.Ffdh.domainOf len D).p) hR0 hR).mono
      (fun _ _ h => ⟨h.1.1.1.2, h.2.1.1.2⟩) fun _ _ h => h) fun x T => ?_)
    obtain ⟨⟨⟨T, G, xx, hx, h, E, hP, hrows, _, _⟩, _⟩, _⟩ := T
    exact WP.mono (combStage_ok h E hP hx hR0 hrows) fun u ⟨S, _, _⟩ => KeyGen.tp_step T S
  · omega


theorem body_trace (hD : Spec.Ffdh.domainValid len D = true) (hl : len ≤ 1024) :
    RelCT isa (Both (KAtC Ex base bytes len dlen args sp D St)) Generate.body fun _ _ => True := by
  show RelCT isa _ (Prog.chain [.block PublicFn.modulusArgs, .block modulusCheck]
    (.ite .e Generate.main (ret 0))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (relCT_both (F := fun u => KAtC Ex base bytes len dlen args sp D St u ∧ Gate u (KeyGen.modOk len D))
    (aEnd (fun _ A => A.run) KeyGen.mod_check) fun x A => ?_) ?_
  · have h := A.run.1
    have G := A.geo.dom
    have fit := G.fit
    have dl := G.dl
    have lw := G.lower
    refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide) (h.arg (i := 2) (by decide))
      (h.arg (i := 3) (by decide))) fun u ⟨P, C, M, K⟩ => ?_)
    have S₁ : Step Ex base bytes len args x u := Step.regs h M K
    have rd : InRegions (u.rd ++ u.wr) (byteAddr (u.gpr .esi)) len := by
      rw [P, K.2.1, K.2.2]
      have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
      rwa [BitVec.add_zero] at this
    refine WP.seq (WP.mono (modulusCheck_ok u (k := len) h.lower' h.upper' (by rw [P]; omega) rd (by rw [C, G.e3]))
      fun v ⟨Z, Mv, Kv⟩ => WP.block_nil ⟨(A.keep S₁ M).keep (Step.regs S₁.inp Mv Kv) Mv, Gate.of_eval Z ?_⟩)
    rw [P, M, ← A.dom, KeyGen.modOk, VG.Proof.Ffdh.domainOf_p x.mem _ (by omega)]
  · exact gate_relCT (fun _ h => h.2) ((main_trace hD hl).mono (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, h.2.1.1, h.2.2⟩)
      fun _ _ h => h) (aEnd (fun _ h => h.1.1.run) KeyGen.ret0_check)

/-- The context's values, as `body_ok` takes them. -/
theorem KAtC.cv {u : State} (A : KAtC Ex base bytes len dlen args sp D St u) :
    CtxVals len args (comp u.mem args len 0) (comp u.mem args len 1)
      (Spec.Ffdh.generationScalarBits (CheckPrivate.params u.mem args len dlen)) u.mem := by
  have dl := A.geo.dom.dl
  have lw := A.geo.dom.lower
  have h2 : 2 * len ≤ dlen := by omega_arith
  rw [comp_p u.mem args h2, comp_g u.mem args h2]
  have hp : CheckPrivate.params u.mem args len dlen = Spec.Ffdh.domainOf len D := congrArg (Spec.Ffdh.domainOf len) A.dom
  rw [hp, show Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) dlen = D from A.dom]
  exact A.vals

end


/-! ## Against the contract -/

section

/-- The status at entry. -/
abbrev status (s : State) : Nat :=
  Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s))
    (Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)) (entryRand s))

theorem pub_facts {s t : State} (H : (Spec.Ffdh.cachedGenerateKeyContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 13, arg s i = arg t i) ∧ entryDom s = entryDom t ∧ status s = status t := by
  sig_pub [Spec.Ffdh.cachedGenerateKeyContract, Spec.Ffdh.cachedGenerateKeySig, Spec.Ffdh.generateKeySig, abi,
    argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a5])
  refine ⟨SP, fun i hi => ?_, inj L₁, List.cons.inj L₂ |>.1⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
    i = 12 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8
  · exact a9
  · exact a10
  · exact a11
  · exact a12

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) :
    Rd s (rd ++ wr) [x, KeyGen.xR s, KeyGen.yR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, _, _, ⟨r'', hr'', hc''⟩⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩,
    ⟨r'', List.mem_append_left _ hr'', hc''⟩⟩

/-- The narrowed state the body runs from, x and y writable. -/
theorem kAt_of {s f : State} (A : CachedABI s) (Bf : BodyAt (Rd s) gArgs s f) :
    KAtC (Rd s) (wsBase gArgs s) (wsSize gArgs s) (pLenOf gArgs s) (arg s 5).toNat (synth gArgs (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s) (status s)
      (narrowed (wsBase gArgs s) (wsSize gArgs s) f [KeyGen.xR s, KeyGen.yR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase gArgs s, wsSize gArgs s⟩
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have rL : (arg s 8).toNat = pLenOf gArgs s := A.randLen
  have D : KeyGen.domOf f.mem (synth gArgs (arg s)) (arg s 5).toNat = entryDom s :=
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega)
  have R : Spec.Rsa.bytesAt f.mem (byteAddr (synth gArgs (arg s) 10)) (pLenOf gArgs s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Bf.2.2.2.2 A.randScratch A.belowRand (by have := A.randBound; omega)
  obtain ⟨CR, cstk, cx⟩ := frame_ctx (f := narrowed (wsBase gArgs s) (wsSize gArgs s) f [KeyGen.xR s, KeyGen.yR s])
    A Bf.2.1 hx
  refine ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [KeyGen.xR s, KeyGen.yR s])
    fun r hr => ?_, Bf.2.1⟩, frame_geo A rfl hx, D, ?_, CR, by rw [← Bf.2.1]; exact cstk, cx, A.valid,
    frame_vals A Bf.2.2.2.2⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.belowX.sub_left sub
    · exact A.belowY.sub_left sub
  · show Spec.Ffdh.keyStatus _ (Spec.Ffdh.vettedScalarOfOctets _ (Spec.Rsa.bytesAt f.mem _ _)) = _
    rw [R]
    rfl


theorem constantTime : ConstantTime isa (Spec.Ffdh.cachedGenerateKeyContract abi stack).pre
    (Spec.Ffdh.cachedGenerateKeyContract abi stack).pub Impl.Ffdh.X86.Cached.Generate.code := by
  intro s t tr ur sf tf S T H E F
  have A := cachedABI_of S
  have B := cachedABI_of T
  obtain ⟨SP, args, dom, st⟩ := pub_facts H
  have hws : wsBase gArgs s = wsBase gArgs t := by
    show (arg s 9).setWidth 64 = (arg t 9).setWidth 64
    rw [args 9 (by decide)]
  have hwz : wsSize gArgs s = wsSize gArgs t := by
    show (arg s 10).toNat * 8 = (arg t 10).toNat * 8
    rw [args 10 (by decide)]
  have hpl : pLenOf gArgs s = pLenOf gArgs t := by
    show (arg s 6).toNat = (arg t 6).toNat
    rw [args 6 (by decide)]
  have hsy : synth gArgs (arg t) = synth gArgs (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hxR : KeyGen.xR t = KeyGen.xR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hyR : KeyGen.yR t = KeyGen.yR s := by
    show (⟨(arg t 2).setWidth 64, (arg t 3).toNat⟩ : Region) = ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    rw [args 2 (by decide), args 3 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 4).setWidth 64) (arg t 5).toNat ∧
        InRegions (rd ++ wr) ((arg t 7).setWidth 64) (arg t 8).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat ∧ InRegions wr ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        InRegions (rd ++ wr) ((arg t 11).setWidth 64) ((arg t 12).toNat * 8)) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 4).setWidth 64) (arg s 5).toNat ∧
        InRegions (rd ++ wr) ((arg s 7).setWidth 64) (arg s 8).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat ∧ InRegions wr ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        InRegions (rd ++ wr) ((arg s 11).setWidth 64) ((arg s 12).toNat * 8)
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide), args 7 (by decide), args 8 (by decide), args 11 (by decide), args 12 (by decide)]
  have hl5 : (arg t 5).toNat = (arg s 5).toNat := by rw [args 5 (by decide)]
  have hx : ∀ {x : State}, CachedABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _ ∧
      InRegions (x.rd ++ _) _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : CachedABI x) (Bf : BodyAt (Rd x) gArgs x f),
      ∃ F, WP isa Impl.Ffdh.X86.Cached.Generate.body
        (narrowed (wsBase gArgs x) (wsSize gArgs x) f [KeyGen.xR x, KeyGen.yR x]) F := fun X Bf => by
    have K := kAt_of X Bf
    have sp' := K.run.2.2
    exact ⟨_, body_ok K.run.1 K.geo.dom (by rw [sp']; exact K.geo.dom40) (by rw [sp']; exact K.geo.cut) K.geo.rWs
      (by rw [sp']; exact K.geo.r40) K.geo.domX (by rw [sp']; exact K.geo.ox) (by rw [sp']; exact K.geo.oy)
      K.geo.e9 K.geo.xy K.rd (by rw [sp']; exact K.stk) K.cx (by rw [K.dom]; exact K.dv) K.cv⟩
  have ho : ∀ {x f : State}, CachedABI x → BodyAt (Rd x) gArgs x f →
      ∀ r ∈ [KeyGen.xR x, KeyGen.yR x], r ∈ f.wr := fun X Bf r hr => by
    rw [Bf.2.2.2.1, X.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [KeyGen.xR s, KeyGen.yR s]) hws hwz (fun f Bf => hw A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact hw B Bg)
      (fun f g Bf Bg => ⟨kAt_of A Bf, ?_⟩) (body_trace A.valid A.pLen.2) (fun f Bf => ho A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact ho B Bg)) E F
  have D₂ := kAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl5, ← SP, hxR, hyR, ← dom, ← st] at D₂
  rw [← hws, ← hwz]
  exact D₂

end

end VG.Proof.Ffdh.X86.Cached
