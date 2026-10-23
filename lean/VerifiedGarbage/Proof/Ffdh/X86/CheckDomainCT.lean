module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Ffdh.X86.Stages

/-!
# `vg_ffdh_check_domain` on i686 in time that depends on the domain only

The contract releases the domain: runs from the same arguments and domain
leak the same traces. Their bodies, narrowed to the working space
(`narrow_body`), run from states with the same domain (`DomAt`), and each
branch tests a condition on it (a `Gate`): that p is a valid modulus, that
g is out of range, whether there is a q, whether q is out of range, whether
q does not divide `p − 1`. Every piece between them is checked by the taint
analysis, but for the calls of a multiplication and the windowed powers
(`powP_trace`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckDomain

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)
open VG.Impl.Ffdh.X86.CheckDomain (subgroup divides withQ checked)

/-! ## The taint checks -/

theorem front_check : ACheck (.seq (.block PublicFn.modulusArgs) (.block modulusCheck)) := by
  dsimp only [ACheck]; taint_decide
theorem checkedFront_check : ACheck (Prog.chain checkedFront (.block [])) := by dsimp only [ACheck]; taint_decide
theorem qTest_check : ACheck (.block Impl.Ffdh.X86.qTest) := by dsimp only [ACheck]; taint_decide
theorem ret0_check : ACheck (ret 0) := by dsimp only [ACheck]; taint_decide
theorem ret1_check : ACheck (ret 1) := by dsimp only [ACheck]; taint_decide
theorem withQFront_check : ACheck (Prog.chain withQFront (.block [])) := by dsimp only [ACheck]; taint_decide
theorem dividesHead_check : ACheck (copy (.slot .wide 11) (.slot .wide 0) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem dividesCopy_check : ACheck (copy (.slot .wide 15) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem dividesTail_check : ACheck (Prog.chain [zero (.slot .wide 17) (one .wide),
    equal (.slot .wide 6) (.slot .wide 17) (one .wide), testMask] (.block [])) := by dsimp only [ACheck]; taint_decide
theorem mul653_check : MulCheck .wide 6 5 3 := by dsimp only [MulCheck]; taint_decide
theorem copy10_check : ACheck (copy (.slot .wide 10) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem copy11_check : ACheck (copy (.slot .wide 11) (.slot .wide 8) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem eqStatus_check : ACheck (Impl.Ffdh.X86.eqStatus 6 3) := by dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckDomain.args)) (.block [])).isSome =
      true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte}

/-- A run of the body, with the domain `D`. -/
structure DomAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (D : List Byte) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : DomGeo args base bytes len dlen u.rd u.wr
  hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  dom : domBytes u.mem args dlen = D

theorem DomAt.step {u v : State} (A : DomAt Ex base bytes len dlen args sp D u)
    (S : Step Ex base bytes len args u v) : DomAt Ex base bytes len dlen args sp D v := by
  refine ⟨⟨S.inp, A.run.2.1.keep S.keeps, S.esp.trans A.run.2.2⟩, A.geo.keep ⟨rfl, rfl⟩ S.keeps, A.hb40, ?_⟩
  show Spec.Rsa.bytesAt v.mem (byteAddr (args 2)) dlen = D
  rw [dom_keep A.run.1 A.geo (by rw [A.run.2.2]; exact A.hb40) S.frame]
  exact A.dom

/-- p, g and q, of the domain `D`. -/
abbrev pD (len : Nat) (D : List Byte) : Nat := (Spec.Ffdh.domainOf len D).p
abbrev gD (len : Nat) (D : List Byte) : Nat := (Spec.Ffdh.domainOf len D).g
abbrev qD (len : Nat) (D : List Byte) : Nat := ((Spec.Ffdh.domainOf len D).q).getD 0

theorem DomAt.comp0 {u : State} (A : DomAt Ex base bytes len dlen args sp D u) :
    comp u.mem args len 0 = pD len D := by
  have := A.geo.dl
  rw [comp_p u.mem args (dlen := dlen) (by omega)]
  exact congrArg (fun d => (Spec.Ffdh.domainOf len d).p) A.dom

theorem DomAt.comp1 {u : State} (A : DomAt Ex base bytes len dlen args sp D u) :
    comp u.mem args len 1 = gD len D := by
  have := A.geo.dl
  rw [comp_g u.mem args (dlen := dlen) (by omega)]
  exact congrArg (fun d => (Spec.Ffdh.domainOf len d).g) A.dom

theorem DomAt.comp2 {u : State} (A : DomAt Ex base bytes len dlen args sp D u) (h3 : dlen = 3 * len) :
    comp u.mem args len 2 = qD len D := by
  have hq := comp_q (len := len) u.mem args
  have hD : Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) (3 * len) = D := by rw [← h3]; exact A.dom
  rw [hD] at hq
  simp only [qD, hq, Option.getD_some]

/-- Past `bodyFront`. -/
def B1 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧ Gate u (Spec.Rsa.modulusValid (pD len D) len = true)

/-- Past `checkedFront`. -/
def C1 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧ Gate u (¬ (1 < gD len D ∧ gD len D < pD len D - 1)) ∧
    sv u.mem base len .wide 9 = pD len D ∧ sv u.mem base len .wide 10 = gD len D ∧
    sv u.mem base len .wide 15 = pD len D - 1

/-- Past `qTest`. -/
def QT (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧ sv u.mem base len .wide 9 = pD len D ∧
    sv u.mem base len .wide 10 = gD len D ∧ sv u.mem base len .wide 15 = pD len D - 1 ∧ Gate u (dlen = 2 * len)

/-- Past `withQFront`. -/
def W1 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧
    Gate u (¬ (qD len D % 2 = 1 ∧ 2 < qD len D ∧ qD len D < pD len D - 1)) ∧
    sv u.mem base len .wide 11 = qD len D ∧ sv u.mem base len .wide 15 = pD len D - 1

theorem subgroup_trace :
    RelCT isa (Both (Run Ex base bytes len args sp)) subgroup fun _ _ => True :=
  VG.RelCT.seq (powP_trace (b := 10) (e := 11) (by decide) (by decide) (by decide) (by decide) copy10_check
    copy11_check) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) eqStatus_check)

theorem dividesFront_trace :
    RelCT isa (Both (Run Ex base bytes len args sp)) (Prog.chain dividesFront (.block [])) fun _ _ => True := by
  show RelCT isa _ (.seq (copy (.slot .wide 11) (.slot .wide 0) (one .wide)) (.seq (prepare .wide)
    (.seq (copy (.slot .wide 15) (.slot .wide 5) (one .wide)) (.seq (CrtRt.mul .wide 6 5 3)
      (Prog.chain [zero (.slot .wide 17) (one .wide), equal (.slot .wide 6) (.slot .wide 17) (one .wide), testMask]
        (.block [])))))) _
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ dividesHead_check fun _ R =>
    copyDown_run (j := 11) (d := 0) (by decide) (by decide) (by decide) R) ?_
  refine VG.RelCT.seq (prepare_relCT .wide) ?_
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ dividesCopy_check fun _ W =>
    copyDown_wst (j := 15) (d := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) W) ?_
  refine VG.RelCT.seq (mul_wst_relCT0 (o := 6) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) mul653_check (ks := [3, 4]) (ks' := []) (by decide) (by decide) (by decide)) ?_
  exact RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) dividesTail_check

theorem divides_relCT :
    RelCT isa (Both fun u => W1 Ex base bytes len dlen args sp D u ∧
      ¬ ¬ (qD len D % 2 = 1 ∧ 2 < qD len D ∧ qD len D < pD len D - 1)) divides fun _ _ => True := by
  rw [divides_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (runRel (F := fun u => Run Ex base bytes len args sp u ∧
      Gate u (¬ (pD len D - 1) % qD len D = 0)) (fun _ h => h.1.1.run) dividesFront_trace fun x h => ?_) ?_
  · obtain ⟨⟨A, _, h11, h15⟩, c⟩ := h
    have c := Classical.not_not.mp c
    exact WP.mono (dividesFront_ok A.run.1 h11 h15 c.1 c.2.1) fun u ⟨S, G, _⟩ => ⟨(A.step S).run, G⟩
  · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1) ret0_check)
      (subgroup_trace.mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1⟩) fun _ _ h => h)

theorem withQ_relCT :
    RelCT isa (Both fun u => QT Ex base bytes len dlen args sp D u ∧ ¬ dlen = 2 * len) withQ fun _ _ => True := by
  rw [withQ_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (F := W1 Ex base bytes len dlen args sp D) (fun _ h => h.1.1.run) withQFront_check
    fun x h => ?_) ?_
  · obtain ⟨⟨A, _, _, h15, _⟩, n2⟩ := h
    have h3 : dlen = 3 * len := by have := A.geo.dl; omega
    have G3 : DomGeo args base bytes len (3 * len) x.rd x.wr := h3 ▸ A.geo
    refine WP.mono (withQFront_ok A.run.1 G3 h15) fun u ⟨S, Gt, q11, kk⟩ => ⟨A.step S, ?_, ?_, ?_⟩
    · rw [A.comp2 h3] at Gt; exact Gt
    · rw [q11, A.comp2 h3]
    · rw [kk 15 (by decide) (by decide) (by decide) (by decide), h15]
  · exact gate_relCT (fun _ h => h.2.1) (aEnd (fun _ h => h.1.1.run) ret0_check) divides_relCT

theorem checked_relCT :
    RelCT isa (Both fun u => B1 Ex base bytes len dlen args sp D u ∧ Spec.Rsa.modulusValid (pD len D) len = true)
      checked fun _ _ => True := by
  rw [checked_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (F := C1 Ex base bytes len dlen args sp D) (fun _ h => h.1.1.run) checkedFront_check
    fun x h => ?_) ?_
  · obtain ⟨⟨A, _⟩, valid⟩ := h
    refine WP.mono (checkedFront_ok A.run.1 A.geo (by rw [A.run.2.2]; exact A.hb40) (by rw [A.comp0]; exact valid))
      fun u ⟨S, Gt, V9, V10, V15⟩ => ⟨A.step S, ?_, ?_, ?_, ?_⟩
    · rw [A.comp0, A.comp1] at Gt; exact Gt
    · rw [V9, A.comp0]
    · rw [V10, A.comp1]
    · rw [V15, A.comp0]
  · refine gate_relCT (fun _ h => h.2.1) (aEnd (fun _ h => h.1.1.run) ret0_check) ?_
    refine VG.RelCT.seq (aRel (F := QT Ex base bytes len dlen args sp D) (fun _ h => h.1.1.run) qTest_check
      fun x h => ?_) ?_
    · obtain ⟨⟨A, _, V9, V10, V15⟩, _⟩ := h
      exact WP.mono (qTest_ok A.run.1 A.geo.e3 A.geo.e12 A.geo.dl) fun u ⟨z, m, K⟩ =>
        ⟨A.step (Step.regs A.run.1 m K), by rw [m]; exact V9, by rw [m]; exact V10, by rw [m]; exact V15,
          Gate.of_eval z decide_eq_true_iff⟩
    · exact gate_relCT (fun _ h => h.2.2.2.2) (aEnd (fun _ h => h.1.1.run) ret1_check) withQ_relCT

theorem body_relCT :
    RelCT isa (Both (DomAt Ex base bytes len dlen args sp D)) Impl.Ffdh.X86.CheckDomain.body fun _ _ => True := by
  unfold Impl.Ffdh.X86.CheckDomain.body
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (aRel (F := B1 Ex base bytes len dlen args sp D) (fun _ A => A.run) front_check
    fun x A => WP.mono (bodyFront_ok A.run.1 A.geo) fun v ⟨S, _, G⟩ => ⟨A.step S, by rw [A.comp0] at G; exact G⟩) ?_
  exact gate_relCT (fun _ h => h.2) checked_relCT (aEnd (fun _ h => h.1.1.run) ret0_check)

end

/-! ## Against the contract -/

theorem pub_facts {s t : State} (H : (Spec.Ffdh.checkDomainContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 5, arg s i = arg t i) ∧ entryDom s = entryDom t := by
  sig_pub [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4⟩ := H
  refine ⟨SP, fun i hi => ?_, (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp L⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) : Rd s (rd ++ wr) [x] :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_left _ hr, hc⟩

/-- The narrowed state the body runs from: a run with the domain at entry. -/
theorem domAt_of {s f : State} (A : CheckDomainABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.CheckDomain.args s f) :
    DomAt (Rd s) (wsBase Impl.Ffdh.X86.CheckDomain.args s) (wsSize Impl.Ffdh.X86.CheckDomain.args s)
      (pLenOf Impl.Ffdh.X86.CheckDomain.args s) (arg s 1).toNat (synth Impl.Ffdh.X86.CheckDomain.args (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s)
      (narrowed (wsBase Impl.Ffdh.X86.CheckDomain.args s) (wsSize Impl.Ffdh.X86.CheckDomain.args s) f) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.CheckDomain.args s, wsSize Impl.Ffdh.X86.CheckDomain.args s⟩
  obtain ⟨G, hb⟩ := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  exact ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A), Bf.2.1⟩, G, hb, frame_dom A Bf.2.2.2.2⟩

theorem constantTime : ConstantTime isa (Spec.Ffdh.checkDomainContract abi stack).pre
    (Spec.Ffdh.checkDomainContract abi stack).pub Impl.Ffdh.X86.CheckDomain.code := by
  intro s t tr ur sf tf S T H E F
  have A := checkDomainABI_of S
  have B := checkDomainABI_of T
  obtain ⟨SP, args, dom⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.CheckDomain.args s = wsBase Impl.Ffdh.X86.CheckDomain.args t := by
    show (arg s 3).setWidth 64 = (arg t 3).setWidth 64
    rw [args 3 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.CheckDomain.args s = wsSize Impl.Ffdh.X86.CheckDomain.args t := by
    show (arg s 4).toNat * 8 = (arg t 4).toNat * 8
    rw [args 4 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.CheckDomain.args s = pLenOf Impl.Ffdh.X86.CheckDomain.args t := by
    show (arg s 2).toNat = (arg t 2).toNat
    rw [args 2 (by decide)]
  have hsy : synth Impl.Ffdh.X86.CheckDomain.args (arg t) = synth Impl.Ffdh.X86.CheckDomain.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 0).setWidth 64) (arg t 1).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 0).setWidth 64) (arg s 1).toNat
    rw [args 0 (by decide), args 1 (by decide)]
  have hl : (arg t 1).toNat = (arg s 1).toNat := by rw [args 1 (by decide)]
  have hx : ∀ {x : State}, CheckDomainABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _
    rw [X.rd]; exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body hws hwz (fun f Bf => ⟨_, body_ok (domAt_of A Bf).run.1 (domAt_of A Bf).geo
        (by rw [(domAt_of A Bf).run.2.2]; exact (domAt_of A Bf).hb40)⟩)
      (fun g Bg => ⟨_, body_ok (domAt_of B Bg).run.1 (domAt_of B Bg).geo
        (by rw [(domAt_of B Bg).run.2.2]; exact (domAt_of B Bg).hb40)⟩)
      (fun f g Bf Bg => ⟨domAt_of A Bf, ?_⟩) body_relCT) E F
  have D₂ := domAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl, ← SP, ← dom] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.CheckDomain
