module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicTop
public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicTop
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_check_public` on i686 in time that depends on the domain and y only

The contract releases the domain and y: runs from the same arguments, domain
and y leak the same traces. Their bodies, narrowed to the working space, run
from states with the same domain and y (`PubAt`), and each branch tests a
condition on them: that y is out of range (against `pm1 p`, what `pSetup`
leaves for any p), whether there is a q.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPublic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Ffdh.X86.CheckDomain (DomAt pD ret0_check ret1_check qTest_check)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem front_check : ACheck (Prog.chain pubFront (.block [])) := by dsimp only [ACheck]; taint_decide
theorem loadQ_check : ACheck (load (.slot .wide 11) (one .wide) 6 7) := by dsimp only [ACheck]; taint_decide
theorem copy12_check : ACheck (copy (.slot .wide 12) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckPublic.args)) (.block [])).isSome =
      true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D Yb : List Byte}

/-- A run of the body, with the domain `D` and y's bytes `Yb`. -/
structure PubAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (D Yb : List Byte) (u : State) : Prop where
  dom : DomAt Ex base bytes len dlen args sp D u
  geo : YGeo args base bytes len u.rd u.wr
  hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below sp 40)
  y : Spec.Rsa.bytesAt u.mem (byteAddr (args 8)) len = Yb

theorem PubAt.yv {u : State} (A : PubAt Ex base bytes len dlen args sp D Yb u) :
    yv u.mem args len = Spec.Rsa.os2ip Yb := congrArg _ A.y

/-- After `pubFront`. -/
def F1 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D Yb : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧
    Gate u (¬ (Spec.Rsa.os2ip Yb < pm1 len (pD len D) ∧ 1 < Spec.Rsa.os2ip Yb))

/-- After `qTest`. -/
def Q1 (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (u : State) : Prop :=
  DomAt Ex base bytes len dlen args sp D u ∧ Gate u (dlen = 2 * len)

theorem pubQ_trace :
    RelCT isa (Both fun u => Q1 Ex base bytes len dlen args sp D u ∧ ¬ dlen = 2 * len) pubQ fun _ _ => True := by
  refine VG.RelCT.seq (aRel (F := Run Ex base bytes len args sp) (fun _ h => h.1.1.run) loadQ_check
    fun x h => ?_) ?_
  · obtain ⟨⟨A, _⟩, n2⟩ := h
    have h3 : dlen = 3 * len := by have := A.geo.dl; omega
    exact WP.mono (loadComp_ok A.run.1 A.geo (k := 2) (j := 11) (by decide) (by omega) (by decide))
      fun u ⟨_, O, K⟩ => ⟨(Step.slot A.run.1 (by decide) O K).inp, A.run.2.1.keep K, (K.1 _ (by decide)).trans A.run.2.2⟩
  · exact VG.RelCT.seq (powP_trace (b := 12) (e := 11) (by decide) (by decide) (by decide) (by decide) copy12_check
      VG.Proof.Ffdh.X86.CheckDomain.copy11_check)
      (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) VG.Proof.Ffdh.X86.CheckDomain.eqStatus_check)

theorem body_relCT :
    RelCT isa (Both (PubAt Ex base bytes len dlen args sp D Yb)) Impl.Ffdh.X86.CheckPublic.body fun _ _ => True := by
  rw [body_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (F := F1 Ex base bytes len dlen args sp D Yb) (fun _ A => A.dom.run) front_check
    fun x A => ?_) ?_
  · refine WP.mono (front_ok A.dom.run.1 A.dom.geo A.geo (by rw [A.dom.run.2.2]; exact A.hy40))
      fun u ⟨S, G, _, _⟩ => ⟨A.dom.step S, ?_⟩
    rw [A.dom.comp0, A.yv] at G
    exact G
  · refine gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.run) ret0_check) ?_
    refine VG.RelCT.seq (aRel (F := Q1 Ex base bytes len dlen args sp D) (fun _ h => h.1.1.run) qTest_check
      fun x h => ?_) ?_
    · obtain ⟨⟨A, _⟩, _⟩ := h
      exact WP.mono (qTest_ok A.run.1 A.geo.e3 A.geo.e12 A.geo.dl) fun u ⟨z, m, K⟩ =>
        ⟨A.step (Step.regs A.run.1 m K), Gate.of_eval z decide_eq_true_iff⟩
    · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.run) ret1_check) pubQ_trace

end

/-! ## Against the contract -/

theorem pub_facts {s t : State} (H : (Spec.Ffdh.checkPublicContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 7, arg s i = arg t i) ∧ entryDom s = entryDom t ∧ entryY s = entryY t := by
  sig_pub [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a1])
  refine ⟨SP, fun i hi => ?_, inj L₁, inj L₂⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) : Rd s (rd ++ wr) [x] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩⟩

/-- The narrowed state the body runs from: a run with the domain and y at entry. -/
theorem pubAt_of {s f : State} (A : CheckPublicABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.CheckPublic.args s f) :
    PubAt (Rd s) (wsBase Impl.Ffdh.X86.CheckPublic.args s) (wsSize Impl.Ffdh.X86.CheckPublic.args s)
      (pLenOf Impl.Ffdh.X86.CheckPublic.args s) (arg s 1).toNat (synth Impl.Ffdh.X86.CheckPublic.args (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s) (entryY s)
      (narrowed (wsBase Impl.Ffdh.X86.CheckPublic.args s) (wsSize Impl.Ffdh.X86.CheckPublic.args s) f) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩
  obtain ⟨G, Y, hb, hy⟩ := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPublic.args s := A.yLen
  refine ⟨⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A), Bf.2.1⟩, G, hb,
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega)⟩, Y, hy, ?_⟩
  show Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _ = Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat
  rw [← yR]
  exact frame_keep A Bf.2.2.2.2 A.yScratch A.belowY (by have := A.yBound; omega)

theorem constantTime : ConstantTime isa (Spec.Ffdh.checkPublicContract abi stack).pre
    (Spec.Ffdh.checkPublicContract abi stack).pub Impl.Ffdh.X86.CheckPublic.code := by
  intro s t tr ur sf tf S T H E F
  have A := checkPublicABI_of S
  have B := checkPublicABI_of T
  obtain ⟨SP, args, dom, yb⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.CheckPublic.args s = wsBase Impl.Ffdh.X86.CheckPublic.args t := by
    show (arg s 5).setWidth 64 = (arg t 5).setWidth 64
    rw [args 5 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.CheckPublic.args s = wsSize Impl.Ffdh.X86.CheckPublic.args t := by
    show (arg s 6).toNat * 8 = (arg t 6).toNat * 8
    rw [args 6 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.CheckPublic.args s = pLenOf Impl.Ffdh.X86.CheckPublic.args t := by
    show (arg s 2).toNat = (arg t 2).toNat
    rw [args 2 (by decide)]
  have hsy : synth Impl.Ffdh.X86.CheckPublic.args (arg t) = synth Impl.Ffdh.X86.CheckPublic.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 0).setWidth 64) (arg t 1).toNat ∧
        InRegions (rd ++ wr) ((arg t 3).setWidth 64) (arg t 4).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 0).setWidth 64) (arg s 1).toNat ∧
        InRegions (rd ++ wr) ((arg s 3).setWidth 64) (arg s 4).toNat
    rw [args 0 (by decide), args 1 (by decide), args 3 (by decide), args 4 (by decide)]
  have hl : (arg t 1).toNat = (arg s 1).toNat := by rw [args 1 (by decide)]
  have hx : ∀ {x : State}, CheckPublicABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _
    rw [X.rd]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : CheckPublicABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.CheckPublic.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.CheckPublic.body
        (narrowed (wsBase Impl.Ffdh.X86.CheckPublic.args x) (wsSize Impl.Ffdh.X86.CheckPublic.args x) f) F :=
    fun X Bf => ⟨_, body_ok (pubAt_of X Bf).dom.run.1 (pubAt_of X Bf).dom.geo (pubAt_of X Bf).geo
      (by rw [(pubAt_of X Bf).dom.run.2.2]; exact (pubAt_of X Bf).dom.hb40)
      (by rw [(pubAt_of X Bf).dom.run.2.2]; exact (pubAt_of X Bf).hy40)⟩
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body hws hwz (fun f Bf => hw A Bf) (fun g Bg => hw B Bg)
      (fun f g Bf Bg => ⟨pubAt_of A Bf, ?_⟩) body_relCT) E F
  have D₂ := pubAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl, ← SP, ← dom, ← yb] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.CheckPublic
