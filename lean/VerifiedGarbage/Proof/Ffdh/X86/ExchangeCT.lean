module

public import VerifiedGarbage.Proof.Ffdh.X86.ExchangeTop
meta import VerifiedGarbage.Proof.Ffdh.X86.ExchangeTop
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT

/-!
# `vg_ffdh_exchange` on i686 in constant time

The body has no branch: its runs from the same arguments leak the same
traces, whatever the domain, x and y (`body_relCT`): the setup and the
loads, and the mask and the output after the power, are checked by the
taint analysis, the power by private CRT's windowed power.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Exchange

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)
open VG.Impl.Ffdh.X86 (argsFrame)

/-! ## The taint checks -/

theorem pSetup_check : ACheck Impl.Ffdh.X86.pSetup := by dsimp only [ACheck]; taint_decide
theorem loads_check : ACheck (Prog.chain [load (.slot .wide 5) (one .wide) 8 9,
    load (.slot .wide 8) (one .wide) 10 11] (.block [])) := by dsimp only [ACheck]; taint_decide
theorem tail_check : ACheck exTail := by dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Exchange.args)) (.block [])).isSome =
      true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen xl : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run of the body. -/
structure ExAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen xl : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  dom : DomGeo args base bytes len dlen u.rd u.wr
  y : YGeo args base bytes len u.rd u.wr
  x : XGeo args base bytes len xl u.rd u.wr
  out : OutGeo args base bytes len u.wr
  hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below sp 40)
  hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 40)

/-- The body up to the power leaks the same traces: p and its copies by the taint analysis, p's
context by `ctxP_relCT`. -/
theorem front_trace :
    RelCT isa (Both (ExAt Ex base bytes len dlen xl args sp)) (Prog.chain exFront (.block [])) fun _ _ => True := by
  show RelCT isa _ (.seq Impl.Ffdh.X86.pSetup (.seq Impl.Ffdh.X86.ctxP
    (Prog.chain [load (.slot .wide 5) (one .wide) 8 9, load (.slot .wide 8) (one .wide) 10 11] (.block [])))) _
  refine VG.RelCT.seq (aRel (F := Run Ex base bytes len args sp) (fun _ A => A.run) pSetup_check fun x A => ?_) ?_
  · have G := A.dom
    have dl := G.dl
    have fit := G.fit
    refine WP.mono (pSetup_ok A.run.1 G.e3 (by omega)
      (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
          rwa [BitVec.add_zero] at this)
      (G.apart.sub_left (Region.sub_prefix (by omega))))
      fun u ⟨I, F, _, _, _, _, K⟩ => run_step A.run ⟨I, F, K⟩
  · refine VG.RelCT.seq ctxP_relCT ?_
    exact RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) loads_check

theorem body_relCT :
    RelCT isa (Both (ExAt Ex base bytes len dlen xl args sp)) Impl.Ffdh.X86.Exchange.body fun _ _ => True := by
  rw [body_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both (F := WSt Ex base bytes len args sp .wide [3, 4] 0)
    front_trace fun x A => ?_) ?_
  · refine WP.mono (front_ok A.run.1 A.dom A.y A.x (by rw [A.run.2.2]; exact A.hy40)
      (by rw [A.run.2.2]; exact A.hx40)) fun u ⟨S, C, one, R2, _⟩ =>
      ⟨_, C, fun j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero _), A.run.2.1.keep S.keeps,
        S.esp.trans A.run.2.2⟩
    have hM := safeM_gt (comp x.mem args len 0)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [one]; exact hM
    · rw [R2]; exact Nat.mod_lt _ (by omega)
  · exact VG.RelCT.seq (windowPower_relCT (winChecks .wide))
      (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) tail_check)

end

/-! ## Against the contract -/

theorem pub_facts {s t : State} (H : (Spec.Ffdh.exchangeContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 11, arg s i = arg t i := by
  sig_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, _, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := H
  refine ⟨SP, fun i hi => ?_⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) :
    Rd s (rd ++ wr) [x, outR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, ⟨r'', hr'', hc''⟩, _⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩, ⟨r'', List.mem_append_left _ hr'', hc''⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.contains_self _ _⟩⟩

/-- The narrowed state the body runs from, the output writable. -/
theorem exAt_of {s f : State} (A : ExchangeABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.Exchange.args s f) :
    ExAt (Rd s) (wsBase Impl.Ffdh.X86.Exchange.args s) (wsSize Impl.Ffdh.X86.Exchange.args s)
      (pLenOf Impl.Ffdh.X86.Exchange.args s) (arg s 3).toNat (arg s 6).toNat
      (synth Impl.Ffdh.X86.Exchange.args (arg s)) (s.gpr .esp - BitVec.ofNat 32 argsFrame)
      (narrowed (wsBase Impl.Ffdh.X86.Exchange.args s) (wsSize Impl.Ffdh.X86.Exchange.args s) f [outR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩
  obtain ⟨G, Y, X, O, hy, hxx⟩ := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  exact ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [outR s]) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact A.belowOut.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide)), Bf.2.1⟩,
    G, Y, X, O, hy, hxx⟩

theorem constantTime : ConstantTime isa (Spec.Ffdh.exchangeContract abi stack).pre
    (Spec.Ffdh.exchangeContract abi stack).pub Impl.Ffdh.X86.Exchange.code := by
  intro s t tr ur sf tf S T H E F
  have A := exchangeABI_of S
  have B := exchangeABI_of T
  obtain ⟨SP, args⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.Exchange.args s = wsBase Impl.Ffdh.X86.Exchange.args t := by
    show (arg s 9).setWidth 64 = (arg t 9).setWidth 64
    rw [args 9 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.Exchange.args s = wsSize Impl.Ffdh.X86.Exchange.args t := by
    show (arg s 10).toNat * 8 = (arg t 10).toNat * 8
    rw [args 10 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.Exchange.args s = pLenOf Impl.Ffdh.X86.Exchange.args t := by
    show (arg s 4).toNat = (arg t 4).toNat
    rw [args 4 (by decide)]
  have hsy : synth Impl.Ffdh.X86.Exchange.args (arg t) = synth Impl.Ffdh.X86.Exchange.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hout : outR t = outR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        InRegions (rd ++ wr) ((arg t 7).setWidth 64) (arg t 8).toNat ∧
        InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        InRegions (rd ++ wr) ((arg s 7).setWidth 64) (arg s 8).toNat ∧
        InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 5 (by decide),
      args 6 (by decide), args 7 (by decide), args 8 (by decide)]
  have hl3 : (arg t 3).toNat = (arg s 3).toNat := by rw [args 3 (by decide)]
  have hl6 : (arg t 6).toNat = (arg s 6).toNat := by rw [args 6 (by decide)]
  have hx : ∀ {x : State}, ExchangeABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : ExchangeABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.Exchange.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.Exchange.body
        (narrowed (wsBase Impl.Ffdh.X86.Exchange.args x) (wsSize Impl.Ffdh.X86.Exchange.args x) f [outR x]) F :=
    fun X Bf => ⟨_, body_ok (exAt_of X Bf).run.1 (exAt_of X Bf).dom (exAt_of X Bf).y (exAt_of X Bf).x
      (exAt_of X Bf).out (by rw [(exAt_of X Bf).run.2.2]; exact (exAt_of X Bf).hy40)
      (by rw [(exAt_of X Bf).run.2.2]; exact (exAt_of X Bf).hx40)⟩
  have ho : ∀ {x f : State}, ExchangeABI x → BodyAt (Rd x) Impl.Ffdh.X86.Exchange.args x f → outR x ∈ f.wr :=
    fun X Bf => by rw [Bf.2.2.2.1, X.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [outR s]) hws hwz (fun f Bf => hw A Bf) (fun g Bg => by rw [← hout]; exact hw B Bg)
      (fun f g Bf Bg => ⟨exAt_of A Bf, ?_⟩) body_relCT
      (fun f Bf r hr => by rw [List.mem_singleton.mp hr]; exact ho A Bf)
      (fun g Bg r hr => by rw [List.mem_singleton.mp hr, ← hout]; exact ho B Bg)) E F
  have D₂ := exAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl3, hl6, ← SP, hout] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.Exchange
