module

public import VerifiedGarbage.Proof.Ffdh.X86.DeriveTop
meta import VerifiedGarbage.Proof.Ffdh.X86.DeriveTop
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Ffdh.X86.KeyGenCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Ffdh.X86.Derive
meta import VerifiedGarbage.Proof.Ffdh.X86.Derive

/-!
# `vg_ffdh_derive_public` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status: runs with the same ones
leak the same traces. The one branch on x, whether it is an invalid scalar,
is whether the status is 2; the rest, x's power over its public `x_len`
bytes (`CheckPrivate.powTop_trace`) and the masked output, has no branch on
it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv RX RG loadX_ok)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem loads_check : ACheck (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 13) (one .wide) 10 11] (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem fail_check : ACheck Impl.Ffdh.X86.DerivePublic.fail := by dsimp only [ACheck]; taint_decide
theorem rest_check : ACheck (.seq (Impl.Ffdh.X86.rangeMask 6) <| .seq (.block [.store (sc accOff) .ecx]) <|
    .seq (copy (.slot .wide 6) (.slot .wide 19) (one .wide)) <| .seq (Impl.Ffdh.X86.exportTo 0 1)
      (.block [.alu .add .eax (.reg .eax), .mov .ecx (.imm 3), .alu .sub .ecx (.reg .eax), .mov .eax (.reg .ecx)])) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.DerivePublic.args))
      (.block [])).isSome = true := by
  taint_decide

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen xl : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

/-- A run of the body, with the domain `D` and the status `St`. -/
structure DAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen xl : Nat)
    (args : Nat → BitVec 32) (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : DomGeo args base bytes len dlen u.rd u.wr
  hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 40)
  x : XGeo args base bytes len xl u.rd u.wr
  hx40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 40)
  dom : domBytes u.mem args dlen = D
  st : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf len D) (xv u.mem args xl) = St

theorem loads_rg {x : State} (A : DAt Ex base bytes len dlen xl args sp D St x) :
    WP isa (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
      load (.slot .wide 13) (one .wide) 10 11] (.block [])) x (RG Ex base bytes len dlen args sp) := by
  have h := A.run.1
  have G := A.geo
  have dl := G.dl
  have fit := G.fit
  have lw := G.lower
  refine WP.seq (WP.mono (pSetup_ok h G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega))))
    fun u₁ ⟨I₁, F₁, _, _, _, _, K₁⟩ => ?_)
  have S₁ : Step Ex base bytes len args x u₁ := ⟨I₁, F₁, K₁⟩
  refine WP.seq (WP.mono (loadComp_ok I₁ (G.keep ⟨rfl, rfl⟩ K₁) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₂ ⟨_, O₂, K₂⟩ => ?_)
  have S₂ := S₁.trans (Step.slot I₁ (by decide) O₂ K₂)
  refine WP.seq (WP.mono (loadX_ok S₂.inp (A.x.keep ⟨rfl, rfl⟩ S₂.keeps)) fun u₃ ⟨_, O₃, K₃⟩ => WP.block_nil ?_)
  have S₃ := S₂.trans (Step.slot S₂.inp (by decide) O₃ K₃)
  exact ⟨run_step A.run S₃, G.keep ⟨rfl, rfl⟩ S₃.keeps⟩

theorem front_trace :
    RelCT isa (Both (DAt Ex base bytes len dlen xl args sp D St)) (Prog.chain dFront (.block []))
      fun _ _ => True := by
  show RelCT isa _ (Prog.chain [Impl.Ffdh.X86.pSetup, load (.slot .wide 10) (one .wide) 4 5,
    load (.slot .wide 13) (one .wide) 10 11]
    (.seq Impl.Ffdh.X86.CheckPrivate.bound
      (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, Impl.Ffdh.X86.testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (fun _ A => A.run) loads_check fun _ A => loads_rg A) ?_
  exact VG.RelCT.seq CheckPrivate.bound_relCT (aEnd (fun _ h => h) CheckPrivate.mask_check)

/-- The tail: x's power over its `xl` bytes, then the mask, the output and the status by the taint
analysis. -/
theorem tail_trace {P : State → Prop}
    (hP : ∀ x, P x → RX Ex base bytes len xl args sp x ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 40)) :
    RelCT isa (Both P) Impl.Ffdh.X86.DerivePublic.tail fun _ _ => True := by
  by_cases hx : (args 11 = BitVec.ofNat 32 xl ∧ 0 < xl ∧ xl ≤ 1024) ∧
    Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 40)
  swap
  · refine VG.RelCT.of_false fun s₁ _ h => hx ?_
    obtain ⟨⟨R, X⟩, d⟩ := hP _ h.1
    exact ⟨⟨X.e11, X.pos, by have := X.le; have := R.1.upper'; omega⟩, d⟩
  unfold Impl.Ffdh.X86.DerivePublic.tail
  exact VG.RelCT.seq ((CheckPrivate.powTop_trace hx.1 hx.2).mono (fun _ _ h => ⟨(hP _ h.1).1, (hP _ h.2).1⟩)
    fun _ _ h => h) (RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) rest_check)

theorem body_relCT :
    RelCT isa (Both (DAt Ex base bytes len dlen xl args sp D St)) Impl.Ffdh.X86.DerivePublic.body
      fun _ _ => True := by
  rw [body_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both
    (F := fun u => (RX Ex base bytes len xl args sp u ∧ Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 40)) ∧
      Gate u (St = 2)) front_trace fun x A => ?_) ?_
  · refine WP.mono (front_ok A.run.1 A.geo A.x (by rw [A.run.2.2]; exact A.hb40) (by rw [A.run.2.2]; exact A.hx40))
      fun u ⟨S, G, _⟩ => ⟨⟨⟨run_step A.run S, A.x.keep ⟨rfl, rfl⟩ S.keeps⟩, A.hx40⟩, G.congr ?_⟩
    rw [← A.st, KeyGen.keyStatus_two, CheckPrivate.params, A.dom]
  · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1.1) fail_check) (tail_trace fun _ h => h.1.1)

end

/-! ## Against the contract -/

/-- The status at entry. -/
abbrev entryStatus (s : State) : Nat :=
  Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)) (Spec.Rsa.os2ip (entryX s))

theorem pub_facts {s t : State} (H : (Spec.Ffdh.derivePublicContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 9, arg s i = arg t i) ∧ entryDom s = entryDom t ∧
      entryStatus s = entryStatus t := by
  sig_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a3])
  refine ⟨SP, fun i hi => ?_, inj L₁, List.cons.inj L₂ |>.1⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0
  · exact a1
  · exact a2
  · exact a3
  · exact a4
  · exact a5
  · exact a6
  · exact a7
  · exact a8

theorem narrowRd {s : State} {rd wr : List Region} (h : Rd s rd wr) (x : Region) :
    Rd s (rd ++ wr) [x, outR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, _⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.contains_self _ _⟩⟩

/-- The narrowed state the body runs from, the output writable: a run with the domain and the status at
entry. -/
theorem dAt_of {s f : State} (A : DerivePublicABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.DerivePublic.args s f) :
    DAt (Rd s) (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s)
      (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (arg s 3).toNat (arg s 6).toNat
      (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s)
      (entryStatus s)
      (narrowed (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s) f
        [outR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩
  have Gm := frame_geo A (sp := s.gpr .esp - BitVec.ofNat 32 argsFrame) rfl hx
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  refine ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [outR s]) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact A.belowOut.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide)), Bf.2.1⟩,
    Gm.dom, Gm.dom40, Gm.x, Gm.x40, ?_, ?_⟩
  · exact frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega)
  · show Spec.Ffdh.keyStatus _ (Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 5) _)) = _
    rw [frame_keep A Bf.2.2.2.2 A.xScratch A.belowX (by have := A.xBound; omega)]
    rfl

theorem constantTime : ConstantTime isa (Spec.Ffdh.derivePublicContract abi stack).pre
    (Spec.Ffdh.derivePublicContract abi stack).pub Impl.Ffdh.X86.DerivePublic.code := by
  intro s t tr ur sf tf S T H E F
  have A := derivePublicABI_of S
  have B := derivePublicABI_of T
  obtain ⟨SP, args, dom, st⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.DerivePublic.args s = wsBase Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 7).setWidth 64 = (arg t 7).setWidth 64
    rw [args 7 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.DerivePublic.args s = wsSize Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 8).toNat * 8 = (arg t 8).toNat * 8
    rw [args 8 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.DerivePublic.args s = pLenOf Impl.Ffdh.X86.DerivePublic.args t := by
    show (arg s 4).toNat = (arg t 4).toNat
    rw [args 4 (by decide)]
  have hsy : synth Impl.Ffdh.X86.DerivePublic.args (arg t) = synth Impl.Ffdh.X86.DerivePublic.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hout : outR t = outR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 2).setWidth 64) (arg t 3).toNat ∧
        InRegions (rd ++ wr) ((arg t 5).setWidth 64) (arg t 6).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 2).setWidth 64) (arg s 3).toNat ∧
        InRegions (rd ++ wr) ((arg s 5).setWidth 64) (arg s 6).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 5 (by decide),
      args 6 (by decide)]
  have hl3 : (arg t 3).toNat = (arg s 3).toNat := by rw [args 3 (by decide)]
  have hl6 : (arg t 6).toNat = (arg s 6).toNat := by rw [args 6 (by decide)]
  have hx : ∀ {x : State}, DerivePublicABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : DerivePublicABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.DerivePublic.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.DerivePublic.body
        (narrowed (wsBase Impl.Ffdh.X86.DerivePublic.args x) (wsSize Impl.Ffdh.X86.DerivePublic.args x) f
          [outR x]) F := fun {x f} X Bf => by
    have Gm := frame_geo X (sp := x.gpr .esp - BitVec.ofNat 32 argsFrame) rfl
      (narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.DerivePublic.args x, wsSize Impl.Ffdh.X86.DerivePublic.args x⟩)
    have D := dAt_of X Bf
    exact ⟨_, body_ok D.run.1 D.geo D.x (by rw [D.run.2.2]; exact D.hb40) (by rw [D.run.2.2]; exact D.hx40)
      (by rw [D.run.2.2]; exact Gm.out) Gm.e1⟩
  have ho : ∀ {x f : State}, DerivePublicABI x → BodyAt (Rd x) Impl.Ffdh.X86.DerivePublic.args x f →
      outR x ∈ f.wr :=
    fun X Bf => by rw [Bf.2.2.2.1, X.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [outR s]) hws hwz (fun f Bf => hw A Bf) (fun g Bg => by rw [← hout]; exact hw B Bg)
      (fun f g Bf Bg => ⟨dAt_of A Bf, ?_⟩) body_relCT
      (fun f Bf r hr => by rw [List.mem_singleton.mp hr]; exact ho A Bf)
      (fun g Bg r hr => by rw [List.mem_singleton.mp hr, ← hout]; exact ho B Bg)) E F
  have D₂ := dAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl3, hl6, ← SP, ← dom, ← st, hout] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.Derive
