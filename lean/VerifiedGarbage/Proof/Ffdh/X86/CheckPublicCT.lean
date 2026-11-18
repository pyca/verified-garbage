module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Stages
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPublic
meta import VerifiedGarbage.Proof.Ffdh.X86.Entry
meta import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.X86.Stages

/-! ### `Ffdh.X86.CheckPublicTop`, which only this module used -/

section

/-! # `vg_ffdh_check_public` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPublic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : CheckPublicABI s) : WrapABI Impl.Ffdh.X86.CheckPublic.args 7 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h), by decide, (fun _ h => by cases h)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega_using [this]
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  wsIn := by rw [A.wr]; exact List.mem_cons_self ..
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

/-- The domain's and y's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat
abbrev entryY (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckPublic.args)) Impl.Ffdh.X86.CheckPublic.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain and y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 0) (arg s 1).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 3) (arg s 4).toNat

/-- The domain and y, as the synthetic arguments give them, for permissions that read them, apart from
the 96 bytes below the frame. -/
theorem frame_geo {s : State} (A : CheckPublicABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPublic.args s)
      (wsSize Impl.Ffdh.X86.CheckPublic.args s) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) (arg s 1).toNat rd wr ∧
    YGeo (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPublic.args s)
      (wsSize Impl.Ffdh.X86.CheckPublic.args s) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) rd wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPublic.args (arg s) 2), (arg s 1).toNat⟩ (below sp 96) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPublic.args (arg s) 8),
      pLenOf Impl.Ffdh.X86.CheckPublic.args s⟩ (below sp 96) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have yl := A.yLen
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega_using [fb, low, st'])
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega_using [fb, low, st'])
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sub40 : Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega_using [low, st']), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPublic.args s := yl
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, ⟨(ofn _).symm, ?_, ?_, ?_⟩, (A.belowDom.sub_left sub40).symm, ?_⟩
  · show (arg s 3).toNat + _ ≤ _
    rw [← yR]; exact A.yBound
  · show InRegions _ (argumentPointer s 3) _
    rw [← yR]; exact hrd.2
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact A.yScratch
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : CheckPublicABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega_using [low, st'])
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- The status the contract asks for, for a valid domain. -/
abbrev spec (s : State) : Nat :=
  if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (arg s 2).toNat (entryDom s), Spec.Rsa.os2ip (entryY s)⟩
  then 1 else 0

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CheckPublicABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.CheckPublic.args s) (wsSize Impl.Ffdh.X86.CheckPublic.args s)
      (pLenOf Impl.Ffdh.X86.CheckPublic.args s) (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.CheckPublic.body f fun t =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (t.gpr .eax).toNat = spec s) ∧
      Frame ([] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.CheckPublic.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.CheckPublic.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, Y, hb40, hy40⟩ := frame_geo A espf I.extra
  have D : domBytes f.mem (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (arg s 1).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega_using [])
  have Yv : yv f.mem (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) =
      Spec.Rsa.os2ip (entryY s) := by
    have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPublic.args s := A.yLen
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _) = _
    rw [← yR]
    exact congrArg _ (frame_keep A Ft A.yScratch A.belowY (by have := A.yBound; omega_using []))
  refine WP.mono (body_ok I G Y hb40 hy40)
    fun t ⟨r, ⟨E, F, K⟩, V⟩ => ⟨fun v => ?_, by rw [List.nil_append]; exact F, K⟩
  rw [show pLenOf Impl.Ffdh.X86.CheckPublic.args s = (arg s 2).toNat from rfl] at V Yv
  rw [D] at V
  rw [E, V v, expected, D, Yv]
  split <;> rfl

theorem operation_ok {s : State} (A : CheckPublicABI s) :
    WP isa Impl.Ffdh.X86.CheckPublic.code s fun u =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (u.gpr .eax).toNat = spec s) ∧
        abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _
    rw [A.rd]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := []) (fun _ h => by cases h)
    (fun _ h => by cases h)
    (P := fun _ e => Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → e.toNat = spec s)
    (hP := fun _ _ _ _ h => h)
    fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.CheckPublic

end

end

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
  hy40 : Region.Disjoint ⟨byteAddr (args 8), len⟩ (below sp 96)
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
    have h3 : dlen = 3 * len := by have := A.geo.dl; omega_using [n2, this]
    exact WP.mono (loadComp_ok A.run.1 A.geo (k := 2) (j := 11) (by decide) (by omega_using [h3]) (by decide))
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
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi])
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
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega_using [])⟩, Y, hy, ?_⟩
  show Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _ = Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat
  rw [← yR]
  exact frame_keep A Bf.2.2.2.2 A.yScratch A.belowY (by have := A.yBound; omega_using [])

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
