module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTChain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86.Checks

/-!
# `vg_ffdh_generate_key` on i686 in time that depends on the domain and the status only

The contract releases the domain and the status: runs with the same ones
leak the same traces. The scan of the bound reads the domain, the cut of
`rand` and the rest have no branch on it; the one branch on the scalar,
whether it is invalid, is whether the status is 2.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Proof.Bignum.X86.PublicRt (Both)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame ret testMask)

/-! ## The taint checks -/

theorem mod_check : ACheck (Prog.chain [.block PublicFn.modulusArgs, .block modulusCheck] (.block [])) := by
  dsimp only [ACheck]; taint_decide
theorem ret0_check : ACheck (ret 0) := by dsimp only [ACheck]; taint_decide
theorem prefix_check : ACheck (Prog.chain prefixList (.block [])) := by dsimp only [ACheck]; taint_decide
theorem fail_check : ACheck Impl.Ffdh.X86.GenerateKey.fail := by dsimp only [ACheck]; taint_decide

theorem copy612_check : ACheck (copy (.slot .wide 6) (.slot .wide 12) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem fill_check :
    (VG.Taint.check taint (τr [.esp]) (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.GenerateKey.args)) (.block [])).isSome =
      true := by
  taint_decide
theorem nil_check : ACheck (.block []) := by dsimp only [ACheck]; taint_decide
theorem copy12_check : ACheck (copy (.slot .wide 12) (.slot .wide 5) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem copy16_check : ACheck (copy (.slot .wide 16) (.slot .wide 8) (one .wide)) := by
  dsimp only [ACheck]; taint_decide
theorem eqAnd_check : ACheck (.seq (equal (.slot .wide 6) (.slot .wide 3) (one .wide))
    (.block [.alu .and .ecx (.mem (sc accOff)), .store (sc accOff) .ecx])) := by
  dsimp only [ACheck]; taint_decide
theorem outStat_check : ACheck (.seq Impl.Ffdh.X86.GenerateKey.outputs (.block statusOf)) := by
  dsimp only [ACheck]; taint_decide

/-! ## The runs of the tail -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run, with the domain's geometry. -/
abbrev TP (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (u : State) : Prop :=
  Run Ex base bytes len args sp u ∧ DomGeo args base bytes len dlen u.rd u.wr

theorem tp_step {x u : State} (T : TP Ex base bytes len dlen args sp x) (S : Step Ex base bytes len args x u) :
    TP Ex base bytes len dlen args sp u :=
  ⟨run_step T.1 S, T.2.keep ⟨rfl, rfl⟩ S.keeps⟩

/-- A mask and-ed into a header word. -/
theorem andStore_ok {x : State} (h : In Ex base bytes len args x) {d : Nat} (hd : d + 4 ≤ 32) :
    WP isa (.block [.alu .and .ecx (.mem (sc d)), .store (sc d) .ecx]) x (Step Ex base bytes len args x) := by
  have r := KeyScan.word_room h hd
  refine wp_logicS (.inl rfl) (readSrc_sc h.scratch (d := d) r) fun u a => ?_
  have su : Scr u base bytes := h.scratch.of_keeps a.keeps (by decide)
  refine wp_storeS (su.ea (d := d) (by omega)) (su.write (d := d) (n := 4) r) fun t m => WP.block_nil ?_
  have O : Outside base d 4 x.mem t.mem := by rw [m.mem, a.mem]; exact writeW32_outside _ _ _ (by omega)
  exact Step.word h hd O (a.keeps.widen (m.keeps []))

theorem powP_tp {b e : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 17) (he9 : 9 ≤ e) (he : e ≤ 17)
    (hcb : ACheck (copy (.slot .wide b) (.slot .wide 5) (one .wide)))
    (hce : ACheck (copy (.slot .wide e) (.slot .wide 8) (one .wide))) :
    RelCT isa (Both (TP Ex base bytes len dlen args sp)) (Impl.Ffdh.X86.powP b e)
      (Both (TP Ex base bytes len dlen args sp)) :=
  VG.Proof.Bignum.X86.PublicRt.relCT_both
    ((powP_trace hb9 hb he9 he hcb hce).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ _ => trivial)
    fun x T => WP.mono (powP_ok T.1.1 (b := b) (e := e) hb9 (by omega) he9 (by omega) rfl)
      fun _ ⟨_, _, _, F, _, K⟩ => tp_step T (Step.ops T.1.1 F K)

theorem qBranch_rel {Q : State → Prop} :
    RelCT isa (Both fun x => TP Ex base bytes len dlen args sp x ∧ Q x) qBranch
      (Both (TP Ex base bytes len dlen args sp)) := by
  refine VG.RelCT.seq ((powP_tp (b := 12) (e := 16) (by decide) (by decide) (by decide) (by decide) copy12_check
    copy16_check).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) ?_
  refine aRel (fun _ T => T.1) eqAnd_check fun x T => ?_
  refine WP.seq (WP.mono (eqW_ok T.1.1 (a := 6) (b := 3) (by decide) (by decide)) fun u ⟨m, _, K⟩ => ?_)
  have Su := Step.regs T.1.1 m K
  exact WP.mono (andStore_ok Su.inp (d := accOff) (by decide)) fun t St => tp_step T (Su.trans St)

theorem tail_trace :
    RelCT isa (Both (TP Ex base bytes len dlen args sp)) Impl.Ffdh.X86.GenerateKey.tail fun _ _ => True := by
  have ao : accOff = 8 := rfl
  have nb : numBase = 3336 := rfl
  rw [tail_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (M := isa) (R := Both fun u => TP Ex base bytes len dlen args sp u ∧ Gate u (dlen = 2 * len)) ?_ ?_
  · refine VG.RelCT.seq (powP_tp (by decide) (by decide) (by decide) (by decide)
      VG.Proof.Ffdh.X86.CheckDomain.copy10_check VG.Proof.Ffdh.X86.CheckPrivate.copy13_check) ?_
    refine VG.RelCT.seq (aRel (F := TP Ex base bytes len dlen args sp) (fun _ T => T.1) copy612_check fun x T =>
      WP.mono (KeyGen.copyW_ok T.1.1 (a := 6) (b := 12) (by decide) (by decide) (by decide))
        fun _ ⟨S, _⟩ => tp_step T S) ?_
    refine VG.RelCT.seq (aRel (F := fun u => TP Ex base bytes len dlen args sp u ∧ ∃ c, u.gpr .ecx = cmask c)
      (fun _ T => T.1) VG.Proof.Ffdh.X86.CheckPrivate.range_check fun x T =>
        WP.mono (rangeMask_ok T.1.1 (a := 12) (by decide)) fun _ ⟨_, e, O, K⟩ =>
          ⟨tp_step T (Step.word T.1.1 (by decide) O K), _, e⟩) ?_
    refine VG.RelCT.seq (aRel (F := TP Ex base bytes len dlen args sp) (fun _ T => T.1.1)
      VG.Proof.Ffdh.X86.CheckPrivate.store_check fun x ⟨T, c, e⟩ =>
        WP.mono (storeMask_ok T.1.1 (d := accOff) (by omega) e) fun _ ⟨_, O, _, _, K⟩ =>
          tp_step T (Step.word T.1.1 (by omega) O K)) ?_
    refine VG.RelCT.seq (aRel (F := fun u => TP Ex base bytes len dlen args sp u ∧ Gate u (dlen = 2 * len))
      (fun _ T => T.1) VG.Proof.Ffdh.X86.CheckDomain.qTest_check fun x T =>
        WP.mono (qTest_ok T.1.1 T.2.e3 T.2.e12 T.2.dl) fun _ ⟨z, m, K⟩ =>
          ⟨tp_step T (Step.regs T.1.1 m K), Gate.of_eval z decide_eq_true_iff⟩) ?_
    exact aRel (fun _ T => T.1.1) nil_check fun _ T => WP.block_nil T
  · refine VG.RelCT.seq (gate_relCT (fun _ h => h.2)
      (aRel (F := TP Ex base bytes len dlen args sp) (fun _ T => T.1.1.1) nil_check fun _ T => WP.block_nil T.1.1)
      ((qBranch_rel (Q := fun _ => True)).mono (fun _ _ h => ⟨⟨h.1.1.1, trivial⟩, h.2.1.1, trivial⟩)
        fun _ _ h => h)) ?_
    exact aEnd (fun _ T => T.1) outStat_check
end

/-! ## The runs of the body -/

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len dlen : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {D : List Byte} {St : Nat}

/-- A run of the body, with the domain `D` and the status `St`. -/
structure KAt (Ex : List Region → List Region → Prop) (base : Addr) (bytes len dlen : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (D : List Byte) (St : Nat) (u : State) : Prop where
  run : Run Ex base bytes len args sp u
  geo : Geo args base bytes len dlen sp u.rd u.wr
  dom : domOf u.mem args dlen = D
  st : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf len D)
    (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf len D) (Spec.Rsa.bytesAt u.mem (byteAddr (args 10)) len)) = St

theorem KAt.keep {x u : State} (A : KAt Ex base bytes len dlen args sp D St x) (S : Step Ex base bytes len args x u)
    (m : u.mem = x.mem) : KAt Ex base bytes len dlen args sp D St u := by
  refine ⟨run_step A.run S, ?_, by rw [m]; exact A.dom, by rw [m]; exact A.st⟩
  rw [S.keeps.2.1, S.keeps.2.2]; exact A.geo

theorem keyStatus_two {a : Spec.Ffdh.Parameters} {x : Nat} :
    Spec.Ffdh.keyStatus a x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.keyStatus
  cases Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, iff_false]
    split <;> decide

/-- The modulus check, as the domain's. -/
abbrev modOk (len : Nat) (D : List Byte) : Prop := Spec.Rsa.modulusValid (Spec.Ffdh.domainOf len D).p len = true

theorem front_trace :
    RelCT isa (Both fun x => KAt Ex base bytes len dlen args sp D St x ∧ modOk len D)
      (Prog.chain mainFront (.block [])) fun _ _ => True := by
  show RelCT isa _ (Prog.chain prefixList (.seq Impl.Ffdh.X86.CheckPrivate.bound
    (Prog.chain [Impl.Ffdh.X86.CheckPrivate.scalarMask, testMask] (.block [])))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (aRel (F := CheckPrivate.RG Ex base bytes len dlen args sp) (fun _ A => A.1.run) prefix_check
    fun x ⟨A, _⟩ => ?_) (VG.RelCT.seq CheckPrivate.bound_relCT (aEnd (fun _ h => h) CheckPrivate.mask_check))
  have sp' := A.run.2.2
  refine WP.mono (prefix_ok A.run.1 A.geo.dom (by rw [sp']; exact A.geo.dom40) (by rw [sp']; exact A.geo.cut)
    A.geo.rWs (by rw [sp']; exact A.geo.r40) A.geo.domX) fun u P => ⟨⟨P.inp, A.run.2.1.keep P.keeps,
      (P.keeps.1 _ (by decide)).trans sp'⟩, A.geo.dom.keep ⟨rfl, rfl⟩ P.keeps⟩

theorem main_relCT :
    RelCT isa (Both fun x => KAt Ex base bytes len dlen args sp D St x ∧ modOk len D)
      Impl.Ffdh.X86.GenerateKey.main fun _ _ => True := by
  rw [main_eq]
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both
    (F := fun u => TP Ex base bytes len dlen args sp u ∧ Gate u (St = 2)) front_trace fun x ⟨A, mv⟩ => ?_) ?_
  · have sp' := A.run.2.2
    refine WP.mono (front_ok A.run.1 A.geo.dom (by rw [sp']; exact A.geo.dom40) (by rw [sp']; exact A.geo.cut)
      A.geo.rWs (by rw [sp']; exact A.geo.r40) A.geo.domX) fun u F => ⟨⟨⟨F.inp, A.run.2.1.keep F.keeps,
        (F.keeps.1 _ (by decide)).trans sp'⟩, A.geo.dom.keep ⟨rfl, rfl⟩ F.keeps⟩, F.gate.congr ?_⟩
    rw [← A.st, keyStatus_two, ← A.dom]
    rw [← A.dom] at mv
    rw [scalar_eq_mod A.geo.dom x.mem mv]
  · exact gate_relCT (fun _ h => h.2) (aEnd (fun _ h => h.1.1.1) fail_check)
      (tail_trace.mono (fun _ _ h => ⟨h.1.1.1, h.2.1.1⟩) fun _ _ h => h)

theorem body_relCT :
    RelCT isa (Both (KAt Ex base bytes len dlen args sp D St)) Impl.Ffdh.X86.GenerateKey.body fun _ _ => True := by
  show RelCT isa _ (Prog.chain [.block PublicFn.modulusArgs, .block modulusCheck]
    (.ite .e Impl.Ffdh.X86.GenerateKey.main (ret 0))) _
  apply VG.RelCT.chain
  refine VG.RelCT.seq (VG.Proof.Bignum.X86.PublicRt.relCT_both
    (F := fun u => KAt Ex base bytes len dlen args sp D St u ∧ Gate u (modOk len D))
    (aEnd (fun _ A => A.run) mod_check) fun x A => ?_) ?_
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
    rw [P, M, ← A.dom, modOk, VG.Proof.Ffdh.domainOf_p x.mem _ (by omega)]
  · exact gate_relCT (fun _ h => h.2) (main_relCT.mono (fun _ _ h => ⟨⟨h.1.1.1, h.1.2⟩, h.2.1.1, h.2.2⟩)
      fun _ _ h => h) (aEnd (fun _ h => h.1.1.run) ret0_check)

end

/-! ## Against the contract -/

/-- The status at entry. -/
abbrev status (s : State) : Nat :=
  Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s))
    (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)) (entryRand s))

theorem pub_facts {s t : State} (H : (Spec.Ffdh.generateKeyContract abi stack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 11, arg s i = arg t i) ∧ entryDom s = entryDom t ∧ status s = status t := by
  sig_pub [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a5])
  refine ⟨SP, fun i hi => ?_, inj L₁, List.cons.inj L₂ |>.1⟩
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
    Rd s (rd ++ wr) [x, xR s, yR s] :=
  let ⟨⟨r, hr, hc⟩, ⟨r', hr', hc'⟩, _, _⟩ := h
  ⟨⟨r, List.mem_append_left _ hr, hc⟩, ⟨r', List.mem_append_left _ hr', hc'⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), Region.contains_self _ _⟩⟩

/-- The narrowed state the body runs from, x and y writable. -/
theorem kAt_of {s f : State} (A : GenerateKeyABI s) (Bf : BodyAt (Rd s) Impl.Ffdh.X86.GenerateKey.args s f) :
    KAt (Rd s) (wsBase Impl.Ffdh.X86.GenerateKey.args s) (wsSize Impl.Ffdh.X86.GenerateKey.args s)
      (pLenOf Impl.Ffdh.X86.GenerateKey.args s) (arg s 5).toNat (synth Impl.Ffdh.X86.GenerateKey.args (arg s))
      (s.gpr .esp - BitVec.ofNat 32 argsFrame) (entryDom s) (status s)
      (narrowed (wsBase Impl.Ffdh.X86.GenerateKey.args s) (wsSize Impl.Ffdh.X86.GenerateKey.args s) f
        [xR s, yR s]) := by
  have hx := narrowRd Bf.1.extra ⟨wsBase Impl.Ffdh.X86.GenerateKey.args s, wsSize Impl.Ffdh.X86.GenerateKey.args s⟩
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have sub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have rL : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.randLen
  have D : domOf f.mem (synth Impl.Ffdh.X86.GenerateKey.args (arg s)) (arg s 5).toNat = entryDom s :=
    frame_keep A Bf.2.2.2.2 A.domScratch A.belowDom (by have := A.domBound; omega)
  have R : Spec.Rsa.bytesAt f.mem (byteAddr (synth Impl.Ffdh.X86.GenerateKey.args (arg s) 10))
      (pLenOf Impl.Ffdh.X86.GenerateKey.args s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Bf.2.2.2.2 A.randScratch A.belowRand (by have := A.randBound; omega)
  refine ⟨⟨VG.Proof.Ffdh.X86.In.narrow Bf.1 hx, Bf.argsOk (wrapABI A) (Out := [xR s, yR s]) fun r hr => ?_, Bf.2.1⟩,
    frame_geo A rfl hx, D, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.belowX.sub_left sub
    · exact A.belowY.sub_left sub
  · show Spec.Ffdh.keyStatus _ (Spec.Ffdh.scalarOfOctets _ (Spec.Rsa.bytesAt f.mem _ _)) = _
    rw [R]
    rfl

theorem constantTime : ConstantTime isa (Spec.Ffdh.generateKeyContract abi stack).pre
    (Spec.Ffdh.generateKeyContract abi stack).pub Impl.Ffdh.X86.GenerateKey.code := by
  intro s t tr ur sf tf S T H E F
  have A := generateKeyABI_of S
  have B := generateKeyABI_of T
  obtain ⟨SP, args, dom, st⟩ := pub_facts H
  have hws : wsBase Impl.Ffdh.X86.GenerateKey.args s = wsBase Impl.Ffdh.X86.GenerateKey.args t := by
    show (arg s 9).setWidth 64 = (arg t 9).setWidth 64
    rw [args 9 (by decide)]
  have hwz : wsSize Impl.Ffdh.X86.GenerateKey.args s = wsSize Impl.Ffdh.X86.GenerateKey.args t := by
    show (arg s 10).toNat * 8 = (arg t 10).toNat * 8
    rw [args 10 (by decide)]
  have hpl : pLenOf Impl.Ffdh.X86.GenerateKey.args s = pLenOf Impl.Ffdh.X86.GenerateKey.args t := by
    show (arg s 6).toNat = (arg t 6).toNat
    rw [args 6 (by decide)]
  have hsy : synth Impl.Ffdh.X86.GenerateKey.args (arg t) = synth Impl.Ffdh.X86.GenerateKey.args (arg s) :=
    synth_congr (wrapABI A).below fun i hi => (args i hi).symm
  have hxR : xR t = xR s := by
    show (⟨(arg t 0).setWidth 64, (arg t 1).toNat⟩ : Region) = ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    rw [args 0 (by decide), args 1 (by decide)]
  have hyR : yR t = yR s := by
    show (⟨(arg t 2).setWidth 64, (arg t 3).toNat⟩ : Region) = ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    rw [args 2 (by decide), args 3 (by decide)]
  have hRd : Rd t = Rd s := by
    show (fun rd wr => InRegions (rd ++ wr) ((arg t 4).setWidth 64) (arg t 5).toNat ∧
        InRegions (rd ++ wr) ((arg t 7).setWidth 64) (arg t 8).toNat ∧
        InRegions wr ((arg t 0).setWidth 64) (arg t 1).toNat ∧ InRegions wr ((arg t 2).setWidth 64) (arg t 3).toNat) =
      fun rd wr => InRegions (rd ++ wr) ((arg s 4).setWidth 64) (arg s 5).toNat ∧
        InRegions (rd ++ wr) ((arg s 7).setWidth 64) (arg s 8).toNat ∧
        InRegions wr ((arg s 0).setWidth 64) (arg s 1).toNat ∧ InRegions wr ((arg s 2).setWidth 64) (arg s 3).toNat
    rw [args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide), args 7 (by decide), args 8 (by decide)]
  have hl5 : (arg t 5).toNat = (arg s 5).toNat := by rw [args 5 (by decide)]
  have hx : ∀ {x : State}, GenerateKeyABI x → Rd x x.rd (⟨frameAt x, argsFrame⟩ :: x.wr) := fun {x} X => by
    show InRegions (x.rd ++ _) _ _ ∧ InRegions (x.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _
    rw [X.rd, X.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  have hw : ∀ {x f : State} (X : GenerateKeyABI x) (Bf : BodyAt (Rd x) Impl.Ffdh.X86.GenerateKey.args x f),
      ∃ F, WP isa Impl.Ffdh.X86.GenerateKey.body
        (narrowed (wsBase Impl.Ffdh.X86.GenerateKey.args x) (wsSize Impl.Ffdh.X86.GenerateKey.args x) f
          [xR x, yR x]) F := fun X Bf => by
    have K := kAt_of X Bf
    have sp' := K.run.2.2
    exact ⟨_, body_ok K.run.1 K.geo.dom (by rw [sp']; exact K.geo.dom40) (by rw [sp']; exact K.geo.cut) K.geo.rWs
      (by rw [sp']; exact K.geo.r40) K.geo.domX (by rw [sp']; exact K.geo.ox) (by rw [sp']; exact K.geo.oy)
      K.geo.e9 K.geo.xy⟩
  have ho : ∀ {x f : State}, GenerateKeyABI x → BodyAt (Rd x) Impl.Ffdh.X86.GenerateKey.args x f →
      ∀ r ∈ [xR x, yR x], r ∈ f.wr := fun X Bf r hr => by
    rw [Bf.2.2.2.1, X.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine wrap_trace (wrapABI A) (wrapABI B) args SP (hx A) (hx B) fill_check
    (fun f Bf => WP.mono (frame_ok A f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (fun f Bf => WP.mono (frame_ok B f Bf.1 Bf.2.1 Bf.2.2.2.2) fun _ h => h.2.2)
    (narrow_body (Out := [xR s, yR s]) hws hwz (fun f Bf => hw A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact hw B Bg)
      (fun f g Bf Bg => ⟨kAt_of A Bf, ?_⟩) body_relCT (fun f Bf => ho A Bf)
      (fun g Bg => by rw [← hxR, ← hyR]; exact ho B Bg)) E F
  have D₂ := kAt_of B Bg
  rw [hRd, ← hws, ← hwz, ← hpl, hsy, hl5, ← SP, hxR, hyR, ← dom, ← st] at D₂
  rw [← hws, ← hwz]
  exact D₂

end VG.Proof.Ffdh.X86.KeyGen
