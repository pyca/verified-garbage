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

end VG.Proof.Ffdh.X86.KeyGen
