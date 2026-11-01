module

public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyDecode
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X25519.AArch64.Ladder
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyDecode
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Merged from `Proof.Ed25519.AArch64.VerifyLit`. -/

@[expose] public section

section
/-! A checked literal for the complete verification program. -/

namespace VG

materialize_code Impl.Ed25519.AArch64.verifyEquation

end VG
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifySetup`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyBody`. -/
section
/-! `R` and `A` decoded by one loop, then the equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem verifyDecode_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa verifyDecode s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) :=
  verifyDecode_wp ⟨h, rfl, rfl, rfl, rfl, rfl⟩

end VG.Proof.Ed25519.AArch64

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecode recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .x8 = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono_syms (verifyScalar_ok h.scratch h.sigHeader h.scalarRead)
    fun a ⟨ka, am, ac⟩ sya => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ (congrArg some ac)
  · intro ht
    refine WP.mono (verifyDecode_ok (h.of_keep kap sya)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.AArch64
end

/-! Save the ABI registers and retain the three public input pointers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [mov .x8 .x2, mov .x2 .x3]) s fun t =>
      t.gpr .x8 = s.gpr .x2 ∧ t.gpr .x2 = s.gpr .x3 ∧ Keeps [.x8, .x2] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .x0 = base ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .x0 ∧
      t.mem.readW (off base 7944) 64 = s.gpr .x1 ∧
      t.mem.readW (off base 7952) 64 = s.gpr .x8 := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write]
    exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_write, write64_eq_writeW, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [mov .x2 .x0, mov .x0 .x8]) s fun t =>
      t.gpr .x2 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x8 ∧ Keeps [.x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 64⟩, ⟨s.syms bSym, 1920⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ BHeld s [⟨s.gpr .x3, 8192⟩]
  post s t := t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 64) (bytesAt s.mem (s.gpr .x2) 64))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    bytesAt s.mem (s.gpr .x0) 32 = bytesAt t.mem (t.gpr .x0) 32 ∧
    bytesAt s.mem (s.gpr .x1) 64 = bytesAt t.mem (t.gpr .x1) 64 ∧
    bytesAt s.mem (s.gpr .x2) 64 = bytesAt t.mem (t.gpr .x2) 64 ∧
    s.syms bSym = t.syms bSym

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  saved : Saved (s.gpr .x3) s.gpr t.mem
  frame : Frame [⟨s.gpr .x3, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], t.gpr r = s.gpr r
  syms : t.syms = s.syms

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hn, hheld⟩ := hs
  have hws : (⟨s.gpr .x3, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  have hbt : BTblAt s (s.gpr .x3) (s.syms bSym) := hheld.tblAt (by rw [hr]; simp) (by simp)
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ sya => ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok asc (ka.wr ▸ hws)) fun b ⟨gb, rb, wb, spb, mb, svb⟩ syb => ?_
  have bs : b.gpr .x2 = s.gpr .x3 := (congrFun gb _).trans asc
  refine WP.mono_syms (verifyHeaders_ok bs (by rw [wb, ka.wr]; exact hws))
    fun c ⟨cs, gc, rc, wc, spc, mc, cp, cr, cc⟩ syc => ?_
  have fm : Frame [⟨s.gpr .x3, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.mem] at f
    exact f
  have sv : Saved (s.gpr .x3) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.gpr
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.rd)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.wr)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.gpr .x0 (by decide)]
    · rw [cr, gb, ka.gpr .x1 (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .x1) 32) d = off (s.gpr .x1) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .x1) 32) d = off (s.gpr .x1) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 16 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro i hi; exact farScr hpk hi (by decide)
    · intro i hi; exact farScr hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact farScr hsig (by omega) (by decide)
    · intro i hi; exact farScr hchallenge hi (by decide)
    · rw [syc, syb, sya]
      refine hbt.of_far (by rw [rr, ww]) fun x hx => fm x fun r hr hcx => ?_
      rw [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at hcx
      simp only [ofs] at hx
      omega
  refine ⟨hc, sv, fm, spc.trans (spb.trans ka.sp), fun r hr => ?_, by rw [syc, syb, sya]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rw [gc _ (by decide), gb, ka.gpr _ (by decide)]

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ev, ke⟩ => ?_
  have er : e.gpr .x2 = s.gpr .x3 := es.trans (kd.scratch hc.scratch).x0
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.wr, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.mem]; exact svd)) fun t ⟨tr, kt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.x19, 0) (by decide)
    · exact tr (.x20, 8) (by decide)
    · exact tr (.x21, 16) (by decide)
    · exact tr (.x22, 24) (by decide)
    · exact tr (.x23, 32) (by decide)
    · exact tr (.x24, 40) (by decide)
    all_goals
      rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide) (by decide) (by decide)]
      exact hc0.regs _ (by decide)
  · exact kt.sp.trans (ke.sp.trans (kd.sp.trans hc0.sp))
  · change t.gpr .x0 = _
    rw [kt.gpr _ (by decide), ev, dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCT`. -/
section
/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) (s.syms bSym) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide), congrFun h.syms bSym⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) (s.syms bSym) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs, hsy⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base, ← hsy] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem verifyBody_base_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecode recoverInvalid))
      (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) :
      WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecode recoverInvalid)) s
        (fun t => t.gpr .x0 = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).x0
  exact (CT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs T)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have setupCT : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x3]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  have whole : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      verifyEquation (fun _ _ => True) := by
    rw [verifyEquation]
    refine CT.seq hp ?_
    intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
    have pa := ha.public hab.1
    have pb := hb.public_right hab.2.1 hab.2.2
    exact CT.seq
      (verifyBody_base_ct (a.gpr .x3) (a.gpr .x0) (a.gpr .x1) (a.gpr .x2)
        (bytesAt a.mem (a.gpr .x0) 32) (bytesAt a.mem (a.gpr .x1) 32)
        (bytesAt a.mem (off (a.gpr .x1) 32) 32) (bytesAt a.mem (a.gpr .x2) 64) (a.syms bSym))
      (verifyFinish_ct (a.gpr .x3)) _ _ _ _ _ _ ⟨hsp, pa, pb⟩ es et
  intro s t ts tt s' t' hs ht hp es et
  exact (whole _ _ _ _ _ _ ⟨hp.1, hs, ht, hp⟩ es et).1

end VG.Proof.Ed25519.AArch64
end

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem := bSatMem
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x100000, 1920⟩]
  wr := [⟨0x4000, 8192⟩]
  syms _ := 0x100000

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := verify_correct hs

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

/-- The shared contract's precondition, from its facts. -/
theorem verify_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 64⟩,
      ⟨s.syms bSym, 8 * bWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x3, 8192⟩])
    (held : ∀ i < bWords.length,
      s.mem.readW (s.syms bSym + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0)
    (fit : (s.syms bSym).toNat + 8 * bWords.length ≤ 2 ^ 64)
    (hdw : Region.Disjoint ⟨s.syms bSym, 8 * bWords.length⟩ ⟨s.gpr .x3, 8192⟩)
    (hal : (s.syms bSym).toNat % 64 = 0)
    (h1 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x3, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x2, 64⟩ ⟨s.gpr .x3, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 64 ≤ 2 ^ 64) (f3 : (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64) :
    (Proof.Ed25519.verifyEquationContract (AArch64.abi.withConsts bConsts)).pre s := by
  sig_pre [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig,
    Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow]
  refine ⟨by rw [hrd]; rfl, held, fit, fun r hr => ?_, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2, f3⟩
  rw [hw, List.mem_singleton] at hr
  rw [hr]; exact hdw

theorem verify_implies :
    verifyLocal.Implies (Proof.Ed25519.verifyEquationContract (AArch64.abi.withConsts bConsts)) where
  pre s h := by
    sig_pre [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts,
      Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, held, fit, hdw, -, ht, hw, d1, d2, d3, -, -, -, f3⟩ := h
    simp only [bWords_length, Nat.reduceMul] at hd held fit hdw
    refine ⟨?_, hw, d1, d2, d3, f3, held, fit, fun r hr => hdw r (by rw [hw]; exact hr)⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post s t _ h := by
    sig_post [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, bConsts_eq, Abi.withConsts] at h
    obtain ⟨sp, hsy, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last, hsy⟩
  sat := by
    have hl := bWords_length
    refine ⟨verifySatState, verify_spec_pre (by rw [hl]; rfl) rfl
      (fun i hi => bSatMem_held i (by rw [hl] at hi; exact hi)) (by rw [hl]; decide)
      (by rw [hl]; exact Region.disjoint_of_sep (by decide)) (by decide) (Region.disjoint_of_sep (by decide))
      (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide)
      (by decide) (by decide) (by decide)⟩

theorem verify_verified :
    Verified AArch64.target verifyEquation
      (Proof.Ed25519.verifyEquationContract (AArch64.abi.withConsts bConsts)) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.AArch64
