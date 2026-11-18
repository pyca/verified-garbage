module

public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Base.Lit
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.X25519.X86_64.Base
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
import VerifiedGarbage.Proof.X25519.Edwards.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
meta import VerifiedGarbage.Impl.X25519.X86_64.Base
meta import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
meta import VerifiedGarbage.Proof.X25519.Edwards.Base
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLit
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
meta import VerifiedGarbage.Proof.X25519.X86_64.Bits
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCTLit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.X25519.X86_64.Finish
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring

/-! ### `X25519.X86_64.Base.CT`, which this module and modules that import it used -/

section

/-! ### `X25519.X86_64.Base.Main`, which this module and modules that import it used -/

section

/-! ### `X25519.X86_64.Base.Engine`, which only this module used -/

section

/-! Clamped scalar bits, fixed-base multiplication, and Montgomery encoding. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs val4 ea_sc writeW8_apply writeW8_outside off_eq_iff)
open VG.Spec.X25519 (Fe P decodeScalar25519)
open VG.Proof.X25519.Edwards (clamped_bit u_rep)

variable {fld : Arith} [EdArith fld]

theorem clampBits_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block clampBits) s fun t => PowersKeep base 56 7368 s t ∧
      env t.mem base 16 = env s.mem base 16 ∧
      ∀ q < 256, t.mem (off base (768 + q)) =
        if q < 3 ∨ q = 255 then 0 else if q = 254 then 1 else s.mem (off base (768 + q)) := by
  have hw : ∀ d, 768 ≤ d → d < 1024 → InRegions s.wr (off base d) 1 := fun d h1 h2 =>
    ⟨_, hs.wr, Offset.contains_base _ (by omega_using [h2]) (by omega_using [h2])⟩
  apply WP.of_runBlock
  simp only [clampBits, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store8, ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hs.rdi,
    hw 768 (by decide) (by decide), hw 769 (by decide) (by decide),
    hw 770 (by decide) (by decide), hw 1022 (by decide) (by decide), hw 1023 (by decide) (by decide),
    ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.some.injEq, exists_eq_left']
  have hm : Proof.X25519.X86_64.Outside base 768 256 s.mem
      (((((s.mem.writeW (off base 768) (0 : Byte)).writeW (off base 769) (0 : Byte)).writeW
        (off base 770) (0 : Byte)).writeW (off base 1023) (0 : Byte)).writeW
        (off base 1022) (1 : Byte)) := by
    intro p hp
    rw [writeW8_outside _ _ _ (by decide) (by omega_using [hp]),
      writeW8_outside _ _ _ (by decide) (by omega_using [hp]),
      writeW8_outside _ _ _ (by decide) (by omega_using [hp]),
      writeW8_outside _ _ _ (by decide) (by omega_using [hp]),
      writeW8_outside _ _ _ (by decide) (by omega_using [hp])]
  refine ⟨⟨fun r _ _ hc => ?_, rfl, rfl, (TableFrame.table hm).mono (by decide) (by decide)⟩,
    ?_, fun q hq => ?_⟩
  · have hr : r ≠ .rax := fun h => hc (by subst h; decide)
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  · exact Outside_F hm (by decide) (Or.inl (by decide))
  · have he : 768 + q < 2 ^ 64 := by omega_using [hq]
    simp only [writeW8_apply,
      off_eq_iff base he (by decide : 1022 < 2 ^ 64),
      off_eq_iff base he (by decide : 1023 < 2 ^ 64),
      off_eq_iff base he (by decide : 770 < 2 ^ 64),
      off_eq_iff base he (by decide : 769 < 2 ^ 64),
      off_eq_iff base he (by decide : 768 < 2 ^ 64)]
    rcases (by omega_using [hq] : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 254 ∨ q = 255 ∨ (3 ≤ q ∧ q < 254)) with
      rfl | rfl | rfl | rfl | rfl | ⟨h1, h2⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [show ¬ 768 + q = 1022 by omega_using [h2], show ¬ 768 + q = 1023 by omega_using [h2],
        show ¬ 768 + q = 770 by omega_using [h1], show ¬ 768 + q = 769 by omega_using [h1],
        show ¬ 768 + q = 768 by omega_using [h1], show ¬ (q < 3 ∨ q = 255) by omega_using [h1, h2],
        show ¬ q = 254 by omega_using [h2], ↓reduceIte]

theorem uOps_eval (e : Ed25519.X86_64.Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

theorem uEncode_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (uEncode fld).inline s fun t => RbxKeep base s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        ((env s.mem base 2 + env s.mem base 1) *
          Spec.X25519.pow (env s.mem base 2 - env s.mem base 1) (P - 2)).val := by
  rw [uEncode]
  simp only [Code.inline]
  refine WP.seq (WP.mono (fieldCodeWide_ok hs uOps) fun a ⟨ka, va⟩ => ?_)
  have kac : RbxKeep base s a := ⟨fun r hc _ => ka.gpr r hc, ka.rd, ka.wr, ka.mem⟩
  refine WP.seq (WP.mono (pointAffine_ok (kac.scratch hs)) fun b ⟨kb, bx, _⟩ => ?_)
  refine WP.mono (freezeWide_ok (kb.scratch (kac.scratch hs)) 0) fun t ⟨tv, kt⟩ => ?_
  refine ⟨(kac.trans kb).trans (RbxKeep.of_keeps kt (by decide)), ?_⟩
  rw [tv, bx, va, (uOps_eval _).1, (uOps_eval _).2]

/-- What an engine of fixed-base X25519 computes: the u-coordinate of `[k]B`, in `r8–r11`. -/
def UEngineOk (eng : Prog isa) : Prop :=
  ∀ {s : State} {base k T : Addr}, Scratch s base → s.gpr .rsi = k →
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) → (∀ q < 32, 8192 ≤ ofs base (off k q)) →
    CombTbl s T → TblFar base T →
    WP isa eng s fun t => PowersKeep base 56 7368 s t ∧ ∃ w : Fe,
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = w.val ∧
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem k 32) Spec.X25519.basePoint =
        Spec.X25519.encodeUCoordinate w

omit [EdArith fld] in
/-- An engine with its calls inlined, for a comb that inlines to `comb'`. -/
theorem engineOf_inline {comb comb' : Prog isa} (hci : comb.inline = comb') :
    (engineOf fld comb).inline =
      .seq (scalarBasePrepare fld) (.seq (.block clampBits) (.seq comb' (uEncode fld).inline)) := by
  rw [engineOf]; simp only [Code.inline]; rw [scalarBasePrepare_inline, hci]

theorem engineOf_ok [DivstepInv] {comb comb' : Prog isa} (hcomb : CombOk comb') (hci : comb.inline = comb') :
    UEngineOk (engineOf fld comb).inline := by
  intro s base k T hs hp hr hd ht hfar
  have hk : (Spec.Ed25519.bytesAt s.mem k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  set kb := Spec.Ed25519.bytesAt s.mem k 32
  rw [engineOf_inline hci]
  refine WP.seq (WP.mono_syms (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, _, bd, bbits, _⟩ bsy => ?_)
  have hsb := kab.scratch hs
  refine WP.seq (WP.mono_syms (clampBits_ok hsb) fun c ⟨kbc, cd, cbits⟩ csy => ?_)
  have hsc := kbc.scratch hsb
  have hS : decodeScalar25519 kb < 2 ^ 256 := by
    have h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega_using [h]
  have cb : ∀ q < 256, c.mem (off base (768 + q)) = BitVec.ofNat 8 ((decodeScalar25519 kb / 2 ^ q) % 2) := by
    intro q hq
    rw [cbits q hq, clamped_bit hk hq]
    split_ifs
    · rfl
    · rfl
    · exact bbits q (by simpa using hq)
  have tc : CombTbl c T := (ht.keep hfar kab bsy).keep hfar kbc csy
  refine WP.seq (WP.mono (hcomb.ok hsc hS (cd.trans bd) cb tc hfar) fun d ⟨dp, kd⟩ => ?_)
  refine WP.mono (uEncode_ok (kd.scratch hsc)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨((kab.trans kbc).trans kd).trans (PowersKeep.of_rbx kt), _, tv, ?_⟩
  -- stated first: as an argument, `u_rep dp` is compared with the expected type before its point is known
  have ur := u_rep dp
  exact VG.Proof.X25519.Edwards.x25519_basePoint hk _ ur

theorem engine_ok [DivstepInv] : UEngineOk (engine fld).inline := engineOf_ok combOk combMultiply_inline

/-! ## Constant time

The comb's constant time is its own (`CombOk.ct`), as Ed25519's fixed-base
engine uses it (`scalarBaseEngineOf_ct`): only the preparation, the clamping
and the encoding are analysed here. -/

/-- A run after the preparation, from the scalar at `k` in `m`. -/
private def Prepped (base T k : Addr) (m : Mem) (u : State) : Prop :=
  Scratch u base ∧ env u.mem base 16 = Spec.Ed25519.d ∧
    (∀ q < 16 * 16, u.mem (off base (768 + q)) =
      BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m k 32) / 2 ^ q) % 2)) ∧
    CombTbl u T ∧ TblFar base T

/-- A run after the clamping: what the comb starts from. -/
private def Clamped (base T k : Addr) (m : Mem) (c : State) : Prop :=
  Scratch c base ∧ env c.mem base 16 = Spec.Ed25519.d ∧
    (∀ q < 256, c.mem (off base (768 + q)) =
      BitVec.ofNat 8 ((decodeScalar25519 (Spec.Ed25519.bytesAt m k 32) / 2 ^ q) % 2)) ∧
    decodeScalar25519 (Spec.Ed25519.bytesAt m k 32) < 2 ^ 256 ∧ CombTbl c T ∧ TblFar base T

private theorem clamped_ok {u : State} {base T k : Addr} {m : Mem} (h : Prepped base T k m u) :
    WP isa (.block clampBits) u (Clamped base T k m) := by
  obtain ⟨hs, hd, hb, ht, hfar⟩ := h
  have hk : (Spec.Ed25519.bytesAt m k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  have hS : decodeScalar25519 (Spec.Ed25519.bytesAt m k 32) < 2 ^ 256 := by
    have h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega_using [h]
  refine WP.mono_syms (clampBits_ok hs) fun c ⟨kbc, cd, cbits⟩ csy =>
    ⟨kbc.scratch hs, cd.trans hd, fun q hq => ?_, hS, ht.keep hfar kbc csy, hfar⟩
  rw [cbits q hq, clamped_bit hk hq]
  split_ifs
  · rfl
  · rfl
  · exact hb q (by simpa using hq)

theorem engineOf_ct {comb comb' : Prog isa} (hcomb : CombOk comb') (hci : comb.inline = comb') (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engineOf fld comb).inline (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (scalarBasePrepare fld) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.rdi.trans h.2.1.rdi.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hp := withRuns hc (fun x y h =>
    ⟨scalarBasePrepareT_ok (fld := fld) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     scalarBasePrepareT_ok (fld := fld) h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩)
  rw [engineOf_inline hci]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hcl : RelCT isa (fun u v => Prepped base T k a.mem u ∧ Prepped base T k b.mem v)
      (.block clampBits) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi) ⟨_, by taint_decide⟩
  have hcl' := (withRuns hcl (F₁ := fun _ => Clamped base T k a.mem) (F₂ := fun _ => Clamped base T k b.mem)
    fun _ _ h => ⟨clamped_ok h.1, clamped_ok h.2⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, _, _, _, hu, hv⟩ => (⟨hu, hv⟩ : Clamped base T k a.mem _ ∧ Clamped base T k b.mem _)
  have hct : RelCT isa (fun u v => Clamped base T k a.mem u ∧ Clamped base T k b.mem v) comb'
      (fun _ _ => True) :=
    hcomb.ct _ (fun _ _ h => ⟨rdi_agree h.1.1.rdi h.2.1.rdi, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn
      exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm⟩)
  have hct' := (withRuns hct fun u v h =>
    ⟨hcomb.ok h.1.1 h.1.2.2.2.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     hcomb.ok h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, c, d, hcd, hu, hv⟩ => And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base) (uEncode fld).inline
      (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact rdi_agree h.1 h.2
  exact (VG.RelCT.seq hcl' (VG.RelCT.seq hct' he)) _ _ _ _ _ _
    ⟨⟨hx.1.1.scratch hab.1.1, hx.1.2.2.1, hx.1.2.2.2.1, hx.2, hab.1.2.2.2.2.2⟩,
     ⟨hy.1.1.scratch hab.2.1, hy.1.2.2.1, hy.1.2.2.2.1, hy.2, hab.2.2.2.2.2.2⟩⟩ ex ey

end VG.Proof.X25519.X86_64.Base

end

end

/-! Memory, output encoding and ABI obligations for fixed-base X25519. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved val4 st4 bytesAt_st4)
open VG.Spec.Ed25519 (bytesAt)
variable {fld : Arith} [EdArith fld]

/-- The contract the proof is written against: the comb's tables at the static `combSym`,
readable after the scalar (`CombHeld`). -/
def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rsi, 32⟩, combRegion (s.syms combSym)] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧
    CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩]
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .rdi) 32 =
    Spec.X25519.x25519 (bytesAt s.mem (s.gpr .rsi) 32) Spec.X25519.basePoint
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.syms combSym = t.syms combSym

/-- `baseLocal` is `scalarBaseLocal`'s precondition. -/
theorem baseLocal_pre {s : State} (hs : baseLocal.pre s) : scalarBaseLocal.pre s := hs

theorem x25519BaseWith_correct (eng : Prog isa) (heng : UEngineOk eng)
    {s : State} (hs : baseLocal.pre s) :
    WP isa (scalarBaseWith eng) s fun t => gprPreserved s t ∧ baseLocal.post s t := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl (baseLocal_pre hs)
  obtain ⟨hr, hw, hd, hro, hrs, hn, hh⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, ma, sva⟩ asy => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ bsy => ?_
  rw [ga] at pb ob mb
  have hb : Scratch b (s.gpr .rdx) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .rdx) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .rsi) 32 = bytesAt s.mem (s.gpr .rsi) 32 := bytesAt32_frame fm hd
  have tblb : CombTbl b (s.syms combSym) := tbl.frame fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hh.2.2 _ (by simp))
    (by rw [rb, wb, ra, wa]) (by rw [bsy, asy])
  apply WP.seq
  refine WP.mono (heng hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .rsi, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩)
    (fun q hq => farScratch hd hq (by decide)) tblb far) fun c ⟨kc, w, vc, xc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .rdx) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have rdxd : d.gpr .rdx = s.gpr .rdx := pd
  have rdid : d.gpr .rdi = s.gpr .rdi := od.trans oc
  have wd : d.wr = s.wr := kd.2.2.2.trans wc
  rw [WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) rdxd (wd ▸ hws) (by rw [kd.2.1]; exact svc))
    fun e ⟨re, ge, me, _, we⟩ => ?_
  have rdie : e.gpr .rdi = s.gpr .rdi := (ge _ (by decide)).trans rdid
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ e.wr := by rw [we, wd, hw]; simp
  refine WP.mono (scalarOut_ok rdie hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fme : Frame [⟨s.gpr .rdx, 8192⟩] s.mem e.mem := by
    rw [me, kd.2.1]; exact fm.trans (scratchFrame mc (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.rbx, 0) (by decide)
    · exact re (.rbp, 8) (by decide)
    · rw [ge _ (by decide), kd.1 _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
    · exact re (.r12, 16) (by decide)
    · exact re (.r13, 24) (by decide)
    · exact re (.r14, 32) (by decide)
    · exact re (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have hc : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega_using [hd])
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fme.mono (by simp)).writeW hm _ (hc 0 (by decide))).writeW hm _
        (hc 8 (by decide))).writeW hm _ (hc 16 (by decide))).writeW hm _ (hc 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change Spec.X25519.bytesAt t.mem (s.gpr .rdi) 32 = _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, ← input, xc, Proof.X25519.encodeUCoordinate_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ge .r8 (by decide), ge .r9 (by decide), ge .r10 (by decide), ge .r11 (by decide),
      kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide)]
    exact vc

theorem x25519Base_correct [DivstepInv] {s : State} (hs : baseLocal.pre s) :
    WP isa (x25519Base fld).inline s fun t => gprPreserved s t ∧ baseLocal.post s t := by
  rw [x25519Base, scalarBaseWith_inline]
  exact x25519BaseWith_correct _ engine_ok hs

end VG.Proof.X25519.X86_64.Base

end

end

/-! Public pointers survive the secret fixed-base arithmetic. -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)
variable {fld : Arith} [EdArith fld]

private def BaseStart (base k T out : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .rdi = out ∧ s.gpr .rsi = k ∧ s.gpr .rdx = base ∧ s.syms combSym = T

private def BasePrepared (base k T out : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k T out : Addr} {s : State} (hs : BaseStart base k T out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k T out) := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl (baseLocal_pre hs.1)
  obtain ⟨⟨hr, hw, hd, _, _, hn, hh⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, ma, _⟩ asy => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ bsy => ?_
  rw [ga, hb] at pb ob mb
  rw [hb] at far
  have hh2 := hh.2.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [hT] at tbl far hh2
  have fm : Frame [⟨base, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_,
    tbl.frame fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← hb]; exact hh2)
      (by rw [rb, wb, ra, wa]) (by rw [bsy, asy]), far⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScratch hd hq (by decide)

private theorem start_ct (base k T out : Addr) :
    RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y) := by
  have hc : RelCT isa (fun x y => BaseStart base k T out x ∧ BaseStart base k T out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi, .rsi, .rdx]) _ (by fld_taint_decide)
    intro x y h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {eng : Prog isa} (heng : UEngineOk eng) {base k T out : Addr} {s : State}
    (hs : BasePrepared base k T out s) : WP isa eng s (BaseReady base out) := by
  refine WP.mono (heng hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2.1 hs.1.2.2.2.2.1 hs.1.2.2.2.2.2)
    fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct {eng : Prog isa} (heng : UEngineOk eng)
    (engine_ct : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      eng (fun _ _ => True)) (base k T out : Addr) :
    RelCT isa (fun x y => BasePrepared base k T out x ∧ BasePrepared base k T out y)
      eng (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k T out _ ∧ BasePrepared base k T out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready heng h.1, engine_ready heng h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : RelCT isa (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .rdx = base ∧ t.gpr .rdi = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine VG.RelCT.seq hc' ?_
  apply taintFld (Taint.ofRegs [.rdx, .rdi]) _ (by fld_taint_decide)
  intro x y h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem x25519BaseWith_ct (eng : Prog isa) (heng : UEngineOk eng)
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      eng (fun _ _ => True)) :
    ConstantTime isa baseLocal.pre baseLocal.pub (scalarBaseWith eng) := by
  apply VG.RelCT.constantTime (Q := fun _ _ => True)
  intro x y tx ty x' y' ⟨hx, hy, _, ho, hk, hb, hT⟩ ex ey
  have hc := VG.RelCT.seq (start_ct (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
    (VG.RelCT.seq (engine_ct heng engineCT (x.gpr .rdx) (x.gpr .rsi) (x.syms combSym) (x.gpr .rdi))
      (finish_ct (x.gpr .rdx) (x.gpr .rdi)))
  exact hc _ _ _ _ _ _ ⟨⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hT.symm⟩⟩ ex ey

theorem x25519Base_ct [DivstepInv]
    (engineCT : ∀ base k T, RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engine fld).inline (fun _ _ => True)) :
    ConstantTime isa baseLocal.pre baseLocal.pub (x25519Base fld).inline := by
  rw [x25519Base, scalarBaseWith_inline]
  exact x25519BaseWith_ct _ engine_ok engineCT

end VG.Proof.X25519.X86_64.Base

end

end

/-! Fixed-base X25519 satisfies the reviewed contract, with either field backend, with 8 bytes
of stack for its call of `vg_gf25519_r64_invert`: correct and constant time as its code with the
inversion inlined (`Verified.of_inline`). -/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
variable {fld : Arith} [EdArith fld]

theorem engine_public (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engine fld).inline (fun _ _ => True) :=
  engineOf_ct combOk combMultiply_inline base k T


theorem x25519Base_ok [DivstepInv] (s : State) (hs : baseLocal.pre s) :
    ∃ tr t, Exec isa (x25519Base fld).inline s tr t ∧ abiPreserved s t ∧ baseLocal.post s t := by
  obtain ⟨tr, t, he, h⟩ := x25519Base_correct (fld := fld) hs
  exact ⟨tr, t, he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; fld_lit_decide) he h.1, h.2⟩

/-- The shared contract's precondition, from its facts. -/
theorem base_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hal : (s.syms combSym).toNat % 64 = 0) :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, f0, f1, f2⟩

theorem base_sat :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)).pre baseSatStateT := by
  refine base_spec_pre rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem base_implies :
    baseLocal.Implies (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow, combWords_length] at h
    obtain ⟨hd, hheld, hfit, hdw, hdr, -, ht, hw, -, h2, h3, r1, -, r3, -, -, f2⟩ := h
    refine ⟨?_, hw, h3, r1, r3, f2, hheld, hfit, fun r hr => ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hdr
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, baseLocal]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨h0, hs, h1, h2, h3⟩ := h
    exact ⟨h0, h1, h2, h3, hs⟩
  sat := ⟨baseSatStateT, base_sat⟩

/-- The shared contract's precondition with 8 bytes of stack, from its facts. -/
theorem base_spec_pre8 {s : State}
    (hrd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.syms combSym, 40448⟩])
    (hw : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (q1 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdi, 32⟩)
    (q2 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rsi, 32⟩)
    (q3 : Region.Disjoint ⟨s.gpr .rsp - 8#64, 8⟩ ⟨s.gpr .rdx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64) (hsp : 8 ≤ (s.gpr .rsp).toNat)
    (ht : CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩])
    (hq : Region.Disjoint ⟨s.syms combSym, 40448⟩ ⟨s.gpr .rsp - 8#64, 8⟩)
    (hal : (s.syms combSym).toNat % 64 = 0) :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    X86_64.abi, X86_64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow, combWords_length]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; exact fun r hr => hdw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]),
    hdw _ (by simp), hq, hal, by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, q1, q2, q3, f0, f1, f2⟩

theorem base_sat8 :
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8).pre baseSatStateT := by
  refine base_spec_pre8 rfl rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) (by decide) ⟨combSatMem_held, by decide, ?_⟩ (Region.disjoint_of_sep (by decide))
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem base_implies8 :
    baseLocal.Implies (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  base_implies.stack8 ⟨baseSatStateT, base_sat8⟩

/-- The output is apart from the call's return address. -/
theorem base_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : baseLocal.pre s)
    (hcl : Clear (hole (s.gpr .rsp)) s) (hp : baseLocal.post s b) :
    baseLocal.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hw, -⟩ := hs
  have hb := Clear.wr_bytes hcl (p := s.gpr .rdi) (n := 32) (by rw [hw]; simp) (by decide)
  exact (bytes_patch hb).trans hp

theorem base_verified_of {c : Prog isa} (hc : c.InlineOk = true)
    (hcor : ∀ s, baseLocal.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s')
    (hct : ConstantTime isa baseLocal.pre baseLocal.pub c.inline) :
    Verified X86_64.target c (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  Verified.of_inline hc hcor hct base_implies8 (fun _ h => Sig.clear_of_pre_consts h)
    (fun s b hv u hs hp => base_patch s b hv u (base_implies8.pre s hs) (Sig.clear_of_pre_consts hs) hp)
    (fun s₁ s₂ h₁ h₂ hp => (base_implies8.pub s₁ s₂ h₁ h₂ hp).1)

theorem x25519Base_verified [DivstepInv] : Verified X86_64.target (x25519Base fld)
    (Spec.X25519.x25519BaseContract (X86_64.abi.withConsts combConsts) 8) :=
  base_verified_of (by fld_lit_decide) x25519Base_ok (x25519Base_ct engine_public)

end VG.Proof.X25519.X86_64.Base
