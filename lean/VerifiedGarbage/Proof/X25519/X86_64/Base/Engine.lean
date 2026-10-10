import VerifiedGarbage.Impl.X25519.X86_64.Base
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedCT
import VerifiedGarbage.Proof.X25519.Edwards.Base
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! Clamped scalar bits, fixed-base multiplication, and Montgomery encoding. -/
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
    ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
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
    rw [writeW8_outside _ _ _ (by decide) (by omega),
      writeW8_outside _ _ _ (by decide) (by omega),
      writeW8_outside _ _ _ (by decide) (by omega),
      writeW8_outside _ _ _ (by decide) (by omega),
      writeW8_outside _ _ _ (by decide) (by omega)]
  refine ⟨⟨fun r _ _ hc => ?_, rfl, rfl, (TableFrame.table hm).mono (by decide) (by decide)⟩,
    ?_, fun q hq => ?_⟩
  · have hr : r ≠ .rax := fun h => hc (by subst h; decide)
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  · exact Outside_F hm (by decide) (Or.inl (by decide))
  · have he : 768 + q < 2 ^ 64 := by omega
    simp only [writeW8_apply,
      off_eq_iff base he (by decide : 1022 < 2 ^ 64),
      off_eq_iff base he (by decide : 1023 < 2 ^ 64),
      off_eq_iff base he (by decide : 770 < 2 ^ 64),
      off_eq_iff base he (by decide : 769 < 2 ^ 64),
      off_eq_iff base he (by decide : 768 < 2 ^ 64)]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem uOps_eval (e : Ed25519.X86_64.Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

theorem uEncode_ok [DivstepInv] {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (uEncode fld) s fun t => RbxKeep base s t ∧
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) =
        ((env s.mem base 2 + env s.mem base 1) *
          Spec.X25519.pow (env s.mem base 2 - env s.mem base 1) (P - 2)).val := by
  rw [uEncode]
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

theorem engineOf_ok [DivstepInv] {comb : Prog isa} (hcomb : CombOk comb) : UEngineOk (engineOf fld comb) := by
  intro s base k T hs hp hr hd ht hfar
  have hk : (Spec.Ed25519.bytesAt s.mem k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  set kb := Spec.Ed25519.bytesAt s.mem k 32
  rw [engineOf]
  refine WP.seq (WP.mono_syms (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, _, bd, bbits, _⟩ bsy => ?_)
  have hsb := kab.scratch hs
  refine WP.seq (WP.mono_syms (clampBits_ok hsb) fun c ⟨kbc, cd, cbits⟩ csy => ?_)
  have hsc := kbc.scratch hsb
  have hS : decodeScalar25519 kb < 2 ^ 256 := by
    have h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega
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
  exact VG.Proof.X25519.Edwards.x25519_basePoint hk _ (u_rep dp)

theorem engine_ok [DivstepInv] : UEngineOk (engine fld) := engineOf_ok combOk

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
    omega
  refine WP.mono_syms (clampBits_ok hs) fun c ⟨kbc, cd, cbits⟩ csy =>
    ⟨kbc.scratch hs, cd.trans hd, fun q hq => ?_, hS, ht.keep hfar kbc csy, hfar⟩
  rw [cbits q hq, clamped_bit hk hq]
  split_ifs
  · rfl
  · rfl
  · exact hb q (by simpa using hq)

theorem engineOf_ct {comb : Prog isa} (hcomb : CombOk comb) (base k T : Addr) :
    RelCT isa (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y)
      (engineOf fld comb) (fun _ _ => True) := by
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
  rw [engineOf]
  refine VG.RelCT.seq hp ?_
  intro x y tx ty x' y' ⟨_, a, b, hab, hx, hy⟩ ex ey
  have hcl : RelCT isa (fun u v => Prepped base T k a.mem u ∧ Prepped base T k b.mem v)
      (.block clampBits) (fun _ _ => True) :=
    taintFld (Taint.ofRegs [.rdi]) (fun _ _ h => rdi_agree h.1.1.rdi h.2.1.rdi) ⟨_, by taint_decide⟩
  have hcl' := (withRuns hcl (F₁ := fun _ => Clamped base T k a.mem) (F₂ := fun _ => Clamped base T k b.mem)
    fun _ _ h => ⟨clamped_ok h.1, clamped_ok h.2⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, _, _, _, hu, hv⟩ => (⟨hu, hv⟩ : Clamped base T k a.mem _ ∧ Clamped base T k b.mem _)
  have hct : RelCT isa (fun u v => Clamped base T k a.mem u ∧ Clamped base T k b.mem v) comb
      (fun _ _ => True) :=
    hcomb.ct _ (fun _ _ h => ⟨rdi_agree h.1.1.rdi h.2.1.rdi, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn
      exact h.1.2.2.2.2.1.sym.trans h.2.2.2.2.2.1.sym.symm⟩)
  have hct' := (withRuns hct fun u v h =>
    ⟨hcomb.ok h.1.1 h.1.2.2.2.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.2.1 h.1.2.2.2.2.2,
     hcomb.ok h.2.1 h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, c, d, hcd, hu, hv⟩ => And.intro (hu.2.scratch hcd.1.1).rdi (hv.2.scratch hcd.2.1).rdi
  have he : RelCT isa (fun u v => u.gpr .rdi = base ∧ v.gpr .rdi = base) (uEncode fld)
      (fun _ _ => True) := by
    apply taintFld (Taint.ofRegs [.rdi]) _ (by fld_taint_decide)
    intro u v h
    exact rdi_agree h.1 h.2
  exact (VG.RelCT.seq hcl' (VG.RelCT.seq hct' he)) _ _ _ _ _ _
    ⟨⟨hx.1.1.scratch hab.1.1, hx.1.2.2.1, hx.1.2.2.2.1, hx.2, hab.1.2.2.2.2.2⟩,
     ⟨hy.1.1.scratch hab.2.1, hy.1.2.2.1, hy.1.2.2.2.1, hy.2, hab.2.2.2.2.2.2⟩⟩ ex ey

end VG.Proof.X25519.X86_64.Base
