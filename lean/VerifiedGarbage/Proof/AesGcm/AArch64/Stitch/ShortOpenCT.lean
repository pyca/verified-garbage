module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenSh
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Open
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.OpenCT
import VerifiedGarbage.Proof.AesGcm.AArch64.OpenToOne
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortCopy
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortOpen

/-!
# AES-GCM on AArch64, short records: `openShort` is constant time

Untrusted: everything here is checked by Lean. As `ShortCT.lean` for
`sealShort`: the head of `openShortA` by the taint analysis, the table and
the rest of `openShortA` (`openRestZ`) by the caller's `tb`; then
`openShortB` by the taint analysis with the result bit public (out of place,
with `dst` loaded from the working space, by the values both runs load),
which both runs agree on when they agree on whether the record opens
(`openShort_rel`). `openSelS_rel`: the rest of `openWithSG c to` after its
entry, generic over `to`; `openWithSh_ct` in place, `openToWithSh_ct` out of
place.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Taint VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- `openShortA` after the table. -/
abbrev openRestZ : Prog isa :=
  .seq (.block Stitch.zeroBufs)
  (.seq Stitch.textIn
  (.seq Stitch.ctToB2
  (.seq Stitch.aadIn
  (.seq (.block (Stitch.lensB ++ Stitch.shortGh ++ Stitch.shortCtr))
  (.seq (Impl.Gcm.AArch64.Stitch.byRounds Stitch.shortAes)
  (.seq (.block (Stitch.shortTagAt uO))
  (.seq cmp
    (.block [imm .x24 1, .sub .x .x24 .x24 .x10]))))))))

/-- The record opens exactly when the tags are equal. -/
theorem tagEqS_iff {Ctx Np A D Tg : Addr} {R al n tl : Nat} (hok : Spec.Gcm.tagLenOk tl = true) (s₀ : State) :
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) tl (bytesAt s₀.mem Np 12) (bytesAt s₀.mem D n)
      (bytesAt s₀.mem A al) (bytesAt s₀.mem Tg tl)).isSome = decide (tagEqS Ctx Np A D Tg R al n tl s₀) := by
  rw [Spec.Gcm.openResult, ite_eq_left hok, Spec.Gcm.decryptWith]
  by_cases h : tagEqS Ctx Np A D Tg R al n tl s₀
  · rw [ite_eq_left h, decide_eq_true h]; rfl
  · rw [ite_eq_right h, decide_eq_false h]; rfl

/-- `openShortG to`, in two runs from the state `open` (or `open_to`) leaves
once the received tag is at `W`, that agree on the arguments and on whether
the record opens, given its table and the rest of `openShortA` in two runs
that agree on `shRegs`. -/
theorem openShort_rel (gh : Gh8Ok) {tb : List Instr} {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R al n tl : Nat}
    {σ₁ σ₂ t₁ t₂ : State}
    (o₁ : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl σ₁ t₁) (o₂ : OpenInG to Ctx W SP Np A D O Tg R 12 al n tl σ₂ t₂)
    (hx₁ : t₁.gpr .x4 = A ∧ t₁.gpr .x5 = BitVec.ofNat 64 al ∧ t₁.gpr .x6 = D ∧ t₁.gpr .x7 = BitVec.ofNat 64 n)
    (hx₂ : t₂.gpr .x4 = A ∧ t₂.gpr .x5 = BitVec.ofNat 64 al ∧ t₂.gpr .x6 = D ∧ t₂.gpr .x7 = BitVec.ofNat 64 n)
    (h16 : al ≤ 16) (hhi : n ≤ 96)
    (rt₁ : bytesAt t₁.mem W tl = bytesAt σ₁.mem Tg tl) (rt₂ : bytesAt t₂.mem W tl = bytesAt σ₂.mem Tg tl)
    (hok : Spec.Gcm.tagLenOk tl = true)
    (hb : decide (tagEqS Ctx Np A D Tg R al n tl σ₁) = decide (tagEqS Ctx Np A D Tg R al n tl σ₂))
    (htb₁ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = σ₁.rd → u.wr = σ₁.wr →
      Frame [workR W, ⟨O, n⟩] σ₁.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH σ₁.mem Ctx) u))
    (htb₂ : ∀ u : State, Env Ctx (W + BitVec.ofNat 64 16) W SP u → u.rd = σ₂.rd → u.wr = σ₂.wr →
      Frame [workR W, ⟨O, n⟩] σ₂.mem u.mem → WP isa (.block tb) u (Stitch.TblPost W (ctxH σ₂.mem Ctx) u))
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = SP → v₂.sp = SP → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr → Frame [workR W, ⟨O, n⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr → Frame [workR W, ⟨O, n⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    RelCT isa (Eq2 t₁ t₂) (Impl.AesGcm.AArch64.Stitch.openShortG to tb) TT := by
  have L := o₁.lay
  obtain ⟨x4₁, x5₁, x6₁, x7₁⟩ := hx₁
  obtain ⟨x4₂, x5₂, x6₂, x7₂⟩ := hx₂
  have hJ₁ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₁.gpr (ctxH σ₁.mem Ctx) Np 12 t₁ :=
    ⟨o₁.env, fun _ _ => rfl, o₁.x23, o₁.x24, o₁.x26, o₁.x27, o₁.non, o₁.vals.2.1⟩
  have hJ₂ : J0In Ctx (W + BitVec.ofNat 64 16) W SP t₂.gpr (ctxH σ₂.mem Ctx) Np 12 t₂ :=
    ⟨o₂.env, fun _ _ => rfl, o₂.x23, o₂.x24, o₂.x26, o₂.x27, o₂.non, o₂.vals.2.1⟩
  have j0W : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W, ∃ r' ∈ [workR W, (⟨O, n⟩ : Region)], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  have F₁ : Frame [workR W, ⟨O, n⟩] σ₁.mem t₁.mem :=
    o₁.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entryFr_work to W r hr⟩
  have F₂ : Frame [workR W, ⟨O, n⟩] σ₂.mem t₂.mem :=
    o₂.fr.sub fun r hr => ⟨_, List.mem_cons_self .., entryFr_work to W r hr⟩
  refine (openShort_split to tb).symm.rel (rel_seq ?_ (openShortA_ok gh o₁ x4₁ x5₁ x6₁ x7₁ h16 hhi rt₁ hok htb₁)
    (openShortA_ok gh o₂ x4₂ x5₂ x6₂ x7₂ h16 hhi rt₂ hok htb₂) fun m₁ m₂ hm₁ hm₂ => ?_)
  · unfold openShortA Impl.AesGcm.AArch64.Stitch.shortPre
    refine RelCT.assoc' (rel_seq (rel_taint [.x4, .x5, .x6, .x7, .x19, .x20, .x21, .x23]
        (by rw [o₁.env.sp, o₂.env.sp])
        (by agree_tac [x4₁, x4₂, x5₁, x5₂, x6₁, x6₂, x7₁, x7₂, o₁.env.x19, o₂.env.x19, o₁.env.x20, o₂.env.x20,
          o₁.env.x21, o₂.env.x21, o₁.x23, o₂.x23]) ⟨_, by taint_decide⟩)
      (shortHead_ok L hJ₁ x4₁ x5₁ x6₁ x7₁ (by omega)) (shortHead_ok L hJ₂ x4₂ x5₂ x6₂ x7₂ (by omega))
      fun τ₁ τ₂ ⟨e₁, a₁, l₁, c₁, n₁, d₁, r₁, t₁', f₁, rd₁, wr₁⟩ ⟨e₂, a₂, l₂, c₂, n₂, d₂, r₂, t₂', f₂, rd₂, wr₂⟩ => ?_)
    refine RelCT.assoc' (htbrel τ₁ τ₂ e₁.sp e₂.sp (fun r hr => ?_) (by rw [rd₁, o₁.rd₀]) (by rw [wr₁, o₁.wr₀])
      (F₁.trans (f₁.sub j0W)) (by rw [rd₂, o₂.rd₀]) (by rw [wr₂, o₂.wr₀]) (F₂.trans (f₂.sub j0W)))
    simp only [shRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [e₁.x19, e₂.x19]
    · rw [e₁.x20, e₂.x20]
    · rw [e₁.x21, e₂.x21]
    · rw [r₁, r₂, o₁.x22, o₂.x22]
    · rw [l₁, l₂]
    · rw [c₁, c₂]
    · rw [n₁, n₂]
    · rw [d₁, d₂]
    · rw [t₁', t₂', o₁.x28, o₂.x28]
  · have x24₂ : m₂.gpr .x24 =
        BitVec.ofNat 64 (1 - if tagEqS Ctx Np A D Tg R al n tl σ₁ then 0 else 1) := by
      have hiff := decide_eq_decide.mp hb
      by_cases h : tagEqS Ctx Np A D Tg R al n tl σ₁
      · rw [hm₂.x24, ite_eq_left (hiff.mp h), ite_eq_left h]
      · rw [hm₂.x24, ite_eq_right (fun h' => h (hiff.mpr h')), ite_eq_right h]
    unfold openShortB
    cases to with
    | false =>
      exact rel_taint [.x19, .x24, .x25, .x26, .x27] (by rw [hm₁.env.sp, hm₂.env.sp])
        (by agree_tac [hm₁.env.x19, hm₂.env.x19, hm₁.x24, x24₂, hm₁.x25, hm₂.x25, hm₁.x26, hm₂.x26, hm₁.x27,
          hm₂.x27]) ⟨_, by taint_decide⟩
    | true =>
      have ou₁ : OutIn Ctx W D O n m₁ := hm₁.out
      have ou₂ : OutIn Ctx W D O n m₂ := hm₂.out
      have hlt : ∀ σ : State, (1 - if tagEqS Ctx Np A D Tg R al n tl σ then 0 else 1 : Nat) < 2 ^ 64 := fun _ => by
        split <;> decide
      have tm : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block [mov .x0 .x24]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      -- The output's address from the slot, and the plaintext's in `B₁`.
      have pl : ∀ {σ u : State}, ShortMid true Ctx W SP Np A D O Tg R al n tl σ u →
          WP isa (.block (Stitch.atP .x12 Stitch.b1O 1 ++ cond true ([.ldr .x .x11 .x19 dstO] : List Instr)
            [mov .x11 .x27] ++ [mov .x13 .x26])) u fun u' => u'.gpr .x11 = O ∧
            u'.gpr .x12 = W + BitVec.ofNat 64 (880 - 16 * ((n + 15) / 16)) ∧ u'.gpr .x13 = BitVec.ofNat 64 n ∧
            u'.sp = u.sp ∧ u'.gpr .x24 = u.gpr .x24 ∧ u'.rd = u.rd ∧ u'.wr = u.wr := fun {σ u} hm => by
        have he := hm.env
        have sO : u.mem.readW (W + BitVec.ofNat 64 320) 64 = O := (hm.out : OutIn Ctx W D O n u).sO
        rw [List.append_assoc, WP.block_append_iff]
        obtain ⟨t₂, run₂, x12t₂, g₂', m₂', _, sp₂', rd₂', wr₂'⟩ := Stitch.atP_ok (c := (n + 15) / 16) .x12
          Impl.AesGcm.AArch64.Stitch.b1O 1 (by decide) (by unfold Impl.AesGcm.AArch64.Stitch.b1O; omega) u he.x19
          hm.x25 (by decide)
        refine WP.of_runBlock ⟨t₂, run₂, ?_⟩
        have he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₂ := he.keep (fun r hr => g₂' r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)) sp₂' rd₂' wr₂'
        have q₃ := he₂.perm.wR (show 320 + 8 ≤ 2560 by decide)
        have e₃ : t₂.mem.read (W + 320#64) 8 = O := by
          rw [show t₂.mem.read (W + 320#64) 8 = t₂.mem.readW (W + BitVec.ofNat 64 320) 64 from rfl, m₂', sO]
        refine WP.run ⟨_, by arun [Bool.cond_true, he₂.x19, q₃, dstO], rfl⟩ fun u' hu' => ?_
        subst hu'
        refine ⟨by simp [gpr_write, e₃], ?_, by simp [gpr_write, g₂' .x26 (by decide), hm.x26], sp₂', ?_, rd₂', wr₂'⟩
        · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
          rw [x12t₂]; rfl
        · simp only [gpr_write, ite_true, ite_false, reduceCtorEq]
          exact g₂' _ (by decide)
      have wpE : ∀ {σ u : State}, ShortMid true Ctx W SP Np A D O Tg R al n tl σ u →
          WP isa (.ite (.zero .x .x24) (wipeG true) (Impl.AesGcm.AArch64.Stitch.plainOutG true)) u
            fun u' => u'.sp = SP ∧ u'.gpr .x24 = u.gpr .x24 := fun {σ u} hm => by
        have ou : OutIn Ctx W D O n u := hm.out
        refine WP.ite _ (eval_zero hm.x24 (hlt σ)) (fun _ => ?_) (fun _ => ?_)
        · exact WP.mono (wipeTo_ok hm.env ou.sO hm.sN ou.dw) fun _ ⟨_, _, g, sp, _, _⟩ =>
            ⟨sp.trans hm.env.sp, g _ (by decide) (by decide) (by decide)⟩
        · unfold Impl.AesGcm.AArch64.Stitch.plainOutG
          refine WP.seq (WP.mono (pl hm) fun _ ⟨x11, x12, x13, sp, x24, rd, wr⟩ =>
            WP.mono (Stitch.copyQ_ok _ ⟨x12, x11, x13, by omega,
              by rw [rd, wr]; exact covers_left (covers_off hm.env.perm.w (by omega) (by decide)),
              by rw [wr]; exact hm.ow.wr, (hm.ow.ok.w.sub_right (Lay.wSub (by omega))).symm⟩)
              fun _ ⟨_, g, sp', _, _⟩ => ⟨sp'.trans (sp.trans hm.env.sp), (g _ (by decide)).trans x24⟩)
      refine rel_seq (rel_ite (eval_zero hm₁.x24 (hlt σ₁)) (eval_zero x24₂ (hlt σ₁))
          (fun _ => wipeTo_rel hm₁.env hm₂.env ou₁.sO ou₂.sO hm₁.sN hm₂.sN) (fun _ => ?_))
        (wpE hm₁) (wpE hm₂)
        fun a b ⟨ea, xa⟩ ⟨eb, xb⟩ => rel_taint [.x24] (by rw [ea, eb]) (by agree_tac [xa, xb, hm₁.x24, x24₂]) tm
      unfold Impl.AesGcm.AArch64.Stitch.plainOutG
      have tq : ∃ h, (taint.check (Taint.ofRegs [.x11, .x12, .x13]) Stitch.copyQ h).isSome = true :=
        ⟨_, by taint_decide⟩
      refine rel_seq (rel_taint [.x19, .x25, .x26] (by rw [hm₁.env.sp, hm₂.env.sp])
          (by agree_tac [hm₁.env.x19, hm₂.env.x19, hm₁.x25, hm₂.x25, hm₁.x26, hm₂.x26]) ⟨_, by taint_decide⟩)
        (pl hm₁) (pl hm₂) fun a b ⟨x11a, x12a, x13a, spa, _⟩ ⟨x11b, x12b, x13b, spb, _⟩ =>
          rel_taint [.x11, .x12, .x13] (by rw [spa, spb, hm₁.env.sp, hm₂.env.sp])
            (by agree_tac [x11a, x11b, x12a, x12b, x13a, x13b]) tq

/-- The branch on the tag length failing, in two runs: 0 returned, and out of
place the output zeroed. -/
theorem failG_rel {to : Bool} {Ctx W SP Np A D O Tg : Addr} {R nl al n tl : Nat} {σ₁ σ₂ s₁ s₂ : State}
    (o₁ : OpenInG to Ctx W SP Np A D O Tg R nl al n tl σ₁ s₁) (o₂ : OpenInG to Ctx W SP Np A D O Tg R nl al n tl σ₂ s₂) :
    RelCT isa (Eq2 s₁ s₂) (.seq (.block [imm .x0 0]) (wipeG to)) TT := by
  cases to with
  | true => exact failTo_rel o₁ o₂
  | false => exact rel_taint [] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac []) ⟨_, by taint_decide⟩

/-- After the entry of `open` or `open_to` (`to`): `openSelS` in two runs that
agree on the arguments and on whether the record opens. -/
theorem openSelS_rel (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {to : Bool}
    {σ₁ σ₂ s₁ s₂ : State} {W O Tg : Addr} {tl : Nat}
    (o₁ : OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ s₁)
    (o₂ : OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ s₂)
    (x12₁ : s₁.gpr .x12 = Tg) (x12₂ : s₂.gpr .x12 = Tg)
    (k₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = σ₁.gpr r) (k₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₂.gpr r = σ₁.gpr r)
    (hb : (Spec.Gcm.openResult (ctxCiph σ₁.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat) (ctxH σ₁.mem (σ₁.gpr .x0)) tl
        (bytesAt σ₁.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        (bytesAt σ₁.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₁.mem Tg tl)).isSome =
      (Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat) (ctxH σ₂.mem (σ₁.gpr .x0)) tl
        (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
        (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₂.mem Tg tl)).isSome)
    (hgh₁ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = σ₁.rd → s'.wr = σ₁.wr → s'.sp = σ₁.sp →
      Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₁.mem s'.mem →
      WP isa cl s' (GhPost s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hgh₂ : ∀ (s' : State) {Y Dd S : Addr} {nb : Nat}, GhCall s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = σ₂.rd → s'.wr = σ₂.wr → s'.sp = σ₁.sp →
      Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₂.mem s'.mem →
      WP isa cl s' (GhPost s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat},
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb → GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) → s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htb₁ : TbForOP tb (σ₁.gpr .x0) W σ₁.sp O (σ₁.gpr .x7).toNat σ₁)
    (htb₂ : TbForOP tb (σ₁.gpr .x0) W σ₁.sp O (σ₁.gpr .x7).toNat σ₂)
    (htbrel : ∀ v₁ v₂ : State, v₁.sp = σ₁.sp → v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      (to = true → v₁.gpr .x15 = v₂.gpr .x15) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec to)) TT)
    (htbrelS : ∀ v₁ v₂ : State, v₁.sp = σ₁.sp → v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr → Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    RelCT isa (Eq2 s₁ s₂) (openSelS v.callees to tb cl true) TT := by
  have hdk := dataOk_of o₁.dat
  have hnb : (σ₁.gpr .x7).toNat + 2560 ≤ 2 ^ 64 := len_of_disjoint hdk.w hdk.wrap o₁.lay.ww
  -- The branch on the tag length, and then `m`.
  have rest : ∀ {m : Prog isa} {u₁ u₂ : State},
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ u₁ →
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ u₂ →
      u₁.gpr .x12 = Tg → u₂.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r) →
      (∀ {σ t : State}, OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg
          (σ₁.gpr .x1).toNat (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ t →
        (σ = σ₁ ∨ σ = σ₂) →
        bytesAt t.mem W tl = bytesAt σ.mem Tg tl → Spec.Gcm.tagLenOk tl = true →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = σ₁.gpr r) →
        WP isa m t (OpenPostG (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) O Tg (σ₁.gpr .x1).toNat
          (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl (bytesAt σ.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
          (fun m => bytesAt m O (σ₁.gpr .x7).toNat = cond to (List.replicate (σ₁.gpr .x7).toNat 0)
            (bytesAt σ.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)) σ)) →
      (∀ {t₁ t₂ : State}, OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg
          (σ₁.gpr .x1).toNat (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ t₁ →
        OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg
          (σ₁.gpr .x1).toNat (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ t₂ →
        bytesAt t₁.mem W tl = bytesAt σ₁.mem Tg tl → bytesAt t₂.mem W tl = bytesAt σ₂.mem Tg tl →
        Spec.Gcm.tagLenOk tl = true →
        (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t₂.gpr r = σ₁.gpr r) →
        RelCT isa (Eq2 t₁ t₂) m TT) →
      RelCT isa (Eq2 u₁ u₂) (.seq tagLenOk (.seq (.ite (.zero .x .x9) (.seq (.block [imm .x0 0]) (wipeG to))
        (.seq tagIn m)) (.block restore))) TT := fun {m u₁ u₂} p₁ p₂ y₁ y₂ kk₁ kk₂ hm hr =>
    openRestWithFl_rel (fl := .seq (.block [imm .x0 0]) (wipeG to)) (m := m)
      (C₁ := bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₁ := fun m => bytesAt m O (σ₁.gpr .x7).toNat = cond to (List.replicate (σ₁.gpr .x7).toNat 0)
        (bytesAt σ₁.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat))
      (C₂ := bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (F₂ := fun m => bytesAt m O (σ₁.gpr .x7).toNat = cond to (List.replicate (σ₁.gpr .x7).toNat 0)
        (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat))
      p₁ p₂ y₁ y₂ (fun o' _ _ hok => failG_ok o' hok) (fun o' _ _ hok => failG_ok o' hok)
      (fun q₁ q₂ _ => failG_rel q₁ q₂)
      (fun o' hT hok hx => hm o' (.inl rfl) hT hok fun r h => (hx r h).trans (kk₁ r h))
      (fun o' hT hok hx => hm o' (.inr rfl) hT hok fun r h => (hx r h).trans (kk₂ r h))
      fun q₁ q₂ rt₁ rt₂ hok hx₁ hx₂ => hr q₁ q₂ rt₁ rt₂ hok (fun r h => (hx₁ r h).trans (kk₁ r h))
        (fun r h => (hx₂ r h).trans (kk₂ r h))
  have regs : ∀ {t : State}, (∀ r ∈ [Reg.x4, .x5, .x6, .x7], t.gpr r = σ₁.gpr r) →
      t.gpr .x4 = σ₁.gpr .x4 ∧ t.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat ∧ t.gpr .x6 = σ₁.gpr .x6 ∧
        t.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := fun kt =>
    ⟨kt _ (by simp), by rw [kt _ (by simp), ofNat_toNat'], kt _ (by simp), by rw [kt _ (by simp), ofNat_toNat']⟩
  have hghσ : ∀ {σ : State}, (σ = σ₁ ∨ σ = σ₂) → ∀ (s' : State) {Y Dd S : Addr} {nb : Nat},
      GhCall s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR W) → Region.Sub ⟨S, 256⟩ (workR W) →
      s'.rd = σ.rd → s'.wr = σ.wr → s'.sp = σ₁.sp →
      Frame [workR W, ⟨O, (σ₁.gpr .x7).toNat⟩] σ.mem s'.mem →
      WP isa cl s' (GhPost s' (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb) := fun {σ} hσ => by
    rcases hσ with rfl | rfl
    · exact hgh₁
    · exact hgh₂
  have htbσ : ∀ {σ : State}, (σ = σ₁ ∨ σ = σ₂) → TbForOP tb (σ₁.gpr .x0) W σ₁.sp O (σ₁.gpr .x7).toNat σ :=
    fun {σ} hσ => by
      rcases hσ with rfl | rfl
      · exact htb₁
      · exact htb₂
  -- The three paths for TLS records.
  have fastP : ∀ {u₁ u₂ : State} (hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12),
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ u₁ →
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ u₂ →
      u₁.gpr .x12 = Tg → u₂.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r) →
      RelCT isa (Eq2 u₁ u₂) (Impl.AesGcm.AArch64.Fast.openFastPG v.callees to cl) TT :=
    fun hc p₁ p₂ y₁ y₂ kk₁ kk₂ => rest p₁ p₂ y₁ y₂ kk₁ kk₂
      (fun o' hσ hT hok hx => have e := regs hx
        openRunWithG_postE cl v hMK (ex := []) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 hT hok (by simp) (by simp)
          (by simp) fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hghσ hσ s' c sY sS hr hw hsp (frame_wD hf))
      fun q₁ q₂ rt₁ rt₂ hok hx₁ hx₂ => openRunWithG_relX v cl hMK (ex := []) (by simp) (by simp) (by simp)
        q₁ q₂ hc.2 (regs hx₁) (regs hx₂) hc.1 rt₁ rt₂ hok hb
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₁ s' c sY sS hr hw hsp (frame_wD hf))
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₂ s' c sY sS hr hw hsp (frame_wD hf))
        fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ (frame_wD f₁) r₂ w₂ (frame_wD f₂)
  have fastS : ∀ {u₁ u₂ : State} (hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12),
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ u₁ →
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ u₂ →
      u₁.gpr .x12 = Tg → u₂.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r) →
      RelCT isa (Eq2 u₁ u₂) (Impl.AesGcm.AArch64.Stitch.openFastSG v.callees to tb cl) TT :=
    fun hc p₁ p₂ y₁ y₂ kk₁ kk₂ => rest p₁ p₂ y₁ y₂ kk₁ kk₂
      (fun o' hσ hT hok hx => have e := regs hx
        WP.mono (openRunWithS_postX v cl hMK gh (ex := []) (I := fun _ => True) o' hc.2 e.1 e.2.1 e.2.2.1 e.2.2.2
          hc.1 hT hok (by simp) (by simp) (by simp) (by simp) (fun _ _ => trivial)
          (fun s' _ _ _ _ c sY sS hr hw hsp hf _ =>
            WP.mono (hghσ hσ s' c sY sS hr hw hsp hf) fun _ g => ⟨g, trivial⟩) (htbσ hσ).tbFor) fun _ q => q.1)
      fun q₁ q₂ rt₁ rt₂ hok hx₁ hx₂ => openRunWithS_relX v cl hMK gh (ex := []) (by simp) (by simp) (by simp)
        (by simp) q₁ q₂ hc.2 (regs hx₁) (regs hx₂) hc.1 rt₁ rt₂ hok hb
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₁ s' c sY sS hr hw hsp hf)
        (fun s' _ _ _ _ c sY sS hr hw hsp hf _ => hgh₂ s' c sY sS hr hw hsp hf)
        (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ _ => hrel c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
        htb₁.tbFor htb₂.tbFor htbrel
  have short : ∀ {u₁ u₂ : State} (hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12),
      (σ₁.gpr .x7).toNat ≤ 96 →
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₁ u₁ →
      OpenInG to (σ₁.gpr .x0) W σ₁.sp (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) O Tg (σ₁.gpr .x1).toNat
        (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat tl σ₂ u₂ →
      u₁.gpr .x12 = Tg → u₂.gpr .x12 = Tg →
      (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r) → (∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r) →
      RelCT isa (Eq2 u₁ u₂) (Impl.AesGcm.AArch64.Stitch.openShortFG to tb) TT :=
    fun hc h96 p₁ p₂ y₁ y₂ kk₁ kk₂ => by
      unfold Impl.AesGcm.AArch64.Stitch.openShortFG
      refine rest p₁ p₂ y₁ y₂ kk₁ kk₂ (fun o' hσ hT hok hx => have e := regs hx
          by rw [hc.2] at o' ⊢
             exact openShort_post gh o' e.1 e.2.1 e.2.2.1 e.2.2.2 hc.1 h96 hT hok
               fun u he hrd hwr hf => htbσ hσ u he hrd hwr hf)
        fun q₁ q₂ rt₁ rt₂ hok hx₁ hx₂ => ?_
      rw [hc.2] at q₁ q₂ hb
      exact openShort_rel gh q₁ q₂ (regs hx₁) (regs hx₂) hc.1 h96 rt₁ rt₂ hok
        (by rw [← tagEqS_iff hok, ← tagEqS_iff hok]; exact hb)
        (fun u he hrd hwr hf => htb₁ u he hrd hwr hf) (fun u he hrd hwr hf => htb₂ u he hrd hwr hf) htbrelS
  unfold openSelS
  have k5₁ : s₁.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₁ .x5 (by simp), ofNat_toNat']
  have k5₂ : s₂.gpr .x5 = BitVec.ofNat 64 (σ₁.gpr .x5).toNat := by rw [k₂ .x5 (by simp), ofNat_toNat']
  refine rel_seq (rel_taint [.x5, .x24] (by rw [o₁.env.sp, o₂.env.sp]) (by agree_tac [k5₁, k5₂, o₁.x24, o₂.x24])
      ⟨_, by taint_decide⟩)
    (cond_ok k5₁ (σ₁.gpr .x5).isLt o₁.x24 (σ₁.gpr .x3).isLt) (cond_ok k5₂ (σ₁.gpr .x5).isLt o₂.x24 (σ₁.gpr .x3).isLt)
    fun u₁ u₂ ⟨c₁, r₁⟩ ⟨c₂, r₂⟩ => ?_
  have v₁ := o₁.of_regs r₁
  have v₂ := o₂.of_regs r₂
  have y12₁ : u₁.gpr .x12 = Tg := by rw [r₁.others _ (by decide), x12₁]
  have y12₂ : u₂.gpr .x12 = Tg := by rw [r₂.others _ (by decide), x12₂]
  have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₁.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₁ r hr]
  have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], u₂.gpr r = σ₁.gpr r := fun r hr => by
    rw [r₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), k₂ r hr]
  have hlt : ((if (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 then 0 else 1 : Nat)) < 2 ^ 64 := by
    split <;> decide
  refine rel_ite (eval_zero c₁ hlt) (eval_zero c₂ hlt) (fun ht => ?_) (fun _ => ?_)
  · have hc : (σ₁.gpr .x5).toNat ≤ 16 ∧ (σ₁.gpr .x3).toNat = 12 := by
      by_contra hc; simp [hc] at ht
    simp only [↓reduceIte]
    have x7u₁ : u₁.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₁ .x7 (by simp), ofNat_toNat']
    have x7u₂ : u₂.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₂ .x7 (by simp), ofNat_toNat']
    -- `shortThr`, on the length, which is public.
    refine rel_seq (rel_taint [.x7] (by rw [v₁.env.sp, v₂.env.sp])
        (by agree_tac [kk₁ .x7 (by simp), kk₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
      (shortThr_ok u₁ x7u₁ (by omega)) (shortThr_ok u₂ x7u₂ (by omega)) fun w₁ w₂ ⟨y9₁, s₁'⟩ ⟨y9₂, s₂'⟩ => ?_
    have v₁ := v₁.of_regs s₁'
    have v₂ := v₂.of_regs s₂'
    have y12₁ : w₁.gpr .x12 = Tg := by rw [s₁'.others _ (by decide), y12₁]
    have y12₂ : w₂.gpr .x12 = Tg := by rw [s₂'.others _ (by decide), y12₂]
    have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [s₁'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₁ r hr]
    have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], w₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [s₂'.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₂ r hr]
    refine rel_ite (eval_zero y9₁ (by omega)) (eval_zero y9₂ (by omega)) (fun hz => ?_) (fun _ => ?_)
    · have h96 := of_decide_eq_true hz
      have x7w₁ : w₁.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₁ .x7 (by simp), ofNat_toNat']
      have x7w₂ : w₂.gpr .x7 = BitVec.ofNat 64 (σ₁.gpr .x7).toNat := by rw [kk₂ .x7 (by simp), ofNat_toNat']
      -- `shortMin`, on the length, which is public.
      refine rel_seq (rel_taint [.x7] (by rw [v₁.env.sp, v₂.env.sp])
          (by agree_tac [x7w₁, x7w₂]) ⟨_, by taint_decide⟩)
        (shortMin_ok w₁ x7w₁ (by omega)) (shortMin_ok w₂ x7w₂ (by omega)) fun z₁ z₂ ⟨m9₁, t₁⟩ ⟨m9₂, t₂⟩ => ?_
      have v₁ := v₁.of_regs t₁
      have v₂ := v₂.of_regs t₂
      have y12₁ : z₁.gpr .x12 = Tg := by rw [t₁.others _ (by decide), y12₁]
      have y12₂ : z₂.gpr .x12 = Tg := by rw [t₂.others _ (by decide), y12₂]
      have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₁.gpr r = σ₁.gpr r := fun r hr => by
        rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₁ r hr]
      have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₂.gpr r = σ₁.gpr r := fun r hr => by
        rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₂ r hr]
      exact rel_ite (eval_zero m9₁ (by omega)) (eval_zero m9₂ (by omega))
        (fun _ => fastP hc v₁ v₂ y12₁ y12₂ kk₁ kk₂) (fun _ => short hc (by omega) v₁ v₂ y12₁ y12₂ kk₁ kk₂)
    -- `thr`, on the length, which is public.
    refine rel_seq (rel_taint [.x7] (by rw [v₁.env.sp, v₂.env.sp])
        (by agree_tac [kk₁ .x7 (by simp), kk₂ .x7 (by simp)]) ⟨_, by taint_decide⟩)
      (Stitch.thr_ok w₁) (Stitch.thr_ok w₂) fun z₁ z₂ ⟨x9₁, t₁⟩ ⟨x9₂, t₂⟩ => ?_
    have e9 : z₂.gpr .x9 = BitVec.ofNat 64 (z₁.gpr .x9).toNat := by
      rw [ofNat_toNat', x9₁, x9₂, kk₁ .x7 (by simp), kk₂ .x7 (by simp)]
    have v₁ := v₁.of_regs t₁
    have v₂ := v₂.of_regs t₂
    have y12₁ : z₁.gpr .x12 = Tg := by rw [t₁.others _ (by decide), y12₁]
    have y12₂ : z₂.gpr .x12 = Tg := by rw [t₂.others _ (by decide), y12₂]
    have kk₁ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₁.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₁.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₁ r hr]
    have kk₂ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], z₂.gpr r = σ₁.gpr r := fun r hr => by
      rw [t₂.others r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide), kk₂ r hr]
    exact rel_ite (eval_zero (a := (z₁.gpr .x9).toNat) (by rw [ofNat_toNat']) (z₁.gpr .x9).isLt)
      (eval_zero e9 (z₁.gpr .x9).isLt) (fun _ => fastP hc v₁ v₂ y12₁ y12₂ kk₁ kk₂)
      (fun _ => fastS hc v₁ v₂ y12₁ y12₂ kk₁ kk₂)
  · unfold openRestG
    exact rest v₁ v₂ y12₁ y12₂ kk₁ kk₂ (fun o' _ hT hok _ => openMainG_post v to o' hT hok)
      fun q₁ q₂ rt₁ rt₂ hok _ _ => openMainG_rel v to q₁ q₂ rt₁ rt₂ hok hb

/-- `vg_aes_gcm_open` with the interleaved path and the path for short
records, `work` the stack argument `w`, is constant time, for a `cl` that
hashes as `vg_ghash` and leaks the same in two runs, called with memory
changed since the entry only in the working space and the text, and a `tb`
that writes the table and leaks the same in two runs. -/
theorem openWithSh_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 2 ∨ w = 3)
    {pre : State → Prop} {extra : State → List Region} (hpre : ∀ s, pre s → openPreXW w (extra s) s)
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨σ.gpr .x6, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htbP : ∀ {σ : State}, pre σ → TbForOP tb (σ.gpr .x0) (stackArg σ w) σ.sp (σ.gpr .x6) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) Impl.Gcm.AArch64.Stitch.dec) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨σ₁.gpr .x6, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openLeakOf s₁ = openLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees false w tb cl true) := by
  rw [openWithSG_eq, show openEntryG false w = oneEntry (8 * w) ++ stashArg 8 ++ ([.ldrSp .x12 0] : List Instr) by
    simp only [openEntryG, Bool.cond_false, List.append_nil]]
  refine open_ct_ofW hw hpre fun {σ₁ σ₂ s₁ s₂} p₁ p₂ hq o₁ o₂ x12₁ x12₂ k₁ k₂ hb => ?_
  have hq₀ := hq
  obtain ⟨q0, -, -, -, -, -, q6, q7, qsp, qa⟩ := hq
  have hgh₂ := @hgh σ₂
  rw [← q0, ← qa w (by omega), ← q6, ← q7] at hgh₂
  have htb₂ := htbP p₂
  rw [← q0, ← qa w (by omega), ← q6, ← q7, ← qsp] at htb₂
  exact openSelS_rel v cl hMK gh o₁ o₂ x12₁ x12₂ k₁ k₂ hb
    (fun s' _ _ _ _ c sY sS hr hw hsp hf => hgh p₁ c sY sS hr hw hsp hf)
    (fun s' _ _ _ _ c sY sS hr hw hsp hf => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf)
    (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    (htbP p₁) htb₂
    (fun v₁ v₂ sp₁ sp₂ hr _ r₁ w₁ f₁ r₂ w₂ f₂ => htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂)
    (fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrelS p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂)

/-- `vg_aes_gcm_open_to` with the interleaved path and the path for short
records, `work` the stack argument `w`, in one pass, is constant time, as
`openWithSh_ct`, with memory changed since the entry only in the working
space and `dst`. -/
theorem openToWithSh_ct (v : GcmImpl) (cl : Prog isa) (hMK : MulKey) (gh : Gh8Ok) {tb : List Instr} {w : Nat}
    (hw : w = 4 ∨ w = 5)
    {pre : State → Prop} {extra extraW : State → List Region}
    (hpre : ∀ s, pre s → openToPreXW w (extra s) s (extraW s))
    (hgh : ∀ {σ s : State} {Y Dd S : Addr} {nb : Nat}, pre σ →
      GhCall s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ w)) →
      s.rd = σ.rd → s.wr = σ.wr → s.sp = σ.sp →
      Frame [workR (stackArg σ w), ⟨stackArg σ 0, (σ.gpr .x7).toNat⟩] σ.mem s.mem →
      WP isa cl s (GhPost s (σ.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb))
    (hrel : ∀ {σ₁ σ₂ s₁ s₂ : State} {Y Dd S : Addr} {nb : Nat}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ →
      GhCall s₁ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      GhCall s₂ (σ₁.gpr .x0 + BitVec.ofNat 64 240) Y Dd S nb →
      Region.Sub ⟨Y, 16⟩ (workR (stackArg σ₁ w)) → Region.Sub ⟨S, 256⟩ (workR (stackArg σ₁ w)) →
      s₁.sp = σ₁.sp → s₂.sp = σ₁.sp →
      s₁.rd = σ₁.rd → s₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₁.mem s₁.mem →
      s₂.rd = σ₂.rd → s₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₂.mem s₂.mem →
      RelCT isa (Eq2 s₁ s₂) cl TT)
    (htbP : ∀ {σ : State}, pre σ → TbForOP tb (σ.gpr .x0) (stackArg σ w) σ.sp (stackArg σ 0) (σ.gpr .x7).toNat σ)
    (htbrel : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ stRegs, v₁.gpr r = v₂.gpr r) → v₁.gpr .x15 = v₂.gpr .x15 →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) (Impl.Gcm.AArch64.Stitch.dec true)) TT)
    (htbrelS : ∀ {σ₁ σ₂ : State}, pre σ₁ → pre σ₂ → onePub (w + 1) σ₁ σ₂ → ∀ v₁ v₂ : State, v₁.sp = σ₁.sp →
      v₂.sp = σ₁.sp → (∀ r ∈ shRegs, v₁.gpr r = v₂.gpr r) →
      v₁.rd = σ₁.rd → v₁.wr = σ₁.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₁.mem v₁.mem →
      v₂.rd = σ₂.rd → v₂.wr = σ₂.wr →
      Frame [workR (stackArg σ₁ w), ⟨stackArg σ₁ 0, (σ₁.gpr .x7).toNat⟩] σ₂.mem v₂.mem →
      RelCT isa (Eq2 v₁ v₂) (.seq (.block tb) openRestZ) TT) :
    ConstantTime isa pre (fun s₁ s₂ => onePub (w + 1) s₁ s₂ ∧ openToLeakOf s₁ = openToLeakOf s₂)
      (Impl.AesGcm.AArch64.Stitch.openWithSG v.callees true w tb cl true) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hpre _ p₁
  have h₂ := hpre _ p₂
  have hq₀ := hq.1
  obtain ⟨hq, hres⟩ := hq
  have T₁ := openToLay h₁
  have T₂ := openToLay h₂
  have hR₁ : rounds (σ₁.gpr .x1) := T₁.rounds
  have hR₂ : rounds (σ₂.gpr .x1) := T₂.rounds
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have qw : stackArg σ₁ w = stackArg σ₂ w := qa w (by omega)
  have qd : stackArg σ₁ 0 = stackArg σ₂ 0 := qa 0 (by omega)
  have qg : stackArg σ₁ 2 = stackArg σ₂ 2 := qa 2 (by omega)
  have qt : stackArg σ₁ 3 = stackArg σ₂ 3 := qa 3 (by omega)
  have ka : (Code.block (openEntryG true w) : Prog isa).allInstrs
      (fun i => [Reg.x4, .x5, .x6, .x7].all fun r => !clobbers i r) = true := by
    rcases hw with rfl | rfl <;> decide
  have kc : (Code.block (openEntryG true w) : Prog isa).noCalls = true := by
    rcases hw with rfl | rfl <;> decide
  have kq : ∀ r ∈ [Reg.x4, .x5, .x6, .x7], σ₂.gpr r = σ₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact q4.symm
    · exact q5.symm
    · exact q6.symm
    · exact q7.symm
  rw [openWithSG_eq]
  refine rel_seq (openEntryTo_rel hw T₁ T₂ qw qsp (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7]))
    (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega) h₁) ka kc)
    (WP.gprs (rs := [.x4, .x5, .x6, .x7]) (openEntryTo_ok (by omega) h₂) ka kc)
    fun s₁ s₂ ⟨⟨o₁, x12₁⟩, k₁⟩ ⟨⟨o₂, x12₂⟩, k₂⟩ => ?_
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qsp, ← qw, ← qd, ← qg, ← qt] at o₂
  rw [← qg] at x12₂
  have hb : (openToRes σ₁).isSome = (openToRes σ₂).isSome := by
    rw [openToLeakOf, openToLeakOf, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₁)),
      ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hR₂))] at hres
    revert hres; cases (openToRes σ₁).isSome <;> cases (openToRes σ₂).isSome <;> simp
  have hr₂ : openToRes σ₂ = Spec.Gcm.openResult (ctxCiph σ₂.mem (σ₁.gpr .x0) (σ₁.gpr .x1).toNat)
      (ctxH σ₂.mem (σ₁.gpr .x0)) (stackArg σ₁ 3).toNat
      (bytesAt σ₂.mem (σ₁.gpr .x2) (σ₁.gpr .x3).toNat) (bytesAt σ₂.mem (σ₁.gpr .x6) (σ₁.gpr .x7).toNat)
      (bytesAt σ₂.mem (σ₁.gpr .x4) (σ₁.gpr .x5).toNat) (bytesAt σ₂.mem (stackArg σ₁ 2) (stackArg σ₁ 3).toNat) := by
    unfold openToRes; rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qt, ← qg]
  rw [hr₂] at hb
  simp only [openToRes] at hb
  have hgh₂ := @hgh σ₂
  rw [← q0, ← qw, ← qd, ← q7] at hgh₂
  have htb₂ := htbP p₂
  rw [← q0, ← qw, ← qd, ← q7, ← qsp] at htb₂
  exact openSelS_rel v cl hMK gh o₁ o₂ x12₁ x12₂ k₁ (fun r hr => (k₂ r hr).trans (kq r hr)) hb
    (fun s' _ _ _ _ c sY sS hr hw hsp hf => hgh p₁ c sY sS hr hw hsp hf)
    (fun s' _ _ _ _ c sY sS hr hw hsp hf => hgh₂ p₂ c sY sS hr hw (hsp.trans qsp) hf)
    (fun c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂ => hrel p₁ p₂ hq₀ c₁ c₂ sY sS sp₁ sp₂ r₁ w₁ f₁ r₂ w₂ f₂)
    (htbP p₁) htb₂
    (fun v₁ v₂ sp₁ sp₂ hr h15 r₁ w₁ f₁ r₂ w₂ f₂ => htbrel p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr (h15 rfl) r₁ w₁ f₁ r₂ w₂ f₂)
    (fun v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂ => htbrelS p₁ p₂ hq₀ v₁ v₂ sp₁ sp₂ hr r₁ w₁ f₁ r₂ w₂ f₂)

end VG.Proof.AesGcm.AArch64.Fast
