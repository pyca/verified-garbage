module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT

/-!
# AES-GCM `seal_split`'s path for TLS records, in two runs

Untrusted: everything here is checked by Lean. Two runs test the same public
lengths (`cond_rel`), so take the same path: `other`, or `Fast.run`, whose
additional data `aad` addresses memory from the environment's registers, the
nonce's pointer and, once they are loaded, the additional data's pointer and
length, which are public (`aad_rel`), and whose end takes the same branch in
both (`fbody_rel`): `sel_rel`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Fast

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.Fast (aadPad aadMul aadReg aadFull aadMulR aadSome)
open VG.Proof.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64.Split
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel condS_of rel_next rel_piece keepsEnv)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

variable {any : Bool}

/-- Before `aad`. -/
def A0 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (Np : Addr)
    (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 12 ∧
    DataOk (W + BitVec.ofNat 64 16) W SP s Np 12

/-- After `j012`. -/
def A1 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  ∃ (H : Block) (iv : List Byte) (σ : State), J0Mid Ctx (W + BitVec.ofNat 64 16) W SP H iv σ.mem s ∧
    OneS M Ctx W SP R A al D n none σ ∧ s.rd = σ.rd ∧ s.wr = σ.wr

/-- After the additional data's length is tested. -/
def A3 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 0))

/-- After the additional data's length is compared with 5. -/
def A5 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 5))

/-- After the additional data's length is compared with 16. -/
def A16 (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  OneS M Ctx W SP R A al D n none s ∧ s.gpr .rcx = BitVec.ofNat 64 al ∧ s.zf = some (decide (al = 16))

theorem envRegs_mem {r : Reg} (hr : r ∈ [Reg.r12, .r13, .r14, .r15, .rsp]) : r = .r12 ∨ r ∈ [Reg.r13, .r14, .r15, .rsp] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

section
variable {M : CtxMode} {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP) {R : Nat} {Np A D : Addr}
  {al n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (h16 : al ≤ 16)
include L hDW h16

/-- `aad` in two runs: the same addresses and branches. -/
theorem aad_rel :
    RelCT isa (fun s₁ s₂ => A0 M Ctx W SP R A al D n Np s₁ ∧ A0 M Ctx W SP R A al D n Np s₂)
      Impl.AesGcm.X86_64.Fast.aad fun _ _ => True := by
  have empty := rel_taint (P := fun _ _ => True) (c := .block []) [] (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  -- `j012`.
  have w₁ : ∀ s, A0 M Ctx W SP R A al D n Np s → WP isa (.block j012) s (A1 M Ctx W SP R A al D n) := fun s h =>
    WP.mono (WP.with_rdwr (j012_ok L ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩)) fun _ ⟨o, hrd, hwr⟩ =>
      ⟨_, _, s, o, h.1, hrd, hwr⟩
  have r₁ := rel_next (rel_taint (P := fun s₁ s₂ => A0 M Ctx W SP R A al D n Np s₁ ∧ A0 M Ctx W SP R A al D n Np s₂)
      [.r12, .r13, .r14, .r15, .rsp] (fun _ _ h r hr => by
        rcases envRegs_mem hr with rfl | hr
        · rw [h.1.2.1, h.2.2.1]
        · exact env_agree h.1.1.env h.2.1.env r hr) ⟨_, by taint_decide⟩) w₁ w₁
  -- `initState`.
  have w₂ : ∀ s, A1 M Ctx W SP R A al D n s → WP isa (.block initState) s (OneS M Ctx W SP R A al D n none) :=
    fun s ⟨_, _, σ, j, O, hrd, hwr⟩ => WP.mono (WP.with_rdwr (initState_ok L j)) fun _ ⟨o, hrd', hwr'⟩ =>
      O.frame L o.env (hrd'.trans hrd) (hwr'.trans hwr) hDW (w_one (j0Frame_one o.frame))
  have r₂ := rel_next (rel_taint (P := fun s₁ s₂ => A1 M Ctx W SP R A al D n s₁ ∧ A1 M Ctx W SP R A al D n s₂)
      [.r13, .r14, .r15, .rsp] (fun _ _ h => by
        obtain ⟨⟨_, _, _, j₁, -⟩, ⟨_, _, _, j₂, -⟩⟩ := h
        exact env_agree j₁.env j₂.env) ⟨_, by taint_decide⟩) w₂ w₂
  -- The additional data's length tested.
  have w₃ : ∀ s, OneS M Ctx W SP R A al D n none s →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)]) s
        (A3 M Ctx W SP R A al D n) := fun s O => by
    have he := O.env
    have h15 := he.r15
    have q₂ := he.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have hal := O.alen
    have hlt := O.dA.lt
    obtain ⟨s₃, run₃, hcx₃, hzf₃, hg₃, hm₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
        [.mov .rcx (.mem (at_ .r15 alenO)), .alu .test .rcx (.reg .rcx)] s = some s₃ ∧
        s₃.gpr .rcx = BitVec.ofNat 64 al ∧ s₃.zf = some (decide (al = 0)) ∧
        (∀ r, r ≠ .rcx → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hal]
      · simp only [zf_arithFlags, gpr_setReg, ite_true, hal]; rw [and_self_beq (by omega)]
      · intro r h; simp [gpr_setReg, h]
      all_goals rfl
    have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₃ := he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hrd₃ hwr₃
    exact WP.of_runBlock ⟨s₃, run₃, O.frame L he₃ hrd₃ hwr₃ hDW (by rw [hm₃]; exact Frame.refl _ _), hcx₃, hzf₃⟩
  have r₃ := rel_next (rel_taint (P := fun s₁ s₂ => OneS M Ctx W SP R A al D n none s₁ ∧
      OneS M Ctx W SP R A al D n none s₂) [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.env h.2.env)
      ⟨_, by simp only [alenO]; taint_decide⟩) w₃ w₃
  -- The additional data padded in `T`, and multiplied.
  have r₄ : RelCT isa (fun s₁ s₂ => A3 M Ctx W SP R A al D n s₁ ∧ A3 M Ctx W SP R A al D n s₂)
      (.ite .e (.block []) aadSome) fun _ _ => True := by
    refine rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2]) (empty.mono (fun _ _ _ => trivial) fun _ _ h => h)
      (StreamTo.RelCT.of_imp (1 ≤ al) (fun _ _ h => by
        have e := h.1.1.2.2.symm.trans h.2
        simp only [Option.some.injEq, decide_eq_false_iff_not] at e
        omega) fun h1 => ?_)
    -- The length compared with 5.
    have w₅ : ∀ s, A3 M Ctx W SP R A al D n s →
        WP isa (.block [.alu .cmp .rcx (imm 5)]) s (A5 M Ctx W SP R A al D n) := fun s h => by
      obtain ⟨t, run, zf, -, g, m, rd, wr⟩ := cmpImm_ok s .rcx h.2.1 h.1.dA.lt (show 5 < 2 ^ 31 by decide)
      have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.1.env.keep (fun r _ => by rw [g]) rd wr
      exact WP.of_runBlock ⟨t, run, h.1.frame L he rd wr hDW (by rw [m]; exact Frame.refl _ _),
        by rw [g]; exact h.2.1, zf⟩
    have r₅ := rel_next (rel_taint (P := fun s₁ s₂ => A3 M Ctx W SP R A al D n s₁ ∧ A3 M Ctx W SP R A al D n s₂)
      [.rcx] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1]) ⟨_, by taint_decide⟩) w₅ w₅
    -- Five bytes, from a register.
    have hr : ∀ s, A5 M Ctx W SP R A al D n s →
        WP isa (.block [.mov .rsi (.mem (at_ .r15 aadO))]) s fun t => t.gpr .rsi = A := fun s h => by
      have q := h.1.env.perm.wR (show 232 + 8 ≤ 2560 by decide)
      have h15 := h.1.env.r15
      have ha := h.1.aad
      obtain ⟨t, run, ht⟩ : ∃ t, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s = some t ∧ t.gpr .rsi = A := by
        refine ⟨_, by xrun [h15, q], ?_⟩
        simp [gpr_setReg, ha]
      exact WP.of_runBlock ⟨t, run, ht⟩
    have reg := rel_piece (F₁ := A5 M Ctx W SP R A al D n) (F₂ := A5 M Ctx W SP R A al D n)
      (c := .block (aadReg ++ aadMulR)) [.rsi] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [aadO]; taint_decide⟩ hr hr (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) ⟨_, by taint_decide⟩
    -- The length compared with 16.
    have w₁₆ : ∀ s, A5 M Ctx W SP R A al D n s →
        WP isa (.block [.alu .cmp .rcx (imm 16)]) s (A16 M Ctx W SP R A al D n) := fun s h => by
      obtain ⟨t, run, zf, -, g, m, rd, wr⟩ := cmpImm_ok s .rcx h.2.1 h.1.dA.lt (show 16 < 2 ^ 31 by decide)
      have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.1.env.keep (fun r _ => by rw [g]) rd wr
      exact WP.of_runBlock ⟨t, run, h.1.frame L he rd wr hDW (by rw [m]; exact Frame.refl _ _),
        by rw [g]; exact h.2.1, zf⟩
    have r₁₆ := rel_next (rel_taint (P := fun s₁ s₂ => A5 M Ctx W SP R A al D n s₁ ∧ A5 M Ctx W SP R A al D n s₂)
      [.rcx] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1]) ⟨_, by taint_decide⟩) w₁₆ w₁₆
    -- Sixteen bytes, loaded whole.
    have hr₁₆ : ∀ s, A16 M Ctx W SP R A al D n s →
        WP isa (.block [.mov .rsi (.mem (at_ .r15 aadO))]) s fun t => t.gpr .rsi = A := fun s h => by
      have q := h.1.env.perm.wR (show 232 + 8 ≤ 2560 by decide)
      have h15 := h.1.env.r15
      have ha := h.1.aad
      obtain ⟨t, run, ht⟩ : ∃ t, runBlock isa [.mov .rsi (.mem (at_ .r15 aadO))] s = some t ∧ t.gpr .rsi = A := by
        refine ⟨_, by xrun [h15, q], ?_⟩
        simp [gpr_setReg, ha]
      exact WP.of_runBlock ⟨t, run, ht⟩
    have full := rel_piece (F₁ := A16 M Ctx W SP R A al D n) (F₂ := A16 M Ctx W SP R A al D n)
      (c := .block (aadFull ++ aadMulR)) [.rsi] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [aadO]; taint_decide⟩ hr₁₆ hr₁₆ (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) ⟨_, by taint_decide⟩
    -- Any other length, padded in `T`, and multiplied.
    have hw : ∀ s, A16 M Ctx W SP R A al D n s →
        WP isa (.block (([.mov32 .rax (imm 0), .store (at_ .r15 tO) .rax, .store (at_ .r15 (tO + 8)) .rax] :
          List Instr) ++ ptr .rdi .r15 tO ++ ([.mov .rsi (.mem (at_ .r15 aadO))] : List Instr))) s
          fun t => t.gpr .rsi = A ∧ t.gpr .rdi = W + BitVec.ofNat 64 96 ∧ t.gpr .rcx = BitVec.ofNat 64 al :=
      fun s h => WP.mono (aadPadHead_ok L h.1.env h.1.dA h1 h16 h.1.aad h.2.1) fun _ ⟨_, _, _, _, lp⟩ =>
        ⟨lp.rsi, lp.rdi, lp.rcx⟩
    have pad := rel_piece (F₁ := A16 M Ctx W SP R A al D n) (F₂ := A16 M Ctx W SP R A al D n) (c := copyLoop)
      [.rsi, .rdi, .rcx] (fun _ h => h.1.env) (fun _ h => h.1.env) (keepsEnv (by decide +kernel))
      ⟨_, by simp only [tO, aadO, ptr]; taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩
    have wp : ∀ s, A16 M Ctx W SP R A al D n s → WP isa aadPad s (Env Ctx (W + BitVec.ofNat 64 16) W SP) :=
      fun s h => WP.mono (aadPad_ok L h.1.env h.1.dA h1 h16 h.1.aad h.2.1) fun _ g => g.1
    have pad' := rel_next (c := aadPad) (by unfold aadPad; exact pad) wp wp
    have mul := rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) (c := .block aadMul) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩
    have some := RelCT.seq r₅ (rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2])
      (reg.mono (fun _ _ h => h.1) fun _ _ h => h) ((RelCT.seq r₁₆ (rel_ite_e (fun _ _ h => by rw [h.1.2.2, h.2.2.2])
        (full.mono (fun _ _ h => h.1) fun _ _ h => h) ((RelCT.seq pad' mul).mono (fun _ _ h => h.1) fun _ _ h => h))).mono
        (fun _ _ h => h.1) fun _ _ h => h))
    unfold aadSome
    exact some.mono (fun _ _ h => h.1) fun _ _ h => h
  unfold Impl.AesGcm.X86_64.Fast.aad
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))

end

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sel_rel (v : GcmImpl) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared) (hF : ShortFacts)
    {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {fin : Prog isa} (hfr : FinRel CtxMode.prepared fin)
    {other : Prog isa} (ho : MidRel CtxMode.prepared other) :
    MidRel CtxMode.prepared (Impl.AesGcm.X86_64.Fast.sel (v.withBlk B) T.fn ks fin other any) := by
  intro s₀ s₀' Ctx W SP Np A D S T' nl al n sl R C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.Fast.sel
  have hw : ∀ {s₀ : State} (C : SplitCtx s₀ Ctx W SP Np A D S T' nl al n sl), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, SEntry s₀ Ctx W SP A D S n sl s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        SEntry s₀ Ctx W SP A D S n sl u :=
    fun C hnl hal s h => WP.mono (condE_ok C.toOneCtx h.toOneEntry hnl hal) fun _ ⟨z, E, K⟩ =>
      ⟨z, E, by rw [K.mem]; exact h.src, by rw [K.mem]; exact h.slen⟩
  have c := rel_next (cond_rel (F₁ := SEntry s₀ Ctx W SP A D S n sl) (F₂ := SEntry s₀' Ctx W SP A D S n sl)
      (fun _ h => condS_of h.toOneEntry hnl hal) (fun _ h => condS_of h.toOneEntry hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    have a := (aad_rel L C.dE (M := CtxMode.prepared) (R := R) (Np := Np) (A := A) (al := al) (by omega)).mono
      (P' := fun (s₁ s₂ : State) => SEntry s₀ Ctx W SP A D S n sl s₁ ∧ SEntry s₀' Ctx W SP A D S n sl s₂)
      (fun _ _ g => ⟨g.1.toOneEntry.aadPre C.toOneCtx X hNp hnl hal hR,
        g.2.toOneEntry.aadPre C'.toOneCtx X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial
    exact (splitRun_rel_of_midB T (fbody_rel hks hkr B hfr) C C' X X' kM hNp hnl hal hR hNp' hnl' hal' hR' a
      (fun s E => aad_mid hF C.toOneCtx X E.toOneEntry hNp hnl hal (by omega))
      (fun s E => aad_mid hF C'.toOneCtx X' E.toOneEntry hNp' hnl' hal' (by omega))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.Fast
