module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
public import VerifiedGarbage.Proof.Framework.TaintRel
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
meta import VerifiedGarbage.Proof.Framework.TaintRel
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore

/-!
# Montgomery multiplication on PPC64LE: the kernel's summary for constant time

The callers' analyses use the kernel's relational summary (`kernelSum`,
`Proof/Framework/TaintRel.lean`) in place of analysing its code at every
call: from states that agree on at least `kernelPre`, the call of the kernel
leaks the same trace and leaves `kernelPost` public, and also what was public
of the callers' registers (`kernelKeep`).

The kernel's body (`kernelBody`) is checked by the taint analysis, which
cannot follow its saves to vector registers (`kernelSave`, `kernelRestore`):
the summary's proof runs the analysis over the body only, from what the call
leaves public of `kernelPre` (`kernelPreC`), and treats the saves and
restores itself (`kernel_run`: they leak nothing and write only the vector
registers, and the saved registers). The callers' registers keep their
values on every run (`kernel_keeps`), the saved ones because the body writes
no vector register (`Exec.vpr`): so what was public of them stays public.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum.PPC64LE

/-- The registers both of `a` and `b` say are public. -/
def regUnion (a b : T) : T := ⟨a.bits ||| b.bits⟩

theorem mem_regUnion {a b : T} {r : Reg} : r ∈ regUnion a b ↔ r ∈ a ∨ r ∈ b := by
  rw [RegSet.mem_iff, RegSet.mem_iff, RegSet.mem_iff]
  show (a.bits ||| b.bits).testBit _ = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true]

/-- What the kernel needs public: `2 w` and the bases. -/
def kernelPre : T := ofRegs [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- What the kernel's analysis from `kernelPre` leaves public. -/
def kernelPost : T := ofRegs [.r3, .r5, .r6, .r7, .r8, .r9, .r11, .r15, .r16, .r17]

/-- The callers' registers: the kernel writes only `kernelSaved`'s, which it
restores, and the call none. -/
def kernelKeep : T := ofRegs [.r2, .r5, .r10, .r21, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The callers' registers that no instruction of the kernel writes. -/
def kernelKeepW : T := ofRegs [.r5, .r21]

/-- The call of the kernel, its code and its summary. -/
def kernelCall : Prog isa := .call kernelName kernel

def kernelSum : VG.Taint.RSum isa taint.T where
  code := kernelCall
  pre := kernelPre
  post τ := regUnion (τ.inter kernelKeep) kernelPost

/-- What the call leaves public of `kernelPre` (`taint.call`). -/
def kernelPreC : T := ((kernelPre.erase .r0).erase .r11).erase .r12

theorem kernel_keep_all : (instrs kernelCall).all (fun i => match dstOf i with
    | some d => !kernelKeepW.mem d
    | none => true) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem kernel_keep : ∀ i ∈ instrs kernelCall, ∀ r ∈ kernelKeepW, dstOf i ≠ some r := fun i hi r hr e => by
  have := List.all_eq_true.mp kernel_keep_all i hi
  rw [e] at this
  have h2 : kernelKeepW.mem r = false := by simpa using this
  exact Bool.false_ne_true (h2.symm.trans hr)

theorem kernel_check : ∃ hc, (taint.check kernelPreC kernelBody hc).map (kernelPost.subset ·) = some true :=
  ⟨_, by taint_decide⟩

theorem block_post {is : List Instr} {s s' : State} {t : List Leak} {Q : State → Prop}
    (hw : WP isa (.block is) s Q) (h : execBlock isa is s = some (s', t)) : Q s' := by
  obtain ⟨t', s'', he, hq⟩ := hw
  cases he with
  | block h' => rw [h] at h'; cases h'; exact hq

theorem execBlock_noLeaks {is : List Instr} (hc : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {s s' : State}
    {t : List Leak} (h : execBlock isa is s = some (s', t)) : t = [] := by
  induction is generalizing s t with
  | nil => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have e : addrs i s = [] := hc i (List.mem_cons_self ..) s
    rw [e, ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2]; rfl

/-- One run of the kernel's call: the call, the saves (no leak, the registers
unchanged, the saved ones in their vector registers), the body, the restores
(no leak, only the saved registers written, from their vector registers),
the return. -/
theorem kernel_run {s s' : State} {t : List Leak} (e : Exec isa kernelCall s t s') :
    ∃ c x tb y d, isa.call s = some c ∧ (∀ r, x.gpr r = c.gpr r) ∧ x.sp = c.sp ∧
      (∀ p ∈ kernelSaved, vdword (x.vpr p.1) 0 = c.gpr p.2) ∧ Exec isa kernelBody x tb y ∧
      (∀ r, r ∉ kernelSaved.map (·.2) → d.gpr r = y.gpr r) ∧ d.sp = y.sp ∧
      (∀ p ∈ kernelSaved, d.gpr p.2 = vdword (y.vpr p.1) 0) ∧ isa.ret c d = some s' ∧
      t = (isa.callAddrs s).map .addr ++ tb ++ (isa.retAddrs d).map .addr := by
  unfold kernelCall kernel at e
  cases e with
  | call hc eb hr =>
    cases eb with
    | seq e₁ e₂ =>
      cases e₁ with
      | block h₁ =>
        cases e₂ with
        | seq eB e₃ =>
          cases e₃ with
          | block h₃ =>
            have hS := block_post (kernelSave_ok _) h₁
            have hR := block_post (kernelRestore_ok _) h₃
            have tS := execBlock_noLeaks (fun i hi s => by
              obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi; rfl) h₁
            have tR := execBlock_noLeaks (fun i hi s => by
              obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi; rfl) h₃
            subst tS tR
            exact ⟨_, _, _, _, _, hc, fun r => hS.1.gpr r (by simp), hS.1.sp, hS.2.2, eB, fun r hr => hR.1.gpr r hr,
              hR.1.sp, hR.2.2, hr, by simp⟩

private theorem kernelBody_noCalls : Code.noCalls kernelBody = true := by
  unfold kernelBody kernelEntry kernelExit tail8 sqrFlag sqr8 sqrInit sqrTri sqrDbl sqrRed sqrCopy zeroAcc roundsK
    subMod64M selectAcc64
  decide +kernel

private theorem kernelBody_noV : ∀ i ∈ instrs kernelBody, vWrites i = false := by
  unfold kernelBody kernelEntry kernelExit tail8 sqrFlag sqr8 sqrInit sqrTri sqrDbl sqrRed sqrCopy zeroAcc roundsK
    subMod64M selectAcc64
  decide +kernel

/-- The callers' registers keep their values over a run of the kernel's call. -/
theorem kernel_keeps {s s' : State} {t : List Leak} (e : Exec isa kernelCall s t s') {r : Reg} (hr : r ∈ kernelKeep) :
    s'.gpr r = s.gpr r := by
  have hl : r ∉ linkRegs := by
    simp only [kernelKeep, mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases hw : r ∈ kernelKeepW
  · exact Exec.gpr (fun i hi => kernel_keep i hi r hw) e (.inr hl)
  obtain ⟨c, x, tb, y, d, hc, -, -, xv, eB, -, -, dv, hrt, -⟩ := kernel_run e
  have yv : y.vpr = x.vpr := Exec.vpr kernelBody_noV kernelBody_noCalls eB
  have hp : ∃ v, (v, r) ∈ kernelSaved := by
    simp only [kernelKeep, kernelKeepW, mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr hw
    simp only [kernelSaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hw ⊢
  obtain ⟨v, hv⟩ := hp
  rw [ret_eq hrt, dv _ hv, yv, xv _ hv, (call_eq hc).2.2.2.2 r hl]

theorem kernelPost_unsaved : ∀ r ∈ kernelPost, r ∉ kernelSaved.map (·.2) := fun r hr => by
  simp only [kernelPost, mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem kernelSum_ok : kernelSum.Ok taint := by
  intro τ hle s₁ s₂ t₁ t₂ s₁' s₂' ha e₁ e₂
  have ha₀ : Agree kernelPre s₁ s₂ := taint.le_sound hle ha
  obtain ⟨c₁, x₁, tb₁, y₁, d₁, hc₁, xg₁, xs₁, -, eB₁, dg₁, ds₁, -, hr₁, ht₁⟩ := kernel_run e₁
  obtain ⟨c₂, x₂, tb₂, y₂, d₂, hc₂, xg₂, xs₂, -, eB₂, dg₂, ds₂, -, hr₂, ht₂⟩ := kernel_run e₂
  obtain ⟨hca, hac⟩ := taint.call_sound (τ' := kernelPreC) ha₀ rfl hc₁ hc₂
  have hx : Agree kernelPreC x₁ x₂ := ⟨by rw [xs₁, xs₂]; exact hac.1, fun r hr => by rw [xg₁, xg₂]; exact hac.2 r hr⟩
  obtain ⟨hb, hk⟩ := kernel_check
  cases hQ : taint.check kernelPreC kernelBody hb with
  | none => rw [hQ] at hk; cases hk
  | some Q =>
  rw [hQ] at hk
  have hPQ : kernelPost.subset Q = true := Option.some.inj hk
  obtain ⟨htb, hQa⟩ := VG.Taint.check_sound hQ hx eB₁ eB₂
  have hd : Agree (Q.inter kernelPost) d₁ d₂ := ⟨by rw [ds₁, ds₂]; exact hQa.1, fun r hr => by
    have hr' := (RegSet.mem_inter (R := Reg)).mp hr
    rw [dg₁ r (kernelPost_unsaved r hr'.2), dg₂ r (kernelPost_unsaved r hr'.2)]
    exact hQa.2 r hr'.1⟩
  obtain ⟨hra, hfin⟩ := taint.ret_sound (τ' := Q.inter kernelPost) hd rfl hr₁ hr₂
  refine ⟨by rw [ht₁, ht₂, hca, htb, hra], hfin.1, fun r hr => ?_⟩
  rcases mem_regUnion.mp hr with hr | hr
  · replace hr := (RegSet.mem_inter (R := Reg) (a := (τ : RegSet Reg))).mp hr
    rw [kernel_keeps e₁ hr.2, kernel_keeps e₂ hr.2]
    exact ha.2 r hr.1
  · exact hfin.2 r ((RegSet.mem_inter (R := Reg)).mpr ⟨RegSet.mem_of_subset hPQ hr, hr⟩)

/-- The summaries the callers' analyses use. -/
def montSums : List (VG.Taint.RSum isa taint.T) := [kernelSum]

theorem montSums_ok : VG.Taint.RAllOk taint montSums := ⟨kernelSum_ok, trivial⟩

end VG.Proof.Bignum.PPC64LE
