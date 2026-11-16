module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Fn
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM-SIV in registers on x86-64: constant time

Untrusted: everything here is checked by Lean. As for the first
implementation, both runs have the same public arguments in the slots of `W`,
so the taint analysis starts from the registers that agree and those slots,
public (`sivT`, `both_agree`). This code calls nothing: the taint analysis
checks each piece whole.
-/

-- separate module: evaluates the taint analysis on the code

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc word_byte)


/-- The taint: the registers `rs`, `r13`, `r15` and `rsp` public, `r15` the
base of the working space (the second writable region) and the slots of the
public arguments `[200, 248)` public. -/
def sivT (rs : List Reg) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.r13, .r15, .rsp]), flags := false, lens := [0, 488], bases := [(.r15, 1, 0)],
    slots := [(1, 200, 48)] }

/-- One run with the public arguments. -/
structure One (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (s : State) : Prop where
  env : Env K W SP s
  sl : Slots W R N A D al n s.mem
  wr : s.wr = [⟨D, n⟩, ⟨W, 488⟩]

/-- Two runs with the same public arguments, agreeing on the registers `rs`. -/
structure Both (K W SP : Addr) (R : Nat) (N A D : Addr) (al n : Nat) (rs : List Reg) (s₁ s₂ : State) :
    Prop where
  o₁ : One K W SP R N A D al n s₁
  o₂ : One K W SP R N A D al n s₂
  agree : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem both_agree {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {rs : List Reg} {s₁ s₂ : State}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 488⟩) (hn : n ≤ 2 ^ 64)
    (h : Both K W SP R N A D al n rs s₁ s₂) : X86_64.Taint.Agree (sivT rs) s₁ s₂ := by
  have wf : ∀ {s : State}, Env K W SP s → s.wr = [⟨D, n⟩, ⟨W, 488⟩] → X86_64.Taint.Wf (sivT rs) s := fun E hw => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [hw]; exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
    · rw [hw]; exact List.pairwise_pair.mpr hDW
    · rw [hw]; intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hn
      · show 488 ≤ 2 ^ 64; decide
    · simp only [sivT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [E.r15, BitVec.add_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h.o₁.wr, h.o₂.wr], wf h.o₁.env h.o₁.wr,
    wf h.o₂.env h.o₂.wr, fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with hr | hr
    · exact h.agree r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.o₁.env.r13, h.o₂.env.r13]
      · rw [h.o₁.env.r15, h.o₂.env.r15]
      · rw [h.o₁.env.rsp, h.o₂.env.rsp]
  · simp only [sivT, List.mem_singleton] at hsl; subst hsl; simp [sivT]
  · have hb : ∀ s : State, s.wr = [⟨D, n⟩, ⟨W, 488⟩] → X86_64.Taint.byteAddr s 1 k = W + BitVec.ofNat 64 k :=
      fun s hw => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, hw, List.getD_cons_succ, List.getD_cons_zero]
    have hw : ∀ d, k = d + (k - d) → W + BitVec.ofNat 64 k = W + BitVec.ofNat 64 d + BitVec.ofNat 64 (k - d) :=
      fun d e => by rw [add_ofNat_assoc, ← e]
    simp only [sivT, List.mem_singleton] at hsl; subst hsl
    rw [hb s₁ h.o₁.wr, hb s₂ h.o₂.wr]
    simp only at hk₁ hk₂
    have S₁ := h.o₁.sl
    have S₂ := h.o₂.sl
    have key : ∀ d, d ∈ [200, 208, 216, 224, 232, 240] → d ≤ k → k < d + 8 →
        s₁.mem (W + BitVec.ofNat 64 k) = s₂.mem (W + BitVec.ofNat 64 k) := fun d hd h₁ h₂ => by
      rw [hw d (by omega_arith)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
      · exact word_byte S₁.rounds S₂.rounds (by omega_arith)
      · exact word_byte S₁.nonce S₂.nonce (by omega_arith)
      · exact word_byte S₁.aad S₂.aad (by omega_arith)
      · exact word_byte S₁.alen S₂.alen (by omega_arith)
      · exact word_byte S₁.data S₂.data (by omega_arith)
      · exact word_byte S₁.len S₂.len (by omega_arith)
    have hq : (k - 200) / 8 = 0 ∨ (k - 200) / 8 = 1 ∨ (k - 200) / 8 = 2 ∨ (k - 200) / 8 = 3 ∨
        (k - 200) / 8 = 4 ∨ (k - 200) / 8 = 5 := by omega_arith
    exact key (200 + 8 * ((k - 200) / 8)) (by
      rcases hq with h | h | h | h | h | h <;> rw [h] <;> decide) (by omega_arith) (by omega_arith)

/-- Code the taint analysis checks from `sivT rs`. -/
theorem rel_taintC {K W SP : Addr} {R : Nat} {N A D : Addr} {al n : Nat} {P : State → State → Prop}
    {c : Prog isa} (rs : List Reg) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 488⟩) (hn : n ≤ 2 ^ 64)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D al n rs s₁ s₂)
    (hc : ∃ hc, (taint.check (sivT rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (sivT rs) (fun s₁ s₂ h => both_agree hDW hn (hP _ _ h)) hc


/-!
## The tag and counter mode are constant time

Untrusted: everything here is checked by Lean. The code around each call of
`vg_aes_ctr32` passes the taint analysis from the public slots and the
registers both runs agree on (`rel_taintC`); each call has the same
arguments in both runs, by correctness.
-/

/-! ## The pieces, checked -/

open VG.Impl.AesGcmSiv.X86_64Reg

theorem derive_check : ∃ hc, (taint.check (sivT []) derive hc).isSome = true := ⟨_, by taint_decide⟩

theorem expand_check : ∃ hc, (taint.check (sivT []) expand hc).isSome = true := ⟨_, by taint_decide⟩

open VG.Impl.AesGcm.X86_64 (at_ imm ptr) in
open VG.Impl.AesGcmSiv.X86_64 (aadO alenO dataO lenO) in
theorem polyA_check : ∃ hc, (taint.check (sivT []) (.block (hkey ++
    ([.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO))] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem absorb_check (four : Bool) : ∃ hc, (taint.check (sivT [.r12, .rbp]) (absorb four) hc).isSome = true := by
  cases four <;> exact ⟨_, by taint_decide⟩

open VG.Impl.AesGcm.X86_64 (at_ imm ptr) in
open VG.Impl.AesGcmSiv.X86_64 (aadO alenO dataO lenO) in
theorem polyD_check : ∃ hc, (taint.check (sivT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem lens_check : ∃ hc, (taint.check (sivT []) (.block lens) hc).isSome = true := ⟨_, by taint_decide⟩

theorem tag_check (o : Nat) (ho : o = 0 ∨ o = 128) : ∃ hc, (taint.check (sivT []) (tag o) hc).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem crypt_check : ∃ hc, (taint.check (sivT []) crypt hc).isSome = true := ⟨_, by taint_decide⟩

end VG.Proof.AesGcmSivReg.X86_64
