module

import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Tag
import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
public import VerifiedGarbage.Proof.AesGcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec

/-!
# AES-GCM on x86-64: `flush`, `lens` and `tag` in two runs

Untrusted: everything here is checked by Lean. Each leaks only what its
public registers (the number of buffered bytes, the lengths) and the
environment say: the code around the calls is checked by the taint
analysis, and the calls of `vg_ghash` and `vg_aes_ctr32` have the same
arguments in both runs (for `tag`, by `tagMid_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- `flush yo`, with the same number of buffered bytes. -/
theorem flush_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx]) (flush v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_regs ([.rbx] ++ [.r13, .r14, .r15, .rsp]) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine rel_reassoc2 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (rel_taint ([.rbx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1) ⟨_, by taint_decide⟩))
    ?_)
  refine (ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (gh1Check_r15_96 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], covers_left (he.perm.wC (by decide))⟩

/-- `padTail yo`, with the same data pointer and number of bytes. -/
theorem padTail_rel : RelCT isa (EnvAgree Ctx St W SP [.rbp, .r12]) (padTail v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_regs ([.rbp, .r12] ++ [.r13, .r14, .r15, .rsp]) ([.rbp, .r12, .rcx] ++ [.r13, .r14, .r15, .rsp]) true
      (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) (RelCT.block_nil fun _ _ _ => trivial) ?_
  refine rel_reassoc2 (RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide)
    (fun _ _ h => h.1.2) (rel_taint ([.rbp, .r12, .rcx] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.1.1.1)
      ⟨_, by taint_decide⟩)) ?_)
  refine (ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (gh1Check_r15_96 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], covers_left (he.perm.wC (by decide))⟩

/-- `absorbPad yo`, for data at the same address, of the same length, with
nothing buffered. -/
theorem absorbPad_rel {H₁ H₂ : Block} {x₁ x₂ : List Byte} {D : Addr} {n : Nat}
    (hx₁ : x₁.length % 16 = 0) (hx₂ : x₂.length % 16 = 0) :
    RelCT isa (fun s₁ s₂ => AbsIn Ctx St W SP yo H₁ x₁ D n s₁ ∧ AbsIn Ctx St W SP yo H₂ x₂ D n s₂)
      (absorbPad v.callees yo) fun _ _ => True := by
  suffices k : RelCT isa (fun s₁ s₂ => ∃ m₁ m₂ : Mem, AbsMid Ctx St W SP yo H₁ x₁ D n m₁ 0 s₁ ∧
      AbsMid Ctx St W SP yo H₂ x₂ D n m₂ 0 s₂) (absorbPad v.callees yo) fun _ _ => True from
    k.mono (fun s₁ s₂ h => ⟨s₁.mem, s₂.mem, h.1.mid hx₁, h.2.mid hx₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun m₁ => RelCT.exists_ fun m₂ => ?_
  have hw := rel_wp (whole_rel v L hyo (H₁ := H₁) (H₂ := H₂) (x₁ := x₁) (x₂ := x₂) (D := D) (n := n) (m₁ := m₁)
      (m₂ := m₂) (j := 0)) (fun _ _ h => h)
    (fun s h => whole_ok v L hyo h (h.data_eq hyo)) (fun s h => whole_ok v L hyo h (h.data_eq hyo))
  refine RelCT.seq hw ((padTail_rel v L hyo).mono (fun _ _ h => ⟨h.2.1.env, h.2.2.env, fun r hr => ?_⟩)
    fun _ _ h => h)
  exact AbsMid.agree h.2.1 h.2.2 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp)

/-- `lens yo`, with the same lengths. -/
theorem lens_rel : RelCT isa (EnvAgree Ctx St W SP [.rbx, .rbp]) (lens v.callees yo) fun _ _ => True := by
  refine RelCT.seq (rel_env (Ctx := Ctx) (St := St) (W := W) (SP := SP) (by decide) (fun _ _ h => ⟨h.1, h.2.1⟩)
    (rel_taint ([.rbx, .rbp] ++ [.r13, .r14, .r15, .rsp]) (fun _ _ h => h.regs) ⟨_, by taint_decide⟩)) ?_
  refine (ghash1_rel v L hyo .r15 96 (.inr rfl) (by decide) (P := W + BitVec.ofNat 64 96)
    (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)) (L.w_w (.inl (by decide)) (by decide) (by decide))
    (L.stk_w (by decide)) (gh1Check_r15_96 hyo) (F₁ := Env Ctx St W SP) (F₂ := Env Ctx St W SP)
    fun s hs => ?_).mono (fun _ _ h => h.2) fun _ _ h => h
  have he : Env Ctx St W SP s := hs.elim id id
  exact ⟨he, by rw [he.r15], covers_left (he.perm.wC (by decide))⟩

end

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

/-- `tag o`, with the same lengths and number of rounds. -/
theorem tag_rel {o R : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun s₁ s₂ => EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧ RoundsAt s₁.mem W R ∧ RoundsAt s₂.mem W R)
      (tag v.callees o) fun _ _ => True := by
  -- The arguments of the call, in each run.
  let G : State → Prop := fun s => Env Ctx St W SP s ∧
    CtrCall s Ctx St (W + BitVec.ofNat 64 o) (W + BitVec.ofNat 64 512) R 1
  have hG : ∀ s, (Env Ctx St W SP s ∧ RoundsAt s.mem W R) → WP isa (.seq (lens v.callees 16)
      (.block ([.mov .rax (.mem (at_ .r14 16)), .store (at_ .r15 o) .rax,
        .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
        .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO))) s G := fun s h =>
    WP.mono (tagMid_ok v L ho h.1 rfl h.2 rfl) fun _ M => ⟨M.env, M.call⟩
  have hL : ∀ s, Env Ctx St W SP s → WP isa (lens v.callees 16) s (Env Ctx St W SP) := fun s he =>
    WP.mono (lens_ok v L (.inr rfl) he rfl) fun _ h => h.1
  have hc : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block ([.mov .rax (.mem (at_ .r14 16)),
      .store (at_ .r15 o) .rax, .mov .rax (.mem (at_ .r14 24)), .store (at_ .r15 (o + 8)) .rax, .mov .rdi (.reg .r13),
      .mov .rsi (.mem (at_ .r15 roundsO)), .mov .rdx (.reg .r14)] ++ ptr .rcx .r15 o ++ [.mov32 .r8 (imm 1)] ++
      ptr .r9 .r15 scrO)) hc).isSome = true := by
    rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  let P₀ : State → State → Prop := fun s₁ s₂ => EnvAgree Ctx St W SP [.rbx, .rbp] s₁ s₂ ∧
    RoundsAt s₁.mem W R ∧ RoundsAt s₂.mem W R
  have l : RelCT isa P₀ (lens v.callees 16) fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ :=
    rel_wp ((lens_rel v L (.inr rfl)).mono (fun _ _ h => h.1) fun _ _ h => h)
      (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) hL hL
  have b : RelCT isa (fun s₁ s₂ => True ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) _ fun _ _ => True :=
    rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.2.1, h.2.2, fun _ h => by cases h⟩) hc
  have pre : RelCT isa P₀ _ fun s₁ s₂ => True ∧ G s₁ ∧ G s₂ :=
    rel_wp (RelCT.seq l b) (fun _ _ h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2.1, h.2.2⟩⟩) (fun s h => hG s h) (fun s h => hG s h)
  refine rel_reassoc2 (RelCT.seq pre (ctr_rel v.ctr fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.2, h.2.2.2, ?_⟩))
  rw [h.2.1.1.rsp, h.2.2.1.rsp]

end

end VG.Proof.AesGcm.X86_64
