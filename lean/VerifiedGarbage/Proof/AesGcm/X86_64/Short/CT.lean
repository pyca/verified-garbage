module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Keep
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Keep
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Open
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Ks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Impl.AesGcm.X86_64.Short
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Short
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-GCM's short path on x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public data go through the short path piece by piece: the first block of
each piece loads, from `W`, the counts and addresses the rest of it uses,
which are the same in both runs (`SJ`, by correctness), and the taint
analysis checks the rest from those registers (`rel_piece`). `cond`'s
branches are on the same public lengths in both runs (`cond_rel`); `open`'s
last branch is on the comparison, which `open` may leak (`openShort_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph)

/-- Code that writes none of the environment's registers, from a check the
kernel evaluates quickly. -/
theorem keepsEnv {c : Prog isa}
    (h : c.allInstrs (fun i => [Reg.r13, .r14, .r15, .rsp].all fun r => !Taint.clobbers i r) = true) :
    ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro r hr i hi
  simpa using List.all_eq_true.mp (h i hi) r hr

/-- A piece whose first block `b` loads what the rest `c` addresses memory
and counts from: `b` checked from the environment's registers, and `c` from
those and the registers `rs`, the same in both runs by correctness. -/
theorem rel_piece {F₁ F₂ G₁ G₂ : State → Prop} {Ctx St W SP : Addr} {b : List Instr} {c : Prog isa}
    (rs : List Reg) (he₁ : ∀ s, F₁ s → Env Ctx St W SP s) (he₂ : ∀ s, F₂ s → Env Ctx St W SP s)
    (hcl : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], ∀ i ∈ instrs (.block b : Prog isa), Taint.clobbers i r = false)
    (hb : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block b) hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa (.block b) s G₁) (hw₂ : ∀ s, F₂ s → WP isa (.block b) s G₂)
    (hag : ∀ t₁ t₂, G₁ t₁ → G₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (rs ++ ([.r13, .r14, .r15, .rsp] : List Reg))) c hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.seq (.block b) c) fun _ _ => True := by
  have a := rel_wp (rel_env hcl (fun _ _ h => ⟨he₁ _ h.1, he₂ _ h.2⟩)
    (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree (he₁ _ h.1) (he₂ _ h.2)) hb))
    (fun _ _ h => h) hw₁ hw₂
  exact RelCT.seq a (rel_taint _ (fun _ _ h => EnvAgree.regs ⟨h.1.2.1, h.1.2.2, hag _ _ h.2.1 h.2.2⟩) hc)

/-- Code with no address or branch from the registers `rs` that the
environments and `hag` say agree. -/
theorem rel_env_regs {F₁ F₂ : State → Prop} {Ctx St W SP : Addr} {c : Prog isa} (rs : List Reg)
    (he₁ : ∀ s, F₁ s → Env Ctx St W SP s) (he₂ : ∀ s, F₂ s → Env Ctx St W SP s)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (rs ++ ([.r13, .r14, .r15, .rsp] : List Reg))) c hc).isSome = true) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True :=
  rel_taint _ (fun _ _ h => EnvAgree.regs ⟨he₁ _ h.1, he₂ _ h.2, hag _ _ h.1 h.2⟩) hc

/-- A piece related in two runs, then what correctness says of each after it. -/
theorem rel_next {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun _ _ => True)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp h (fun _ _ h => h) hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-! ## `cond` -/

/-- `cond` in two runs with the same lengths: the same branches. -/
theorem cond_rel {W : Addr} {nl al n : Nat} {F₁ F₂ : State → Prop}
    (h₁ : ∀ s, F₁ s → CondS W nl al n s) (h₂ : ∀ s, F₂ s → CondS W nl al n s)
    (hnl : nl < 2 ^ 64) (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) cond fun _ _ => True := by
  have w₁ : ∀ {F : State → Prop}, (∀ s, F s → CondS W nl al n s) → ∀ s, F s →
      WP isa (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)]) s fun t =>
        t.zf = some (decide (nl = 12)) ∧ CondS W nl al n t := fun hF s h =>
    WP.mono (condB1_ok (hF s h) hnl) fun _ ⟨z, _, k⟩ => ⟨z, (hF s h).keep k⟩
  have b1 := rel_next (rel_taint (P := fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) [.rbp] (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ _ h.1).rbp, (h₂ _ h.2).rbp]) ⟨_, by taint_decide⟩)
    (w₁ h₁) (w₁ h₂)
  have last := rel_taint (P := fun _ _ => True) (c := .block [.alu .test .rax (.reg .rax)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have none := rel_taint (P := fun _ _ => True) (c := .block []) [] (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  have one := rel_taint (P := fun _ _ => True) (c := .block [.mov32 .rax (imm 1)]) []
    (fun _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩
  refine RelCT.seq b1 (RelCT.seq (RelCT.ite (fun _ _ h => by
      rw [eval_ne h.1.1, eval_ne h.2.1]) (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
    (last.mono (fun _ _ _ => trivial) fun _ _ h => h))
  -- The lengths' OR compared with 512.
  have w₂ : ∀ s, (s.zf = some (decide (nl = 12)) ∧ CondS W nl al n s) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .or .rcx (.mem (at_ .r15 lenO)),
        .alu .cmp .rcx (imm 512)]) s fun t => t.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n t :=
    fun s h => WP.mono (condB2_ok h.2 hal hn) fun _ ⟨c, _, k⟩ => ⟨c, h.2.keep k⟩
  have b2 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₁) ∧ (s₂.zf = some (decide (nl = 12)) ∧ CondS W nl al n s₂))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.r15, h.2.2.r15]) ⟨_, by taint_decide⟩) w₂ w₂
  refine RelCT.seq (b2.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_ae h.1.1).trans (eval_ae h.2.1).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
  -- The blocks of both lengths compared with 32.
  have w₃ : ∀ s, ((s.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n s) ∧ al < 512 ∧ n < 512) →
      WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15), .shift .shr .rcx 4,
        .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4, .alu .add .rcx (.reg .rdx),
        .alu .cmp .rcx (imm 32)]) s fun t => t.cf = some (decide (nb16 al + nb16 n < 32)) ∧
          CondS W nl al n t ∧ al < 512 ∧ n < 512 :=
    fun s h => WP.mono (condB3_ok h.1.2 h.2.1 h.2.2) fun _ ⟨c, _, k⟩ => ⟨c, h.1.2.keep k, h.2⟩
  have b3 := rel_next (rel_taint (P := fun s₁ s₂ =>
      ((s₁.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n s₁) ∧ al < 512 ∧ n < 512) ∧
      ((s₂.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n s₂) ∧ al < 512 ∧ n < 512))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.2.r15, h.2.1.2.r15]) ⟨_, by taint_decide⟩) w₃ w₃
  have h5 : ∀ {s₁ s₂ : State}, ((s₁.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n s₁) ∧
      (s₂.cf = some (decide (al ||| n < 512)) ∧ CondS W nl al n s₂)) ∧ isa.eval .ae s₁ = some false →
      al < 512 ∧ n < 512 := fun h => by
    have e := (eval_ae h.1.1.1).symm.trans h.2
    simp only [Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at e
    exact or_lt_512.mp e
  refine RelCT.seq (b3.mono (fun _ _ h => ⟨⟨h.1.1, h5 h⟩, ⟨h.1.2, h5 h⟩⟩) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_ae h.1.1).trans (eval_ae h.2.1).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) ?_)
  -- `al + 17 n` compared with 17.
  have w₄ : ∀ s, (s.cf = some (decide (nb16 al + nb16 n < 32)) ∧ CondS W nl al n s ∧ al < 512 ∧ n < 512) →
      WP isa (.block [.mov .rdx (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rdx), .shift .shl .rcx 4,
        .alu .add .rcx (.reg .rdx), .alu .add .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)]) s
        fun t => t.cf = some (decide (al + 17 * n < 17)) :=
    fun s h => WP.mono (condB4_ok h.2.1 h.2.2.1 h.2.2.2) fun _ ⟨c, _⟩ => c
  have b4 := rel_next (rel_taint (P := fun s₁ s₂ =>
      (s₁.cf = some (decide (nb16 al + nb16 n < 32)) ∧ CondS W nl al n s₁ ∧ al < 512 ∧ n < 512) ∧
      (s₂.cf = some (decide (nb16 al + nb16 n < 32)) ∧ CondS W nl al n s₂ ∧ al < 512 ∧ n < 512))
      [.r15] (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1.r15, h.2.2.1.r15]) ⟨_, by taint_decide⟩) w₄ w₄
  refine RelCT.seq (b4.mono (fun _ _ h => h.1) fun _ _ h => h)
    (RelCT.ite (fun _ _ h => (eval_b h.1).trans (eval_b h.2).symm)
      (none.mono (fun _ _ _ => trivial) fun _ _ h => h) (one.mono (fun _ _ _ => trivial) fun _ _ h => h))

/-! ## The pieces -/

/-- What constant time needs of a GHASH code `gh`: its addresses and
branches in two runs from the states before it. -/
def GhTaint (gh : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State} {Ctx W SP A D : Addr} {R al n : Nat} {J J' : Block} {tl tl' : BitVec 64},
    nb16 al + nb16 n < 32 →
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂) gh
      fun _ _ => True

/-- What constant time needs of a table of powers' code `pw`: its addresses
and branches in two runs from the states after `J₀` and the counts; and of
the GHASH code `gh` that goes with it. -/
structure PowCT (pw gh : Prog isa) : Prop where
  pw : ∀ {s₀ s₀' : State} {Ctx W SP A D : Addr} {R al n : Nat} {J J' : Block} {tl tl' : BitVec 64},
    RelCT isa (fun s₁ s₂ => SM s₀ Ctx W SP A D R al n J tl s₁ ∧ SM s₀' Ctx W SP A D R al n J' tl' s₂) pw
      fun _ _ => True
  gh : GhTaint gh

/-- `ghash` in two runs. -/
theorem ghash_taint : GhTaint ghash := by
  intro s₀ s₀' Ctx W SP A D R al n J J' tl tl' h32
  have h32' := h32
  simp only [nb16] at h32'
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block ghSetup) s fun t => t.gpr .rdx = W + BitVec.ofNat 64 384 ∧
        t.gpr .r9 = BitVec.ofNat 64 (grp al n) ∧ t.gpr .r11 = W + BitVec.ofNat 64 (1344 + 64 * grp al n) :=
    fun s h => WP.mono (ghSetup_ok s h.sm.env.r15 h.sm.r288 hg8 (h.sm.env.perm.wR (by decide)))
      fun _ ⟨dx, r9, r11, _⟩ => ⟨dx, r9, r11⟩
  exact rel_piece [.rdx, .r9, .r11] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩

theorem powers_ct (hF : ShortFacts) : PowCT powers ghash := by
  refine ⟨fun {s₀ s₀' Ctx W SP A D R al n J J' tl tl'} => ?_, ghash_taint⟩
  exact rel_piece [.rax, .r11] (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩
      (fun s h => hF.powHead s h.env h.r288) (fun s h => hF.powHead s h.env h.r288)
      (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J J' : Block} {tl tl' : BitVec 64}
  {k k' : Nat} (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (C' : OneCtx s₀' k' Ctx W SP Np A D nl al n)
include C C'

/-- A table of powers' code `pw` in two runs. -/
theorem pw_rel {pw gh : Prog isa} {tm tm' : Mem → Mem} (hpc : PowCT pw gh) (hpw : PowFrom pw gh tm s₀ Ctx W SP D n)
    (hpw' : PowFrom pw gh tm' s₀' Ctx W SP D n) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SM s₀ Ctx W SP A D R al n J tl s₁ ∧ SM s₀' Ctx W SP A D R al n J' tl' s₂) pw
      fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ :=
  rel_next hpc.pw (fun _ h => powSj C hpw h32 h) (fun _ h => powSj C' hpw' h32 h)

theorem zeroG_rel :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      (.block zeroG) fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ :=
  rel_next (rel_env_regs [] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (fun _ _ _ _ _ hr => by cases hr)
      ⟨_, by taint_decide⟩)
    (fun _ h => zeroG_sj C h) (fun _ h => zeroG_sj C' h)

theorem copyA_rel (hal5 : al < 512) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      copyA fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block [.mov .rdi (.mem (at_ .r15 leadO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
        .alu .add .rdi (imm gO), .mov .rsi (.mem (at_ .r15 aadO)), .mov .rcx (.mem (at_ .r15 alenO))]) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1))) ∧ t.gpr .rsi = A ∧
        t.gpr .rcx = BitVec.ofNat 64 al := fun s h => by
    obtain ⟨t, run, di, si, cx, -⟩ := copyAArgs_ok s h.sm.env.r15 h.sm.env.perm.w h.sm.r296 h.sm.r232 h.sm.r184
      (by omega)
    exact WP.of_runBlock ⟨t, run, di, si, cx⟩
  exact rel_next (rel_piece [.rdi, .rsi, .rcx] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩)
    (fun _ h => copyA_sj C hal5 h32 h) (fun _ h => copyA_sj C' hal5 h32 h)

theorem keystream_rel (hR : R = 10 ∨ R = 12 ∨ R = 14) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      keystream fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block ksSetup) s fun t => t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 R ∧
        t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * R) ∧ t.gpr .rdx = W + BitVec.ofNat 64 1024 ∧
        t.gpr .r9 = BitVec.ofNat 64 ((nb16 n + 4) / 4) := fun s h =>
    WP.mono (ksSetup_ok s h.sm.env h.sm.r176 h.sm.r280 (by omega) (by omega) h.z0)
      fun _ ⟨_, _, _, di, si, r10, dx, r9, _⟩ => ⟨di, si, r10, dx, r9⟩
  exact rel_next (rel_piece [.rdi, .rsi, .r10, .rdx, .r9] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2.1, h₂.2.2.2.1]
        · rw [h₁.2.2.2.2, h₂.2.2.2.2]) ⟨_, by taint_decide⟩)
    (fun _ h => keystream_sj C hR h32 h) (fun _ h => keystream_sj C' hR h32 h)

theorem text_rel (g : Bool) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      (.seq (.block textArgs) (xorText g))
      fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block textArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)) ∧
        t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧ t.gpr .rcx = BitVec.ofNat 64 n := fun s h => by
    obtain ⟨t, run, di, si, dx, cx, -⟩ := textArgs_ok s h.sm.env.r15 h.sm.env.perm.w h.sm.r296 h.sm.r272
      h.sm.r200 h.sm.r208 (by omega)
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  exact rel_next (rel_piece [.rdi, .rsi, .rdx, .rcx] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]) (by cases g <;> exact ⟨_, by taint_decide⟩))
    (fun _ h => text_sj g C hn5 h32 h) (fun _ h => text_sj g C' hn5 h32 h)

theorem copyC_rel (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      copyC fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block (gText ++ [.mov .rsi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 lenO))])) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)) ∧
        t.gpr .rsi = D ∧ t.gpr .rcx = BitVec.ofNat 64 n := fun s h => by
    obtain ⟨t, run, di, si, cx, -⟩ := copyCArgs_ok s h.sm.env.r15 h.sm.env.perm.w h.sm.r296 h.sm.r272
      h.sm.r200 h.sm.r208 (by omega)
    exact WP.of_runBlock ⟨t, run, di, si, cx⟩
  exact rel_next (rel_piece [.rdi, .rsi, .rcx] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩)
    (fun _ h => copyC_sj C hn5 h32 h) (fun _ h => copyC_sj C' hn5 h32 h)

theorem lens_rel (hal5 : al < 512) (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      (.block Short.lens)
      fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have h32' := h32
  simp only [nb16] at h32'
  have hg8 : grp al n ≤ 8 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SJ s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block [.mov .rdi (.mem (at_ .r15 mpO)), .shift .shl .rdi 4, .alu .add .rdi (.reg .r15),
        .alu .add .rdi (imm (gO - 16))]) s fun t => t.gpr .rdi = W + BitVec.ofNat 64 (496 + 16 * (4 * grp al n)) :=
    fun s h => lensHead_ok s h.sm.env.r15 h.sm.env.perm.w h.sm.r288 (by omega)
  refine rel_next (rel_block_split (rel_piece [.rdi] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) ⟨_, by taint_decide⟩))
    (fun _ h => lens_sj C hal5 hn5 h32 h) (fun _ h => lens_sj C' hal5 hn5 h32 h)

theorem gh_rel {gh : Prog isa} {tm tm' : Mem → Mem} (hgc : GhTaint gh) (hgh : GhFrom gh tm s₀ Ctx W SP)
    (hgh' : GhFrom gh tm' s₀' Ctx W SP) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      gh fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂ :=
  rel_next (hgc h32) (fun _ h => gh_sj hgh C h32 h) (fun _ h => gh_sj hgh' C' h32 h)

end

/-- `tagK 0` in two runs. -/
theorem tagK_rel {s₀ s₀' : State} {Ctx W SP A D : Addr} {al n R : Nat} {J J' : Block} {tl tl' : BitVec 64} :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J tl s₁ ∧ SJ s₀' Ctx W SP A D R al n J' tl' s₂)
      (.block (tagK 0)) fun _ _ => True :=
  rel_env_regs [] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (fun _ _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩

/-! ## The end of a long `seal` -/

/-- What `finish`'s pieces keep, in each run: the rounds, and the address
and the number of the bytes left. -/
structure FinI (Ctx W SP D : Addr) (R r : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : s.mem.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 r

theorem FinI.keep {Ctx W SP D : Addr} {R r : Nat} {s s' : State} (h : FinI Ctx W SP D R r s)
    (hg : ∀ g ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr g = s.gpr g) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨W + BitVec.ofNat 64 1024, 64⟩] s.mem s'.mem) : FinI Ctx W SP D R r s' := by
  have kp : ∀ d, d + 8 ≤ 1024 → s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Offset.disjoint W (.inl (by omega)) (by omega) (by decide))
      (by decide)
  exact ⟨h.env.keep hg hrd hwr, by rw [kp 176 (by decide)]; exact h.rounds, by rw [kp 200 (by decide)]; exact h.dat,
    by rw [kp 208 (by decide)]; exact h.len⟩

/-- What `finishWith` needs of its keystream program `ks` in two runs with
the same rounds and bytes left. -/
def KsRel (ks : Prog isa) : Prop :=
  ∀ {Ctx W SP D : Addr} {R r : Nat}, (R = 10 ∨ R = 12 ∨ R = 14) →
    RelCT isa (fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂) ks fun _ _ => True

theorem finKs_rel : KsRel finKs := fun {Ctx W SP D R r} _ => by
  have wCtrs : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finCtrs) s fun t =>
      t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 R ∧ t.gpr .r10 = Ctx + BitVec.ofNat 64 (16 * R) := fun s h => by
    obtain ⟨t, run, -, -, -, -, di, si, r10, -⟩ := finCtrs_ok s h.env h.rounds
    exact WP.of_runBlock ⟨t, run, di, si, r10⟩
  exact rel_piece [.rdi, .rsi, .r10] (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel))
      ⟨_, by taint_decide⟩ wCtrs wCtrs (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]) ⟨_, by taint_decide⟩

/-- `finishWith ks` after `H'` and `H'²`, in two runs with the same rounds
and bytes left: the keystream, the bytes left and the tag. -/
theorem finRest_rel {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr}
    {R r : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂)
      (.seq ks (.seq (.block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)])
        (.ite .e (.block (finLens ++ finGh1 ++ tagK 0))
          (.seq (.block finTextArgs) (.seq (xorText true) (.block (finLens ++ finGh2 ++ tagK 0)))))))
      fun _ _ => True := by
  have wKs : ∀ s, FinI Ctx W SP D R r s → WP isa ks s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (hks s h.env h.rounds hR) fun _ ⟨_, _, f, g, rd, wr, _⟩ => h.keep (fun g' hg => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) rd wr f
  have wTest : ∀ s, FinI Ctx W SP D R r s → WP isa (.block [.mov .rax (.mem (at_ .r15 lenO)),
      .alu .test .rax (.reg .rax)]) s fun t => t.zf = some (decide (r = 0)) ∧ FinI Ctx W SP D R r t := fun s h =>
    WP.mono (finTest_ok hr s h.env h.len) fun _ ⟨z, g, m, rd, wr, _⟩ => ⟨z, h.keep (fun g' hg => g _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) rd wr (by rw [m]; exact Frame.refl _ _)⟩
  have wArgs : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finTextArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 512 ∧ t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧
        t.gpr .rcx = BitVec.ofNat 64 r := fun s h => by
    obtain ⟨t, run, -, di, si, dx, cx, -⟩ := finTextArgs_ok s h.env h.dat h.len
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  have k := rel_next (hkr hR) wKs wKs
  have t := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block [.mov .rax (.mem (at_ .r15 lenO)), .alu .test .rax (.reg .rax)]) ⟨_, by taint_decide⟩) wTest wTest
  have b₀ := rel_env_regs [] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r) (fun _ h => h.env) (fun _ h => h.env)
    (fun _ _ _ _ _ hr => by cases hr) (c := .block (finLens ++ finGh1 ++ tagK 0)) ⟨_, by taint_decide⟩
  have b₁ := rel_piece [.rdi, .rsi, .rdx, .rcx] (F₁ := FinI Ctx W SP D R r) (F₂ := FinI Ctx W SP D R r)
    (fun _ h => h.env) (fun _ h => h.env) (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ wArgs wArgs
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2])
    (c := .seq (xorText true) (.block (finLens ++ finGh2 ++ tagK 0))) ⟨_, by taint_decide⟩
  refine RelCT.seq k (RelCT.seq t (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    (b₀.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)
    (b₁.mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h)))

/-- `finishWith ks` in two runs with the same rounds and bytes left. -/
theorem finish_rel (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {Ctx W SP D : Addr}
    {R r : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hr : r < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => FinI Ctx W SP D R r s₁ ∧ FinI Ctx W SP D R r s₂) (finishWith ks) fun _ _ => True := by
  have wPow : ∀ s, FinI Ctx W SP D R r s → WP isa (.block finPow) s (FinI Ctx W SP D R r) := fun s h =>
    WP.mono (hF.finPow s (by rw [h.env.r13, BitVec.ofInt_natCast]; exact h.env.perm.ctxR (by decide)))
      fun _ ⟨_, _, _, _, o⟩ => h.keep (fun g hg => o.gpr g (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> decide)) o.rd o.wr (by rw [o.mem]; exact Frame.refl _ _)
  have p := rel_next (rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
    (c := .block finPow) ⟨_, by taint_decide⟩) wPow wPow
  exact RelCT.seq p (finRest_rel hks hkr hR hr)

/-- After the entry, the long `seal` in two runs: `oneAad`, `oneBlocks` and
`finishWith ks`. -/
theorem sealRunF_rel (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₀' : State}
    {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) :
    RelCT isa (fun s₁ s₂ => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (finishWith ks))) fun _ _ => True := by
  have L := C.lay
  have hDW := C.dE
  have hn := C.data.ok.lt
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have a := (oneAad_rel v L hDW (T := none) (R := R) (Np := Np) (nl := nl)).mono
    (P' := fun (s₁ s₂ : State) => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
    (fun _ _ h => ⟨h.2.1.aadPre C X hNp hnl hal hR, h.2.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ h => h
  have bl := oneBlocksE_rel B L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24
  have fi : ∀ {s : State}, OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s →
      FinI Ctx W SP (D + BitVec.ofNat 64 (16 * (n / 16))) R (n - 16 * (n / 16)) s :=
    fun h => ⟨h.env, h.rounds.1, h.dat, h.len⟩
  exact (RelCT.seq a (RelCT.seq bl ((finish_rel hF hks hkr hRr (by omega)).mono (fun _ _ h => ⟨fi h.1, fi h.2⟩)
    fun _ _ h => h))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- After the entry, the long `seal` in two runs, with the additional data
absorbed by `aadP`, which leaves what `oneAad` does: `aadP` (which branches
alike in both runs), `oneBlocks` and `finishWith ks`. -/
theorem sealRunW_rel (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (hkr : KsRel ks) {M : Gcm.X86_64.Stitch.CtxMode}
    (B : BlkFn M) {aadP : Prog isa} {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R)
    (har : RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂) aadP
      fun _ _ => True)
    (ha : ∀ s, OneEntry s₀ Ctx W SP A D n s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (ha' : ∀ s, OneEntry s₀' Ctx W SP A D n s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq aadP (.seq (oneBlocks B.enc) (finishWith ks))) fun _ _ => True := by
  have L := C.lay
  have hDW := C.dE
  have hn := C.data.ok.lt
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have w : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n)
      (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀), s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R → ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa aadP s (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem) →
      WP isa aadP s (OneS M Ctx W SP R A al D n none) :=
    fun C X hNp hnl hal hR _ h ha => WP.mono ha fun _ Mi =>
      (h.aadPre C X hNp hnl hal hR).1.frame L Mi.env (Mi.rd.trans h.rd.symm) (Mi.wr.trans h.wr.symm)
        C.dE (wFrame_one (.inl rfl) (wFrame_cons Mi.fr))
  have a := rel_wp har (fun _ _ h => h) (fun s h => w C X hNp hnl hal hR s h (ha s h))
    (fun s h => w C' X' hNp' hnl' hal' hR' s h (ha' s h))
  have bl := oneBlocksE_rel B L (R := R) (A := A) (al := al) (T := none) C.t_c C.t_w C.t_d C.sp24
  have fi : ∀ {s : State}, OneS M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) s →
      FinI Ctx W SP (D + BitVec.ofNat 64 (16 * (n / 16))) R (n - 16 * (n / 16)) s :=
    fun h => ⟨h.env, h.rounds.1, h.dat, h.len⟩
  exact (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩)
    (RelCT.seq bl ((finish_rel hF hks hkr hRr (by omega)).mono (fun _ _ h => ⟨fi h.1, fi h.2⟩)
    fun _ _ h => h))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- What `seal` needs of the code `lng` it runs when the short path does not
apply, in two runs: what `sealRunF_rel` gives. -/
def SealLongRel (M : Gcm.X86_64.Stitch.CtxMode) (lng : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat},
    OneCtx s₀ 4 Ctx W SP Np A D nl al n → OneCtx s₀' 4 Ctx W SP Np A D nl al n →
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀' →
    s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
    s₀'.gpr .rdx = Np → (s₀'.gpr .rcx).toNat = nl → (s₀'.gpr .r9).toNat = al → (s₀'.gpr .rsi).toNat = R →
    RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂) lng fun _ _ => True

theorem sealLongRel_sealLong (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    SealLongRel M (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)) :=
  fun C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' =>
    (sealRunF_rel hF finKs_ksOk finKs_rel v B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨trivial, h⟩) fun _ _ h => h

/-! ## `seal` -/

/-- The short `seal` in two runs with the same public data. -/
theorem sealShort_rel {pw gh : Prog isa} {tm tm' : Mem → Mem} (hpc : PowCT pw gh) {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hpw : PowFrom pw gh tm s₀ Ctx W SP D n) (hpw' : PowFrom pw gh tm' s₀' Ctx W SP D n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hs : IsShort nl al n) :
    RelCT isa (fun s₁ s₂ => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂) (sealShort pw gh)
      fun _ _ => True := by
  obtain ⟨h12, hal5, hn5, h32, -⟩ := hs
  subst h12
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have b0 := rel_next (rel_env_regs [.r12] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r12, h₂.r12, hNp, hNp'])
        (c := .block (j012 ++ sizes)) ⟨_, by taint_decide⟩)
      (G₁ := fun t => ∃ tl, SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) tl t)
      (G₂ := fun t => ∃ tl, SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12)) tl t)
      (fun s E => WP.mono (shortStart_ok C E hNp hnl rfl hal hal5 hn5) fun _ ⟨S, _, _⟩ => ⟨_, hR ▸ S⟩)
      (fun s E => WP.mono (shortStart_ok C' E hNp' hnl' rfl hal' hal5 hn5) fun _ ⟨S, _, _⟩ => ⟨_, hR' ▸ S⟩)
  refine RelCT.seq b0 ((RelCT.exists_ (P := fun (p : BitVec 64 × BitVec 64) s₁ s₂ =>
      SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) p.1 s₁ ∧
      SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12)) p.2 s₂) fun _ => ?_).mono
    (fun _ _ ⟨⟨tl, h₁⟩, ⟨tl', h₂⟩⟩ => ⟨(tl, tl'), h₁, h₂⟩) fun _ _ h => h)
  exact RelCT.seq (pw_rel C C' hpc hpw hpw' h32) (RelCT.seq (zeroG_rel C C') (RelCT.seq (copyA_rel C C' hal5 h32)
    (RelCT.seq (keystream_rel C C' hRr h32) (RelCT.seq (text_rel C C' true hn5 h32)
    (RelCT.seq (RelCT.seq (lens_rel C C' hal5 hn5 h32) (gh_rel C C' hpc.gh hpw.gh hpw'.gh h32)) tagK_rel)))))

/-! ## `open` -/

/-- The comparison's result, as `openResult` says. -/
theorem openK_eq {s₀ : State} {Ctx Np A D Tp : Addr} {al n R t : Nat} (hok : Spec.Gcm.tagLenOk t = true) :
    openK s₀ Ctx A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) t Tp =
      if (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np 12)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome then 1 else 0 := by
  simp only [openK, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
    length_bytesAt]
  split <;> simp

/-- `tagK uO`, the tag's length and address, and the comparison, in two runs. -/
theorem chkTail_rel {s₀ s₀' : State} {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat} {J J' : Block} {k k' : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (C' : OneCtx s₀' k' Ctx W SP Np A D nl al n)
    (hTa : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp) (hTa' : s₀'.mem.readW (SP + BitVec.ofNat 64 24) 64 = Tp)
    (hTar : InRegions (s₀.rd ++ s₀.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTar' : InRegions (s₀'.rd ++ s₀'.wr) (SP + BitVec.ofNat 64 24) 8)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩) :
    RelCT isa (fun s₁ s₂ => SJ s₀ Ctx W SP A D R al n J (BitVec.ofNat 64 t) s₁ ∧
        SJ s₀' Ctx W SP A D R al n J' (BitVec.ofNat 64 t) s₂)
      (.seq (.block (tagK uO ++ ([.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] : List Instr)))
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))
      fun _ _ => True :=
  rel_piece [.rbx, .rsi] (fun _ h => h.sm.env) (fun _ h => h.sm.env) (keepsEnv (by decide +kernel))
    ⟨_, by taint_decide⟩ (G₁ := fun u => u.gpr .rbx = BitVec.ofNat 64 t ∧ u.gpr .rsi = Tp)
    (G₂ := fun u => u.gpr .rbx = BitVec.ofNat 64 t ∧ u.gpr .rsi = Tp)
    (fun _ h => WP.mono (tagMov_ok C h hTa hTar oA) fun _ ⟨_, b, si⟩ => ⟨b, si⟩)
    (fun _ h => WP.mono (tagMov_ok C' h hTa' hTar' oA) fun _ ⟨_, b, si⟩ => ⟨b, si⟩)
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) ⟨_, by taint_decide⟩

/-- The data decrypted, from `SM`, in two runs. -/
theorem textSM_rel {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n R : Nat} {J J' : Block}
    {tl tl' : BitVec 64} {k k' : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (C' : OneCtx s₀' k' Ctx W SP Np A D nl al n)
    (hn5 : n < 512) (h32 : nb16 al + nb16 n < 32) :
    RelCT isa (fun s₁ s₂ => SM s₀ Ctx W SP A D R al n J tl s₁ ∧ SM s₀' Ctx W SP A D R al n J' tl' s₂)
      (.seq (.block textArgs) (xorText false))
      fun s₁ s₂ => SM s₀ Ctx W SP A D R al n J tl s₁ ∧ SM s₀' Ctx W SP A D R al n J' tl' s₂ := by
  have h32' := h32
  simp only [nb16] at h32'
  have hlead : 4 * grp al n - (nb16 al + nb16 n + 1) < 4 := by simp only [grp, nb16]; omega
  have hw : ∀ {s₀ : State} {J : Block} {tl : BitVec 64} (s : State), SM s₀ Ctx W SP A D R al n J tl s →
      WP isa (.block textArgs) s fun t =>
      t.gpr .rdi = W + BitVec.ofNat 64 (512 + 16 * (4 * grp al n - (nb16 al + nb16 n + 1) + nb16 al)) ∧
        t.gpr .rsi = D ∧ t.gpr .rdx = W + BitVec.ofNat 64 1040 ∧ t.gpr .rcx = BitVec.ofNat 64 n := fun s h => by
    obtain ⟨t, run, di, si, dx, cx, -⟩ := textArgs_ok s h.env.r15 h.env.perm.w h.r296 h.r272 h.r200 h.r208
      (by omega)
    exact WP.of_runBlock ⟨t, run, di, si, dx, cx⟩
  exact rel_next (rel_piece [.rdi, .rsi, .rdx, .rcx] (fun _ h => h.env) (fun _ h => h.env)
      (keepsEnv (by decide +kernel)) ⟨_, by taint_decide⟩ hw hw (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]) ⟨_, by taint_decide⟩)
    (fun _ h => WP.mono (text_sm false C hn5 h32 h) fun _ h => h.1)
    (fun _ h => WP.mono (text_sm false C' hn5 h32 h) fun _ h => h.1)

/-- The short `open` in two runs with the same public data, whose results
`open` may leak (`hres`). -/
theorem openShort_rel (hF : ShortFacts) {pw gh : Prog isa} {tm tm' : Mem → Mem} (hpc : PowCT pw gh) {s₀ s₀' : State}
    {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 5 Ctx W SP Np A D nl al n)
    (hpw : PowFrom pw gh tm s₀ Ctx W SP D n) (hpw' : PowFrom pw gh tm' s₀' Ctx W SP D n)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hs : IsShort nl al n) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr)) (hTr' : Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂) (openShort pw gh)
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  obtain ⟨h12, hal5, hn5, h32, -⟩ := hs
  subst h12
  have hRr : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have oA := C.arg24 (by decide)
  have hTar := C.args 2 (by decide)
  have hTar' := C'.args 2 (by decide)
  -- `J₀` and the counts.
  have b0 := rel_next (rel_env_regs (F₁ := OpenIn s₀ Ctx W SP A D n t) (F₂ := OpenIn s₀' Ctx W SP A D n t) [.r12]
        (fun _ h => h.1.env) (fun _ h => h.1.env) (fun _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r12, h₂.1.r12, hNp, hNp'])
        (c := .block (j012 ++ sizes)) ⟨_, by taint_decide⟩)
      (G₁ := fun u => SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12))
        (BitVec.ofNat 64 t) u ∧ bytesAt u.mem A al = bytesAt s₀.mem A al ∧ bytesAt u.mem D n = bytesAt s₀.mem D n)
      (G₂ := fun u => SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12))
        (BitVec.ofNat 64 t) u ∧ bytesAt u.mem A al = bytesAt s₀'.mem A al ∧ bytesAt u.mem D n = bytesAt s₀'.mem D n)
      (fun s h => WP.mono (shortStart_ok C h.1 hNp hnl rfl hal hal5 hn5) fun _ ⟨S, a, d⟩ => by
        rw [h.2.2, hR] at S; exact ⟨S, a, d⟩)
      (fun s h => WP.mono (shortStart_ok C' h.1 hNp' hnl' rfl hal' hal5 hn5) fun _ ⟨S, a, d⟩ => by
        rw [h.2.2, hR'] at S; exact ⟨S, a, d⟩)
  -- Up to the comparison: the pieces, then what correctness says of the comparison.
  have pfx := rel_next (F₁ := fun u => SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12))
        (BitVec.ofNat 64 t) u ∧ bytesAt u.mem A al = bytesAt s₀.mem A al ∧ bytesAt u.mem D n = bytesAt s₀.mem D n)
      (F₂ := fun u => SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12))
        (BitVec.ofNat 64 t) u ∧ bytesAt u.mem A al = bytesAt s₀'.mem A al ∧ bytesAt u.mem D n = bytesAt s₀'.mem D n)
    ((RelCT.seq (pw_rel C C' hpc hpw hpw' h32) (RelCT.seq (zeroG_rel C C') (RelCT.seq
      (copyA_rel C C' hal5 h32) (RelCT.seq (keystream_rel C C' hRr h32) (RelCT.seq (copyC_rel C C' hn5 h32)
      (RelCT.seq (lens_rel C C' hal5 hn5 h32) (RelCT.seq (gh_rel C C' hpc.gh hpw.gh hpw'.gh h32)
      (chkTail_rel C C' hT hT' hTar hTar' oA)))))))).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ ⟨S, a, d⟩ => front_ok C hpw hR.symm hal5 hn5 h32 S a d fun _ F =>
      openChk_ok hF hpw.gh hpw.view C hal5 hn5 h32 F hb.1 hb.2 hT hTar hTr oT oA)
    (fun _ ⟨S, a, d⟩ => front_ok C' hpw' hR'.symm hal5 hn5 h32 S a d fun _ F =>
      openChk_ok hF hpw'.gh hpw'.view C' hal5 hn5 h32 F hb.1 hb.2 hT' hTar' hTr' oT oA)
  have hk : openK s₀ Ctx A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) t Tp =
      openK s₀' Ctx A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12)) t Tp := by
    rw [openK_eq hok, openK_eq hok, hres]
  -- The branch on the comparison, then the result loaded.
  have none := rel_next (rel_env_regs (F₁ := SM s₀ Ctx W SP A D R al n
      (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12)) (BitVec.ofNat 64 t))
      (F₂ := SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12)) (BitVec.ofNat 64 t))
      [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) (c := .block [])
      ⟨_, by taint_decide⟩) (fun _ h => WP.block_nil h) (fun _ h => WP.block_nil h)
  have fin := rel_env (keepsEnv (by decide +kernel)) (fun _ _ h => ⟨h.1.env, h.2.env⟩)
    (rel_env_regs (F₁ := SM s₀ Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np 12))
      (BitVec.ofNat 64 t))
      (F₂ := SM s₀' Ctx W SP A D R al n (Spec.Gcm.j0 (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np 12)) (BitVec.ofNat 64 t))
      [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr)
      (c := .block [.mov .rax (.mem (at_ .r15 auxO))]) ⟨_, by taint_decide⟩)
  refine RelCT.seq b0 (RelCT.seq pfx (RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.1.zf, h.2.zf, hk])
    (none.mono (fun _ _ h => ⟨h.1.1.sm, h.1.2.sm⟩) fun _ _ h => h)
    ((textSM_rel C C' hn5 h32).mono (fun _ _ h => ⟨h.1.1.sm, h.1.2.sm⟩) fun _ _ h => h))
    (fin.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-! ## The functions -/

/-- `vg_aes_gcm_seal` with the short path, the table of powers from `pw`,
and `lng` when the short path does not apply, in two runs. -/
theorem sealMW_rel (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {pw gh lng : Prog isa} (hpw : PowOk M pw gh) (hpc : PowCT pw gh) (hlng : SealLongOk M lng)
    (hlr : SealLongRel M lng) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealX86_64M M).pre s₀')
    (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) pw gh lng)
      fun _ _ => True :=
  sealM_relOf hp hp' hq (sealMid_ok hF hpw hlng) fun {Ctx W SP _ A D nl al n _} C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' => by
    have hlt := C.data.ok.lt
    have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
        (s₀.gpr .r9).toNat = al → ∀ s, OneEntry s₀ Ctx W SP A D n s →
        WP isa cond s fun u => u.zf = some (decide ¬IsShort nl al n) ∧ OneEntry s₀ Ctx W SP A D n u :=
      fun C hnl hal s h => WP.mono (condE_ok C h hnl hal) fun _ ⟨z, E, _⟩ => ⟨z, E⟩
    have c := rel_next ((cond_rel (F₁ := OneEntry s₀ Ctx W SP A D n) (F₂ := OneEntry s₀' Ctx W SP A D n)
        (fun _ h => condS_of h hnl hal) (fun _ h => condS_of h hnl' hal')
        (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega)))
      (hw C hnl hal) (hw C' hnl' hal')
    refine RelCT.seq (c.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h) (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
      ((hlr C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
        (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
    by_cases hs : IsShort nl al n
    · exact (sealShort_rel hpc C C' (hpw X).choose_spec (hpw X').choose_spec hNp hnl hal hR hNp' hnl' hal' hR' hs).mono
        (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

theorem sealM_rel (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s₀) (hp' : (Proof.AesGcm.sealX86_64M M).pre s₀')
    (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B))
      fun _ _ => True :=
  sealMW_rel hF v B (powOk_powers hF) (powers_ct hF) (sealLongOk_sealLong hF v B) (sealLongRel_sealLong hF v B)
    hp hp' hq

theorem sealMW_ct (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {pw gh lng : Prog isa} (hpw : PowOk M pw gh) (hpc : PowCT pw gh) (hlng : SealLongOk M lng)
    (hlr : SealLongRel M lng) :
    ConstantTime isa (Proof.AesGcm.sealX86_64M M).pre Proof.AesGcm.sealX86_64.pub
      (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) pw gh lng) :=
  ct_of_rel fun _ _ hp hp' hq => sealMW_rel hF v B hpw hpc hlng hlr hp hp' hq

theorem sealM_ct (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.sealX86_64M M).pre Proof.AesGcm.sealX86_64.pub
      (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) :=
  sealMW_ct hF v B (powOk_powers hF) (powers_ct hF) (sealLongOk_sealLong hF v B) (sealLongRel_sealLong hF v B)

/-- What `open` needs of the code `lng` it runs when the short path does not
apply, in two runs: what `openOk_rel` gives. -/
def LongRel (M : Gcm.X86_64.Stitch.CtxMode) (lng : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State} {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat},
    OneCtx s₀ 5 Ctx W SP Np A D nl al n → OneCtx s₀' 5 Ctx W SP Np A D nl al n →
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ → CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀' →
    s₀.gpr .rdx = Np → (s₀.gpr .rcx).toNat = nl → (s₀.gpr .r9).toNat = al → (s₀.gpr .rsi).toNat = R →
    s₀'.gpr .rdx = Np → (s₀'.gpr .rcx).toNat = nl → (s₀'.gpr .r9).toNat = al → (s₀'.gpr .rsi).toNat = R →
    ArgT SP Tp s₀ → ArgT SP Tp s₀' → Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr) → Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr) →
    OutWDS W D SP n ⟨Tp, t⟩ →
    (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome →
    Spec.Gcm.tagLenOk t = true →
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂) lng
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂

theorem longRel_openLong (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    LongRel M (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) :=
  fun C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok =>
    openOk_rel v B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok

/-- `vg_aes_gcm_open` with the short path, the table of powers from `pw`,
and `lng` when the short path does not apply, in two runs. -/
theorem openMW_rel (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {pw lng gh : Prog isa} (hpw : PowOk M pw gh) (hpc : PowCT pw gh) (hlr : LongRel M lng) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s₀) (hp' : (Proof.AesGcm.openX86_64M M).pre s₀')
    (hq : Proof.AesGcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) pw lng gh)
      fun _ _ => True :=
  openM_relOf hp hp' hq fun {Ctx W SP _ A D _ nl al n _ t} C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr
      hTr' oT hres hok => by
    have hlt := C.data.ok.lt
    have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
        (s₀.gpr .r9).toNat = al → ∀ s, OpenIn s₀ Ctx W SP A D n t s →
        WP isa cond s fun u => u.zf = some (decide ¬IsShort nl al n) ∧ OpenIn s₀ Ctx W SP A D n t u :=
      fun C hnl hal s h => WP.mono (condE_ok C h.1 hnl hal) fun _ ⟨z, E, K⟩ =>
        ⟨z, E, by rw [K.gpr _ (by decide) (by decide) (by decide), h.2.1], by rw [K.mem]; exact h.2.2⟩
    have c := rel_next ((cond_rel (F₁ := OpenIn s₀ Ctx W SP A D n t) (F₂ := OpenIn s₀' Ctx W SP A D n t)
        (fun _ h => condS_of h.1 hnl hal) (fun _ h => condS_of h.1 hnl' hal')
        (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega)))
      (hw C hnl hal) (hw C' hnl' hal')
    refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
      ((hlr C C' X X' hNp hnl hal hR hNp' hnl' hal' hR' hT hT' hTr hTr' oT hres hok).mono
        (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
    by_cases hs : IsShort nl al n
    · exact (openShort_rel hF hpc C C' (hpw X).choose_spec (hpw X').choose_spec hNp hnl hal hR hNp' hnl' hal' hR' hs hT hT' hTr hTr' oT hres
        hok).mono
        (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
    · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

theorem openM_rel (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₀' : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s₀) (hp' : (Proof.AesGcm.openX86_64M M).pre s₀')
    (hq : Proof.AesGcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B))
      fun _ _ => True :=
  openMW_rel hF v B (powOk_powers hF) (powers_ct hF) (longRel_openLong v B) hp hp' hq

theorem openMW_ct (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {pw lng gh : Prog isa} (hpw : PowOk M pw gh) (hpc : PowCT pw gh) (hlr : LongRel M lng) :
    ConstantTime isa (Proof.AesGcm.openX86_64M M).pre Proof.AesGcm.openX86_64.pub
      (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) pw lng gh) :=
  ct_of_rel fun _ _ hp hp' hq => openMW_rel hF v B hpw hpc hlr hp hp' hq

theorem openM_ct (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    ConstantTime isa (Proof.AesGcm.openX86_64M M).pre Proof.AesGcm.openX86_64.pub
      (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) :=
  openMW_ct hF v B (powOk_powers hF) (powers_ct hF) (longRel_openLong v B)

end VG.Proof.AesGcm.X86_64.Short
