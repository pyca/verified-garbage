module

public import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.AArch64.Entry
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Entry
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesCcm.AArch64.Env
public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
import VerifiedGarbage.Proof.AesCcm.AArch64.Mac
meta import VerifiedGarbage.Impl.AesCcm.AArch64
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Env
meta import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Mac

/-! ### `AesCcm.AArch64.EntryCT`, which the modules that import this one used -/

section

/-! ### `AesCcm.AArch64.MacCT`, which the modules that import this one used -/

section

/-!
# AES-CCM on AArch64: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states that its correctness proof describes with the same public
values, leaks the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and those the correctness
proofs pin (the pointer and the length in `x23` and `x24`), and each call of
`vg_cmac_aes_update` by its proof (`rel_upd`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop minK)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite eval_zero Others)
open VG.Proof.CmacAes.Stream.AArch64 (upd_call upd_callLe)
open VG.Proof.AesCcm (headLen)

section
variable (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {σ₁ σ₂ : State} (E₁ : Env c σ₁)
  (E₂ : Env c σ₂) {y : Nat} (hy : y = 0 ∨ y = 96)
include L hv E₁ E₂ hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (updArgs y ++ ([ptr .x3 .x19 bO, imm .x4 1] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (rel_env [] E₁ E₂ (by simp) t) (updArgs_ok L E₁ hy) (updArgs_ok L E₂ hy)
    fun τ₁ τ₂ ⟨F₁, A₁, _⟩ ⟨F₂, A₂, _⟩ => rel_upd v hv A₁ A₂ (by rw [F₁.sp, F₂.sp])

/-- `absTail y`. -/
theorem absTail_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) (h13₁ : σ₁.gpr .x13 = BitVec.ofNat 64 (len % 16))
    (h13₂ : σ₂.gpr .x13 = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail v.callee y) TT := by
  refine RelCT.assoc (rel_seq (rel_env [.x23, .x24, .x13] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂, h13₁, h13₂])
      ⟨_, by taint_decide⟩)
    (absTailPre_ok E₁ hP₁ h23₁ h24₁ h13₁ h0) (absTailPre_ok E₂ hP₂ h23₂ h24₂ h13₂ h0) fun τ₁ τ₂ a₁ a₂ => ?_)
  exact updBlock_rel v L hv a₁.1 a₂.1 hy

/-- `absorbPad y`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h23₁ : σ₁.gpr .x23 = P) (h23₂ : σ₂.gpr .x23 = P) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 len)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.x23, .x24]))
      (.block (updArgs y ++ ([mov .x3 .x23, .lsr .x .x4 .x24 4] : List Instr))) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have hl := hP₁.lt
  -- After the call: the environment, the string's pointer and length.
  have call : ∀ {σ τ : State}, Env c σ → Buf c σ P len → σ.gpr .x23 = P → σ.gpr .x24 = BitVec.ofNat 64 len →
      Proof.CmacAes.Stream.AArch64.UArgsW c.N τ c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R
        (len / 16) → Env c τ → Others [.x0, .x1, .x2, .x3, .x4, .x5] σ τ → τ.rd = σ.rd → τ.wr = σ.wr →
      WP isa (callUpdate v.callee) τ fun ρ => Env c ρ ∧ Buf c ρ P len ∧ ρ.gpr .x23 = P ∧
        ρ.gpr .x24 = BitVec.ofNat 64 len :=
    fun _ hP h23 h24 U F g rd wr => WP.mono (upd_callLe v v.callee.name hv U) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, hP.of_eq (by rw [h.rd, rd]) (by rw [h.wr, wr]),
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h23],
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h24]⟩
  refine rel_seq (rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) t)
    (absArgs_ok L E₁ hy hP₁ h23₁ h24₁) (absArgs_ok L E₂ hy hP₂ h23₂ h24₂)
    fun τ₁ τ₂ ⟨U₁, F₁, g₁, _, rd₁, wr₁⟩ ⟨U₂, F₂, g₂, _, rd₂, wr₂⟩ => ?_
  refine rel_seq (rel_upd v hv U₁ U₂ (by rw [F₁.sp, F₂.sp])) (call E₁ hP₁ h23₁ h24₁ U₁ F₁ g₁ rd₁ wr₁)
    (call E₂ hP₂ h23₂ h24₂ U₂ F₂ g₂ rd₂ wr₂) fun ρ₁ ρ₂ ⟨G₁, B₁, x23₁, x24₁⟩ ⟨G₂, B₂, x23₂, x24₂⟩ => ?_
  refine rel_seq (rel_env [.x24] G₁ G₂ (by agree_tac [x24₁, x24₂]) ⟨_, by taint_decide⟩)
    (absMask_ok hl x24₁) (absMask_ok hl x24₂)
    fun κ₁ κ₂ ⟨x13₁, og₁, _, sp₁, rd₁', wr₁'⟩ ⟨x13₂, og₂, _, sp₂, rd₂', wr₂'⟩ => ?_
  have H₁ : Env c κ₁ := G₁.others og₁ (by first | decide | omega) sp₁ rd₁' wr₁'
  have H₂ : Env c κ₂ := G₂.others og₂ (by first | decide | omega) sp₂ rd₂' wr₂'
  refine rel_ite (eval_zero x13₁ (by omega_using [])) (eval_zero x13₂ (by omega_using [])) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] H₁ H₂ (by simp) ⟨_, by taint_decide⟩
  · exact absTail_rel v L hv H₁ H₂ hy (B₁.of_eq rd₁' wr₁') (B₂.of_eq rd₂' wr₂')
      (by rw [og₁ _ (by first | decide | omega), x23₁]) (by rw [og₂ _ (by first | decide | omega), x23₂])
      (by rw [og₁ _ (by first | decide | omega), x24₁]) (by rw [og₂ _ (by first | decide | omega), x24₂]) x13₁ x13₂ (of_decide_eq_false hf)

/-- `aadHead y`. -/
theorem aadHead_rel {A : Addr} {a : Nat} (hA₁ : Buf c σ₁ A a) (hA₂ : Buf c σ₂ A a) (ha0 : 0 < a)
    (h23₁ : σ₁.gpr .x23 = A) (h23₂ : σ₂.gpr .x23 = A) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 a)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 a) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead v.callee y) TT :=
  rel_assoc5 (rel_seq (rel_env [.x23, .x24] E₁ E₂ (by agree_tac [h23₁, h23₂, h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (aadHeadPre_ok E₁ hA₁ ha0 h23₁ h24₁) (aadHeadPre_ok E₂ hA₂ ha0 h23₂ h24₂)
    fun _ _ a₁ a₂ => updBlock_rel v L hv a₁.1 a₂.1 hy)

/-- The associated data, if there is any. -/
theorem aadPart_rel (h23₁ : σ₁.gpr .x23 = c.A) (h23₂ : σ₂.gpr .x23 = c.A)
    (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al) (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .x .x24) (.block []) (.seq (aadHead v.callee y) (absorbPad v.callee y)))
      TT := by
  have ha := L.al_lt
  refine rel_ite (eval_zero h24₁ ha) (eval_zero h24₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := of_decide_eq_false hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seq (aadHead_rel v L hv E₁ E₂ hy hA₁ hA₂ (by omega_using [h0]) h23₁ h23₂ h24₁ h24₂)
    (aadHead_ok v L hv E₁ hy hA₁ (by omega_using [h0]) h23₁ h24₁) (aadHead_ok v L hv E₂ hy hA₂ (by omega_using [h0]) h23₂ h24₂)
    fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : headLen c.al ≤ c.al := by unfold headLen; omega_using []
  exact absorbPad_rel v L hv A₁.env A₂.env hy ((hA₁.drop hn1).of_eq A₁.rd A₁.wr) ((hA₂.drop hn1).of_eq A₂.rd A₂.wr)
    A₁.x23 A₂.x23 A₁.x24 A₂.x24

/-- `b0 y`. -/
theorem b0_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) (h24₁ : σ₁.gpr .x24 = BitVec.ofNat 64 c.al)
    (h24₂ : σ₂.gpr .x24 = BitVec.ofNat 64 c.al) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (b0 v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [])) (.block (b0Seg y)) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine rel_seq (rel_env [.x24] E₁ E₂ (by agree_tac [h24₁, h24₂]) ⟨_, by taint_decide⟩)
    (flags_ok L E₁ S₁ h24₁) (flags_ok L E₂ S₂ h24₂)
    fun τ₁ τ₂ ⟨x9₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x9₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env c τ₁ := E₁.others g₁ (by first | decide | omega) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := E₂.others g₂ (by first | decide | omega) sp₂ rd₂ wr₂
  exact rel_seq (rel_env [] F₁ F₂ (by simp) t) (b0Seg_ok L F₁ hn₁ (by rw [m₁]; exact hc₁) x9₁ hy)
    (b0Seg_ok L F₂ hn₂ (by rw [m₂]; exact hc₂) x9₂ hy) fun _ _ a₁ a₂ => updBlock_rel v L hv a₁.1 a₂.1 hy

/-- `mac y`. -/
theorem mac_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (mac v.callee y) TT := by
  refine rel_seq (rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (aadLd_ok E₁ S₁) (aadLd_ok E₂ S₂)
    fun τ₁ τ₂ ⟨x23₁, x24₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x23₂, x24₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have F₁ : Env c τ₁ := E₁.others g₁ (by first | decide | omega) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := E₂.others g₂ (by first | decide | omega) sp₂ rd₂ wr₂
  refine rel_seq (b0_rel v L hv F₁ F₂ hy (by rw [m₁]; exact S₁) (by rw [m₂]; exact S₂) x24₁ x24₂ hn₁ hn₂
      (by rw [m₁]; exact hc₁) (by rw [m₂]; exact hc₂))
    (b0_ok v L hv F₁ (by rw [m₁]; exact S₁) x24₁ hn₁ (by rw [m₁]; exact hc₁) hy)
    (b0_ok v L hv F₂ (by rw [m₂]; exact S₂) x24₂ hn₂ (by rw [m₂]; exact hc₂) hy)
    fun κ₁ κ₂ ⟨M₁, y23₁, y24₁⟩ ⟨M₂, y23₂, y24₂⟩ => ?_
  refine rel_seq (aadPart_rel v L hv M₁.env M₂.env hy (by rw [y23₁, x23₁]) (by rw [y23₂, x23₂])
      (by rw [y24₁, x24₁]) (by rw [y24₂, x24₂]))
    (aadPart_ok v L hv M₁.env hy (by rw [y23₁, x23₁]) (by rw [y24₁, x24₁]))
    (aadPart_ok v L hv M₂.env hy (by rw [y23₂, x23₂]) (by rw [y24₂, x24₂])) fun ρ₁ ρ₂ P₁ P₂ => ?_
  refine rel_seq (rel_env [] P₁.env P₂.env (by simp) ⟨_, by taint_decide⟩) (dataArgs_ok P₁.env) (dataArgs_ok P₂.env)
    fun ω₁ ω₂ ⟨z23₁, z24₁, h₁, _, sp₁', rd₁', wr₁'⟩ ⟨z23₂, z24₂, h₂, _, sp₂', rd₂', wr₂'⟩ => ?_
  have G₁ : Env c ω₁ := P₁.env.others h₁ (by first | decide | omega) sp₁' rd₁' wr₁'
  have G₂ : Env c ω₂ := P₂.env.others h₂ (by first | decide | omega) sp₂' rd₂' wr₂'
  exact absorbPad_rel v L hv G₁ G₂ hy (L.bufD G₁.perm) (L.bufD G₂.perm) z23₁ z23₂ z24₁ z24₂

end

end VG.Proof.AesCcm.AArch64

end

end

/-!
# AES-CCM on AArch64: the arguments and the entry in two runs

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`,
the tag length and `tag` from the stack, which the taint analysis takes as
secret (it reads memory): the block is split after the loads
(`Proof.AesGcm.AArch64.RelCT.block_split`), and the rest runs from `x9`,
`x10` and `x11`, which hold `work`, the tag length and `tag`, public, in both
runs (`entry_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Impl.AesGcm.AArch64 (save)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint save_ok save_ok256 covers_prefix)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {Nw : Nat} {hNw : Nw ≤ 2176} {σ₁ σ₂ : State} (A₁ : Args (cxOf Nw hNw σ₁) (σ₁.gpr .x2) σ₁)
    (A₂ : Args (cxOf Nw hNw σ₂) (σ₂.gpr .x2) σ₂) (hq : onePub σ₁ σ₂) :
    Args (cxOf Nw hNw σ₁) (σ₁.gpr .x2) σ₁ ∧ Args (cxOf Nw hNw σ₁) (σ₁.gpr .x2) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have hcx : cxOf Nw hNw σ₂ = cxOf Nw hNw σ₁ := by
    simp only [cxOf, q0, q1, q3, q4, q5, q6, q7, qsp, qa 0 (by first | decide | omega), qa 1 (by first | decide | omega), qa 2 (by first | decide | omega)]
  rw [hcx, ← q2] at A₂
  exact ⟨A₁, A₂⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂)
    (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have run : ∀ {σ : State}, Args c N σ →
      WP isa (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9)) σ fun s' =>
        s'.gpr .x9 = c.W ∧ s'.gpr .x10 = BitVec.ofNat 64 c.tl ∧ s'.gpr .x11 = c.T ∧
        (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = σ.gpr r) ∧ s'.sp = σ.sp := fun A =>
    WP.block_append (WP.mono (ldr_ok A) fun s₁ ⟨x9₁, x10₁, x11₁, g₁, sp₁, _, _, wr₁⟩ => by
      obtain ⟨s₂, run₂, g₂, sp₂, _, _, _⟩ := save_ok256 s₁ .x9 x9₁ (by rw [wr₁]; exact covers_prefix A.perm.w (by omega))
      exact WP.of_runBlock ⟨s₂, run₂, by rw [g₂, x9₁], by rw [g₂, x10₁], by rw [g₂, x11₁],
        fun r h h' h'' => by rw [g₂, g₁ r h h' h''], by rw [sp₂, sp₁]⟩)
  have qsp : σ₁.sp = σ₂.sp := by rw [A₁.sp, A₂.sp]
  show RelCT isa _ (.block (([.ldrSp .x9 16, .ldrSp .x10 8, .ldrSp .x11 0] : List Instr) ++ save .x9 ++ _)) _
  refine Proof.AesGcm.AArch64.RelCT.block_split (rel_seq (Proof.AesGcm.AArch64.RelCT.block_split
      (rel_seq (rel_taint [] qsp (by simp) ⟨_, by taint_decide⟩) (ldr_ok A₁) (ldr_ok A₂)
        fun τ₁ τ₂ ⟨x9₁, _, _, _, sp₁, _⟩ ⟨x9₂, _, _, _, sp₂, _⟩ => ?_))
    (run A₁) (run A₂) fun τ₁ τ₂ ⟨x9₁, x10₁, x11₁, g₁, sp₁⟩ ⟨x9₂, x10₂, x11₂, g₂, sp₂⟩ => ?_)
  · exact rel_taint [.x9] (by rw [sp₁, sp₂, qsp]) (by agree_tac [x9₁, x9₂]) ⟨_, by taint_decide⟩
  refine rel_taint [.x9, .x10, .x11, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by rw [sp₁, sp₂, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; rw [x9₁, x9₂]
  by_cases h10 : r = .x10
  · subst h10; rw [x10₁, x10₂]
  by_cases h11 : r = .x11
  · subst h11; rw [x11₁, x11₂]
  rw [g₁ r h9 h10 h11, g₂ r h9 h10 h11]
  exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, h10, h11, false_or] at hr ⊢; exact hr)

end VG.Proof.AesCcm.AArch64

end

end

/-!
# AES-CCM on AArch64: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y` and `ctr`, run from
two states that their correctness proofs describe with the same public
values, leak the same: the code between calls by the taint analysis
(`rel_env`), each call of `vg_aes_ctr32` by its proof
(`Proof.AesGcm.AArch64.rel_ctr`), and the chunks of `ctr` by induction on
the blocks left (`RelCT.loop`): both runs encrypt the same number of blocks
in each chunk, which depends only on the length.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_ite rel_ctr eval_zero eval_nonzero Others ctr_call ctr_callLe CtrCall)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- Two runs from any states related by `P`, from those of each pair. -/
theorem rel_of_eq2 {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- What correctness says of the final states, added to two related runs. -/
theorem rel_post {σ₁ σ₂ : State} {c : Prog isa} {F₁ F₂ : State → Prop} (h : RelCT isa (Eq2 σ₁ σ₂) c TT)
    (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂) : RelCT isa (Eq2 σ₁ σ₂) c fun a b => F₁ a ∧ F₂ b :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

section
variable (v : Ctr32Impl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
include L hv E₁ E₂

/-- `tag y`. -/
theorem tag_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    RelCT isa (Eq2 σ₁ σ₂) (tag v.callee y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (([imm .x9 0] : List Instr) ++ ctrAt ++ ctrArgs ++ ([ptr .x3 .x19 y, imm .x4 1] : List Instr))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seq (rel_env [] E₁ E₂ (by simp) t) (tagArgs_ok L E₁ hn₁ hc₁ hy) (tagArgs_ok L E₂ hn₂ hc₂ hy)
    fun τ₁ τ₂ ⟨F₁, C₁, _⟩ ⟨F₂, C₂, _⟩ => rel_ctrLe v hv C₁ C₂ (by rw [F₁.sp, F₂.sp])

/-- `ctrTail`. -/
theorem ctrTail_rel {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0)
    (h23₁ : σ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h23₂ : σ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25₁ : σ₁.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h25₂ : σ₂.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16))
    (h26₁ : σ₁.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) (h26₂ : σ₂.gpr .x26 = BitVec.ofNat 64 (c.n % 16)) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrTail v.callee) TT := by
  have hj : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by
    have := L.hn
    have := Nat.le_self_pow (show 15 - c.nl ≠ 0 by have := L.h13; omega_arith) 256
    omega_arith
  -- After the call: the environment, the pointer and the length of the last bytes.
  have call : ∀ {σ τ : State}, σ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) →
      σ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) → Env c τ →
      CtrCall τ c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 c.N →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] σ τ →
      WP isa (callCtr v.callee) τ fun ρ => Env c ρ ∧ ρ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
        ρ.gpr .x26 = BitVec.ofNat 64 (c.n % 16) :=
    fun h23 h26 F C g => WP.mono (ctr_callLe v hv C) fun ρ h =>
      ⟨F.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h23],
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h26]⟩
  refine rel_seq (rel_env [.x25] E₁ E₂ (by agree_tac [h25₁, h25₂]) ⟨_, by taint_decide⟩)
    (tailSetup_ok L hn₁ E₁ hc₁ hj h25₁) (tailSetup_ok L hn₂ E₂ hc₂ hj h25₂)
    fun τ₁ τ₂ ⟨F₁, C₁, _, _, _, g₁, _⟩ ⟨F₂, C₂, _, _, _, g₂, _⟩ => ?_
  refine rel_seq (rel_ctrLe v hv C₁ C₂ (by rw [F₁.sp, F₂.sp])) (call h23₁ h26₁ F₁ C₁ g₁) (call h23₂ h26₂ F₂ C₂ g₂)
    fun ρ₁ ρ₂ ⟨G₁, x23₁, x26₁⟩ ⟨G₂, x23₂, x26₂⟩ => ?_
  exact rel_env [.x23, .x26] G₁ G₂ (by agree_tac [x23₁, x23₂, x26₁, x26₂]) ⟨_, by taint_decide⟩

end

/-- One chunk, from two states after the same number of blocks. -/
theorem chunk_rel (v : Ctr32Impl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl)
    (hn₂ : n₂.length = c.nl) {s₁ s₂ : State}
    (hc₁ : bytesAt s₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt s₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) {b : Nat} {σ₁ σ₂ : State}
    (I₁ : CtrInv c n₁ s₁ b σ₁) (I₂ : CtrInv c n₂ s₂ b σ₂) (hb : b < c.n / 16) :
    RelCT isa (Eq2 σ₁ σ₂) (ctrChunk v.callee) TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  refine RelCT.assoc (rel_seq (rel_env [.x24, .x25] I₁.env I₂.env (by agree_tac [I₁.x24, I₂.x24, I₁.x25, I₂.x25])
      ⟨_, by taint_decide⟩)
    (kSel_ok (b := b) I₁.x24 I₁.x25 (by omega_arith)) (kSel_ok (b := b) I₂.x24 I₂.x25 (by omega_arith))
    fun τ₁ τ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at x26₁ x26₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_arith
  have F₁ : Env c τ₁ := I₁.env.others g₁ (by first | decide | omega) sp₁ rd₁ wr₁
  have F₂ : Env c τ₂ := I₂.env.others g₂ (by first | decide | omega) sp₂ rd₂ wr₂
  have c0 : ∀ {n : List Byte} {s σ τ : State}, CtrInv c n s b σ → τ.mem = σ.mem →
      bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
      bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
    rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by first | decide | omega))) (by first | decide | omega), hc]
  have y23₁ : τ₁.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₁ _ (by first | decide | omega), I₁.x23]
  have y23₂ : τ₂.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) := by rw [g₂ _ (by first | decide | omega), I₂.x23]
  have y25₁ : τ₁.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₁ _ (by first | decide | omega), I₁.x25]
  have y25₂ : τ₂.gpr .x25 = BitVec.ofNat 64 (1 + b) := by rw [g₂ _ (by first | decide | omega), I₂.x25]
  have y24₁ : τ₁.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₁ _ (by first | decide | omega), I₁.x24]
  have y24₂ : τ₂.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) := by rw [g₂ _ (by first | decide | omega), I₂.x24]
  refine rel_seq (rel_env [.x23, .x25, .x26] F₁ F₂ (by agree_tac [y23₁, y23₂, y25₁, y25₂, x26₁, x26₂])
      ⟨_, by taint_decide⟩)
    (setup_ok L hn₁ hkb hk1 F₁ (c0 I₁ m₁ hc₁) y23₁ y25₁ x26₁) (setup_ok L hn₂ hkb hk1 F₂ (c0 I₂ m₂ hc₂) y23₂ y25₂ x26₂)
    fun ρ₁ ρ₂ ⟨G₁, C₁, _, _, h₁, _⟩ ⟨G₂, C₂, _, _, h₂, _⟩ => ?_
  have call : ∀ {τ ρ : State}, τ.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) → τ.gpr .x25 = BitVec.ofNat 64 (1 + b) →
      τ.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) → τ.gpr .x26 = BitVec.ofNat 64 k → Env c ρ →
      CtrCall ρ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k c.N →
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] τ ρ →
      WP isa (callCtr v.callee) ρ fun ω => Env c ω ∧ ω.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b) ∧
        ω.gpr .x25 = BitVec.ofNat 64 (1 + b) ∧ ω.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b) ∧
        ω.gpr .x26 = BitVec.ofNat 64 k :=
    fun h23 h25 h24 h26 G C g => WP.mono (ctr_callLe v hv C) fun ω h =>
      ⟨G.of_saved h.saved h.sp h.rd h.wr, by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h23],
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h25],
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h24],
        by rw [h.saved _ (by first | decide | omega) (by first | decide | omega), g _ (by first | decide | omega), h26]⟩
  refine rel_seq (rel_ctrLe v hv C₁ C₂ (by rw [G₁.sp, G₂.sp])) (call y23₁ y25₁ y24₁ x26₁ G₁ C₁ h₁)
    (call y23₂ y25₂ y24₂ x26₂ G₂ C₂ h₂) fun ω₁ ω₂ ⟨H₁, z23₁, z25₁, z24₁, z26₁⟩ ⟨H₂, z23₂, z25₂, z24₂, z26₂⟩ => ?_
  exact rel_env [.x23, .x24, .x25, .x26] H₁ H₂ (by agree_tac [z23₁, z23₂, z24₁, z24₂, z25₁, z25₂, z26₁, z26₂])
    ⟨_, by taint_decide⟩

/-- `ctr`. -/
theorem ctr_rel (v : Ctr32Impl) {c : Cx} (L : Lay c) (hv : v.scratch ≤ c.N) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂)
    {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (ctr v.callee) TT := by
  have hn64 := L.n_lt
  refine RelCT.assoc (rel_seq ?_ (ctrHead_ok v L hv hn₁ E₁ hc₁) (ctrHead_ok v L hv hn₂ E₂ hc₂) fun τ₁ τ₂ I₁ I₂ => ?_)
  · refine rel_seq (rel_env [] E₁ E₂ (by simp) ⟨_, by taint_decide⟩) (ctrHeadBlk_ok L (nonce := n₁) E₁)
      (ctrHeadBlk_ok L (nonce := n₂) E₂) fun τ₁ τ₂ I₁ I₂ => ?_
    have e₁ := eval_zero (a := c.n / 16) (by rw [I₁.x24, Nat.sub_zero]) (by omega_arith)
    have e₂ := eval_zero (a := c.n / 16) (by rw [I₂.x24, Nat.sub_zero]) (by omega_arith)
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega_arith, I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel v L hv hn₁ hn₂ hc₁ hc₂ J₁ J₂ hj) (chunk_ok v L hv hn₁ hc₁ J₁ hj)
      (chunk_ok v L hv hn₂ hc₂ J₂ hj)).mono (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₁.x24 (by omega_arith)
    have ev₂ := eval_nonzero (r := .x24) (a := c.n / 16 - (j + k)) K₂.x24 (by omega_arith)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega_arith
    · rw [ev₁] at ht; simp at ht; omega_arith
  · refine rel_seq (rel_env [] I₁.env I₂.env (by simp) ⟨_, by taint_decide⟩) (lastLen_ok L I₁.env) (lastLen_ok L I₂.env)
      fun ρ₁ ρ₂ ⟨x26₁, g₁, m₁, sp₁, rd₁, wr₁⟩ ⟨x26₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
    have F₁ : Env c ρ₁ := I₁.env.others g₁ (by first | decide | omega) sp₁ rd₁ wr₁
    have F₂ : Env c ρ₂ := I₂.env.others g₂ (by first | decide | omega) sp₂ rd₂ wr₂
    refine rel_ite (eval_zero x26₁ (by omega_arith)) (eval_zero x26₂ (by omega_arith)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_env [] F₁ F₂ (by simp) ⟨_, by taint_decide⟩
    · have c0 : ∀ {n : List Byte} {s σ τ : State}, CtrInv c n s (c.n / 16) σ → τ.mem = σ.mem →
          bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 →
          bytesAt τ.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n 0 := fun I hm hc => by
        rw [hm, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by first | decide | omega))) (by first | decide | omega), hc]
      exact ctrTail_rel v L hv F₁ F₂ hn₁ hn₂ (c0 I₁ m₁ hc₁) (c0 I₂ m₂ hc₂)
        (by rw [g₁ _ (by first | decide | omega), I₁.x23]) (by rw [g₂ _ (by first | decide | omega), I₂.x23])
        (by rw [g₁ _ (by first | decide | omega), I₁.x25]) (by rw [g₂ _ (by first | decide | omega), I₂.x25]) x26₁ x26₂

end VG.Proof.AesCcm.AArch64
