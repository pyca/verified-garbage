module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on AArch64, `sign_message`: pieces of the correctness proofs

Untrusted: everything here is checked by Lean. The branch on whether the
context string is longer than 255 bytes (`lsr_ok`, `wp_ite_t`, `wp_ite_f`),
and the values of the saves (`Ctx.slotOffV`, `signSaves_vals`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_lsr wp_movz eval_nonzero ne_zero_iff)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `x9 ← ctx_len >> 8`, and the branch on it. -/
theorem lsr_ok (s : State) :
    WP isa (.block [.lsr .x .x9 .x4 8]) s fun s1 => Only [.x9] s s1 ∧
      isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (s.gpr .x4).toNat < 256) := by
  refine wp_lsr (by decide) fun s1 o1 e1 => wp_nil ⟨o1, ?_⟩
  rw [eval_nonzero, e1, ne_zero_iff, Proof.MlKem.AArch64.toNat_lsr]
  congr 1
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem Ctx.slotOffV {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx L g vv m₀ t) (o : Nat) : (Arg.slotOff fKey o).val t = L.key + BitVec.ofNat 64 o := by
  have := hc.slotV (f := fKey) (j := 0) rfl (by omega)
  simp only [Arg.val] at this ⊢
  rw [this]; rfl

theorem signSaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < signSaves.length), s1.gpr (signSaves[j]'hj).1 = (slay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signSaves, Lay.vals, slay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

end VG.Proof.MlDsa.AArch64.Message
