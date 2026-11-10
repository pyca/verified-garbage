module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Body
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Prime
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: the results and the mask

`status`: the results and-ed, and with 1, into the frame (`status_ok`);
`maskArgs`: the mask `0 - st` into the frame, `edx` at `pre` and `ecx` its
bytes (`maskArgs_ok`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PrivPre (status maskArgs shl statusOffset stackAt)

section
variable {s t : State}

theorem status_ok (A : PPABI s) (B : Body s t) :
    WP isa (.block status) t fun u => Body s u ∧ Keeps [.eax] t u ∧ Frame [⟨slot s statusOffset, 4⟩] t.mem u.mem ∧
      u.mem.readW (slot s statusOffset) 32 = (t.gpr .eax &&& t.mem.readW (slot s statusOffset) 32) &&& 1 := by
  unfold status
  refine wp_logicS (.inl rfl) (B.readSlot A (d := statusOffset) (by decide)) fun u₁ a₁ => wp_andi fun u₂ a₂ => ?_
  have B₂ : Body s u₂ := B.next ((a₂.other _ (by decide)).trans (a₁.other _ (by decide))) (by rw [a₂.rd, a₁.rd])
    (by rw [a₂.wr, a₁.wr]) (by rw [a₂.mem, a₁.mem]; exact Frame.refl _ _)
  refine wp_slot A B₂ (d := statusOffset) (by decide) fun u₃ B₃ M₃ => WP.block_nil ⟨B₃, ?_, ?_, ?_⟩
  · exact ⟨fun r hr => by
      rw [M₃.gpr, a₂.other _ (by simpa using hr), a₁.other _ (by simpa using hr)],
      by rw [M₃.rd, a₂.rd, a₁.rd], by rw [M₃.wr, a₂.wr, a₁.wr]⟩
  · rw [M₃.mem, a₂.mem, a₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [M₃.mem, Mem.readW_writeW_self32, a₂.gpr, a₁.gpr]
    rfl

theorem maskArgs_ok (A : PPABI s) (B : Body s t) :
    WP isa (.block maskArgs) t fun u => Body s u ∧ Keeps [.eax, .ecx, .edx] t u ∧
      Frame [⟨slot s (statusOffset + 4), 4⟩] t.mem u.mem ∧
      u.mem.readW (slot s (statusOffset + 4)) 32 = 0 - t.mem.readW (slot s statusOffset) 32 ∧
      u.gpr .edx = arg s 0 ∧ (u.gpr .ecx).toNat = (arg s 1).toNat * 8 := by
  have pb := A.preBound
  rw [show maskArgs = [.mov .eax (.mem (stackAt statusOffset)), .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
    .store (stackAt (statusOffset + 4)) .ecx, .mov .edx (.mem (Impl.Bignum.X86.PrivPre.incoming 0)),
    .mov .ecx (.mem (Impl.Bignum.X86.PrivPre.incoming 1))] ++ (shl .ecx 3 ++ []) by simp [maskArgs]]
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (B.readSlot A (d := statusOffset) (by decide)) fun u₁ a₁ _ => wp_movi fun u₂ a₂ =>
    wp_sub fun u₃ a₃ _ => ?_
  have B₃ : Body s u₃ := B.next ((a₃.other _ (by decide)).trans ((a₂.other _ (by decide)).trans
    (a₁.other _ (by decide)))) (by rw [a₃.rd, a₂.rd, a₁.rd]) (by rw [a₃.wr, a₂.wr, a₁.wr])
    (by rw [a₃.mem, a₂.mem, a₁.mem]; exact Frame.refl _ _)
  refine wp_slot A B₃ (d := statusOffset + 4) (by decide) fun u₄ B₄ M₄ => ?_
  refine wp_movS (B₄.readArg A (by decide)) fun u₅ a₅ _ => ?_
  have B₅ : Body s u₅ := B₄.next (a₅.other _ (by decide)) a₅.rd a₅.wr (by rw [a₅.mem]; exact Frame.refl _ _)
  refine wp_movS (B₅.readArg A (by decide)) fun u₆ a₆ _ => shl_ok 3 fun u₇ K₇ m₇ e₇ => WP.block_nil ?_
  have M : u₇.mem = t.mem.writeW (slot s (statusOffset + 4)) (u₃.gpr .ecx) := by
    rw [m₇, a₆.mem, a₅.mem, M₄.mem, a₃.mem, a₂.mem, a₁.mem]
  refine ⟨B₅.next ((K₇.1 _ (by decide)).trans (a₆.other _ (by decide))) (by rw [K₇.2.1, a₆.rd])
    (by rw [K₇.2.2, a₆.wr]) (by rw [m₇, a₆.mem]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, by rw [K₇.2.1, a₆.rd, a₅.rd, M₄.rd, a₃.rd, a₂.rd, a₁.rd],
      by rw [K₇.2.2, a₆.wr, a₅.wr, M₄.wr, a₃.wr, a₂.wr, a₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K₇.1 _ (by simp [hr.2.1]), a₆.other _ hr.2.1, a₅.other _ hr.2.2, M₄.gpr, a₃.other _ hr.2.1,
      a₂.other _ hr.2.1, a₁.other _ hr.1]
  · rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [M, Mem.readW_writeW_self32, a₃.gpr, a₂.gpr, a₂.other .eax (by decide), a₁.gpr]
  · rw [K₇.1 _ (by decide), a₆.other _ (by decide), a₅.gpr]
  · rw [e₇, a₆.gpr]
    simp only [Nat.reducePow]
    have hl := A.preLength
    simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
      Spec.Rsa.modulusWords] at hl
    have l := A.lengths
    simp only [Spec.Rsa.lenValid] at l
    have := A.pLength
    have := A.qLength
    omega

end
end VG.Proof.Bignum.X86.PrivPre
