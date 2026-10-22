module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesCcm.AArch64.Header
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The seven-block loop and the remaining-block loop -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

def advance (d : Nat) : List Instr :=
  [.addImm .x .x2 .x2 (16*d), .subImm .x .x3 .x3 d]

theorem advance_ok {s₀ s : State} {c d : Nat} (hd : d < 256) (hc : c+d ≤ N s₀)
    (hI : Inv s₀ (c+d) c s) :
    WP isa (.block (advance d)) s fun t => Inv s₀ (c+d) (c+d) t ∧ t.gpr .x13 = s.gpr .x13 := by
  rw [advance,WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16*d) (by omega), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := d) (by omega), WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_,?_,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,rfl⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega), show N s₀-c-d=N s₀-(c+d) by omega]

theorem flag_bound (m : Nat) : (if m<7 then 1 else 0) < 2^64 := by
  split <;> decide

theorem check_ok {s₀ s : State} (hp : UPre s₀) {c p : Nat} (hI : Inv s₀ c p s) :
    WP isa (.block Impl.AesCbc.AArch64.Decrypt.checkEnough) s fun t =>
      Inv s₀ c p t ∧ t.gpr .x13=BitVec.ofNat 64 (if N s₀-p<7 then 1 else 0) := by
  rw [Impl.AesCbc.AArch64.Decrypt.checkEnough,WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := 7) (by decide),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_lsr_x (sh := 63) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    hI.x2,hI.x3,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,?_⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hI.x3]
  exact Proof.AesCcm.AArch64.sign63 (by have := hp.data_wrap; omega) (by decide)

theorem eval_short {s : State} {m : Nat}
    (h : s.gpr .x13=BitVec.ofNat 64 (if m<7 then 1 else 0)) :
    AArch64.eval (.nonzero .x .x13) s=some (decide (m<7)) := by
  rw [eval_nonzero h (flag_bound m)]
  by_cases hm : m<7 <;> simp [hm]

theorem batch_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+7 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.batch (R s₀)) s fun t =>
      Inv s₀ (c+7) (c+7) t ∧
        t.gpr .x13=BitVec.ofNat 64 (if N s₀-(c+7)<7 then 1 else 0) := by
  unfold Impl.AesCbc.AArch64.Decrypt.batch
  refine group_ok hp Impl.AesCbc.AArch64.Decrypt.regs7 (.inl rfl) hc hI _ fun u hi _ => ?_
  change WP isa (.block (advance 7 ++ Impl.AesCbc.AArch64.Decrypt.checkEnough)) u _
  rw [WP.block_append_iff]
  exact WP.mono (advance_ok (by decide) hc hi) fun _ ⟨hi',_⟩ => check_ok hp hi'

theorem tail_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+1 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.tail (R s₀)) s (Inv s₀ (c+1) (c+1)) := by
  unfold Impl.AesCbc.AArch64.Decrypt.tail
  change WP isa (.seq (.block (ldData [.v0] 0))
    (.seq (Impl.AesCbc.AArch64.Decrypt.rounds (R s₀) [.v0])
      (.block (Impl.AesCbc.AArch64.Decrypt.finishData [.v0] 0 ++ advance 1)))) s _
  exact group_ok hp [.v0] (.inr rfl) hc hI _ fun _ hi _ =>
    WP.mono (advance_ok (by decide) hc hi) fun _ hi' => hi'.1

abbrev loops := Impl.AesCbc.AArch64.Decrypt.loops

theorem loops_ok {s₀ s₁ : State} (hp : UPre s₀) (hI₀ : Inv s₀ 0 0 s₁) :
    WP isa (loops (R s₀)) s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : N s₀ < 2^64 := (s₀.gpr .x4).isLt
  unfold loops Impl.AesCbc.AArch64.Decrypt.loops
  refine WP.seq (WP.mono (check_ok hp hI₀) fun s₁ ⟨hI₁,h13⟩ => ?_)
  simp only [Nat.sub_zero] at h13
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀-c < 7 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c,hc,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀<7)) (eval_short h13) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0,by simp at h; omega,hI₁⟩
    · refine WP.seq ?_
      rw [WP.block_cons_iff]
      refine ⟨_,rfl,WP.block_nil ?_⟩
      let I7 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c+7≤N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I7 m s → WP isa (Impl.AesCbc.AArch64.Decrypt.batch (R s₀)) s
          (fun t => (AArch64.eval (.zero .x .x13) t=some false ∧
            ∃ c, N s₀-c<7 ∧ Inv s₀ c c t) ∨
          (AArch64.eval (.zero .x .x13) t=some true ∧ ∃ m'<m,I7 m' t)) := by
        rintro m s ⟨c,rfl,hc,hi⟩
        refine WP.mono (batch_ok hp hc hi) fun t ⟨hi',h13'⟩ => ?_
        rw [eval_zero h13' (flag_bound _)]
        by_cases hlt : N s₀-(c+7)<7
        · exact .inl ⟨by simp [hlt],c+7,hlt,hi'⟩
        · exact .inr ⟨by simp [hlt],N s₀-(c+7),by omega,c+7,rfl,by omega,hi'⟩
      exact WP.loop (M := isa) I7 hstep (N s₀) s₁ ⟨0,rfl,by simp at h; omega,hI₁⟩
  refine WP.ite (decide (N s₀-c=0)) (eval_zero hI₂.x3 (by omega)) (fun h => ?_) (fun h => ?_)
  · have he : c=N s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (he ▸ hI₂)
  · refine WP.seq ?_
    rw [WP.block_cons_iff]
    refine ⟨_,rfl,WP.block_nil ?_⟩
    let I1 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c<N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (Impl.AesCbc.AArch64.Decrypt.tail (R s₀)) s
        (fun t => (AArch64.eval (.nonzero .x .x3) t=some false ∧ Inv s₀ (N s₀) (N s₀) t) ∨
          (AArch64.eval (.nonzero .x .x3) t=some true ∧ ∃ m'<m,I1 m' t)) := by
      rintro m s ⟨c,rfl,hc,hi⟩
      refine WP.mono (tail_ok hp (by omega) hi) fun t hi' => ?_
      rw [eval_nonzero hi'.x3 (by omega)]
      by_cases hlast : N s₀-(c+1)=0
      · have he : c+1=N s₀ := by omega
        exact .inl ⟨by simp [hlast],he ▸ hi'⟩
      · exact .inr ⟨by simp [hlast],N s₀-(c+1),by omega,c+1,rfl,by omega,hi'⟩
    exact WP.loop (M := isa) I1 hstep (N s₀-c) s₂
      ⟨c,rfl,by have := hI₂.le; simp at h; omega,hI₂⟩

end VG.Proof.AesCbc.AArch64.Decrypt
