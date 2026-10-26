module

public import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Group
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.AesCcm.AArch64.Header
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs

/-! # The eight-block loop and the remaining-block loop -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

abbrev advance := Impl.AesCfb.AArch64.Decrypt.advance

theorem advance_ok {s₀ s : State} {c d : Nat} (hd : d < 256) (hc : c+d ≤ N s₀)
    (hI : Inv s₀ (c+d) c s) :
    WP isa (.block (advance d)) s fun t => Inv s₀ (c+d) (c+d) t ∧ t.gpr .x13 = s.gpr .x13 := by
  rw [advance,Impl.AesCfb.AArch64.Decrypt.advance,WP.block_cons_iff]
  refine ⟨_, exec_addImm_x (imm := 16*d) (by omega), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := d) (by omega), WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_,?_,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,rfl⟩
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true,hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega), show N s₀-c-d=N s₀-(c+d) by omega]

theorem flag_bound (d m : Nat) : (if m<d then 1 else 0) < 2^64 := by
  split <;> decide

theorem check_ok {s₀ s : State} (hp : UPre s₀) {c p : Nat} (hI : Inv s₀ c p s) (d : Nat) (hd : d < 256) :
    WP isa (.block (Impl.AesCfb.AArch64.Decrypt.checkEnough d)) s fun t =>
      Inv s₀ c p t ∧ t.gpr .x13=BitVec.ofNat 64 (if N s₀-p<d then 1 else 0) := by
  rw [Impl.AesCfb.AArch64.Decrypt.checkEnough,WP.block_cons_iff]
  refine ⟨_,exec_subImm_x (imm := d) (by omega),?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_lsr_x (sh := 63) (by decide),WP.block_nil ?_⟩
  refine ⟨⟨hI.le,hI.keys.of_v (vs := []) ⟨by simp,by simp⟩ (fun _ _ => rfl) rfl rfl,
    hI.x2,hI.x3,hI.x11,hI.chain,hI.data,hI.frame,hI.rd,hI.wr⟩,?_⟩
  simp only [State.write,State.read,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,hI.x3]
  exact Proof.AesCcm.AArch64.sign63 (by have := hp.data_wrap; omega) (by omega)

theorem eval_short {s : State} {d m : Nat}
    (h : s.gpr .x13=BitVec.ofNat 64 (if m<d then 1 else 0)) :
    AArch64.eval (.nonzero .x .x13) s=some (decide (m<d)) := by
  rw [eval_nonzero h (flag_bound d m)]
  by_cases hm : m<d <;> simp [hm]

theorem group_advance_ok {s₀ s : State} (hp : UPre s₀) (b : VReg) (bs : List VReg)
    (hbr : BlockRegs (b::bs)) (h31 : .v31 ∉ b::bs) (hlen : (b::bs).length ≤ 8)
    {c : Nat} (hc : c+(b::bs).length ≤ N s₀) (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCfb.AArch64.Decrypt.group (b::bs)) s
      (Inv s₀ (c+(b::bs).length) (c+(b::bs).length)) := by
  exact group_ok hp b bs hbr h31 hlen hc hI _ fun _ hi _ =>
    WP.mono (advance_ok (by omega) hc hi) fun _ hi' => hi'.1

theorem batch_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+8 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa Impl.AesCfb.AArch64.Decrypt.batch s fun t =>
      Inv s₀ (c+8) (c+8) t ∧
        t.gpr .x13=BitVec.ofNat 64 (if N s₀-(c+8)<8 then 1 else 0) := by
  unfold Impl.AesCfb.AArch64.Decrypt.batch
  exact WP.seq (WP.mono (group_advance_ok hp .v0 [.v1,.v2,.v3,.v4,.v5,.v6,.v7]
    ⟨by decide,by decide⟩ (by decide) (by decide) hc hI) fun _ hi => check_ok hp hi 8 (by decide))

theorem tail_ok {s₀ s : State} (hp : UPre s₀) {c : Nat} (hc : c+1 ≤ N s₀)
    (hI : Inv s₀ c c s) :
    WP isa (Impl.AesCfb.AArch64.Decrypt.group [.v0]) s (Inv s₀ (c+1) (c+1)) :=
  group_advance_ok hp .v0 [] ⟨by decide,by decide⟩ (by decide) (by decide) hc hI

abbrev loops := Impl.AesCfb.AArch64.Decrypt.loops

theorem loops_ok {s₀ s₁ : State} (hp : UPre s₀) (hI₀ : Inv s₀ 0 0 s₁) :
    WP isa (loops) s₁ (Inv s₀ (N s₀) (N s₀)) := by
  have hn : N s₀ < 2^64 := (s₀.gpr .x4).isLt
  unfold loops Impl.AesCfb.AArch64.Decrypt.loops
  refine WP.seq (WP.mono (check_ok hp hI₀ 8 (by decide)) fun s₁ ⟨hI₁,h13⟩ => ?_)
  simp only [Nat.sub_zero] at h13
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀-c < 8 ∧ Inv s₀ c c s) ?_
    fun s₂ ⟨c,hc,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀<8)) (eval_short h13) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0,by simp at h; omega,hI₁⟩
    · refine WP.seq ?_
      rw [WP.block_cons_iff]
      refine ⟨_,rfl,WP.block_nil ?_⟩
      let I8 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c+8≤N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (Impl.AesCfb.AArch64.Decrypt.batch) s
          (fun t => (AArch64.eval (.zero .x .x13) t=some false ∧
            ∃ c, N s₀-c<8 ∧ Inv s₀ c c t) ∨
          (AArch64.eval (.zero .x .x13) t=some true ∧ ∃ m'<m,I8 m' t)) := by
        rintro m s ⟨c,rfl,hc,hi⟩
        refine WP.mono (batch_ok hp hc hi) fun t ⟨hi',h13'⟩ => ?_
        rw [eval_zero h13' (flag_bound 8 _)]
        by_cases hlt : N s₀-(c+8)<8
        · exact .inl ⟨by simp [hlt],c+8,hlt,hi'⟩
        · exact .inr ⟨by simp [hlt],N s₀-(c+8),by omega,c+8,rfl,by omega,hi'⟩
      exact WP.loop (M := isa) I8 hstep (N s₀) s₁ ⟨0,rfl,by simp at h; omega,hI₁⟩
  refine WP.seq (WP.mono (check_ok hp hI₂ 4 (by decide)) fun s₃ ⟨hi₃,h4⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun t => ∃ c, Inv s₀ c c t) ?_
    fun s₂ ⟨c,hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀-c<4)) (eval_short h4) (fun _ => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c,hi₃⟩
    · exact WP.mono (group_advance_ok hp .v0 [.v1,.v2,.v3] ⟨by decide,by decide⟩
        (by decide) (by decide) (by simp only [List.length_cons,List.length_nil]; simp at h; have := hi₃.le; omega) hi₃) fun _ hi => ⟨c+4,hi⟩
  refine WP.ite (decide (N s₀-c=0)) (eval_zero hI₂.x3 (by omega)) (fun h => ?_) (fun h => ?_)
  · have he : c=N s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (he ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m=N s₀-c ∧ c<N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (Impl.AesCfb.AArch64.Decrypt.group [.v0]) s
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

end VG.Proof.AesCfb.AArch64.Decrypt
