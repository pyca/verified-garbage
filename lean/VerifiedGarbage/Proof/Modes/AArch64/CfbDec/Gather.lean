module

public import VerifiedGarbage.Impl.Modes.AArch64.CfbDec
public import VerifiedGarbage.Proof.Modes.AArch64.Copy
import VerifiedGarbage.Proof.Modes.AArch64.Words
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Address setup and the optional preceding-ciphertext copy -/

@[expose] public section
namespace VG.Proof.Modes.AArch64.CfbDec
open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
variable {c : Core}

/-- The first gathered block is already present; copy the remaining `n` blocks. -/
theorem copy_tail_wp {S T : Addr} {n : Nat} {s : State}
    (hbw : 0 < c.bw) (hbw2 : c.bw ≤ 2)
    (hfit : 8 * c.bw * n < 2 ^ 63)
    (hS : ∀ t < c.bw * n, InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 (8*t)) 8)
    (hT : ∀ t < c.bw * n, InRegions s.wr (T + BitVec.ofNat 64 (8*t)) 8)
    (hsep : Region.Disjoint ⟨S,8*c.bw*n⟩ ⟨T,8*c.bw*n⟩)
    (ha : s.gpr .x14 = T) (hb : s.gpr .x15 = S)
    (hc : s.gpr .x17 = BitVec.ofNat 64 n) :
    WP isa (.ite (.zero .x .x17) (.block []) c.copyBlocks) s fun s' =>
      CopyInv c S T n s n s' ∧ s'.gpr .x15 = S + BitVec.ofNat 64 (8*c.bw*n) := by
  have hn : n < 2^64 := by
    have := Nat.le_mul_of_pos_left n (show 0 < 8*c.bw by omega_arith)
    omega_arith
  have hz : isa.eval (.zero .x .x17) s = some (decide (n = 0)) := by
    rw [eval_zero, hc, ofNat_beq_zero hn]
  refine WP.ite (decide (n=0)) hz (fun h => ?_) (fun h => ?_)
  · have hn0 : n = 0 := of_decide_eq_true h
    subst n
    refine WP.of_runBlock ⟨s,rfl,⟨?_,Frame.refl _ _,fun _ _ _ _ _ => rfl,rfl,rfl⟩,?_⟩
    · intro t ht; simp at ht
    · simpa using hb
  · exact copyBlocks_wp hbw hbw2 (by have := of_decide_eq_false h; omega_arith) hfit hS hT hsep ha hb hc

/-- Point past the first gathered block and count only the ciphertext copies. -/
theorem gatherArgs_ok (hbI : 8*c.buf < 4096) (hd14 : c.dataReg ≠ .x14)
    (s : State) {B : Addr} (hB : s.gpr sb = B) :
    ∃ s', runBlock isa c.cfbDecGatherArgs s = some s' ∧
      s'.gpr .x14 = B + BitVec.ofNat 64 (8*c.buf+16) ∧
      s'.gpr .x15 = s.gpr c.dataReg ∧ s'.gpr .x17 = s.gpr .x16 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁,e₁,a₁,o₁,m₁,rd₁,wr₁⟩ := addImm_ok s .x14 sb hbI
  obtain ⟨s₂,e₂,a₂,o₂,m₂,rd₂,wr₂⟩ := addImm_ok s₁ .x14 .x14 (v:=16) (by decide)
  obtain ⟨s₃,e₃,a₃,o₃,m₃,rd₃,wr₃⟩ := movR_ok s₂ .x15 c.dataReg
  obtain ⟨s₄,e₄,a₄,o₄,m₄,rd₄,wr₄⟩ := subImm_ok s₃ .x17 .x16 (v:=1) (by decide)
  refine ⟨s₄,?_,?_,?_,?_,fun r h1 h2 h3 => ?_,by rw [m₄,m₃,m₂,m₁],
    by rw [rd₄,rd₃,rd₂,rd₁],by rw [wr₄,wr₃,wr₂,wr₁]⟩
  · rw [Core.cfbDecGatherArgs, show ([.addImm .x .x14 sb (8*c.buf),.addImm .x .x14 .x14 16,
        movR .x15 c.dataReg,.subImm .x .x17 .x16 1] : List Instr) =
        [.addImm .x .x14 sb (8*c.buf)] ++ ([.addImm .x .x14 .x14 16] ++
        ([movR .x15 c.dataReg] ++ [.subImm .x .x17 .x16 1])) from rfl,
      runBlock_app,e₁,Option.bind_some,runBlock_app,e₂,Option.bind_some,runBlock_app,e₃,Option.bind_some,e₄]
  · rw [o₄ _ (by decide),o₃ _ (by decide),a₂,a₁,hB,addr_add]
  · rw [o₄ _ (by decide),a₃,o₂ _ hd14,o₁ _ hd14]
  · rw [a₄,o₃ _ (by decide),o₂ _ (by decide),o₁ _ (by decide)]
  · rw [o₄ r h3,o₃ r h2,o₂ r h1,o₁ r h1]

/-- The gathered inputs and the next chaining value, before encryption. -/
structure Gathered (c : Core) (B A : Addr) (n : Nat) (s₀ s : State) : Prop where
  inputs : ∀ t < 16*n, s.mem (B + BitVec.ofNat 64 (8*c.buf) + BitVec.ofNat 64 t) =
    if t < 16 then s₀.mem (B + BitVec.ofNat 64 (8*c.hiSlot) + BitVec.ofNat 64 t)
    else s₀.mem (A + BitVec.ofNat 64 (t-16))
  chain : ∀ u < 16, s.mem (B + BitVec.ofNat 64 (8*c.hiSlot) + BitVec.ofNat 64 u) =
    s₀.mem (A + BitVec.ofNat 64 (16*(n-1)+u))
  frame : Frame [⟨B + BitVec.ofNat 64 (8*c.buf),16*n⟩,
    ⟨B + BitVec.ofNat 64 (8*c.hiSlot),16⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .x8 → r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Gathering preserves the original ciphertext, including in a short final group. -/
theorem gather_wp {B A : Addr} {n : Nat} {s : State}
    (hbw : c.bw = 2) (hn : 0 < n) (hfit : 16*n < 2^63)
    (hbuf : 8*c.buf < 4096) (hhi : 8*c.hiSlot+16 ≤ 32768)
    (hd8 : c.dataReg ≠ .x8) (hd14 : c.dataReg ≠ .x14)
    (hB : s.gpr sb = B) (hA : s.gpr c.dataReg = A)
    (hc : s.gpr .x16 = BitVec.ofNat 64 n)
    (inT : ∀ w < 2*n, InRegions s.wr (B + BitVec.ofNat 64 (8*c.buf) + BitVec.ofNat 64 (8*w)) 8)
    (inH : ∀ w < 2, InRegions s.wr (B + BitVec.ofNat 64 (8*c.hiSlot) + BitVec.ofNat 64 (8*w)) 8)
    (inA : ∀ w < 2*n, InRegions (s.rd++s.wr) (A + BitVec.ofNat 64 (8*w)) 8)
    (dTA : Region.Disjoint ⟨B+BitVec.ofNat 64 (8*c.buf),16*n⟩ ⟨A,16*n⟩)
    (dTH : Region.Disjoint ⟨B+BitVec.ofNat 64 (8*c.buf),16*n⟩ ⟨B+BitVec.ofNat 64 (8*c.hiSlot),16⟩)
    (dHA : Region.Disjoint ⟨B+BitVec.ofNat 64 (8*c.hiSlot),16⟩ ⟨A,16*n⟩) :
    WP isa c.cfbDecGather s (Gathered c B A n s) := by
  let T := B + BitVec.ofNat 64 (8*c.buf)
  let H := B + BitVec.ofNat 64 (8*c.hiSlot)
  let U := T + BitVec.ofNat 64 16
  have h16 : 16 ≤ 16*n := by omega_arith
  have subT : Region.Sub ⟨T,16⟩ ⟨T,16*n⟩ := Region.sub_prefix h16
  have subU : Region.Sub ⟨U,16*(n-1)⟩ ⟨T,16*n⟩ := VG.Offset.sub_base T (by omega_arith)
  have subA : Region.Sub ⟨A,16*(n-1)⟩ ⟨A,16*n⟩ := Region.sub_prefix (by omega_arith)
  unfold Core.cfbDecGather
  refine WP.seq (WP.block_append (WP.mono (copyN_wp (k:=2) (P:=T) (Q:=H) (u:=.x8)
    ⟨by rw [hB],by rw [hB],by decide,by decide,by decide,by decide,
      by omega_arith,by omega_arith,by omega_arith, hhi,
      fun w hw => inT w (by omega_arith),fun w hw => inRd (inH w hw),dTH.sub_left subT,by decide⟩) fun s₁ h₁ => ?_))
  obtain ⟨s₂,e₂,a₂,b₂,c₂,o₂,m₂,rd₂,wr₂⟩ := gatherArgs_ok hbuf hd14 s₁
    (by rw [h₁.regs _ (by decide) (by decide),hB])
  refine WP.of_runBlock ⟨s₂,e₂,?_⟩
  have cm₂ : s₂.mem = over s.mem T 16 (fun i => s.mem (H+BitVec.ofNat 64 i)) := by rw [m₂,h₁.mem]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂,h₁.rd]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂,h₁.wr]
  refine WP.seq (WP.mono (copy_tail_wp (c:=c) (S:=A) (T:=U) (n:=n-1)
    (by omega_arith) (by omega_arith) (by rw [hbw]; omega_arith)
    (fun w hw => by rw [rd₂',wr₂']; exact inA w (by rw [hbw] at hw; omega_arith))
    (fun w hw => by
      rw [wr₂',addr_add,show 16+8*w = 8*(2+w) by omega_arith]
      exact inT (2+w) (by rw [hbw] at hw; omega_arith))
    (by simpa [hbw] using (dTA.symm.sub_left subA).sub_right subU)
    (by rw [a₂]; exact (addr_add B (8*c.buf) 16).symm)
    (by rw [b₂,h₁.regs _ hd8 hd8,hA])
    (by rw [c₂,h₁.regs _ (by decide) (by decide),hc,VG.Offset.ofNat_sub_ofNat (by omega_arith)]))
    fun s₃ ⟨h₃,p₃⟩ => ?_)
  have base₃ : s₃.gpr sb = B := by
    rw [h₃.regs _ (by decide) (by decide) (by decide) (by decide),o₂ _ (by decide) (by decide) (by decide),h₁.regs _ (by decide) (by decide),hB]
  have A₂ : ∀ t < 16*n, s₂.mem (A+BitVec.ofNat 64 t) = s.mem (A+BitVec.ofNat 64 t) := by
    intro t ht; rw [cm₂]; exact over_sep (dTA.sub_left subT) ht (by omega_arith)
  have A₃ : ∀ t < 16*n, s₃.mem (A+BitVec.ofNat 64 t) = s.mem (A+BitVec.ofNat 64 t) := by
    intro t ht
    have fr := h₃.frame
    rw [hbw] at fr
    exact (fr.bytes (R:=⟨A,16*n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dTA.symm.sub_right subU) (by simp only; omega_arith) ht).trans (A₂ t ht)
  refine WP.mono (copyN_wp (k:=2) (P:=H) (Q:=A+BitVec.ofNat 64 (16*(n-1))) (u:=.x8)
    ⟨by rw [base₃],by rw [p₃,hbw]; simp,
      by decide,by decide,by decide,by decide,by omega_arith,by decide,hhi,by decide,
      fun w hw => by rw [h₃.wr,wr₂']; exact inH w hw,
      fun w hw => by
        rw [h₃.rd,h₃.wr,rd₂',wr₂',addr_add,show 16*(n-1)+8*w=8*(2*(n-1)+w) by omega_arith]
        exact inA _ (by omega_arith),
      dHA.sub_right (VG.Offset.sub_base A (by omega_arith)),by decide⟩) fun s₄ h₄ => ?_
  have T₄ : ∀ t < 16*n, s₄.mem (T+BitVec.ofNat 64 t) = s₃.mem (T+BitVec.ofNat 64 t) := by
    intro t ht; rw [h₄.mem]; exact over_sep dTH.symm ht (by omega_arith)
  refine ⟨?_,?_,?_,fun r h8 h14 h15 h17 => by
    rw [h₄.regs r h8 h8,h₃.regs r h8 h14 h15 h17,o₂ r h14 h15 h17,h₁.regs r h8 h8],
    by rw [h₄.rd,h₃.rd,rd₂'],by rw [h₄.wr,h₃.wr,wr₂']⟩
  · intro t ht
    rw [T₄ t ht]
    by_cases h : t < 16
    · rw [ite_eq_left h]
      have fr := h₃.frame
      rw [hbw] at fr
      have keep := fr.bytes (R:=⟨T,16⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.base_disjoint T (e:=16) (n:=16*(n-1)) (by decide) (by omega_arith))
        (by simp only; decide) h
      rw [keep,cm₂,over_at h (by decide)]
    · rw [ite_eq_right h,show T+BitVec.ofNat 64 t=U+BitVec.ofNat 64 (t-16) by
        change T+BitVec.ofNat 64 t=(T+BitVec.ofNat 64 16)+BitVec.ofNat 64 (t-16)
        have e := addr_add T 16 (t-16)
        rw [show 16+(t-16)=t by omega_arith] at e
        exact e.symm,
        h₃.copied _ (by rw [hbw]; omega_arith),A₂ _ (by omega_arith)]
  · intro u hu
    rw [h₄.mem,over_at hu (by decide),addr_add,A₃ _ (by omega_arith)]
  · have f₁ : Frame [⟨T,16⟩] s.mem s₁.mem := by rw [h₁.mem]; exact over_frame _ _ _ _
    have f₂ : Frame [⟨T,16⟩] s.mem s₂.mem := by rw [m₂]; exact f₁
    have f₃ := h₃.frame
    rw [hbw] at f₃
    refine ((f₂.sub (fun r hr => ⟨⟨T,16*n⟩,List.mem_cons_self,by
      simp only [List.mem_singleton] at hr; subst hr; exact subT⟩)).trans
      (f₃.sub (fun r hr => ⟨⟨T,16*n⟩,List.mem_cons_self,by
        simp only [List.mem_singleton] at hr; subst hr; exact subU⟩))).trans ?_
    rw [h₄.mem]
    exact (over_frame _ _ _ _).sub fun r hr => ⟨⟨H,16⟩,List.mem_cons_of_mem _ List.mem_cons_self,by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ hx => hx⟩

end VG.Proof.Modes.AArch64.CfbDec
