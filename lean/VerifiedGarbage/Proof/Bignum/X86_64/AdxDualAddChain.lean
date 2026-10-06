import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core

namespace VG.Proof.Bignum.X86_64.AdxDualAdd
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols number)

theorem chain_ok (s : State) (a b : Nat → Src) (va vb : Nat → BitVec 64) {c o : Bool}
    (hc : s.cf = some c) (ho : s.of = some o)
    (ha : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs s t → readSrc t (a k) = some (va k))
    (hb : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs s t → readSrc t (b k) = some (vb k))
    (hia : ∀ k < 8, ∀ n, a k ≠ .imm n) (hib : ∀ k < 8, ∀ n, b k ≠ .imm n) :
    WP isa (.block (AdxDualAdd.chain a b)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      cols t + 2^512*(c'.toNat+o'.toNat) = cols s + number va + number vb + c.toNat + o.toNat ∧
      Keeps AdxDualAdd.regs s t := by
  have k0 : Keeps [] s s := ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
  change WP isa (.block (
    AdxDualAdd.word .r8 (a 0) (b 0) ++ AdxDualAdd.word .r9 (a 1) (b 1) ++ AdxDualAdd.word .r10 (a 2) (b 2) ++ AdxDualAdd.word .r11 (a 3) (b 3) ++ AdxDualAdd.word .r12 (a 4) (b 4) ++ AdxDualAdd.word .r13 (a 5) (b 5) ++ AdxDualAdd.word .r14 (a 6) (b 6) ++ AdxDualAdd.word .r15 (a 7) (b 7))) s _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s (dst := .r8) (ha 0 (by decide) s (k0.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 0 (by decide) u ((k0.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 0 (by decide)) (hib 0 (by decide)) hc ho)
    fun s1 ⟨c1,o1,hc1,ho1,e1,q1⟩ => ?_
  have k1 := k0.trans q1
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s1 (dst := .r9) (ha 1 (by decide) s1 (k1.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 1 (by decide) u ((k1.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 1 (by decide)) (hib 1 (by decide)) hc1 ho1)
    fun s2 ⟨c2,o2,hc2,ho2,e2,q2⟩ => ?_
  have k2 := k1.trans q2
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s2 (dst := .r10) (ha 2 (by decide) s2 (k2.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 2 (by decide) u ((k2.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 2 (by decide)) (hib 2 (by decide)) hc2 ho2)
    fun s3 ⟨c3,o3,hc3,ho3,e3,q3⟩ => ?_
  have k3 := k2.trans q3
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s3 (dst := .r11) (ha 3 (by decide) s3 (k3.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 3 (by decide) u ((k3.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 3 (by decide)) (hib 3 (by decide)) hc3 ho3)
    fun s4 ⟨c4,o4,hc4,ho4,e4,q4⟩ => ?_
  have k4 := k3.trans q4
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s4 (dst := .r12) (ha 4 (by decide) s4 (k4.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 4 (by decide) u ((k4.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 4 (by decide)) (hib 4 (by decide)) hc4 ho4)
    fun s5 ⟨c5,o5,hc5,ho5,e5,q5⟩ => ?_
  have k5 := k4.trans q5
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s5 (dst := .r13) (ha 5 (by decide) s5 (k5.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 5 (by decide) u ((k5.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 5 (by decide)) (hib 5 (by decide)) hc5 ho5)
    fun s6 ⟨c6,o6,hc6,ho6,e6,q6⟩ => ?_
  have k6 := k5.trans q6
  rw [WP.block_append_iff]
  refine WP.mono (word_ok s6 (dst := .r14) (ha 6 (by decide) s6 (k6.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 6 (by decide) u ((k6.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 6 (by decide)) (hib 6 (by decide)) hc6 ho6)
    fun s7 ⟨c7,o7,hc7,ho7,e7,q7⟩ => ?_
  have k7 := k6.trans q7
  refine WP.mono (word_ok s7 (dst := .r15) (ha 7 (by decide) s7 (k7.mono (by simp [AdxDualAdd.regs])))
    (fun u ku => hb 7 (by decide) u ((k7.trans ku).mono (by simp [AdxDualAdd.regs])))
    (hia 7 (by decide)) (hib 7 (by decide)) hc7 ho7)
    fun s8 ⟨c8,o8,hc8,ho8,e8,q8⟩ => ?_
  have k8 := k7.trans q8
  rw [k1.gpr (by decide : Reg.r9 ∉ _)] at e2
  rw [k2.gpr (by decide : Reg.r10 ∉ _)] at e3
  rw [k3.gpr (by decide : Reg.r11 ∉ _)] at e4
  rw [k4.gpr (by decide : Reg.r12 ∉ _)] at e5
  rw [k5.gpr (by decide : Reg.r13 ∉ _)] at e6
  rw [k6.gpr (by decide : Reg.r14 ∉ _)] at e7
  rw [k7.gpr (by decide : Reg.r15 ∉ _)] at e8
  have f1 : s8.gpr .r8 = s1.gpr .r8 := ((((((q2.trans q3).trans q4).trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f2 : s8.gpr .r9 = s2.gpr .r9 := (((((q3.trans q4).trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f3 : s8.gpr .r10 = s3.gpr .r10 := ((((q4.trans q5).trans q6).trans q7).trans q8).gpr (by decide)
  have f4 : s8.gpr .r11 = s4.gpr .r11 := (((q5.trans q6).trans q7).trans q8).gpr (by decide)
  have f5 : s8.gpr .r12 = s5.gpr .r12 := ((q6.trans q7).trans q8).gpr (by decide)
  have f6 : s8.gpr .r13 = s6.gpr .r13 := (q7.trans q8).gpr (by decide)
  have f7 : s8.gpr .r14 = s7.gpr .r14 := q8.gpr (by decide)
  refine ⟨c8,o8,hc8,ho8,?_,k8.mono (by simp [AdxDualAdd.regs])⟩
  unfold cols number
  rw [f1,f2,f3,f4,f5,f6,f7]
  omega

end VG.Proof.Bignum.X86_64.AdxDualAdd
