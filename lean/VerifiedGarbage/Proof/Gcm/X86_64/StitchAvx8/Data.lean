import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.YFrame
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# Applying the encrypted counter to one data block

The memory-operand XOR avoids a separate input load. The following lemma
states its exact memory effect and preserves every other vector register.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (xorData)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (blockAt)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast inRegions_wr off_toNat
  blockAt_frame blockAt_writeW_xor blockAt_writeW_sep)

theorem xorData_one_ok (s : State) (b : XReg) (j : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.ea (at_ .rdx (16 * j))) 16)
    (hw : InRegions s.wr (s.ea (at_ .rdx (16 * j))) 16) :
    WP isa (.block (xorData [b] j)) s fun t =>
      t.mem = s.mem.writeW (s.ea (at_ .rdx (16 * j)))
        (s.lane b 0 ^^^ s.mem.readW (s.ea (at_ .rdx (16 * j))) 128) ∧
      YFrame [b] (s.setMem t.mem) t := by
  apply WP.of_runBlock
  simp only [xorData, List.append_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, State.load128, hr, ite_true, Option.map_some, VBinOp.sse,
    XBinOp.eval, State.store128_eq, State.setV_ea, State.setV_wr, hw,
    xmm_setV, ite_true, State.setV_mem, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · simp only [State.setMem_gpr, State.setV_gpr]
  · rfl
  · simp only [State.setMem_rd, State.setV_rd]
  · simp only [State.setMem_wr, State.setV_wr]
  · intro r hr l hl
    have hn : r ≠ b := by simpa using hr
    simp only [State.lane, State.setMem_xmm, State.setMem_ymmHi, xmm_setV, ymmHi_setV_128, hn, ite_false]

theorem xorData_ok : ∀ (regs : List XReg) (j : Nat) (s : State), regs.Nodup →
    (∀ k < regs.length, InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) →
    (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64 →
    WP isa (.block (xorData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.lane regs[k] 0) revMask) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l)
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, hin, hw => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin hw
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    have hiw : InRegions s.wr (s.ea (at_ .rdx (16 * j))) 16 := by
      rwa [ea_at]
    refine WP.mono (xorData_one_ok s b j (inRegions_wr hiw) hiw) fun s₁ ⟨m₁, f₁⟩ => ?_
    have g₁ : s₁.gpr = s.gpr := f₁.gpr
    have rd₁ : s₁.rd = s.rd := f₁.rd
    have wr₁ : s₁.wr = s.wr := f₁.wr
    have x₁ : ∀ r, r ≠ b → ∀ l < 2, s₁.lane r l = s.lane r l := by
      intro r hr l hl
      simpa only [State.setMem_lane] using f₁.lane r (by simpa using hr) l hl
    rw [ea_at] at m₁
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (xorData_ok bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    have ofs : ∀ a : Nat, (s.gpr .rdx + BitVec.ofInt 64 (a : Int)) = s.gpr .rdx + BitVec.ofNat 64 a :=
      fun a => by rw [ofInt_natCast]
    rw [ofs] at m₁
    -- Block `j` is not in the rest's frame.
    have hdj : ∀ r ∈ [(⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16⟩ r := by
      simp only [List.mem_singleton, forall_eq]
      intro a h₁ h₂
      simp only [Region.Contains] at h₁ h₂
      rw [off_toNat _ _ (by omega)] at h₁ h₂
      have := (a - s.gpr .rdx).isLt
      omega
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r hr' l hl => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf hdj, m₁]
        exact blockAt_writeW_xor s.mem _ (s.lane b 0)
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, blockAt_writeW_sep _ _ (by
            intro a h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rdx).isLt
            omega),
          x₁ _ (fun h => hbs (h ▸ List.getElem_mem hk')) 0 (by decide)]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega
    · simp only [List.mem_cons, not_or] at hr'
      rw [hx r hr'.2 l hl, x₁ r hr'.1 l hl]


end VG.Proof.Gcm.X86_64.StitchAvx8
