module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Applying the encrypted counter to one data block

The memory-operand XOR avoids a separate input load. The following lemma
states its exact memory effect and preserves every other vector register.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (xorData srcAt)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (blockAt)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast inRegions_wr off_toNat
  blockAt_frame blockAt_writeW_xor blockAt_writeW_sep)

/-- Where the block written to `rdx + d` is read from: there, or, out of
place, at `rdx + rbx + d` (`srcAt`). -/
def srcAddr (s : State) (ix : Bool) (d : Nat) : Addr :=
  s.gpr .rdx + (if ix then s.gpr .rbx else BitVec.ofNat 64 0) + BitVec.ofNat 64 d

theorem ea_srcAt (s : State) (ix : Bool) (d : Nat) : s.ea (srcAt ix d) = srcAddr s ix d := by
  cases ix
  · simp only [srcAt, srcAddr, ea_at, ofInt_natCast, Bool.false_eq_true, ite_false, BitVec.add_zero]
  · show s.gpr .rdx + s.gpr .rbx * BitVec.ofNat 64 1 + BitVec.ofInt 64 (d : Int) = _
    simp only [srcAddr, BitVec.mul_one, ofInt_natCast, ite_true]

theorem srcAddr_false (s : State) (d : Nat) : srcAddr s false d = s.gpr .rdx + BitVec.ofNat 64 d := by
  simp only [srcAddr, Bool.false_eq_true, ite_false, BitVec.add_zero]

theorem xorData_one_ok (ix : Bool) (s : State) (b : XReg) (j : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.ea (srcAt ix (16 * j))) 16)
    (hw : InRegions s.wr (s.ea (at_ .rdx (16 * j))) 16) :
    WP isa (.block (xorData ix [b] j)) s fun t =>
      t.mem = s.mem.writeW (s.ea (at_ .rdx (16 * j)))
        (s.lane b 0 ^^^ s.mem.readW (s.ea (srcAt ix (16 * j))) 128) ∧
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

/-- `xorData ix regs j`: block `k` written to `rdx + 16 (j + k)` is the one
read from `srcAddr s ix (16 (j + k))` XORed with lane 0 of register `k`, for
a source each block of which is apart from the outputs written before it is
read (in place, the blocks are distinct). -/
theorem xorData_ok (ix : Bool) : ∀ (regs : List XReg) (j : Nat) (s : State), regs.Nodup →
    (∀ k < regs.length, InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) →
    (∀ k < regs.length, InRegions (s.rd ++ s.wr) (srcAddr s ix (16 * (j + k))) 16) →
    (∀ a b, a < b → b < regs.length → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s ix (16 * (j + b)), 16⟩) →
    (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64 →
    WP isa (.block (xorData ix regs j)) s fun s' =>
      (∀ k (h : k < regs.length), blockAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        blockAt s.mem (srcAddr s ix (16 * (j + k))) ^^^
          XBinOp.eval .pshufb (s.lane regs[k] 0) revMask) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → ∀ l < 2, s'.lane r l = s.lane r l)
  | [], _, s, _, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl,
      fun _ _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, hin, hsr, hsep, hw => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin hsr hsep hw
    rw [xorData, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    have hiw : InRegions s.wr (s.ea (at_ .rdx (16 * j))) 16 := by
      rwa [ea_at]
    have hir : InRegions (s.rd ++ s.wr) (s.ea (srcAt ix (16 * j))) 16 := by
      rw [ea_srcAt]; simpa only [Nat.add_zero] using hsr 0 (by omega)
    refine WP.mono (xorData_one_ok ix s b j hir hiw) fun s₁ ⟨m₁, f₁⟩ => ?_
    have g₁ : s₁.gpr = s.gpr := f₁.gpr
    have rd₁ : s₁.rd = s.rd := f₁.rd
    have wr₁ : s₁.wr = s.wr := f₁.wr
    have x₁ : ∀ r, r ≠ b → ∀ l < 2, s₁.lane r l = s.lane r l := by
      intro r hr l hl
      simpa only [State.setMem_lane] using f₁.lane r (by simpa using hr) l hl
    rw [ea_at, ea_srcAt] at m₁
    have hsa : ∀ d, srcAddr s₁ ix d = srcAddr s ix d := fun d => by simp only [srcAddr, g₁]
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (xorData_ok ix bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (fun k hk => by
        rw [rd₁, wr₁, hsa, show j + 1 + k = j + (k + 1) by omega]; exact hsr (k + 1) (by omega))
      (fun a c hac hc => by
        rw [hrdx, hsa, show j + 1 + a = j + (a + 1) by omega, show j + 1 + c = j + (c + 1) by omega]
        exact hsep (a + 1) (c + 1) (by omega) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    simp only [hsa] at hb
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
        rw [blockAt_frame hf hdj, m₁, blockAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide),
          blockAt_eq, pshufb_rev_xor, BitVec.xor_comm]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show j + (k + 1) = j + 1 + k by omega, hb k hk', m₁, blockAt_writeW_sep _ _ (by
            have hd := hsep 0 (k + 1) (by omega) (by omega)
            rw [Nat.add_zero, show j + (k + 1) = j + 1 + k by omega] at hd
            exact hd.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)),
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

/-- In place, block `j + a` is apart from block `j + b` for `a ≠ b`. -/
theorem xorData_sep_inplace (s : State) (j n : Nat) (hw : (s.gpr .rdx).toNat + 16 * (j + n) ≤ 2 ^ 64) :
    ∀ a b, a < b → b < n → Region.Disjoint
      ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * (j + a)), 16⟩ ⟨srcAddr s false (16 * (j + b)), 16⟩ := by
  intro a b hab hb
  rw [srcAddr_false]
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

end VG.Proof.Gcm.X86_64.StitchAvx8
