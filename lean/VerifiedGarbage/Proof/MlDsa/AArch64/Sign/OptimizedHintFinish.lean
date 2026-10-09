import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHintFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64 (Only wp_lsr wp_nil)

theorem hintResultFlag_ok (s : State) :
    WP isa (.block [.lsr .x .x0 .x0 32,.logic .and .w .x24 .x24 .x0]) s fun t =>
      Only [.x0,.x24] s t ∧
      t.gpr .x24=((s.gpr .x24).setWidth 32 &&& ((s.gpr .x0)>>>32).setWidth 32).setWidth 64 := by
  refine wp_lsr (by decide) fun a ha hv => wp_and32 fun t ht htval => wp_nil ?_
  refine ⟨(ha.trans ht).mono (by simp),?_⟩
  rw [htval,ha.get .x24,hv]

/-- Exact combined counter and acceptance update; no branch depends on either. -/
theorem hintFinish_ok {S : Nat} (s : State)
    (hr : InRegions (s.rd++s.wr) (pa s (sc oONES)) 8)
    (hw : InRegions s.wr (pa s (sc oONES)) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Sign.Optimized.hintFinish) s fun t =>
      PPostB S s t [(sc oONES,8)] ∧
      t.mem=s.mem.writeW (pa s (sc oONES))
        (((s.mem.readW (pa s (sc oONES)) 64).setWidth 32+(s.gpr .x0).setWidth 32).setWidth 64) ∧
      t.gpr .x24=((s.gpr .x24).setWidth 32 &&& ((s.gpr .x0)>>>32).setWidth 32).setWidth 64 := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintFinish
  rw [WP.block_append_iff]
  refine WP.mono (onesAdd_ok s hr hw) fun a ⟨hm,ha⟩ => ?_
  refine WP.mono (hintResultFlag_ok a) fun t ⟨ht,hv⟩ => ?_
  have hmem := ht.mem.trans hm
  have hf : Frame [⟨pa s (sc oONES),8⟩] s.mem t.mem := by
    rw [hmem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨postB_of_keep (ha.trans ht.keep) (by decide) hf,hmem,?_⟩
  rw [hv,ha.get .x24,ha.get .x0]


/-- The low word carries only the hint count. -/
theorem hintPacked_count (c : Nat) (b : Prop) [Decidable b] :
    (BitVec.ofNat 64 (c + if b then 4294967296 else 0)).setWidth 32 = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  by_cases hb : b <;> simp [hb, BitVec.toNat_ofNat]

/-- The high word carries exactly the norm acceptance bit. -/
theorem hintPacked_flag (c : Nat) (hc : c < 2^32) (b : Prop) [Decidable b] :
    ((BitVec.ofNat 64 (c + if b then 4294967296 else 0)) >>> 32).setWidth 32 =
      if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  by_cases hb : b <;>
    simp [hb, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega

/-- Fold one helper result into the total count and strict acceptance flag. -/
theorem hintFinish_semantic {S : Nat} (s : State) (total count : Nat)
    (a b : Prop) [Decidable a] [Decidable b]
    (hr : InRegions (s.rd++s.wr) (pa s (sc oONES)) 8)
    (hw : InRegions s.wr (pa s (sc oONES)) 8)
    (hcount : total + count < 2^32)
    (hones : s.mem.readW (pa s (sc oONES)) 64 = BitVec.ofNat 64 total)
    (hresult : s.gpr .x0 = BitVec.ofNat 64 (count + if b then 4294967296 else 0))
    (hflag : s.gpr .x24 = bit a) :
    WP isa (.block Impl.MlDsa.AArch64.Sign.Optimized.hintFinish) s fun t =>
      PPostB S s t [(sc oONES,8)] ∧
      t.mem = s.mem.writeW (pa s (sc oONES)) (BitVec.ofNat 64 (total+count)) ∧
      t.gpr .x24 = bit (a ∧ b) := by
  refine WP.mono (hintFinish_ok (S := S) s hr hw) fun t ⟨hp,hm,hf⟩ => ?_
  refine ⟨hp,?_,?_⟩
  · rw [hm,ones32 hones,hresult,hintPacked_count,← BitVec.ofNat_add,sw_ofNat hcount]
  · rw [hf]
    apply bit_and hflag
    rw [hresult]
    exact hintPacked_flag count (by omega) b

end VG.Proof.MlDsa.AArch64.Sign
