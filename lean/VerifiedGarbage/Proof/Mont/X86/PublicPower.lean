module

public import VerifiedGarbage.Impl.Mont.X86.PublicPower
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.PowerHigh
import VerifiedGarbage.Proof.Mont.X86.PowerHighBounds
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The high-bit branch and padded fallback establish the same seed. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem publicPower_ok {s : State} {base : Addr} {size m acc out : Nat} {M : Mod}
    (hs : Scr s base size) (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (apart : out+8*M.n≤M.mo ∨ M.mo+8*M.n≤out)
    (small : 128*M.n<2^32) (positive : 1<m) (odd : m%2=1) :
    WP isa (publicPower M acc out) s fun t =>
      wordsVal t.mem base out M.n=2^(65*M.n)%m ∧ Modulus M size m t.mem base ∧
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] s.mem t.mem ∧ Keeps powerClob s t := by
  unfold publicPower
  refine WP.seq (wp_movS (readSrc_sc hs (d := M.mo+4*(2*M.n-1))
    (by have := hm.mo;have := hm.n0;omega)) fun u₁ U₁ _ => ?_)
  refine wp_shr (by decide) fun u₂ U₂ _ => ?_
  refine wp_cmpS rfl fun w U₃ Z => WP.block_nil ?_
  have mem : w.mem=s.mem := U₃.mem.trans (U₂.mem.trans U₁.mem)
  have K : Keeps powerClob s w :=
    ((U₁.keeps.mono (by decide)).widen U₂.keeps).trans (U₃.keeps powerClob)
  have Mw : Modulus M size m w.mem base := mem ▸ hm
  have finish : ∀ t, wordsVal t.mem base out M.n=2^(65*M.n)%m →
      Modulus M size m t.mem base →
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] w.mem t.mem → Keeps powerClob w t →
      wordsVal t.mem base out M.n=2^(65*M.n)%m ∧ Modulus M size m t.mem base ∧
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] s.mem t.mem ∧ Keeps powerClob s t := by
    intro t V T O L
    exact ⟨V,T,mem ▸ O,K.trans L⟩
  refine WP.ite (u₂.gpr .eax-1==0) (by simpa only [isa,eval] using Z) ?_ ?_
  · intro high
    have shifted : (s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32) >>> 31=1 := by
      have eq : (s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32) >>> 31-1=0 := by
        simpa only [beq_iff_eq,U₂.gpr,U₁.gpr] using high
      have add := congrArg (fun x : BitVec 32 => x+1) eq
      simpa only [BitVec.sub_add_cancel,show (0 : BitVec 32)+1=1 from rfl] using add
    have top : 2^31≤w32 s.mem base (M.mo+4*(2*M.n-1)) := by
      have h := congrArg BitVec.toNat shifted
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at h
      change _/2^31=1 at h
      change 2^31≤(s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32).toNat
      omega
    have full : 2^(64*M.n-1)<m :=
      high_seed_reduced hm.n0 (hm.val ▸ high_word_bound hm.n0 top) odd
    refine WP.mono (highPower_ok (hs.of_keeps K (by decide)) Mw hl apart full
      (by omega) (by omega)) fun t ⟨V,_,T,O,L⟩ => ?_
    apply finish t ?_ T O L
    simpa only [high_seed_doubled hm.n0] using V
  · intro _
    exact WP.mono (powerTwo_ok (hs.of_keeps K (by decide)) Mw hl apart positive
      (by have := hm.n0;omega) (by omega)) fun t ⟨V,_,T,O,L⟩ => finish t V T O L

end VG.Proof.Mont.X86.Dynamic
