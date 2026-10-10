import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedHintFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLowState

/-! ## From `OptimizedHintFinish.lean` -/

section

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

end

/-! ## From `OptimizedHintState.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)

/-- Completed hint rows replace signed low coefficients in place. -/
structure PositiveIHb (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : PositiveKB p S σ t s
  z : SignedFam s (yBase p) p.ℓ (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1)
  high : NatFam s (wBase p) p.k (WHighv p σ (p.ℓ*t))
  low : SignedFam s (5+i) (p.k-i) (fun j=>R0v p σ (p.ℓ*t) (i+j)) (-(p.γ₂:Int)) p.γ₂
  h : HFam s 5 i (Hv p σ (p.ℓ*t))
  ones : s.mem.readW (pa s (sc oONES)) 64=BitVec.ofNat 64 (onesSum (Hv p σ (p.ℓ*t)) i)

def PositiveIH (p : Params) (S : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  PositiveIHb p S σ t i s ∧
    s.gpr .x24=bit ((ZOk p σ (p.ℓ*t) ∧ R0Ok p σ (p.ℓ*t)) ∧
      ∀j<i,normRq [CT0v p σ (p.ℓ*t) j]<p.γ₂)

theorem positiveIH_of_IR {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (h : PositiveIR p S σ t p.k s) : PositiveIH p S σ t 0 s := by
  refine ⟨⟨h.1.b,h.1.z,h.1.high,?_,by intro j hj; omega,?_⟩,?_⟩
  · simpa using h.1.low
  · simpa [onesSum] using h.1.ones
  · rw [h.2]
    apply bit_congr
    simp [R0Ok]


def positiveHfam (p : Params) (ws : List (VG.Impl.MlDsa.AArch64.Call.Ptr × Nat)) (i : Nat) : Bool :=
  kbChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ &&
  famChk (sgR p) (sgW p) ws (wBase p) p.k &&
  famChk (sgR p) (sgW p) ws (5+i) (p.k-i) &&
  famChk (sgR p) (sgW p) ws 5 i && keepB (sgR p) (sgW p) ws (sc oONES) 8

theorem PositiveIHb.step {p : Params} {S : Nat} {σ s u : State} {t i : Nat}
    (h : PositiveIHb p S σ t i s) {ws : List (VG.Impl.MlDsa.AArch64.Call.Ptr × Nat)}
    (hP : PPostB S s u ws) (hy : u.syms=s.syms) (hc : positiveHfam p ws i=true)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true) : PositiveIHb p S σ t i u := by
  simp only [positiveHfam,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hb,hz⟩,hh⟩,hl⟩,hf⟩,ho⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP hy hb hw,h.z.keep L hP hz,h.high.keep L hP hh,
    h.low.keep L hP hl,HFam.keep L hP hf h.h,(L.keepW hP ho).trans h.ones⟩

theorem SignedFam.shift {s : State} {b m : Nat} {f : Nat → Poly} {lo hi : Int}
    (h : SignedFam s b m f lo hi) (hm : 0<m) :
    SignedFam s (b+1) (m-1) (fun j=>f (j+1)) lo hi := by
  intro j hj
  have ht := h (j+1) (by omega)
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

end VG.Proof.MlDsa.AArch64.Sign

end
