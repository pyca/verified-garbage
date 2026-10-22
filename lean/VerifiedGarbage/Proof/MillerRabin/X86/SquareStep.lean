module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareFlag
public import VerifiedGarbage.Proof.MillerRabin.X86.StageEqual
public import VerifiedGarbage.Proof.MillerRabin.X86.ProductFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts

/-! # A squaring and its strong probable-prime flag update -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

def squareAreas (base : Addr) (w : Nat) (sp : BitVec 32) : List Region :=
  [⟨off base (arrAt w 6), 8 * w⟩, ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
    below sp 40, ⟨off base sE2, 4⟩, ⟨off base sF, 4⟩, ⟨off base sQ, 4⟩]

theorem square_step {σ s : State} {base : Addr} {bytes w q r : Nat} {F : Bool}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (hq : 0 < q ∧ q < 2 ^ 31) (hr : r < 2 ^ 31)
    (count : s.mem.readW (off base sQ) 32 = BitVec.ofNat 32 q)
    (threshold : s.mem.readW (off base sR) 32 = BitVec.ofNat 32 r)
    (flag : s.mem.readW (off base sF) 32 = BitVec.ofNat 32 F.toNat)
    (reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)) :
    WP isa sqStep s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sQ = q - 1 ∧ t.zf = some (decide (q = 1)) ∧
      numAt t.mem base w 6 = VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w 6) (numAt s.mem base w 6) ∧
      w32 t.mem base sF = (F || (decide (r < q) && decide
        (VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
          (numAt s.mem base w 6) (numAt s.mem base w 6) = numAt s.mem base w 8))).toNat ∧
      Frame (squareAreas base w (s.gpr .esp)) s.mem t.mem := by
  unfold sqStep seqs
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (facts.multiply (o := 6) (a := 6) (b := 6) h (by decide) (by decide)
    (by decide) (.inr (.inl rfl)) reduced) ?_)
  rintro u ⟨value, hu, _, productFrame⟩
  have sameP (d : Nat) (hd : d + 4 ≤ 256) : u.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    product_frame_header h.context h.room facts.fit (by decide) hd productFrame
  have minus := product_frame_num h.context h.room facts.fit (by decide)
    (show 5 ≤ 8 ∧ 8 < 28 by decide) (by decide) productFrame
  refine WP.seq (WP.mono (hu.equal (a := 6) (b := 8) (d := sE2) facts.lower facts.upper facts.fit
    (by decide) (by decide) (by decide) facts.width) ?_)
  rintro v ⟨equal, hv, outside, _⟩
  have prefixFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) facts.fit
  have equalFrame : Frame [⟨off base sE2, 4⟩] u.mem v.mem :=
    VG.Proof.Bignum.outside_frame outside (by decide)
  have sameE (d : Nat) (hd : d + 4 ≤ 256) (sep : d + 4 ≤ sE2 ∨ sE2 + 4 ≤ d) :
      v.mem.readW (off base d) 32 = u.mem.readW (off base d) 32 :=
    workspace_frame_word hu.context.ws.nowrap (Nat.le_trans hd prefixFit)
      (Nat.le_trans (by decide : sE2 + 4 ≤ 256) prefixFit) sep equalFrame
  simp only [← candidate_words] at equal
  rw [value, minus] at equal
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  have eqWord := readW_of_w32 (boolSmall _) equal
  refine WP.seq (WP.mono (square_flag hv facts.fit hq hr
    ((sameE sQ (by decide) (by decide)).trans ((sameP sQ (by decide)).trans count))
    ((sameE sR (by decide) (by decide)).trans ((sameP sR (by decide)).trans threshold))
    ((sameE sF (by decide) (by decide)).trans ((sameP sF (by decide)).trans flag)) eqWord) ?_)
  rintro t ⟨ht, countT, flagT, zero, flagFrame⟩
  have yE := header_frame_num hu.context.ws.nowrap facts.fit (show 6 < 28 by decide)
    (by decide : sE2 + 4 ≤ 256) equalFrame
  have yF := headers_frame_num (ds := [sF, sQ]) hv.context.ws.nowrap facts.fit (show 6 < 28 by decide)
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl <;> decide)
    flagFrame
  refine WP.block_nil ⟨ht, countT, zero, yF.trans (yE.trans value), flagT, ?_⟩
  have p : Frame (squareAreas base w (s.gpr .esp)) s.mem u.mem := productFrame.mono (by
    intro r hr; simp only [squareAreas, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  have e : Frame (squareAreas base w (s.gpr .esp)) u.mem v.mem := equalFrame.mono (by
    intro r hr; rw [List.mem_singleton.mp hr]; simp [squareAreas])
  have f : Frame (squareAreas base w (s.gpr .esp)) v.mem t.mem := flagFrame.mono (by
    intro r hr; simp only [squareAreas, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  exact (p.trans e).trans f

end VG.Proof.MillerRabin.X86
