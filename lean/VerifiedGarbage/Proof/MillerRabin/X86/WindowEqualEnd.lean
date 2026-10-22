module

public import VerifiedGarbage.Proof.MillerRabin.X86.WindowEnd
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowHeaders
public import VerifiedGarbage.Proof.MillerRabin.X86.StageEqual

/-! # Compare the window result with one and minus one, then update headers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem window_equal_end {σ s : State} {base : Addr} {bytes w d k : Nat} {v : BitVec 32} {F : Bool}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128) (hf : arrAt w 28 ≤ bytes)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w)
    (headers : WindowHeaders s.mem base v k F) (hd : d < 16) (hk : 0 < k ∧ k < 2 ^ 32)
    (digit : v >>> 28 = BitVec.ofNat 32 d) :
    WP isa (.seq (equal sE1 aY aT0) (.seq (equal sE2 aY aM1) (.block winEnd))) s fun t =>
      Stage base bytes w σ t ∧
      w32 t.mem base sF = (if d = 0 then F else
        decide (numAt s.mem base w 6 = numAt s.mem base w 11) ||
        decide (numAt s.mem base w 6 = numAt s.mem base w 8)).toNat ∧
      w32 t.mem base sV = (v <<< 4).toNat ∧ w32 t.mem base sK = k - 1 ∧
      t.zf = some (decide ((k - 1) % 8 = 0)) ∧
      (∀ a, a < 28 → numAt t.mem base w a = numAt s.mem base w a) := by
  refine WP.seq (WP.mono (h.equal (a := 6) (b := 11) (d := sE1) hw hu hf
    (by decide) (by decide) (by decide) width) ?_)
  rintro u ⟨eq1, huStage, outside1, _⟩
  have f1 : Frame [⟨off base sE1, 4⟩] s.mem u.mem := VG.Proof.Bignum.outside_frame outside1 (by decide)
  have headersU := headers.of_equal h.context hf (.inl rfl) f1
  have same1 (a : Nat) (ha : a < 28) : numAt u.mem base w a = numAt s.mem base w a :=
    header_frame_num h.context.ws.nowrap hf ha (by decide : sE1 + 4 ≤ 256) f1
  simp only [← candidate_words] at eq1
  refine WP.seq (WP.mono (huStage.equal (a := 6) (b := 8) (d := sE2) hw hu hf
    (by decide) (by decide) (by decide) width) ?_)
  rintro z ⟨eq2, hz, outside2, _⟩
  have f2 : Frame [⟨off base sE2, 4⟩] u.mem z.mem := VG.Proof.Bignum.outside_frame outside2 (by decide)
  have headersZ := headersU.of_equal huStage.context hf (.inr rfl) f2
  have same2 (a : Nat) (ha : a < 28) : numAt z.mem base w a = numAt u.mem base w a :=
    header_frame_num huStage.context.ws.nowrap hf ha (by decide : sE2 + 4 ≤ 256) f2
  simp only [← candidate_words] at eq2
  rw [same1 6 (by decide), same1 8 (by decide)] at eq2
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  have eq1U := readW_of_w32 (boolSmall _) eq1
  have hdrFit : 256 ≤ bytes := Nat.le_trans (Nat.le_add_right _ _) hf
  have eq1Z : z.mem.readW (off base sE1) 32 =
      BitVec.ofNat 32 (decide (numAt s.mem base w 6 = numAt s.mem base w 11)).toNat :=
    (workspace_frame_word huStage.context.ws.nowrap (Nat.le_trans (by decide : sE1 + 4 ≤ 256) hdrFit)
      (Nat.le_trans (by decide : sE2 + 4 ≤ 256) hdrFit) (by decide) f2).trans eq1U
  refine WP.mono (window_end hz hf hd hk (by rw [headersZ.word, digit]) headersZ.count headersZ.flag
    eq1Z (readW_of_w32 (boolSmall _) eq2)) ?_
  rintro t ⟨ht, flag, word, count, zero, fEnd⟩
  rw [headersZ.word] at word
  refine ⟨ht, flag, word, count, zero, ?_⟩
  intro a ha
  have last := headers_frame_num (ds := [sF, sV, sK]) hz.context.ws.nowrap hf ha
    (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl <;> decide) fEnd
  exact last.trans ((same2 a ha).trans (same1 a ha))

end VG.Proof.MillerRabin.X86
