module

public import VerifiedGarbage.Proof.Bignum.X86.TwoPowerStep

/-! The branchless x86 helper produces the complete shared 64-bit metadata word. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.TwoPower
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.TwoPower

theorem code_pair_ok (s : State) :
    WP isa (.block code) s fun t =>
      (t.gpr .eax, t.gpr .edx) = rotatePower (s.gpr .ecx) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  unfold code
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_logicS (Or.inl rfl) rfl fun a A => wp_movS rfl fun b B _ => ?_
  have x : b.gpr .ecx = s.gpr .ecx &&& 63 := by rw [B.other .ecx (by decide), A.gpr]; rfl
  refine WP.block_append (WP.mono (step_input_ok (j := 0) (by decide) x B.gpr) ?_)
  rintro c ⟨yc, xc, mc, Kc⟩
  refine WP.block_append (WP.mono (step_input_ok (j := 1) (by decide) xc yc) ?_)
  rintro d ⟨yd, xd, md, Kd⟩
  refine WP.block_append (WP.mono (step_input_ok (j := 2) (by decide) xd yd) ?_)
  rintro e ⟨ye, xe, me, Ke⟩
  refine WP.block_append (WP.mono (step_input_ok (j := 3) (by decide) xe ye) ?_)
  rintro f ⟨yf, xf, mf, Kf⟩
  refine WP.block_append (WP.mono (step_input_ok (j := 4) (by decide) xf yf) ?_)
  rintro g ⟨yg, xg, mg, Kg⟩
  have K : Keeps [.eax, .ebx, .ecx, .edx] s g :=
    ((((((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans
      (Kc.mono (by decide))).trans (Kd.mono (by decide))).trans
      (Ke.mono (by decide))).trans (Kf.mono (by decide))).trans (Kg.mono (by decide))
  have mem : g.mem = s.mem := mg.trans (mf.trans (me.trans (md.trans (mc.trans (B.mem.trans A.mem)))))
  refine wp_movS rfl fun h H _ => wp_shr (by decide) fun i I _ =>
    wp_logicS (Or.inl rfl) rfl fun j J => wp_movS rfl fun k K₁ _ =>
    wp_subS rfl fun l L _ => wp_movS rfl fun m M _ =>
    wp_logicS (Or.inl rfl) rfl fun n N => wp_logicS (Or.inr rfl) rfl fun t T => WP.block_nil ?_
  have highBit : j.gpr .edx = ((s.gpr .ecx &&& 63) >>> 5) &&& 1 := by
    rw [J.gpr, I.gpr, H.gpr, xg]
    rfl
  have high : n.gpr .edx = (rotatePower (s.gpr .ecx)).2 := by
    rw [N.gpr, M.gpr, L.other .eax (by decide), K₁.other .eax (by decide),
      J.other .eax (by decide), I.other .eax (by decide), H.other .eax (by decide), yg,
      M.other .ebx (by decide), L.gpr, K₁.gpr, K₁.other .edx (by decide), highBit]
    rfl
  have low : t.gpr .eax = (rotatePower (s.gpr .ecx)).1 := by
    rw [T.gpr, N.other .eax (by decide), M.other .eax (by decide), L.other .eax (by decide),
      K₁.other .eax (by decide), J.other .eax (by decide), I.other .eax (by decide), H.other .eax (by decide), yg, high]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext low
    rw [T.other .edx (by decide), high]
  · rw [T.mem, N.mem, M.mem, L.mem, K₁.mem, J.mem, I.mem, H.mem, mem]
  · exact (((((((K.widen H.keeps).widen I.keeps).widen J.keeps).widen K₁.keeps).widen
      L.keeps).widen M.keeps).widen N.keeps).widen T.keeps


theorem code_ok (s : State) :
    WP isa (.block code) s fun t =>
      (t.gpr .edx ++ t.gpr .eax : BitVec 64) = BitVec.twoPow 64 ((s.gpr .ecx).toNat % 64) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s t := by
  refine WP.mono (code_pair_ok s) ?_
  rintro t ⟨pair, mem, K⟩
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change t.gpr .eax = (rotatePower (s.gpr .ecx)).1 at low
  change t.gpr .edx = (rotatePower (s.gpr .ecx)).2 at high
  have value := rotate_power_value (s.gpr .ecx).toNat
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at value
  refine ⟨?_, mem, K⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (t.gpr .eax).isLt, Nat.shiftLeft_eq,
    low, high, BitVec.toNat_twoPow_of_lt (Nat.mod_lt _ (by decide : 0 < 64))]
  omega

end VG.Proof.Bignum.X86.TwoPower
