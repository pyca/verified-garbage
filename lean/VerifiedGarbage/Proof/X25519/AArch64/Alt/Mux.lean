module

public import VerifiedGarbage.Impl.X25519.AArch64.AltOps
public import VerifiedGarbage.Proof.X25519.AArch64.Alt.Mem
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # `mux_4`

The field element at `a` if `Z` is clear, else the one at `b`, into `o`. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Alt
variable {large : Bool}

open VG VG.AArch64 VG.Proof.Ed25519.AArch64

theorem mux4_ok {s : State} {base : Addr} (hs : Scr s base large) {o a b : Nat}
    (ho : AltRange o large) (ha : AltRange a large) (hb : AltRange b large)
    (hoa : SameOrApart o a) (hob : SameOrApart o b) :
    WP isa (.block (Impl.X25519.AArch64.Alt.mux4 o a b)) s fun t =>
      AltOp base o s t ∧ t.zf = s.zf ∧
        fe t.mem base o = if s.zf then fe s.mem base b else fe s.mem base a := by
  have _hcap := workSize_le large
  obtain ⟨oa, ob, oc⟩ := ho
  obtain ⟨aa, ab, ac⟩ := ha
  obtain ⟨ba, bb, bc⟩ := hb
  simp only [SameOrApart] at hoa hob
  have a16 : (a + 16) % 8 = 0 := by omega
  have b16 : (b + 16) % 8 = 0 := by omega
  have o16 : (o + 16) % 8 = 0 := by omega
  have w4 : Reg.x4 ≠ .x0 := by decide
  have w5 : Reg.x5 ≠ .x0 := by decide
  have w6 : Reg.x6 ≠ .x0 := by decide
  have w7 : Reg.x7 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [Impl.X25519.AArch64.Alt.mux4, runBlock_cons, runStep_some, runBlock_nil,
    ldp_sc hs aa (by omega) (by omega) (by decide : Reg.x4 ≠ .x5),
    ldp_sc ((hs.write w4 _).write w5 _) ba (by omega) (by omega) (by decide : Reg.x6 ≠ .x7),
    exec_cselc_x,
    stp_sc ((((((hs.write w4 _).write w5 _).write w6 _).write w7 _).write w4 _).write w5 _) oa
      (by omega) (by omega),
    ldp_sc (((((((hs.write w4 _).write w5 _).write w6 _).write w7 _).write w4 _).write w5 _).withMem _)
      a16 (by omega) (by omega) (by decide : Reg.x4 ≠ .x5),
    ldp_sc ((((((((hs.write w4 _).write w5 _).write w6 _).write w7 _).write w4 _).write w5 _).withMem
      _).write w4 _ |>.write w5 _) b16 (by omega) (by omega) (by decide : Reg.x6 ≠ .x7),
    stp_sc (((((((((((hs.write w4 _).write w5 _).write w6 _).write w7 _).write w4 _).write w5 _).withMem
      _).write w4 _).write w5 _).write w6 _).write w7 _ |>.write w4 _ |>.write w5 _) o16
      (by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.gpr_write, RegUpd.zf_write, mem_withMem, gpr_withMem,
    zf_withMem, CondCode.holds, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
    Bool.not_eq_true']
  have e1 : ∀ v w, word (st2 s.mem base o v w) base (a + 16) = word s.mem base (a + 16) :=
    fun v w => word_st2 _ _ v w (by omega) (by omega) (by omega)
  have e2 : ∀ v w, word (st2 s.mem base o v w) base (a + 16 + 8) = word s.mem base (a + 24) :=
    fun v w => (word_st2 _ _ v w (by omega) (by omega) (by omega)).trans (by rw [Nat.add_assoc])
  have e3 : ∀ v w, word (st2 s.mem base o v w) base (b + 16) = word s.mem base (b + 16) :=
    fun v w => word_st2 _ _ v w (by omega) (by omega) (by omega)
  have e4 : ∀ v w, word (st2 s.mem base o v w) base (b + 16 + 8) = word s.mem base (b + 24) :=
    fun v w => (word_st2 _ _ v w (by omega) (by omega) (by omega)).trans (by rw [Nat.add_assoc])
  simp only [e1, e2, e3, e4]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl, ?_⟩, trivial, ?_⟩
  · simp only [altClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_withMem, RegUpd.gpr_write, hr, ite_false]
  · simp only [mem_withMem]
    rw [st2_st2]
    exact st4_outside _ _ (by omega) _ _ _ _
  · rw [st2_st2, fe_st4 _ _ (by omega)]
    cases s.zf <;> rfl

end VG.Proof.X25519.AArch64.Alt
