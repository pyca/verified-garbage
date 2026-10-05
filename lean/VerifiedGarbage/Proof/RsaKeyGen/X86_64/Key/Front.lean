import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Pieces
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE

/-!
# An RSA key from its primes on x86-64: the primes

The loads of `p`, `q` and `e` (`loads_k`), `p` and `q` ordered (`order_k`),
and `p − 1` and `q − 1` (`decTo_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

theorem sxM1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem maskNot (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- A header slot the pieces may change, written. -/
theorem KS.hdrW {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) {i : Nat} (hi : 29 ≤ i ∧ i < 32)
    {v : BitVec 64} (hm : t.mem = s.mem.writeW (off I.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) :
    KS I m₀ t ∧ KF I.B I.W [.hdr i] s.mem t.mem ∧ word t.mem I.B (8 * i) = v := by
  have hn := h.ws.scr.nowrap
  have := h.ws.h256
  have o := writeW_outside s.mem I.B v (d := 8 * i) (by omega)
  rw [← hm] at o
  have f : KF I.B I.W [.hdr i] s.mem t.mem := KF.of_outside o (.hdr i) (List.mem_singleton_self _)
    (by simp [Rc.range]) (by simp [Rc.range])
  exact ⟨h.step f (by simp [Rc.mut, hi.1, hi.2]) k hr, f, by rw [hm, word_writeW_self]⟩

/-! ## The loads -/

/-- `p`, `q` (`pl` octets each) into `aPa` and `aQa`, and `e` into `kEv`. -/
theorem loads_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (hpl : I.pb.length = I.pl)
    (hql : I.qb.length = I.pl) (hel : I.eb.length = I.el) (hpl1 : 1 ≤ I.pl) (hplW : I.pl ≤ 8 * I.W)
    (hel1 : 1 ≤ I.el) (hel8 : I.el ≤ 8) :
    WP isa (seqs (loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa)))))) s
      fun t => KS I m₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa, .hdr kEv] s.mem t.mem ∧
        av I t.mem aPa = Spec.Rsa.os2ip I.pb ∧ av I t.mem aQa = Spec.Rsa.os2ip I.qb ∧
        word t.mem I.B (8 * kEv) = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
  have hZ := h.hZ
  refine wp_seqs_append (by simp [loadA]) (by simp [loadA]) (WP.mono (loadA_ok h.ws (j := aPa) (by decide)
    (by decide) (by decide) h.args.pp h.args.pl h.p hpl hpl1 hplW) fun s₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have f₁ := KF.arr1 (I := I) (j := aPa) o₁ (Nat.le_refl _) (Nat.le_refl _)
  have h₁ := h.step f₁ (all_mut_arr (by decide)) k₁ (by decide)
  refine wp_seqs_append (by simp [loadA]) (by simp [loadE]) (WP.mono (loadA_ok h₁.ws (j := aQa) (by decide)
    (by decide) (by decide) h₁.args.qp h₁.args.pl h₁.q hql hpl1 hplW) fun s₂ ⟨v₂, o₂, k₂⟩ => ?_)
  have f₂ := KF.arr1 (I := I) (j := aQa) o₂ (Nat.le_refl _) (Nat.le_refl _)
  have h₂ := h₁.step f₂ (all_mut_arr (by decide)) k₂ (by decide)
  obtain ⟨hg, hZ8⟩ := h₂.ws.good
  refine wp_seqs_append (by simp [loadE]) (by simp) (WP.mono (loadE_ok hg hZ8 h₂.args.e
    (by rw [h₂.args.el, hel]) (by omega) (by omega) h₂.e) fun s₃ ⟨hbx, m₃, k₃⟩ => ?_)
  have h₃ := h₂.step (cs := []) (by rw [m₃]; exact KF.refl _ _ _) rfl k₃ (by decide)
  simp only [seqs]
  have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
    (BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb))) (by
      have hbx' : s₃.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
        rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hst, hbx']) rfl) fun t ⟨hm, k₄⟩ => ?_
  obtain ⟨ht, f₄, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega) hm k₄ (by decide)
  have hok : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  refine ⟨ht, ((f₁.trans f₂).trans (by rw [← m₃]; exact f₄)).mono (by simp), ?_, ?_, hw⟩
  · dsimp only [av]
    rw [f₄.arr (by decide) (j := aPa) (by decide) (by decide) h.hZ, m₃,
      f₂.arr (by decide) (j := aPa) (by decide) (by decide) h.hZ]; exact v₁
  · dsimp only [av]
    rw [f₄.arr (by decide) (j := aQa) (by decide) (by decide) h.hZ, m₃]; exact v₂

/-! ## The order -/

/-- `order`: `p` and `q` swapped if `p < q`. -/
theorem order_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) :
    WP isa (seqs order) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem ∧
      av I t.mem aPa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aQa else av I s.mem aPa) ∧
      av I t.mem aQa = (if av I s.mem aPa < av I s.mem aQa then av I s.mem aPa else av I s.mem aQa) := by
  have hn := h.ws.scr.nowrap
  have sP := h.ws.sl (j := aPa) (by decide)
  have sQ := h.ws.sl (j := aQa) (by decide)
  have sp := slot_far (w := I.W) (i := aPa) (j := aQa) (by decide)
  unfold order
  refine wp_seqs_append (by simp [ltA]) (by simp) (WP.mono (ltA_k h (a := aPa) (b := aQa) (by decide) (by decide))
    fun s₁ ⟨h₁, m₁, hbp, hbx, h10, h12, k₁⟩ => ?_)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (decide (av I s.mem aPa < av I s.mem aQa)) ∧
    t.mem = s₁.mem) (by xrun [hbp]) rfl) fun s₂ ⟨⟨h15, m₂⟩, k₂⟩ => ?_)
  refine WP.mono (cswap_ok (h₁.ws.scr.congr k₂.2.2) ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h10)
    h15 ((k₂.gpr (by decide)).trans h12) (by have := h.ws.w1; omega) (by have := h.ws.w2; omega) (by omega)
    (by omega) (by omega)) fun t ⟨hX, hY, hf, k₃⟩ => ?_
  have f : KF I.B I.W [.arr aPa, .arr aQa] s.mem t.mem := by
    rw [m₂, m₁] at hf
    exact KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aPa, by simp, by simp [Rc.range], by simp [Rc.range]⟩
      · exact ⟨.arr aQa, by simp, by simp [Rc.range], by simp [Rc.range]⟩
  rw [m₂, m₁] at hX hY
  refine ⟨h.step f (all_mut_arrs (js := [aPa, aQa]) (by decide)) ((k₁.trans k₂).trans k₃) (by decide), f, ?_, ?_⟩
  · dsimp only [av]; rw [hX]; split <;> simp_all
  · dsimp only [av]; rw [hY]; split <;> simp_all

/-! ## Minus one -/

theorem dec_arith {x y L : Nat} {b : Bool} (hx : x < L)
    (hv : x + (if (!decide (y = 0)) = true then 1 else 0) = y + L * b.toNat) : x = y - 1 := by
  by_cases hz : y = 0
  · simp only [hz, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.zero_add] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega
  · simp only [hz, decide_false, Bool.not_false, ite_true] at hv
    cases b <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at hv <;> omega

/-- `decTo o j`: `[o] := [j] − 1` (0 for 0), with word `W` zero. -/
theorem decTo_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {o j : Nat} (ho : o < 16) (hj : j < 16)
    (hoj : o ≠ j) (hoC : o ≠ aC) (hjC : j ≠ aC) :
    WP isa (seqs (decTo o j)) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr o, .arr aC] s.mem t.mem ∧
      av I t.mem o = av I s.mem j - 1 ∧ atop I t.mem o = 0 := by
  have hn := h.ws.scr.nowrap
  have hZ := h.hZ
  have e : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (eqMask j aC ++
      ([.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] ++ (constA 1 ++ subC o o)))) := by
    simp only [decTo, subC, List.append_assoc]
  rw [e]
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (zc_k h ho hj hoj) fun s₁ ⟨h₁, f₁, v₁, t₁⟩ => ?_)
  refine wp_seqs_append (by simp [constA]) (by simp [eqMask, eqA]) (WP.mono (constA_k h₁ 0) fun s₂ ⟨h₂, f₂, c₂, _⟩ => ?_)
  have hok : [Rc.arr aC].all Rc.ok = true := by decide
  have cz : av I s₂.mem aC = 0 := av_of_full c₂ (Nat.two_pow_pos _)
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) (WP.mono (eqMask_k h₂ (a := j) (b := aC) hj (by decide))
    fun s₃ ⟨h₃, m₃, hbp, _, k₃⟩ => ?_)
  have vj : av I s₂.mem j = av I s.mem j := by
    dsimp only [av]
    rw [f₂.arr hok hj (by simp [hjC]) hZ]
    exact f₁.arr (by simp [Rc.ok, ho]) hj (by simp [hoj.symm]) hZ
  rw [cz, vj] at hbp
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!decide (av I s.mem j = 0)) ∧ t.mem = s₃.mem)
    (by xrun [hbp, sxM1, maskNot]) rfl) fun s₄ ⟨⟨h15, m₄⟩, k₄⟩ => ?_
  have h₄ := h₃.step (cs := []) (by rw [m₄]; exact KF.refl _ _ _) rfl k₄ (by decide)
  refine wp_seqs_append (by simp [constA]) (by simp [subC]) (WP.mono (constA_k h₄ 1) fun s₅ ⟨h₅, f₅, c₅, k₅⟩ => ?_)
  have c1 : av I s₅.mem aC = 1 := av_of_full c₅ (Nat.one_lt_two_pow (by have := h.ws.w1; omega))
  refine WP.mono (subC_k h₅ (o := o) (a := o) ho ho hoC hoC (.inl rfl) (c := !decide (av I s.mem j = 0))
    (by rw [(k₅.gpr (by decide)), h15])) fun t ⟨ht, f₆, hb, t₆, _⟩ => ?_
  obtain ⟨b, hv⟩ := hb
  have vo : av I s₅.mem o = av I s.mem j := by
    dsimp only [av]
    rw [f₅.arr hok ho (by simp [hoC]) hZ, m₄, m₃, f₂.arr hok ho (by simp [hoC]) hZ]; exact v₁
  have tO : atop I s₅.mem o = 0 := by
    dsimp only [atop]
    rw [f₅.top hok ho (by simp [hoC]) hZ, m₄, m₃, f₂.top hok ho (by simp [hoC]) hZ]; exact t₁
  refine ⟨ht, ((((f₁.trans f₂).trans (by rw [← m₃, ← m₄]; exact f₅)).trans f₆)).mono (by simp), ?_, by rw [t₆]; exact tO⟩
  rw [c1, vo] at hv
  exact dec_arith (wv_lt t.mem I.B (slot I.W o) I.W) hv

end VG.Proof.RsaKeyGen.X86_64.Key
