import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Vec
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Lit

/-!
# Poly1305 on AArch64: `update`, with AdvSIMD

Untrusted: everything here is checked by Lean. `vg_poly1305_update_neon` is
`Radix64`'s `update` with `Vector.whole` absorbing the whole blocks of the
data: `vec` (at least 128 bytes) then the rest one at a time. `vec` uses `v8`–`v14`, whose low halves it
restores (`VPres`); the rest of the code writes no callee-saved vector
register.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.AArch64 (st off contains_off sub_sR sR wR eval_zero count_mod)
open VG.Proof.Poly1305.AArch64.Radix64 (UPre UCommon Cons ConsB Done Acc Keys Bounds dp dl kb Bf Dt dR Temps
  temps_of dl_lt hval)
open VG.Spec.Poly1305 (P bytesAt)

/-- The low halves of the callee-saved vector registers are those of `s`. -/
def VPres (s s' : State) : Prop := ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

theorem VPres.refl (s : State) : VPres s s := fun _ _ => rfl

theorem VPres.trans {s₁ s₂ s₃ : State} (h₁ : VPres s₁ s₂) (h₂ : VPres s₂ s₃) : VPres s₁ s₃ :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem VPres.of_v {s s' : State} (h : s'.v = s.v) : VPres s s' := fun r _ => by rw [h]

theorem lsr9_ok (s : State) :
    WP isa (.block [.lsr .x .x9 .x3 7]) s fun t =>
      t.gpr .x9 = s.gpr .x3 >>> 7 ∧ (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, ?_⟩
  refine WP.block_nil_iff.mpr ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · allstep
  · allstep

/-! ## `vec` within `update` -/

theorem vec_cons {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (hc : Cons s₀ c s)
    (h128 : 128 ≤ dl s₀ - c) :
    WP isa vec s fun t => Cons s₀ (c + 64 * ((dl s₀ - c) / 64)) t ∧ VPres s t := by
  have hdl := dl_lt s₀
  have hcl := hc.c_le
  have hx3 : (s.gpr .x3).toNat = dl s₀ - c := by rw [hc.x3, BitVec.toNat_ofNat]; omega
  have hst : s.gpr .x0 = st s₀ := hc.x0
  refine WP.mono (vec_ok hc.keys (by omega) (fun k hk => by
      rw [hc.wr, hst]; exact ⟨sR (st s₀), hp.wr, contains_off (by omega) (by omega)⟩)
    (fun d hd => by
      rw [hc.rd, hc.wr, hp.rd, hc.x2, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ⟨dR s₀, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega) (by omega)⟩))
    fun t ⟨M, hS, hE⟩ => ⟨?_, ?_⟩
  · have hq : nq s = (dl s₀ - c) / 64 := by simp only [nq, hx3]
    have hF : Frame [wR (st s₀)] s₀.mem M := hc.frame.trans (by
      rw [← hst]
      exact hS.frame.sub fun r hr => ⟨wR (s.gpr .x0), List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub (s.gpr .x0) (by decide) (by decide)⟩)
    refine { x0 := by rw [hE.x0, hst]
             keys := hc.keys.of_regs fun r hr => by
               simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
               rcases hr with rfl | rfl | rfl
               · exact hE.x7
               · exact hE.x8
               · exact hE.x17
             rd := by rw [hE.rd, hc.rd]
             wr := by rw [hE.wr, hc.wr]
             frame := by rw [hE.mem]; exact hF
             c_le := by omega
             whole := by have := hc.whole; omega
             x2 := by rw [hE.x2, hc.x2, BitVec.add_assoc, ← BitVec.ofNat_add, hq]
             x3 := by
               apply BitVec.eq_of_toNat_eq
               rw [hE.x3, hx3, BitVec.toNat_ofNat]; omega
             acc := fun hA => ?_ }
    obtain ⟨hv, hb⟩ := hc.acc hA
    obtain ⟨ev, eb⟩ := hE.acc hb
    refine ⟨?_, eb⟩
    have hX : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
      simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact hc.whole
    have hV : bytesAt M (s.gpr .x2) (64 * nq s) = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (64 * nq s) := by
      rw [hc.x2]
      refine Poly1305.bytesAt_frame hF (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.symm.sub_left (Offset.sub_base _ (by simp only [nq] at *; omega))).sub_right
        (sub_sR _ (by decide))
    rw [ev, hV, show Dt s₀ (c + 64 * ((dl s₀ - c) / 64)) = Dt s₀ c ++
        bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (64 * nq s) by rw [Dt, Dt, Poly1305.bytesAt_add, hq],
      ← List.append_assoc, Poly1305.absorbAll_append hX]
    exact Poly1305.absorbAll_congr hv _
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hE.vlow 0 (by decide)
    · exact hE.vlow 1 (by decide)
    · exact hE.vlow 2 (by decide)
    · exact hE.vlow 3 (by decide)
    · exact hE.vlow 4 (by decide)
    · exact hE.vlow 5 (by decide)
    · exact hE.vlow 6 (by decide)
    · rw [hE.v15]

/-! ## The whole blocks -/

theorem whole_keepsV : (Impl.Poly1305.AArch64.Radix64.whole).allInstrs keepsV = true := by decide +kernel

theorem vwhole_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .x3 = 0)) :
    WP isa Impl.Poly1305.AArch64.Vector.whole s fun s' =>
      ((∃ c, ConsB s₀ c s' ∧ dl s₀ - c < 16) ∨ (Done s₀ s' ∧ s'.gpr .x3 = 0)) ∧ VPres s s' := by
  have hdl := dl_lt s₀
  unfold Impl.Poly1305.AArch64.Vector.whole
  refine WP.seq (WP.mono (lsr9_ok s) fun s1 ⟨h9, hg, hv, hm, hrd, hwr⟩ => ?_)
  have ht : Temps s s1 := temps_of (fun r hr => hg r (by revert hr; decide +revert)) hm hrd hwr
  -- then the blocks one at a time
  have tail : ∀ s2, ((∃ c, Cons s₀ c s2) ∨ (Done s₀ s2 ∧ s2.gpr .x3 = 0)) → VPres s s2 →
      WP isa Impl.Poly1305.AArch64.Radix64.whole s2 fun s' =>
        ((∃ c, ConsB s₀ c s' ∧ dl s₀ - c < 16) ∨ (Done s₀ s' ∧ s'.gpr .x3 = 0)) ∧ VPres s s' :=
    fun s2 h2 v2 => WP.mono (WP.preservedV (Radix64.whole_ok hp h2) whole_keepsV) fun s' ⟨h', v'⟩ =>
      ⟨h', v2.trans v'⟩
  rcases h with ⟨c, hc⟩ | ⟨hd, hz⟩
  · have hc1 : Cons s₀ c s1 := { Temps.ucommon hc.toUCommon ht with
      c_le := hc.c_le, whole := hc.whole
      x2 := by rw [hg _ (by decide)]; exact hc.x2
      x3 := by rw [hg _ (by decide)]; exact hc.x3
      acc := Temps.acc hc.acc ht }
    have hcl := hc.c_le
    have h9' : s1.gpr .x9 = BitVec.ofNat 64 ((dl s₀ - c) / 128) := by
      rw [h9, hc.x3]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    refine WP.seq (WP.ite (decide ((dl s₀ - c) / 128 = 0))
      (by rw [eval_zero, h9', Poly1305.ofNat_beq_zero (by omega)]) (fun _ => ?_) (fun hnz => ?_))
    · exact WP.block_nil (tail s1 (.inl ⟨c, hc1⟩) (VPres.of_v hv))
    · simp only [decide_eq_false_iff_not] at hnz
      exact WP.mono (vec_cons hp hc1 (by omega)) fun s2 ⟨hc2, v2⟩ =>
        tail s2 (.inl ⟨_, hc2⟩) ((VPres.of_v hv).trans v2)
  · have h90 : s1.gpr .x9 = 0 := by rw [h9, hz]; rfl
    refine WP.seq (WP.ite true (by rw [eval_zero, h90]; rfl) (fun _ => ?_) (fun h => absurd h (by decide)))
    exact WP.block_nil (tail s1 (.inr ⟨Temps.done hd ht, by rw [hg _ (by decide)]; exact hz⟩) (VPres.of_v hv))

/-! ## The whole function -/

theorem prologue_keepsV : (Code.block (Impl.Poly1305.AArch64.Radix64.setup ++
    ([.movz .x .x9 15 0, .logic .and .x .x9 .x1 .x9] : List Instr)) : Prog isa).allInstrs keepsV = true := by
  decide +kernel

theorem fill_keepsV : (Code.ite (.zero .x .x9) (.block []) Impl.Poly1305.AArch64.Radix64.fill : Prog isa).allInstrs
    keepsV = true := by decide +kernel

theorem rest_keepsV : (Impl.Poly1305.AArch64.Radix64.rest).allInstrs keepsV = true := by decide +kernel

theorem epilogue_keepsV : (Code.block (Impl.Poly1305.AArch64.Radix64.reduce ++
    Impl.Poly1305.AArch64.Radix64.storeH) : Prog isa).allInstrs keepsV = true := by decide +kernel

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa Impl.Poly1305.AArch64.Vector.update s₀ fun s' =>
      Proof.Poly1305.updateAArch64.post s₀ s' ∧ VPres s₀ s' := by
  rw [Impl.Poly1305.AArch64.Vector.update]
  refine WP.seq (WP.mono (WP.preservedV (Radix64.uprologue_ok hp) prologue_keepsV) fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV
    (Q := fun s : State => (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .x3 = 0)) ?_ fill_keepsV)
    fun s₂ ⟨h₂, v₂⟩ => ?_)
  · refine WP.ite (decide (kb s₀ = 0))
      (by rw [eval_zero, h₁.x9, Poly1305.ofNat_beq_zero (by have := Radix64.kb_lt s₀; omega)]) (fun h => ?_)
      (fun _ => Radix64.fill_ok hp h₁)
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil (.inl ⟨0, h₁.cons h⟩)
  refine WP.seq (WP.mono (vwhole_ok hp h₂) fun s₃ ⟨h₃, v₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (Radix64.rest_ok hp h₃) rest_keepsV) fun s₄ ⟨h₄, v₄⟩ => ?_)
  exact WP.mono (WP.preservedV (Radix64.uepilogue_ok hp h₄) epilogue_keepsV) fun s' ⟨h', v'⟩ =>
    ⟨h', VPres.trans (VPres.trans (VPres.trans (VPres.trans v₁ v₂) v₃) v₄) v'⟩

def updateSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x5000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x5000, 128⟩]

theorem update_untouched : Untouched Impl.Poly1305.AArch64.Vector.update :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem update_ok (s : State) (hs : Proof.Poly1305.updateAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.Vector.update s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.updateAArch64.post s s' := by
  obtain ⟨t, s', he, h, hv⟩ := update_correct (UPre.of s hs)
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (update_untouched r hr) he, Exec.sp he, hv⟩, h⟩

theorem update_ct : ConstantTime isa Proof.Poly1305.updateAArch64.pre
    Proof.Poly1305.updateAArch64.pub Impl.Poly1305.AArch64.Vector.update := by
  refine VG.Taint.constantTime (A := VG.AArch64.taint) (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem update_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.Vector.update (Spec.Poly1305.updateContract AArch64.abi) :=
  Verified.of_correct update_ok update_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, AArch64.abi,
            AArch64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, AArch64.abi,
          AArch64.argRegs, Proof.Poly1305.AArch64.Vector.updateSat]
          [Proof.Poly1305.AArch64.Vector.updateSat] using Proof.Poly1305.AArch64.Vector.updateSat }

end VG.Proof.Poly1305.AArch64.Vector
