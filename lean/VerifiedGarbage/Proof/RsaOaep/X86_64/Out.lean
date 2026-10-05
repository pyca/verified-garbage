import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-!
# RSAES-OAEP on x86-64: zeros to `out`

`zeroOut` writes `k` zeros to `out` (`zeroOut_ok`), a region apart from the
frame, the working space and the stack below the frame, which it leaves as
`Rep` says (`Rep.apart`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off word Scr off_off)

/-- A region apart from the frame, our working space and the stack below the
frame. -/
structure Apart (F S : Addr) (r : Region) : Prop where
  dF : Region.Disjoint ⟨F, frameBytes⟩ r
  dS : Region.Disjoint ⟨S, oRsa⟩ r
  dK : Region.Disjoint (retR F) r

/-- Writes to such a region leave `Rep`. -/
theorem Rep.apart {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep m F S V W) {r : Region} (ha : Apart F S r) (hf : Frame [r] m m') : Rep m' F S V W where
  scr o ho := by
    rw [← R.scr o ho]
    refine hf _ fun r' hr' hc => ?_
    rw [List.mem_singleton.mp hr'] at hc
    exact ha.dS _ ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide)) hc
  fr k hk := by
    rw [Bignum.X86_64.word, hf.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r' hr' => ?_)
      (by decide)]
    · exact R.fr k hk
    · rw [List.mem_singleton.mp hr']
      exact ha.dF.sub_left (Offset.sub_base F (by unfold nW frameBytes at *; omega))

structure ZeroI (u₀ : State) (o : Addr) (k j : Nat) (v : State) : Prop where
  keep : Keep [.r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  fr : Frame [⟨o, k⟩] u₀.mem v.mem
  zero : ∀ i < j, v.mem (o + BitVec.ofNat 64 i) = 0

theorem zeroOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o : Addr} {k : Nat} (ho : W 21 = o) (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k)
    (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr) (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa zeroOut u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      u'.gpr .rax = 0 ∧ Spec.Rsa.bytesAt u'.mem o k = List.replicate k 0 ∧ Frame [⟨o, k⟩] u.mem u'.mem := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rax, .r8] (Q := fun v => v.gpr .rdi = o ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk'⟩ => ?_)
  · xrun [zeroOut, ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.slot (d := sOut) (k := 21) rfl (by decide) ho, R.slot (d := sK) (k := 23) rfl (by decide) hk]
  have hsc : Scr v o k := Scr.of_mem (by rw [hk'.2.2]; exact hw) hnw
  refine WP.mono (byteLoop_ok hk0 (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.r8] by decide) (by decide) h₂)
    (ZeroI v o k) ?_ ⟨Keep.refl _ _, h₄, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun w I => ?_
  · intro j hj w I
    have hdw : w.gpr .rdi = o := (I.keep.gpr (by decide)).trans h₁
    have haw : w.gpr .rax = 0 := (I.keep.gpr (by decide)).trans h₃
    have hst : InRegions w.wr (o + BitVec.ofNat 64 j) 1 := by
      have := hsc.st8 (d := j) (by omega); rw [I.keep.2.2]; exact this
    refine WP.mono (WP.keep [] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.mem = w.mem.writeW (o + BitVec.ofNat 64 j) (0 : Byte)) ?_ rfl)
      fun w' ⟨⟨h8', hm'⟩, k'⟩ => ⟨(I.keep.trans k').mono (by decide), h8', fun w'' k'' hm'' h8'' => ?_⟩
    · xrun [ea_ix, hdw, haw, I.r8, show o + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = o + BitVec.ofNat 64 j from
        BitVec.add_zero _, hst]
      rfl
    · refine ⟨(I.keep.trans (k'.trans k'')).mono (by decide), h8'', ?_, fun i hi => ?_⟩
      · rw [hm'', hm']
        exact I.fr.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
      · rw [hm'', hm', VG.WriteBytes.writeW8_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [ifn (Offset.add_ofNat_ne o (by omega) (by omega) h), I.zero i (by omega)]
  · have fr : Frame [⟨o, k⟩] u.mem w.mem := by rw [← hm]; exact I.fr
    have Rw : Rep w.mem F S V W := Rep.apart R ha fr
    refine ⟨L.congr ((I.keep.gpr (by decide)).trans (hk'.gpr (by decide))) (I.keep.2.2.trans hk'.2.2) ?_,
      (hk'.trans I.keep).mono (by decide), Rw, (I.keep.gpr (by decide)).trans h₃, ?_, fr⟩
    · rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, Rw.fr 14 (by decide), R.fr 14 (by decide)]
    · simp only [Spec.Rsa.bytesAt]
      exact (List.map_congr_left fun i hi => I.zero i (List.mem_range.mp hi)).trans
        (by rw [List.map_const', List.length_range])

end VG.Proof.RsaOaep.X86_64
