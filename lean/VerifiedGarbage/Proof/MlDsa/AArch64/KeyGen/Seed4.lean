import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp

/-! ## From `Mask4.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrw wp_strw wp_addImm wp_subImm
  count_loop)
open VG.Spec.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)

theorem coeffAt_writeW32_4 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 1024) (hj : j < 1024) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

theorem ofNat4_sub1 {i : Nat} (h : i < 1024) : BitVec.ofNat 64 (1024 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (1024 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem mask4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 4096 = true) (hin : inB (rbs ++ wbs) a 4096 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (mask4 a) s fun s' => PPostB S s s' [(a, 4096)] ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧
      ∀ i < 1024, coeffAt s'.mem (pa s a) i =
        if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 4096 := L.inW hw
  have hn : (pa s a).toNat + 4096 ≤ 2 ^ 64 := L.nwp hin
  have hb : a.1 ∈ keptRegs := L.ptrBs hin
  have h1 : a.1 ≠ .x1 := by intro e; rw [e] at hb; revert hb; decide
  have h8 : a.1 ≠ .x8 := by intro e; rw [e] at hb; revert hb; decide
  unfold mask4
  refine WP.seq ?_
  refine wp_movz fun s₁ h₁ e₁ => wp_sub32 fun s₂ h₂ e₂ => lea_ok h1.symm a.2 fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ : Keep [.x1, .x2, .x8, .x9] s s₄ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono (by simp)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x8 : s₄.gpr .x8 = BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (s.gpr .x0).setWidth 32) := by
    rw [h₄.get .x8, h₃.get .x8, e₂, e₁, h₁.get .x0]; rfl
  have x1 : s₄.gpr .x1 = pa s a := by
    rw [h₄.get .x1, e₃, h₂.get a.1 (by simpa using h8), h₁.get a.1 (by simpa using h8)]
  refine WP.mono (count_loop (cr := .x2) (n := 1024) (by decide) (fun i s' =>
      s'.gpr .x1 = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .x2 = BitVec.ofNat 64 (1024 - i) ∧
      s'.gpr .x8 = s₄.gpr .x8 ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧ Frame [⟨pa s a, 4096⟩] s.mem s'.mem ∧
      ∀ j < 1024, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s₄.gpr .x8).setWidth 32 else coeffAt s.mem (pa s a) j)
    (fun i hi s' ⟨e1, e2, e8, kk, hf, hc⟩ => ?_)
    ⟨by rw [x1, Nat.mul_zero, BitVec.add_zero], by rw [e₄]; rfl, rfl, k₄, by rw [m₄]; exact Frame.refl _ _,
      fun j _ => by rw [Proof.MlDsa.KeyGen.ifn (Nat.not_lt_zero j), m₄]⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨postB_of_keep kk (by decide) hf, kk, fun j hj => ?_⟩
  · have hc4 : (⟨pa s a, 4096⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hinw : InRegions s'.wr (s'.gpr .x1) 4 := by
      rw [kk.wr, e1]; exact inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .x1) 4 := VG.Proof.MlKem.AArch64.in_rd_wr hinw
    refine WP.mono (maskBody_ok s' hin0 hinw) fun s'' ⟨⟨hm, e1', e2'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [k'.get .x8, e8],
      (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [e1', e1, off_add4]
    · rw [e2', e2, ofNat4_sub1 hi]
    · rw [hm, e1]; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, e1, coeffAt_writeW32_4 _ _ hj (by omega), e8]
      by_cases e : i = j
      · subst e
        rw [Proof.MlDsa.KeyGen.ifp rfl, Proof.MlDsa.KeyGen.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [Proof.MlDsa.KeyGen.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [Proof.MlDsa.KeyGen.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [Proof.MlDsa.KeyGen.ifp hji, Proof.MlDsa.KeyGen.ifp (by omega)]
        · rw [Proof.MlDsa.KeyGen.ifn hji, Proof.MlDsa.KeyGen.ifn (by omega)]
    · rw [e2', e2, ofNat4_sub1 hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hc j hj, Proof.MlDsa.KeyGen.ifp hj, x8, and_mask hr]


end VG.Proof.MlDsa.AArch64.KeyGen

end

/-! ## From `Call4.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
/-! ## `RejNTTPoly` -/

def rej4Chk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 136 a 4096 && sepB rbs wbs seed 136 ss 8192 && sepB rbs wbs a 4096 ss 8192 &&
    inB (rbs ++ wbs) seed 136 && inB (rbs ++ wbs) a 4096 && inB (rbs ++ wbs) ss 8192 && inB wbs a 4096 &&
    inB wbs ss 8192

abbrev rej4Args (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : rej4Chk rbs wbs seed a ss = true)
include L hc

theorem rej4_cov : Covers ([⟨pa s seed, 136⟩] ++ [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩] s.wr := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : Args (rej4Args seed a ss) s s1) :
    (rejNTT4Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 136⟩] [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) := by
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej4_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (c4 : inB bs seed 136 = true)
    (c5 : inB bs a 4096 = true) (c6 : inB bs ss 8192 = true) :
    ∀ x ∈ rej4Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rej4At_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : rej4Chk rbs wbs seed a ss = true) :
    WP isa (rej4At P ss seed a) s fun s' => PPostB S s s' [(a, 4096), (ss, 8192)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced s'.mem (poly4 (pa s a) k)) ∧
      (((s'.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        ((s'.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (rej4_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => rej4_pre L hc h1) (rej4_cov L hc).1 (rej4_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rej4At_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 136 = bytesAt y.mem (pa y seed) 136 ∧ SameB x y) :
    RelCT isa Q (rej4At P ss seed a) fun _ _ => True := by
  have hc' := hc
  simp only [rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej4_pre Lx hc h1, ?_, ?_, (rej4_cov Lx hc).1, (rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej4_cov Ly hc).2


end VG.Proof.MlDsa.AArch64.KeyGen

end

/-! ## From `Seed4.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa (Params Poly IPoly Reduced PolyIs polyAt poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

theorem copySeed4_generic {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : inB (rbs++wbs) (sc oSA) 32 = true)
    (hdst : inB wbs (sc (oSA4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oSA) 32 (sc (oSA4+34*j)) 32 = true) :
    WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  unfold copySeed4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oSA4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oSA,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oSA),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oSA4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oSA4+34*j))) (sb := .x28) (db := .x10) (so := oSA) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oSA),32⟩ : Region).Disjoint ⟨pa s (sc (oSA4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

theorem copySeed4_ok {S : Nat} {p : Params} (hF : PFacts p) {s : State} (L : Lay S kgR (kgW p) s)
    {j : Nat} (hj : j < 4) : WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  exact copySeed4_generic L (by layd) (by layd) (by layd)

structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : KSamp p σ e 0 s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 =
    seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ)

theorem slot_ok {P : Params} (hF : PFacts P) {S : Nat} {σ : State} (hp : kgPre P S σ)
    {e j : Nat} (he : e+4 ≤ P.k*P.ℓ) (hj : j < 4) {s : State} (h : GS P σ e j s) :
    WP isa (seedSlot4 P e j) s (GS P σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq P
  have L := h.ks.k1.kc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (copySeed4_ok hF L hj) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.ks.keep hF hp hP1 (by unfold k1Chk kcChk; layd)
    (fun k hk => by layd) (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk1.get .x24)
  have L1 := h1.k1.kc.lay hF hp
  unfold setSR
  refine WP.mono (setTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%P.ℓ) (b := (e+j)/P.ℓ)
    (by dsimp only [oSA4]; omega) (by layd) (by layd)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by unfold k1Chk kcChk; layd) (fun k hk => by layd)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [bytes34,L1.keepBytes hP2 (by layd),sc_pa hP2,sc_pa hP1,hb1,h.ks.k1.sa,
      sc_add,← sc_pa hP1,hb2,Proof.MlDsa.KeyGen.seedA_eq]
  · rw [L1.keepBytes hP2 (by layd),L.keepBytes hP1 (by layd)]
    exact h.done k (by omega)
end VG.Proof.MlDsa.AArch64.KeyGen

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem slot_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs [.x28]) (seedSlot4 p e j) (.seq (Taint.ofRegs [.x28,.x10]) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 copySeed4 lea
  rw [VG.Proof.MlDsa.KeyGen.ifp (by dsimp only [oSA4]; omega : oSA4+34*j < 4096)]
  with_unfolding_all rfl

theorem slot_piece {p : Params} (hF : PFacts p) {S e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) :
    Piece p S (GS p · e j) (GS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => slot_ok hF hp he hj h,
    rel_of (Q := Two p S) (taintRel [.x28] (fun _ _ h => Two.x28 h) (slot_taint p e hj))
      fun _ _ _ _ hp hp' hq h h' => kc_two hF hp hp' hq h.ks.k1.kc h'.ks.k1.kc⟩
end VG.Proof.MlDsa.AArch64.KeyGen

end
