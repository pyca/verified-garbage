module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit

import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDotValue
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPieceTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRest
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPackSecret
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRest
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
import VerifiedGarbage.Proof.MlDsa.RejNTT2Contract

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRoundTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

theorem p2rAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {t t1 t0 : Ptr} (hc : p2rChk rbs wbs t t1 t0 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x t) ∧ Reduced y.mem (pa y t) ∧
      SameB x y) :
    RelCT isa Q (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P t t1 t0) fun _ _ => True := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : t.1 ∈ bases ∧ t1.1 ∈ bases ∧ t0.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (p2r_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, p2r_pre Lx hc rx h1, ?_, ?_, (p2r_cov Lx hc).1, (p2r_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact p2r_pre Ly hc ry h2
  · sig_pub [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRowPieces.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)

abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat} (hi : i<p.k)
include hP hF hi

theorem addS2_piece : Piece p S' (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => tK p A S i)) (Impl.MlDsa.AArch64.KeyGen.Optimized.addAt P (tP p) (sP p (p.ℓ + i))) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.addAt
  exact accAt_tr (op := add) hP.add (kgOk p) (add_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p S' (RowI p i (tIs p fun A S => tK p A S i)) (RowI p i (p2rIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr hP.power2Round (kgOk p) (p2r_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p S' (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt
  exact sbpAt_tr hP.simpleBitPack (kgOk p) (sbp_chk hF hi) sbpOk_t1 fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem bp_piece : Piece p S' (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (t0P p)) ∧ BpRange x.mem (pa x (t0P p)) 4095 4096) ∧
    (Reduced y.mem (pa y (t0P p)) ∧ BpRange y.mem (pa y (t0P p)) 4095 4096)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1.1, range_t0 t₁.1⟩, ⟨t₂.1.1, range_t0 t₂.1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  exact bpAt_tr hP.bitPack (kgOk p) (bp_chk hF hi) bpOk_t0 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

end
end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedDotTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Impl.MlDsa.AArch64.Call (Arg)
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem slot_add (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dotRow_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {i : Nat} (hi : i<p.k)
    (h : KRx p (p.ℓ+p.k) p.ℓ i σ s) (roots : Sign.StaticRoots S' s) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (VG.Impl.MlDsa.AArch64.Call.sc oSS) s := by
  obtain ⟨A,T,R,h⟩ := h
  refine optimizedDotReady hF (optimizedDotChk_ok hF i hi) hp h.kc roots ?_ ?_
  · intro j hj
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [slot_add] at hv
    exact (PosPolyIs.of_canonical hv).bound
  · intro j hj
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [slot_add] at hv
    have hv' : PosPolyIs s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (T j))) := by
      simpa only [sP,Nat.add_zero] using hv
    exact hv'.bound

theorem dotRow_tr {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) fun _ _=>True := by
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  apply dotAt_tr (S:=S') hn
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨dotRow_ready hF hσ hi ⟨A,T,R,hx'⟩ rx,
    dotRow_ready hF hτ hi ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),
    ht.same.2,et.2⟩

theorem dotRow_relCT {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i)
      (RootPair p S' (RowI p i (tIs p fun A T=>nttInv (dotK p A T i p.ℓ)))) := by
  apply rootPair_progress (ht:=dotRow_tr hF hi)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (dotRow_value hF hp hi h roots) fun t ⟨ht,rt,hv⟩=>⟨⟨A,T,R,ht,hv⟩,rt⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRowTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen

theorem row_relCT {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {i : Nat} (hi : i<p.k)
    (hd : 16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ (i+1))) := by
  have hd' : (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S'/16 :=
    (Nat.le_div_iff_mul_le (by decide : 0<16)).mpr (by simpa only [Nat.mul_comm] using hd)
  simp only [Impl.MlDsa.AArch64.KeyGen.Optimized.row,Code.aarch64Depth,Nat.max_le] at hd'
  have hrem := Nat.div_mul_le_self S' 16
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.row
  exact (dotRow_relCT hF hi).seq
    ((piece_rooted (addS2_piece hP hF hi) (by omega) hP.s64).seq
      ((piece_rooted (p2r_piece hP hF hi) (by omega) hP.s64).seq
        ((piece_rooted (sbp_piece hP hF hi) (by omega) hP.s64).seq
          (piece_rooted (bp_piece hP hF hi) (by omega) hP.s64))))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedNttTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Arg)

theorem nttSecret_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j<p.ℓ)
    (h : KRx p (p.ℓ+p.k) j 0 σ s) (roots : Sign.StaticRoots S' s) :
    NttCallReady (sP p j) s := by
  obtain ⟨A,T,R,h⟩ := h
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hr : inB (kgR++kgW p) (sP p j) 1024=true := by layd
  have hw : inB (kgW p) (sP p j) 1024=true := by layd
  have hv := h.s1 j hj
  simp only [ite_eq_right (Nat.lt_irrefl j)] at hv
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),hv.1,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttSecret_tr {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j) fun _ _ => True := by
  apply positiveNttAt_tr (S := S') (show (Arg.ptr (sP p j)).Ok from ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨nttSecret_ready hF hσ hj ⟨A,T,R,hx'⟩ rx,
    nttSecret_ready hF hτ hj ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.2,et.1⟩

theorem nttSecret_relCT {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j)
      (RootPair p S' (KRx p (p.ℓ+p.k) (j+1) 0)) := by
  apply rootPair_progress (ht := nttSecret_tr hF hj)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (nttSecret_ok hF hp hj h roots) fun t ht => ⟨⟨A,T,R,ht.1⟩,ht.2⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRestTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem canonicalRootPair {p : Params} {S : Nat} {x y : State}
    (h : RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ+p.k) 0 0) x y) :
    RootPair p S (KRx p (p.ℓ+p.k) 0 0) x y :=
  rootPair_mono (fun _ _ ⟨A,T,R,h⟩ => ⟨A,T,R,PositiveKR.of_canonical h⟩) h

theorem rest_tr_of_rows {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hr : ∀i<p.k,RelCT isa (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ (i+1)))) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) fun _ _ => True := by
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.restWith
  apply RelCT.seq (piece_rooted (copies_piece hF) (by change 0≤S; omega) hP.s64)
  apply RelCT.seq
    (seqR_tr (Q := fun j => RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p j 0 0))
      (p.ℓ+p.k) 0 (fun j _ hj => piece_rooted (packSecret_piece hP hF (by omega)) (hdpack j (by omega)) hP.s64))
  simp only [Nat.zero_add]
  apply RelCT.seq
    (RelCT.mono (seqR_tr (Q := fun j => RootPair p S (KRx p (p.ℓ+p.k) j 0))
      p.ℓ 0 (fun j _ hj => nttSecret_relCT hF (by omega)))
      (fun _ _ h => canonicalRootPair h) (fun _ _ h => h))
  simp only [Nat.zero_add]
  apply RelCT.seq (seqR_tr (Q := fun i => RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
    p.k 0 (fun i _ hi => hr i (by omega)))
  simp only [Nat.zero_add]
  apply RelCT.mono (trHash_piece (keccak := keccak) hF hP.s16 hP.s64).tr
  · rintro x y ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,_⟩
    exact ⟨σ,τ,hσ,hτ,pub,hx.1,hy.1⟩
  · intro _ _ _
    trivial

theorem rest_relCT {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) (R p S (KFin p)) :=
  rootPair_finish (fun _ _ hp h roots => rest_ok hP hF hp h roots hdpack hdrow)
    (rest_tr_of_rows hP hF hdpack (fun i hi => row_relCT hP hF hi (hdrow i hi)))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem codeWith_ct {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2)
    (hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    ConstantTime isa (fun s => kgPre p S s ∧ Sign.StaticRoots S s)
      (fun s t => kgPub p S s t ∧ TableEq s t) (codeWith keccak.callee P cd p) := by
  have ht : RelCT isa (RootPair p S (fun σ s => s=σ))
      (codeWith keccak.callee P cd p) (fun _ _ => True) :=
    RelCT.seq (piece_rooted (prefix_piece hP C hF hm hs) hdprefix hP.s64)
      (RelCT.seq (rest_relCT hP hF hdpack hdrow) (epi_piece hF).tr)
  intro s t tr ur s' t' hs ht' pub es et
  exact (ht _ _ _ _ _ _ ⟨⟨s,t,hs.1,ht'.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht'.2⟩⟩,pub.2⟩ es et).1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts signRootConsts_eq)

theorem keyGen_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (keyGenWith v.callee p) (keyGenContract p (abi.withConsts signRootConsts) 16) := by
  have hF := pfacts hp
  have hm : p.k*p.ℓ%4=0∨p.k*p.ℓ%4=2 := by rcases hp with rfl|rfl|rfl <;> decide
  have hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3 := by rcases hp with rfl|rfl|rfl <;> decide
  have hP := primitives_ok (keccak := v)
  have hdpre : 16*(prefixWith v.callee (primitives v.callee)
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p).aarch64Depth≤16 := by
    have h := (prefix_dle v hF).le; omega
  have hdpack : ∀j<p.ℓ+p.k,16*(packSecret (primitives v.callee) p j).aarch64Depth≤16 := by
    intro j _; have h := (packSecret_dle v p j).le; omega
  have hdrow : ∀i<p.k,16*(row (primitives v.callee) p i).aarch64Depth≤16 := by
    intro i _; have h := (row_dle v hp i).le; omega
  refine ⟨?_,?_,⟨keyGenSat p,keyGen_sat hp⟩⟩
  · intro s h
    obtain ⟨pre,roots⟩ := staticRoots_entry (by decide) h
    exact codeWith_ok hP two_callee hF hm hs pre roots hdpre hdpack hdrow
  · intro s t tr ur s' t' hσ hτ pub es et
    have preσ := staticRoots_entry (by decide) hσ
    have preτ := staticRoots_entry (by decide) hτ
    have pb : kgPub p 16 s t ∧ TableEq s t := by
      sig_pub [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq] at pub
      obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := pub
      refine ⟨?_,hf,hi⟩
      dsimp only [kgPub]
      sig_pub [keyGenContract,keyGenSig,abi,argRegs]
      exact ⟨hsp,hb,h0,h1,h2,h3⟩
    exact codeWith_ct hP two_callee hF hm hs hdpre hdpack hdrow
      s t tr ur s' t' preσ preτ pb es et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
