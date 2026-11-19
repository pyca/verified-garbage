module

public import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.RowSum
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Spec.MlDsa.Contract
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
meta import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.MlKem.Arm.KemLay
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Lay
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Lay
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlKem.Arm.KemLay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlKem.Arm.CallsCT

/-! ### `MlDsa.Arm.KeyGen.Mask`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on 32-bit ARM: masking a sampled polynomial

After each sampler, `r11` is ANDed with its result (0 or 1, in `r0`), and each
coefficient of the polynomial it wrote with `-r0`: the polynomial is kept if
the sampler succeeded, and zeroed if it failed (`mask_ok`), without a branch.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega_arith) (by omega_using [hi]) (by omega_using [hj])) (by decide)

/-- The coefficients after masking with `-r`, for `r` 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) : x &&& (0 - r) = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

/-! ## One coefficient -/

section
variable {s : State} {x c M : BitVec 32}

theorem maskBody_ok (h1 : s.gpr .r1 = x) (h2 : s.gpr .r2 = c) (h12 : s.gpr .r12 = M)
    (ir : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
    (ow : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block maskBody) s fun s' =>
      s'.gpr .r1 = x + 4 ∧ s'.gpr .r2 = c - 1 ∧ s'.gpr .r12 = M ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 &&& M) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [maskBody, h1, h2, h12, ir, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After masking `k` coefficients of the polynomial at `P` with `M`. -/
structure MaskInv (P M : BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = P + BitVec.ofNat 32 (4 * k)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - k))
  r12 : s.gpr .r12 = M
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [regA P 1024] s₀.mem s.mem
  co : ∀ t < 256, coeffAt s.mem (State.addr P) t =
    if t < k then coeffAt s₀.mem (State.addr P) t &&& M else coeffAt s₀.mem (State.addr P) t

theorem mask_step {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    {k : Nat} (hk : k < 256) {s : State} (h : MaskInv P M s₀ k s) :
    WP isa (.block maskBody) s fun s' => MaskInv P M s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have eP : State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 (4 * k) := by
    rw [addr_ptr _ _ _ (by omega_using [fP, hk])]; simp
  have cP : (regA P 1024).Contains (State.addr P + BitVec.ofNat 64 (4 * k)) 4 := contains_off (by omega_using [hk]) (by omega_using [hk])
  have ow : InRegions s.wr (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 := by
    rw [eP, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩
  have ir : InRegions (s.rd ++ s.wr) (State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 4 :=
    let ⟨r, hr, hc⟩ := ow; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (maskBody_ok h.r1 h.r2 h.r12 ir ow)
    fun s' ⟨r1, r2, r12, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, r12, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r1]; exact ptr_succ _ 4 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eP]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, eP, coeffAt_writeW32 _ _ ht hk]
    by_cases e : k = t
    · subst e
      have := h.co k hk
      rw [ifn (Nat.lt_irrefl _)] at this
      rw [ifp rfl, ifp (Nat.lt_succ_self _), ← this]; rfl
    · rw [ifn e, h.co t ht]
      by_cases htk : t < k
      · rw [ifp htk, ifp (by omega_using [htk])]
      · rw [ifn htk, ifn (by omega_using [e, htk])]
  · rw [z]; exact count_z (k := 1) hk (by decide) (by decide)

theorem mask_loop {P M : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32) (cw : Covers [regA P 1024] s₀.wr)
    (h1 : s₀.gpr .r1 = P) (h2 : s₀.gpr .r2 = BitVec.ofNat 32 256) (h12 : s₀.gpr .r12 = M) :
    WP isa (.loop (.block maskBody) .ne) s₀ fun s =>
      Kept [regA P 1024] s₀ s ∧ ∀ t < 256, coeffAt s.mem (State.addr P) t = coeffAt s₀.mem (State.addr P) t &&& M :=
  wp_loop_ne (MaskInv P M s₀) (N := 256) (by decide) (fun k hk s h => mask_step fP cw hk h)
    (fun s h => ⟨⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, h.frame⟩, fun t ht => by
      rw [h.co t ht, ifp ht]⟩)
    ⟨by rw [h1]; simp, by rw [h2], h12, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t _ => by rw [ifn (Nat.not_lt_zero t)]⟩

/-! ## The polynomial -/

abbrev maskPre (a : Ptr) : List Instr :=
  [.mov .r12 (.imm 0), .dp .sub .r12 .r12 (.reg .r0)] ++ Arg.instrs .r1 (.ptr a) ++ [.mov .r2 (.imm 256)]

theorem maskPre_ok {a : Ptr} (ha : argOk (.ptr a) = true) (s : State) :
    WP isa (.block (maskPre a)) s fun s' =>
      Only s s' ∧ s'.gpr .r12 = 0 - s.gpr .r0 ∧ s'.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2 ∧
        s'.gpr .r2 = BitVec.ofNat 32 256 := by
  obtain ⟨-, n1, -, -, n12⟩ := pres_ne (base_pres (r := a.1) (by simpa [argOk] using ha)).1
    (base_pres (r := a.1) (by simpa [argOk] using ha)).2
  have n1' : ¬ a.1 = .r1 := n1
  have n12' : ¬ a.1 = .r12 := n12
  run_block [maskPre, Arg.instrs, ldc, n1', n12', ldc_eq]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, ?_⟩
  · obtain ⟨-, m1, m2, -, m12⟩ := pres_ne hr hl
    simp only [m1, m2, m12, ite_false]
  · simp

theorem mask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (mask a) s fun s' => Kept (L.RL [tri a 1024]) s s' ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  have gb := hs.val pa.1
  simp only [argVal] at gb
  have ea := hs.addrE pa (by decide)
  have fa := hs.fitE pa (by decide)
  have cw := hs.cwE pa hw
  rw [← hs.regE pa (by decide)] at cw
  unfold mask
  refine WP.seq (WP.mono (maskPre_ok pa.1 s) fun s₁ ⟨o₁, g12, g1, g2⟩ => ?_)
  rw [gb] at g1
  refine WP.mono (mask_loop fa (by rw [o₁.wr]; exact cw) g1 g2 g12) fun s' ⟨k, co⟩ => ⟨?_, fun t ht => ?_⟩
  · refine (o₁.kept _).trans (k.mono fun r hr => ?_)
    rw [List.mem_singleton] at hr; subst hr
    rw [hs.regE pa (by decide)]
    exact List.mem_singleton_self _
  · rw [← ea, co t ht, o₁.mem, and_mask hr]

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-! ### `MlDsa.Arm.KeyGen.SeedsCT`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.KeyGen.Seeds`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.KeyGen.Inv`, which only this module used -/

section

/-!
# ML-DSA key generation on 32-bit ARM: what holds throughout, and the prologue

What holds of the state throughout (`KC`: the layout, the permissions and
stack pointer of the entry state, our caller's registers saved in `scratch`,
and the seed `ξ`), which a part keeps if it writes apart from the saved
registers and the seed (`kcChk`); the pieces of key generation (`KPiece`); and
the prologue, which saves our caller's registers and keeps the pointers
(`pro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (pSeed σ)) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.2

/-- The public data of `keyGenContract`. -/
def kgPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ pSeed σ₁ = pSeed σ₂ ∧ pPk σ₁ = pPk σ₂ ∧ pSk σ₁ = pSk σ₂ ∧ pScr σ₁ = pScr σ₂ ∧
    keyGenLeak p (xiOf σ₁) = keyGenLeak p (xiOf σ₂)

/-- The pieces of key generation. -/
abbrev KPiece (p : Params) (STK : Nat) := Piece (Pre p STK) (kgPub p)

/-- Two runs of a key generation with public data that agree have the same layout. -/
theorem lay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : kgPub p σ₁ σ₂) : lay p STK σ₁ = lay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [lay, pSeed, pPk, pSk, pScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (lay p STK σ) kWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : Saved s.mem ((lay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((lay p STK σ).A 0 872) 32 = σ.gpr .lr
  xi : bytesAt s.mem ((lay p STK σ).A 2 0) 32 = xiOf σ

theorem xi_eq (p : Params) (STK : Nat) (σ : State) : bytesAt σ.mem ((lay p STK σ).A 2 0) 32 = xiOf σ := by
  simp only [Lay.A, add_ofNat_zero]; rfl

/-- A part that writes the regions `W` keeps `KC`. -/
def kcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, 840, 36) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (2, 0, 32) W

theorem KC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : KC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : kcChk p STK W = true) : KC p STK σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 0 840 36).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp hc.1 w hw) (.inl (by decide))
  have hd2 : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 2 0 32).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      have hs := List.all_eq_true.mp hc.2 w hw
      refine disjW' hL hs (.inr ?_)
      have hb : w.1 < 5 := by
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq, List.length_cons, List.length_nil] at hs
        exact hs.1.1.1.2
      rcases (by omega_using [hb] : w.1 = 0 ∨ w.1 = 1 ∨ w.1 = 2 ∨ w.1 = 3 ∨ w.1 = 4) with e | e | e | e | e <;> rw [e]
      · exact .inl (by decide)
      · exact .inl (by decide)
      · exact .inr rfl
      · exact .inl (by decide)
      · exact .inl (by decide)
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW (r := (lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith) hd (by decide)]
    exact h.lr
  · rw [Proof.MlKem.bytesAt_frame hk.frame hd2 (by decide)]; exact h.xi

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The prologue -/

theorem pro_ok {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : Pre p STK σ) :
    WP isa (.block pro) σ fun s => KC p STK σ s ∧ s.gpr .r11 = 1 := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (lay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (lay p STK σ).buf 0 = regA (pScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have eA : ∀ o, (lay p STK σ).A 0 o = State.addr (σ.gpr .r3) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((lay p STK σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by rw [lay_size0]; omega_using [hs1, h]) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega_using [hs1]) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega_using [hi])) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = pScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (lay p STK σ).A 0 872 := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega_using [fc, hs1])
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have e1 : encodable (1 : BitVec 32) = true := by decide
  run_block [i872, o1, e1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay p STK σ).A 0 872) v).readW
      ((lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega_arith) (by decide)
  have fr : Frame [(lay p STK σ).R 0 840 36] σ.mem (s₁.mem.writeW ((lay p STK σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(lay p STK σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (lay p STK σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega_arith
    · simp only [Region.Contains, eA]; bv_omega_arith
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by rw [lay_size0]; omega_using [hs1], rfl,
    show σ.sp - BitVec.ofNat 32 STK = s₁.sp - BitVec.ofNat 32 STK by rw [h₁.sp], hSTK,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [kWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [Lay.buf, lay]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay]
    · simp [Lay.buf, lay]
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega_using [hi, hi1] : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, lay]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (lay p STK σ).A 0 872 = (lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, ← xi_eq p STK σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disjW' (i := 2) (o := 0) (l := 32) (j := 0) (o' := 840) (l' := 36) hL (by lsep hF)
        (.inr (.inl (by decide)))) (by decide)
  · trivial

theorem pro_piece {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) :
    KPiece p STK (fun σ s => s = σ) (fun σ s => KC p STK σ s ∧ s.gpr .r11 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hF hSTK hp,
    Sample.taint_block [.r0, .r1, .r2, .r3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by native_taint_decide)⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM: the seeds

`(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed of `RejNTTPoly` and
`ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`, `K1`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (Piece)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  kc : KC p STK σ s
  hx : bytesAt s.mem ((lay p STK σ).A 0 oHX) 128 = hxOf p σ
  sa : bytesAt s.mem ((lay p STK σ).A 0 oSA) 32 = rhoOf p σ
  sb : bytesAt s.mem ((lay p STK σ).A 0 oSB) 64 = rho'Of p σ
  z : bytesAt s.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0]

/-- A part that writes the regions `W` keeps `K1`. -/
def k1Chk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  kcChk p STK W && sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oHX, 128) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSA, 32) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB, 64) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oSB + 65, 1) W

theorem K1.keep {p : Params} {STK : Nat} {σ s s' : State} (h : K1 p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : k1Chk p STK W = true) : K1 p STK σ s' := by
  simp only [k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.kc.site.ok
  exact ⟨h.kc.keep hk h0, by rw [bytes_keepW hL hk.frame h1 (by decide) (by decide)]; exact h.hx,
    by rw [bytes_keepW hL hk.frame h2 (by decide) (by decide)]; exact h.sa,
    by rw [bytes_keepW hL hk.frame h3 (by decide) (by decide)]; exact h.sb,
    by rw [bytes_keepW hL hk.frame h4 (by decide) (by decide)]; exact h.z⟩

theorem shake31 : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem hx_eq (p : Params) (σ : State) :
    hxOf p σ = Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 31)
      (xiOf σ ++ ([BitVec.ofNat 8 p.k] ++ [BitVec.ofNat 8 p.ℓ])))) 0 128 := by
  rw [hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, shake31,
    List.append_assoc]
  exact Proof.MlKem.shake256_eq _ _

theorem rho_eq (p : Params) (σ : State) : rhoOf p σ = (hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : rho'Of p σ = ((hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : kOf p σ = ((hxOf p σ).drop 96).take 32 := rfl

theorem sc_ok (o : Nat) : argOk (.ptr (sc o)) = true := rfl

theorem seeds_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {s : State}
    (h : KC p STK σ s) (h11 : s.gpr .r11 = 1) : WP isa (seeds p) s fun s' => K1 p STK σ s' ∧ s'.gpr .r11 = 1 := by
  obtain hk := hF.k; have hl := hF.l
  have hs := h.site
  unfold seeds
  -- `k` and `ℓ`
  obtain blk : WP isa (.block (setB (sc oKL) p.k ++ setB (sc (oKL + 1)) p.ℓ)) s fun s₂ =>
      KC p STK σ s₂ ∧ s₂.gpr .r11 = 1 ∧
        bytesAt s₂.mem ((lay p STK σ).A 0 oKL) 2 = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    refine WP.block_append (WP.mono (setB_ok hs (q := sc oKL) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, b₂⟩ => ⟨(h.keep k₁ (by lsep hF [kcChk])).keep k₂ (by lsep hF [kcChk]), ?_, ?_⟩)
    · rw [k₂.cs .r11 (by decide) (by decide), k₁.cs .r11 (by decide) (by decide), h11]
    · have b₁' := bytes_keepW hs.ok k₂.frame (i := 0) (o := oKL) (l := 1) (by lsep hF) (by decide) (by decide)
      rw [show (2 : Nat) = 1 + 1 from rfl, Proof.MlKem.bytesAt_add, b₁'.trans b₁, add_ofNat_add]
      exact congrArg _ b₂
  refine WP.seq (WP.mono blk fun s₂ ⟨h₂, r₂, b₂⟩ => ?_)
  -- `H(ξ ‖ k ‖ ℓ, 128)`
  have hs₂ := h₂.site
  obtain hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
      i ∈ kWb ∨ j ∈ kWb := fun i hi j hj hij _ _ _ _ => by
    simp only [kWb, List.mem_cons, List.not_mem_nil, or_false]; omega_using [hi, hj, hij]
  refine WP.seq (WP.mono (hashS hs₂ hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
      (ins := [⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩]) (q := ⟨.r7, oHX, 128⟩) (by simp) (fun pc hpc => ?_)
      (pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size]) (.inl rfl)
        fun _ => by decide)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact pieceS hs₂ rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  obtain h₃ := h₂.keep k₃ (by lsep hF [kcChk])
  have hs₃ := h₃.site
  obtain hx₃ : bytesAt s₃.mem ((lay p STK σ).A 0 oHX) 128 = hxOf p σ := by
    have o₃' : bytesAt s₃.mem ((lay p STK σ).A 0 oHX) 128 = _ := o₃
    rw [o₃', hx_eq]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s₂.mem (State.addr ((lay p STK σ).ptr (ix Reg.r4)) + 0#64) 32 = xiOf σ := h₂.xi
    have e2 : bytesAt s₂.mem (State.addr ((lay p STK σ).ptr (ix Reg.r7)) + BitVec.ofNat 64 oKL) 2 =
      [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := b₂
    rw [e1, e2]; rfl
  -- `ρ` and `ρ′ ‖ 0` to the seeds
  refine WP.seq (WP.mono (copyS hs₃ (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
    ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
    fun s₄ ⟨k₄, b₄⟩ => ?_)
  obtain h₄ := h₃.keep k₄ (by lsep hF [kcChk])
  obtain hx₄ := (bytes_keepW hs₃.ok k₄.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)).trans hx₃
  refine WP.seq (WP.mono (copyS h₄.site (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64)
    ⟨rfl, by lsep hF⟩ ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by lsep hF)) fun s₅ ⟨k₅, b₅⟩ => ?_)
  obtain h₅ := h₄.keep k₅ (by lsep hF [kcChk])
  refine WP.mono (setB_ok h₅.site (q := sc (oSB + 65)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) 0)
    fun s₆ ⟨k₆, b₆⟩ => ⟨⟨h₅.keep k₆ (by lsep hF [kcChk]), ?_, ?_, ?_, b₆⟩, ?_⟩
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide),
      bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oHX) (l := 128) (by lsep hF) (by decide) (by decide)]
    exact hx₄
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide),
      bytes_keepW h₄.site.ok k₅.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₄.mem (lpa (lay p STK σ) (.r7, oSA)) 32 = _
    rw [b₄, rho_eq, ← hx₃]
    exact (Proof.MlKem.bytesAt_take _ _ (by decide)).symm
  · rw [bytes_keepW h₅.site.ok k₆.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)]
    show bytesAt s₅.mem (lpa (lay p STK σ) (.r7, oSB)) 64 = _
    rw [b₅, rho'_eq, ← hx₄, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide), add_ofNat_add]
    rfl
  · rw [k₆.cs .r11 (by decide) (by decide), k₅.cs .r11 (by decide) (by decide), k₄.cs .r11 (by decide) (by decide),
      k₃.cs .r11 (by decide) (by decide), r₂]

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM: the seeds leak nothing

Two runs of the seeds in the same layout leak the same (`seeds_two`): the
bytes `k` and `ℓ` are public, and every access is through the pointers of the
layout; which gives the piece of the seeds (`seeds_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params)

/-- Two runs whose entry states have the same layout. -/
def KTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (lay p STK σ) kWb STK x y

theorem kc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : Two (lay p STK σ₁) kWb STK x y :=
  ⟨h₁.site, lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem kc_two {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : KTwo p STK x y :=
  ⟨σ₁, kc_twoL pub h₁ h₂⟩

/-- A part that leaks the same in two runs in every layout of key generation. -/
theorem ktwo {p : Params} {STK : Nat} {c : Prog isa} (h : ∀ σ, RelCT isa (Two (lay p STK σ) kWb STK) c fun _ _ => True) :
    RelCT isa (KTwo p STK) c fun _ _ => True :=
  RelCT.exists_ h

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem ktrue : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → (fun _ => true) i = true → (fun _ => true) j = true →
    i ∈ kWb ∨ j ∈ kWb := fun i _ j _ hij _ _ _ _ => by
  simp only [kWb, List.mem_cons, List.not_mem_nil, or_false]; omega_arith

theorem seeds_two {p : Params} (hF : PFacts p) {STK : Nat} (σ : State) :
    RelCT isa (Two (lay p STK σ) kWb STK) (seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  have hP : ∀ x y, Two (lay p STK σ) kWb STK x y → Two (lay p STK σ) kWb STK x y := fun _ _ h => h
  unfold seeds
  refine RelCT.seq (RelCT.two hP (taint7 hP (setKL_taint p.k (by omega_using [hk]) p.ℓ (by omega_using [hl]))) fun x hs => ?_) ?_
  · refine WP.block_append (WP.mono (setB_ok hs (q := sc oKL) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) p.k)
      fun s₁ ⟨k₁, _⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oKL + 1)) ⟨sc_ok _, by lsep hF⟩ (by decide)
        (by decide) p.ℓ) fun s₂ ⟨k₂, _⟩ => ⟨_, (k₁.monoL (W' := [tri (sc oKL) 1, tri (sc (oKL + 1)) 1])
          (by simp)).trans (k₂.monoL (by simp))⟩)
  have hin : ∀ s, Site (lay p STK σ) kWb STK s → ∀ pc ∈ ([⟨.r4, 0, 32⟩, ⟨.r7, oKL, 2⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc := fun s hs pc hpc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have hq : ∀ s, Site (lay p STK σ) kWb STK s →
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r7, oHX, 128⟩ : Impl.MlKem.Arm.Piece) := fun s hs =>
    pieceS hs rfl (by decide) (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size]) (.inl rfl)
      fun _ => by decide
  refine RelCT.seq (RelCT.two hP (hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
    (by simp) hin hq hP) fun x hs => WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by decide) (by decide) (by simp) (hin x hs) (hq x hs)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint7 hP (by native_taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r7) (so := oHX) (db := .r7) (dO := oSA) (len := 32) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint7 hP (by native_taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r7) (so := oHX + 32) (db := .r7) (dO := oSB) (len := 64) ⟨rfl, by lsep hF⟩
      ⟨rfl, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  exact taint7 hP (by native_taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KC p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => K1 p STK σ s ∧ s.gpr .r11 = 1) (seeds p) :=
  ⟨fun _ _ _ h => seeds_ok hF h.1 h.2,
    rel_of (ktwo fun σ => seeds_two hF σ) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM: the samplers

The primitives key generation calls, verified with at most `S` bytes of stack
(`PrimsOk`); and the entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂`
(`expS_piece`): after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`
(`KSamp`), each polynomial is reduced (and those of `s₁ ‖ s₂` small), and
`r11` is what `Good` says.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly toRq Outcome)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Small Good ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract Arm.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract Arm.abi stk) S
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract Arm.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract Arm.abi stk) S
  add : Callee P.add (fun stk => Proof.MlDsa.addContract Arm.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract Arm.abi stk) S
  rejBounded : Callee P.rejBounded (fun stk => Proof.MlDsa.rejBoundedContract Arm.abi stk) S
  power2Round : Callee P.power2Round (fun stk => Proof.MlDsa.power2RoundContract Arm.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract Arm.abi stk) S
  bitPack : Callee P.bitPack (fun stk => Proof.MlDsa.bitPackContract Arm.abi stk) S

/-! ## `r11` -/

theorem and11_ok (s : State) :
    WP isa (.block and11) s (· = s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) := by
  apply WP.of_runBlock
  simp only [and11, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left']

theorem Site.setReg {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (h : Site L Wb STK s) {r : Reg}
    (hr : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7) (v : BitVec 32) : Site L Wb STK (s.setReg r v) :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, h.p1, h.s8, h.spk,
    by rw [gpr_setReg_of_ne _ _ hr.2.2.2.symm]; exact h.r7, by rw [gpr_setReg_of_ne _ _ hr.1.symm]; exact h.r4,
    by rw [gpr_setReg_of_ne _ _ hr.2.1.symm]; exact h.r5, by rw [gpr_setReg_of_ne _ _ hr.2.2.1.symm]; exact h.r6,
    h.cw, h.cr⟩

theorem K1.r11 {p : Params} {STK : Nat} {σ s : State} (h : K1 p STK σ s) (v : BitVec 32) :
    K1 p STK σ (s.setReg .r11 v) :=
  ⟨⟨h.kc.site.setReg (by decide) v, h.kc.rd, h.kc.wr, h.kc.sp, h.kc.sav, h.kc.lr, h.kc.xi⟩, h.hx, h.sa, h.sb, h.z⟩

/-! ## What the samplers leave -/

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (STK : Nat) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p STK σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem ((lay p STK σ).A 0 (oP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r'))) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p (xiOf σ) e r A S (s.gpr .r11)

/-- A part that keeps `K1`, the polynomials sampled so far and `r11` keeps `KSamp`. -/
theorem KSamp.keep {p : Params} {STK : Nat} {σ : State} {e r : Nat} {s s' : State} (h : KSamp p STK σ e r s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((lay p STK σ).RL W) s s') (hc : k1Chk p STK W = true)
    (ha : ∀ e' < e, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e', 1024) W = true)
    (hs : ∀ r' < r, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + r'), 1024) W = true)
    (h11 : s'.gpr .r11 = s.gpr .r11) : KSamp p STK σ e r s' := by
  have hL := h.k1.kc.site.ok
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.keep hk hc, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h11]; exact hG⟩
  · exact polyIs_keepW hL hk.frame (ha e' he') (by decide) rfl (hA e' he')
  · exact ⟨polyIs_keepW hL hk.frame (hs r' hr') (by decide) rfl (hS r' hr').1, (hS r' hr').2⟩

theorem KSamp.zero {p : Params} {STK : Nat} {σ s : State} (h : K1 p STK σ s) (h11 : s.gpr .r11 = 1) :
    KSamp p STK σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h11]; exact Proof.MlDsa.KeyGen.good_zero _ _ _ _⟩

/-! ## A sampled polynomial, masked -/

/-- `and11` and `mask`, after a sampler whose result `r0` is 0 or 1. -/
theorem andMask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : s.gpr .r0 = 0 ∨ s.gpr .r0 = 1) :
    WP isa (.seq (.block and11) (mask a)) s fun s' =>
      Kept (L.RL [tri a 1024]) (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)) s' ∧
      s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0 ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .r0 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  refine WP.seq (WP.mono (and11_ok s) fun s₁ e₁ => ?_)
  subst e₁
  obtain h0 : (s.setReg .r11 (s.gpr .r11 &&& s.gpr .r0)).gpr .r0 = s.gpr .r0 := gpr_setReg_of_ne _ _ (by decide)
  refine WP.mono (mask_ok (hs.setReg (by decide) _) pa hw (by rw [h0]; exact hr)) fun s' ⟨k, co⟩ =>
    ⟨k, ?_, fun t ht => by rw [co t ht, h0]; rfl⟩
  rw [k.cs .r11 (by decide) (by decide)]
  exact gpr_setReg_self _ _ _

/-- What a sampler and its mask leave in entry `j` of the polynomials, from
the facts the sampler's contract gives. -/
theorem masked_poly {m m' : Mem} {q : Addr} {r : BitVec 32} (hred : r = 1 → Reduced m q)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (polyAt m' q) ∧ (r = 1 → polyAt m' q = polyAt m q) ∧
      (r ≠ 1 → PolyIs m' q (toRq (Vector.replicate 256 0))) := by
  by_cases h1 : r = 1
  · have := Proof.MlDsa.KeyGen.masked_one h1 h
    exact ⟨⟨this.2 (hred h1), rfl⟩, fun _ => this.1, fun h => absurd h1 h⟩
  · have := Proof.MlDsa.KeyGen.masked_zero h1 h
    exact ⟨⟨this.1, rfl⟩, fun h => absurd h h1, fun _ => this⟩

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) : seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-- The seed and the call of `RejNTTPoly`. -/
theorem rnA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (hs : Site (lay p STK σ) kWb STK s) {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (aP e) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP e))) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem ((lay p STK σ).A 0 oSA) 34)) (s'.gpr .r0)
        (polyAt s'.mem ((lay p STK σ).A 0 (oP e))) → Q s') :
    WP isa (rejNttAt P (sc oSA) (aP e)) s Q := by
  have := hF.kl
  exact rn_ok hP.rejNtt hs (by omega_using [hS]) (sd := sc oSA) (a := aP e) (w := sc oSS)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, show ix Reg.r7 ∈ kWb by decide, by lsep hF,
      by lsep hF, by lsep hF⟩ hQ

theorem expA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : KSamp p STK σ e 0 s) :
    WP isa (expA P p e) s (KSamp p STK σ (e + 1) 0) := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  obtain hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  have hs := h.k1.kc.site
  unfold expA sampled
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok _, by lsep hF⟩ (by decide)
    (by decide) (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSA + 33))
      ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ?_))
  obtain h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₁.cs .r11 (by decide) (by decide))
  obtain h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₂.cs .r11 (by decide) (by decide))
  have hs₂ := h₂.k1.kc.site
  obtain hseed : bytesAt s₂.mem ((lay p STK σ).A 0 oSA) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    obtain b₁' := bytes_keepW hs.ok k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₂.k1.sa,
      add_ofNat_add, add_ofNat_add, seedA_eq, List.append_assoc]
    refine congrArg _ ?_
    obtain e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    rw [e1, e2]; rfl
  -- the call
  refine WP.seq (rnA_ok hP hF hS he hs₂ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  obtain hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  obtain hs₃ := hs₂.kept k₃
  -- the result and the mask
  refine WP.mono (andMask_ok hs₃ (a := aP e) ⟨sc_ok _, by lsep hF⟩ (show ix Reg.r7 ∈ kWb by decide) hr01) fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _)) (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, _, hG⟩ := h₃.ex
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [k1Chk, kcChk]),
    fun e' => if e' = e then polyAt s₄.mem ((lay p STK σ).A 0 (oP e)) else A e', S', fun e' he' => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega_using [he'])]; exact polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he')
    · rw [ifp rfl]; exact pi
  · rw [r₄]; exact Proof.MlDsa.KeyGen.good_A he hG hout p1

/-! ## An entry of `s₁ ‖ s₂` -/

omit hP hF hS in
theorem seedS_eq (ρ' : List Byte) {r : Nat} (hr : r < 256) : seedS ρ' r = ρ' ++ [BitVec.ofNat 8 r, 0] := by
  simp only [seedS, Proof.MlDsa.KeyGen.integerToBytes_two hr]

omit hP hS in
theorem eta_of : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

/-- The call of `RejBoundedPoly`. -/
theorem rbS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (hs : Site (lay p STK σ) kWb STK s)
    {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (sP p r) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) →
      Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (bytesAt s.mem ((lay p STK σ).A 0 oSB) 66)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) → Q s') :
    WP isa (rejBoundedAt P (sc oSB) p.η (sP p r)) s Q := by
  have := hF.kl
  exact rb_ok hP.rejBounded hs (by omega_using [hS]) (sd := sc oSB) (a := sP p r) (w := sc oSS)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩ (eta_of hF) hQ

theorem expS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (h : KSamp p STK σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (KSamp p STK σ (p.k * p.ℓ) (r + 1)) := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold expS sampled
  refine WP.seq (WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) r)
    fun s₁ ⟨k₁, b₁⟩ => ?_)
  obtain h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₁.cs .r11 (by decide) (by decide))
  have hs₁ := h₁.k1.kc.site
  obtain hseed : bytesAt s₁.mem ((lay p STK σ).A 0 oSB) 66 = seedS (rho'Of p σ) r := by
    rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₁.k1.sb,
      add_ofNat_add, add_ofNat_add, seedS_eq _ (by omega_using [hr, hl, hk]), List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
    have e2 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := h₁.k1.z
    rw [e1, e2]; rfl
  refine WP.seq (rbS_ok hP hF hS hr hs₁ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  obtain hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  obtain hs₃ := hs₁.kept k₃
  refine WP.mono (andMask_ok hs₃ (a := sP p r) ⟨sc_ok _, by lsep hF⟩ (show ix Reg.r7 ∈ kWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain h₃ := h₁.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
    (k₃.cs .r11 (by decide) (by decide))
  obtain ⟨A, S', hA, hS', hG⟩ := h₃.ex
  obtain ⟨pi, p1, p0⟩ := masked_poly hred co
  obtain ⟨z, hz, hz1, hz0, hG'⟩ := Proof.MlDsa.KeyGen.good_S hr hG hout
  have hL := hs.ok
  refine ⟨(h₃.k1.r11 _).keep k₄ (by lsep hF [k1Chk, kcChk]), A, fun r' => if r' = r then z else S' r',
    fun e' he' => polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hA e' he'), fun r' hr' => ?_,
    by rw [r₄]; exact hG'⟩
  dsimp only
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
  · rw [ifn (by omega_using [hr'])]
    exact ⟨polyIs_keepW hL k₄.frame (by lsep hF) (by decide) rfl (hS' r' hr').1, (hS' r' hr').2⟩
  · rw [ifp rfl]
    refine ⟨?_, hz⟩
    show PolyIs s₄.mem (lpa (lay p STK σ) (sP p r')) (toRq z)
    by_cases h1 : s₃.gpr .r0 = 1
    · rw [hz1 h1, ← p1 h1]; exact pi
    · rw [hz0 h1]; exact p0 h1

/-! ## Constant time -/

omit hP hF hS in
theorem rho_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

omit hP hF hS in
theorem rej_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

omit hP hF hS in
theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem setS_taint : ∀ v < 16, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem andMask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem expA_two {e : Nat} (he : e < p.k * p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32) (expA P p e)
      fun _ _ => True := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  obtain hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  unfold expA sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 ++
      [BitVec.ofNat 8 (e % p.ℓ), BitVec.ofNat 8 (e / p.ℓ)]
  obtain hF1 : ∀ x, Site (lay p STK σ) kWb STK x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide)
      (e % p.ℓ)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSA + 33)) ⟨sc_ok _, by lsep hF⟩
        (by decide) (by decide) (e / p.ℓ)) fun s₂ ⟨k₂, b₂⟩ => ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSA + 32)) 1,
          tri (sc (oSA + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩, by
        have hL := hs.ok
        obtain b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
        obtain b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, List.append_assoc]
        refine congrArg _ ?_
        obtain e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32 + 1)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (taint7 (fun _ _ h => h.1) (setIJ_taint _ (by omega_using [hl, hr]) _ (by omega_using [hk, hq]))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        bytesAt x.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  obtain ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rnA_ok hP hF hS he hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt (by omega_using [hS]) (sd := sc oSA) (a := aP e) (w := sc oSS)
      ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
        show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (andMask_taint _ (by omega_using [he, hkl]))

theorem expA_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ e 0 s) (expA P p e) fun _ _ => True :=
  rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (RelCT.exists_ fun σ => expA_two hP hF hS he σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
      ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, by
        rw [h₁.k1.sa, lay_pub pub, h₂.k1.sa, rho_pub pub]⟩

theorem expS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧ bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r)) (expS P p r)
      fun _ _ => True := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold expS sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    (bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] →
      bytesAt x'.mem ((lay p STK σ).A 0 oSB) 66 = seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r)
  obtain hF1 : ∀ x, Site (lay p STK σ) kWb STK x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x hs =>
    WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok _, by lsep hF⟩ (by decide) (by decide) r) fun x' ⟨k₁, b₁⟩ =>
      ⟨⟨_, k₁⟩, fun hz => by
        have hL := hs.ok
        obtain b₀ := bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)
        obtain b₂ := bytes_keepW hL k₁.frame (i := 0) (o := oSB + 64 + 1) (l := 1) (by lsep hF) (by decide) (by decide)
        rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, seedS_eq _ (by omega_using [hr, hl, hk]), List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt x'.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
        have e2 : bytesAt x.mem ((lay p STK σ).A 0 (oSB + 64 + 1)) 1 = [0] := hz
        rw [e1, b₂, e2]; rfl⟩
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧ bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r))
    (taint7 (fun _ _ h => h.1) (setS_taint _ (by omega_using [hr, hl, hk]))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem ((lay p STK σ).A 0 oSB) 66) =
          Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem ((lay p STK σ).A 0 oSB) 66))
      fun x' y' ⟨_, x, y, ⟨T, zx, zy, hl⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx zx, by' zy, hl]⟩) ?_
  obtain ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rbS_ok hP hF hS hr hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rb_tr hP.rejBounded (by omega_using [hS]) (sd := sc oSB) (a := sP p r)
      (w := sc oSS) ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩,
        show ix Reg.r7 ∈ kWb by decide, show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      (eta_of hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (andMask_taint _ (by omega_using [hr, hkl, hl, hk]))

theorem expS_tr {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (expS P p r)
      fun _ _ => True :=
  rel_of (RelCT.exists_ fun σ => expS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, h₁.k1.z, by rw [lay_pub pub]; exact h₂.k1.z, by
      rw [h₁.k1.sb, lay_pub pub, h₂.k1.sb]; exact rej_pub pub hr⟩

/-! ## The pieces -/

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) :
    KPiece p STK (fun σ s => KSamp p STK σ e 0 s) (fun σ s => KSamp p STK σ (e + 1) 0 s) (expA P p e) :=
  ⟨fun _ _ _ h => expA_ok hP hF hS he h, expA_tr hP hF hS he⟩

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (r + 1) s)
      (expS P p r) :=
  ⟨fun _ _ _ h => expS_ok hP hF hS hr h, expS_tr hP hF hS hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece :
    KPiece p STK (fun σ s => K1 p STK σ s ∧ s.gpr .r11 = 1) (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s)
      (seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p STK σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => expA_piece hP hF hS (by omega_using [he])) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => KSamp p STK σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => expS_piece hP hF hS (by omega_using [hr])) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.Arm.KeyGen
