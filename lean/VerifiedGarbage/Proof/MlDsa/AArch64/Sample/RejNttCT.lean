module

import VerifiedGarbage.Proof.MlKem.AArch64.Sample
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.Sample
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rel
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Zero
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp

/-! ### `MlDsa.AArch64.Sample.RejNtt`, which this module and modules that import it used -/

section

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`

Correctness: the function runs in pieces, the prologue (`J0`), the sponge,
whose output is `G(ρ, 1008)` (`J6`), `a` set to zeros, the loop, which stores
the coefficients `rnFold` samples from it (`RejNttLoop.lean`), and the end,
which returns whether there are 256 of them. The postcondition of the contract
follows from the prefix lemmas (`rejNTT_some`, `rejNTT_none`).

Constant time up to the seed, relating two runs piece by piece (`Rel.lean`):
the prologue, the sponge, the zeros and the end by the taint analysis, from
registers that correctness makes equal in both runs; the loop by `memTaint`,
since both runs have the same output (a function of the seed, which the
contract lets the function leak) and zeros in `a`, and the loop touches
nothing else.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_subImm wp_lsr ptr_add toNat_lsr toNat_sub_n agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt shakeSuffix)

/-- `vg_mldsa_rej_ntt_poly(seed = x0, a = x1, scratch = x2) -> w0`, with 16
bytes of stack below `sp`: the contract the proof is written against. -/
def rnK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 34⟩
    let a : Region := ⟨s.gpr .x1, 1024⟩
    let scratch : Region := ⟨s.gpr .x2, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 then 1 else 0) ∧
      ((rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 →
        PolyIs s'.mem (s.gpr .x1) (toPoly (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008))))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp ∧ bytesAt s₁.mem (s₁.gpr .x0) 34 = bytesAt s₂.mem (s₂.gpr .x0) 34

namespace RejNtt

/-- The call. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .x0, 34, σ.gpr .x2, σ.gpr .x1, 0⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G ((spOf σ).msg σ) 1008

theorem X_length (σ : State) : (X σ).length = 1008 := G_length _ _

theorem spOk {σ : State} (hp : rnK.pre σ) : SpOk (spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2, by show (34 : Nat) < 2 ^ 64; decide⟩

theorem pro_ok {σ : State} (hp : rnK.pre σ) :
    WP isa (.block (pro .x2 .x1 (.movz .x .x27 0 0) (.movz .x .x4 34 0))) σ (J0 (spOf σ) σ) :=
  Sample.pro_ok (spOk hp) rfl rfl (by decide) rfl
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

/-- After the sponge, and `a` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  out : bytesAt s.mem ((spOf σ).at' 840) 1008 = X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x1) i = 0

theorem zero_ok {σ s : State} (hp : rnK.pre σ) (h : J6 168 1008 (spOf σ) σ s) :
    WP isa zeroPoly s (Z σ) :=
  WP.mono (zeroPoly_ok (fun i hi => inA (spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (a_scr' (spOk hp) (by omega_using [])).symm) (by omega_using []), h.out,
        (G_eq _ _).symm], z⟩

theorem lpre {σ s : State} (hp : rnK.pre σ) (h : Z σ s) :
    RejNtt.LPre (X σ) ((spOf σ).at' 840) (σ.gpr .x1) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [at_add]; exact inScrRd (spOk hp) h.env.rd h.env.wr (by omega_using [hp']),
    fun i hi => inA (spOk hp) h.env.wr hi, (a_scr' (spOk hp) (by omega_using [])).symm,
    by rw [h.env.x25], h.env.x26⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : Env (spOf σ) σ s
  x4 : (s.gpr .x4).toNat = 256 - (rnFold [] (X σ)).length
  st : Stored s.mem (σ.gpr .x1) (rnFold [] (X σ))

theorem loopP_ok {σ s : State} (hp : rnK.pre σ) (h : Z σ s) : WP isa rnLoop s (LP σ) :=
  WP.mono (RejNtt.loop_ok (X_length σ) (lpre hp h)) fun u hu => by
    have x4 := hu.x4
    have st := hu.st
    rw [RejNtt.Lt_336 (X_length σ)] at x4 st
    exact ⟨h.env.keepA (spOk hp) hu.keep hu.frame, x4, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {σ s : State} (hp : rnK.pre σ) (h : LP σ s) :
    WP isa (.block (retZ ++ epi)) s fun s' => abiPreserved σ s' ∧ rnK.post σ s' := by
  rw [retZ, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subImm (by decide) fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => ?_
  have hl := rnFold_length_le (a := ([] : List Zq)) (by simp) (X σ)
  have v0 : (s₂.gpr .x0).toNat = if (rnFold [] (X σ)).length = 256 then 1 else 0 := by
    have one : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, h.x4, one]
    simp only [VG.Spec.MlDsa.n, Nat.reducePow] at hl ⊢
    split <;> omega_arith
  have e1 := (h.env.keep (h₁.keep.trans h₂.keep) (by rw [h₂.mem, h₁.mem]))
  refine WP.mono (epi_ok (spOk hp) e1) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₂.mem, h₁.mem]
    exact stored_polyIs h.st hf

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa (rejNTTWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (spongeWith_ok (v := v) (spOk hp) (rate := 168) (outlen := 1008) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (loopP_ok hp h3) fun _ h4 => end_ok hp h4))))

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample

end

end

/-!
# ML-DSA on AArch64: `vg_mldsa_rej_ntt_poly`, constant time and verified

Two runs whose seeds and pointers agree leak the same (`ctWith`), piece by
piece (`Rel.lean`), and the shared contract follows from `rnK`
(`rejNTT_verifiedWith`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs coeffAt)
open VG.Spec.Sha3 (bytesAt)

theorem toNat_inj {a b : BitVec 64} {n : Nat} (ha : a.toNat = n) (hb : b.toNat = n) : a = b :=
  BitVec.eq_of_toNat_eq (ha.trans hb.symm)

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyR p).Contains y 1) : m y = 0 :=
  Proof.MlKem.AArch64.Sample.byte_zero (p := p) (fun i hi => h i hi) hy

namespace RejNtt

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(spOf σ).at' 840, 1008⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x1)]

theorem pub_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : spOf σ₁ = spOf σ₂ := by
  rw [spOf, spOf, hq.1, hq.2.1, hq.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : rnK.pub σ₁ σ₂) : X σ₁ = X σ₂ := by
  simp only [X, Sp.msg]; rw [hq.2.2.2.2]

theorem loop_ct : RelCT isa (Rel2 rnK.pre rnK.pub Z) rnLoop fun _ _ => True := by
  refine relMem lrd lwr [.x25, .x26]
    (fun σ₁ σ₂ _ _ hq => by simp [lrd, lwr, pub_eq hq, hq.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [regions (spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · exact ⟨(spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (spOk hp).wr]
      exact ⟨polyR (σ.gpr .x1), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := lpre hp h
    obtain ⟨t, u, e, -⟩ := RejNtt.loop_ok (X_length σ) (s₀ := s.withRegions (lrd σ) (lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega_using [hp']) (by omega_using [hp']))),
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out, X_eq hq]
      · rw [byte_zero h₁.zero hc, byte_zero h₂.zero (by rw [← hq.2.1]; exact hc)]

theorem regs3 {s₁ s₂ : State} {a b c : Reg} (ha : s₁.gpr a = s₂.gpr a) (hb : s₁.gpr b = s₂.gpr b)
    (hc : s₁.gpr c = s₂.gpr c) : ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun r hr => by
  rcases mem3 hr with rfl | rfl | rfl <;> with_reducible assumption

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa rnK.pre rnK.pub (rejNTTWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaNttTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True) (P := Rel2 rnK.pre rnK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0, .x1, .x2]
    (fun σ s hp h => by subst h; exact pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂; exact ⟨hq.2.2.2.1, regs3 hq.1 hq.2.1 hq.2.2.1⟩) (by taint_decide)) ?_
  refine RelCT.seq (vectorRelTaintStep (J' := fun σ => J6 168 1008 (spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => spongeWith_ok (v := v) (spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, pub_eq hq]
      · rw [h₁.x3, h₂.x3, pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) hhint) ?_
  refine RelCT.seq (relTaintStep (J' := Z) [.x26] (fun σ s hp h => zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := LP) (fun σ s hp h => loopP_ok hp h) loop_ct) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, pub_eq hq]⟩) (by taint_decide)

end RejNtt

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def rnSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejNTT_verifiedWith (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sample.rejNTTWith v.callee) (Proof.MlDsa.rejNTTContract AArch64.abi 16) :=
  Verified.of_correct (RejNtt.correctWith v) (RejNtt.ctWith v)
    { pre := by sig_implies_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, AArch64.abi,
        AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs]
        dsimp only [rnK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
            show Spec.MlDsa.rejNTTPoly 1008 _ = _
            rw [rejNTT_some hf, hpoly]⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2⟩ := h
        exact ⟨hx0, hx1, hx2, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, rnK, AArch64.abi,
        AArch64.argRegs] [rnSat] using rnSat }

end VG.Proof.MlDsa.AArch64.Sample
