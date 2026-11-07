module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.ReadCache
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStart
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedHintPack


-- separate module: keeps cached-row contracts independent of the private verification composition that consumes them.

@[expose] public section

/-! ## VerifyCopy -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

abbrev PublicCache (p : Params) (S : Nat) (σ s : State) : Prop :=
  ReadCache p.k S (fun r => VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) s

theorem copy_public_optimized {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s) (cache : PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧ PublicCache p S σ t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L := hs.vc.lay hF hp
  have hk := hF.k
  have hl := hF.l
  have hkl := hF.kl
  have hsc := hF.scr
  have hwrite : inB (vW p) (tmP p) 1024 = true := by vlayd
  refine WP.mono_syms (cache.copy_poly (show Reg.x28 ∈ keptRegs by decide)
    (L.inW hwrite) hr) fun t ⟨ht, h24, hc, hpoly⟩ hy => ?_
  refine ⟨hs.keep hF hp ht (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hw' => by obtain rfl := List.mem_singleton.mp hw'; exact hwrite) h24,
    L.keepPoly ht (by vlayd) hw, hc, PosPolyIs.of_canonical hpoly⟩

theorem copy_public_scalar {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {r : Nat} (hr : r < p.k)
    (state : Verify.RowI p r (Verify.F1 p r p.ℓ) σ s) (cache : PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) s fun t =>
      Verify.RowI p r (Verify.F4 p r) σ t ∧ PublicCache p S σ t := by
  obtain ⟨h, A, c0, q, hs, hw⟩ := state
  have L := hs.vc.lay hF hp
  have hk := hF.k
  have hl := hF.l
  have hkl := hF.kl
  have hsc := hF.scr
  have hwrite : inB (vW p) (tmP p) 1024 = true := by vlayd
  refine WP.mono (cache.copy_poly (show Reg.x28 ∈ keptRegs by decide)
    (L.inW hwrite) hr) fun t ⟨ht, h24, hc, hpoly⟩ => ?_
  exact ⟨⟨h, A, c0, q, hs.keep hF hp ht (by scchks hF (Nat.le_of_lt hr)) h24,
    L.keepPoly ht (by vlayd) hw, hpoly⟩, hc⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## VerifyKeyRow -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

theorem keyRow_optimized {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = true)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (hw : Verify.Optimized.W p σ A r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true r t ∧
      Verify.Optimized.W p σ A r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (VG.Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  refine WP.ite (M := isa) (s.gpr .x22 != 0) rfl (fun hn => ?_) (fun _ => ?_)
  · exact WP.mono (copy_public_optimized hF hp hr hs hw (cache (bne_iff_ne.mp hn)))
      fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.2⟩
  · refine WP.seq (WP.mono (Verify.Optimized.unpack_ok hP hF hp hr hs hw)
      fun t ⟨ht, hw', hv⟩ => ?_)
    simpa [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired] using
      Verify.Optimized.nttT_ok hF hp hr ht hw' hv

theorem keyRow_scalar {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = false)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {r : Nat} (hr : r < p.k)
    (hs : Verify.RowI p r (Verify.F1 p r p.ℓ) σ s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r) s
      (Verify.RowI p r (Verify.F4 p r) σ) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  refine WP.ite (M := isa) (s.gpr .x22 != 0) rfl (fun hn => ?_) (fun _ => ?_)
  · exact WP.mono (copy_public_scalar hF hp hr hs (cache (bne_iff_ne.mp hn))) fun _ ht => ht.1
  · refine WP.seq (WP.mono ((Verify.t1_vpiece hP hF hr).ok σ s hp hs) fun t ht => ?_)
    simpa [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired] using
      (Verify.nttT_vpiece hP hF hr).ok σ t hp ht

theorem row_optimized {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = true)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A : Nat → Nat → Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.Optimized.dot p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r).aarch64Depth ≤ S)
    (hs : Verify.Optimized.SC p S σ h A c0 q p.ℓ true r s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r) s fun t =>
      Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1) t ∧
      (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r) s
      (Verify.Optimized.SC p S σ h A c0 q p.ℓ true (r + 1)) := by
    simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, ↓reduceIte]
    refine WP.seq (WP.mono (WP.optionalCache (Verify.Optimized.dot_ok hF hp hr hs)
      cache hdot hP.s64
      (fun t ht => (ht.1.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
      (fun t ht => (ht.1.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm))
      fun t ⟨⟨ht, hw⟩, hc⟩ => ?_)
    refine WP.seq (WP.mono (keyRow_optimized hpaired hP hF hp hr ht hw hc)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.product_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw, hv⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.subtract_ok hF hp hr ht hw hv)
      fun t ⟨ht, hw⟩ => ?_)
    refine WP.seq (WP.mono (Verify.Optimized.inverse_ok hF hp hr ht hw)
      fun t ⟨ht, hw⟩ => ?_)
    exact Verify.Optimized.hintPack_ok hF hp hr ht hw
  exact WP.optionalCache main cache hrow hP.s64
    (fun t ht => (ht.vc.top.cs .x21 (by decide)).trans (hs.vc.top.cs .x21 (by decide)).symm)
    (fun t ht => (ht.vc.top.cs .x22 (by decide)).trans (hs.vc.top.cs .x22 (by decide)).symm)

theorem row_scalar {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = false)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {r : Nat} (hr : r < p.k)
    (hdot : 16 * (VG.Impl.MlDsa.AArch64.Verify.dot P p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r).aarch64Depth ≤ S)
    (hs : Verify.SCx p p.ℓ true r σ s)
    (cache : s.gpr .x22 ≠ 0 → PublicCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r) s fun t =>
      Verify.SCx p p.ℓ true (r + 1) σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
  have old (t : State) (ht : Verify.SCx p p.ℓ true r σ t) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ t := by
    obtain ⟨_, _, _, _, h⟩ := ht
    exact h.vc.top
  have next (t : State) (ht : Verify.RowI p r (Verify.F1 p r p.ℓ) σ t) :
      VG.Proof.MlDsa.AArch64.KeyGen.Top σ t := by
    obtain ⟨_, _, _, _, h, _⟩ := ht
    exact h.vc.top
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r) s
      (Verify.SCx p p.ℓ true (r + 1) σ) := by
    simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, Bool.false_eq_true, ↓reduceIte]
    refine WP.seq (WP.mono (WP.optionalCache ((Verify.dot_vpiece hP hF hr).ok σ s hp hs)
      cache hdot hP.s64
      (fun t ht => ((next t ht).cs .x21 (by decide)).trans ((old s hs).cs .x21 (by decide)).symm)
      (fun t ht => ((next t ht).cs .x22 (by decide)).trans ((old s hs).cs .x22 (by decide)).symm))
      fun t ⟨ht, hc⟩ => ?_)
    refine WP.seq (WP.mono (keyRow_scalar hpaired hP hF hp hr ht hc) fun t ht => ?_)
    exact ((Verify.mulT_vpiece hP hF hr).seq ((Verify.sub_vpiece hP hF hr).seq
      ((Verify.inv_vpiece hP hF hr).seq ((Verify.uh_vpiece hP hF hr).seq
        (Verify.sbpR_vpiece hP hF hr))))).ok σ t hp ht
  have final (t : State) (ht : Verify.SCx p p.ℓ true (r + 1) σ t) :
      VG.Proof.MlDsa.AArch64.KeyGen.Top σ t := by
    obtain ⟨_, _, _, _, h⟩ := ht
    exact h.vc.top
  exact WP.optionalCache main cache hrow hP.s64
    (fun t ht => ((final t ht).cs .x21 (by decide)).trans ((old s hs).cs .x21 (by decide)).symm)
    (fun t ht => ((final t ht).cs .x22 (by decide)).trans ((old s hs).cs .x22 (by decide)).symm)

def verifyCoreK (p : Params) (optimized : Bool) : Contract isa where
  pre s := vPre p 16 s ∧ (optimized = true → Sign.StaticRoots 16 s) ∧
    (s.gpr .x22 ≠ 0 → PublicCache p 16 s s)
  post := (verifyContract p abi 16).post
  pub x y := vPub p 16 x y ∧
    (optimized = true → x.syms "VG_MLDSA_NTT_EXPANDED" = y.syms "VG_MLDSA_NTT_EXPANDED" ∧
      x.syms "VG_MLDSA_INV_FOLDED" = y.syms "VG_MLDSA_INV_FOLDED") ∧ SameIn [.x21, .x22] x y

end VG.Proof.MlDsa.AArch64.PreparedKey
