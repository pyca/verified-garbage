module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.ReadCache
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecode
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Sign
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedLoopConcrete
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Copy

@[expose] public section

/-! ## SignCopy -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr seqR)
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

abbrev SecretCache (p : Params) (S : Nat) (σ s : State) : Prop :=
  ReadCache (p.ℓ + 2 * p.k) S (fun i => (preparedSecretPolys p (skOf p σ))[i]!) s

theorem copy_secret_ok {p : Params} {S : Nat} {σ s : State} {a b c i j : Nat}
    (hi : i < p.ℓ + 2 * p.k) (hwrite : inB (sgW p) (pS j) 1024 = true)
    (hid : idChk p [(pS j, 1024)] a b c = true)
    (h : PositiveID p S σ a b c s) (cache : SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (pS j) (.x21, 1024 * i) 1024) s fun t =>
      PositiveID p S σ a b c t ∧ SecretCache p S σ t ∧
      PosPl t j (preparedSecretPolys p (skOf p σ))[i]! := by
  have hw := h.im.st.lay.inW hwrite
  have hd := (cache.apart_write hw).sub_left (cache.slice_sub hi)
  refine WP.mono_syms (copy_core (n := 64) (by decide) (by decide) (pS_bases j)
    (show Reg.x21 ∈ keptRegs by decide) s (cache.inR hi) hw hd)
    fun t ⟨hb, hf, hk⟩ hy => ?_
  have ht : PPostB S s t [(pS j, 1024)] := postB_of_keep hk (by decide) hf
  have hws : ∀ w ∈ [(pS j, 1024)], inB (sgW p) w.1 w.2 = true := by simpa using hwrite
  refine ⟨h.step ht hy hid hws, cache.step ht (fun w hw' => h.im.st.lay.inW (hws w hw')), ?_⟩
  change PosPolyIs t.mem (pa t (pS j)) _
  rw [ht.pa (pS_bases j)]
  exact PosPolyIs.of_canonical (VG.Proof.MlDsa.PreparedKey.polyIs_of_copy hb (cache.values i hi))

theorem copy_s1 {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : dChk p = true) (hi : i < p.ℓ)
    (h : PositiveID p S σ i 0 0 s) (cache : SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (s1P p i) (.x21, 1024 * i) 1024) s
      fun t => PositiveID p S σ (i + 1) 0 0 t ∧ SecretCache p S σ t := by
  obtain ⟨hd, _⟩ := (dChk_spec hc).1 i hi
  simp only [decChk, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hbu, _⟩, hid⟩, _⟩ := hd
  have hw := (rw_parts hbu).2.2
  refine WP.mono (copy_secret_ok (by omega) hw hid h cache) fun t ⟨ht, hcache, hpoly⟩ => ?_
  rw [VG.Proof.MlDsa.PreparedKey.secret_s1 p (skOf p σ) hi] at hpoly
  exact ⟨⟨ht.im, ht.roots, ht.s1.snoc hpoly, ht.s2, ht.t0⟩, hcache⟩

theorem copy_s2 {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : dChk p = true) (hi : i < p.k)
    (h : PositiveID p S σ p.ℓ i 0 s) (cache : SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (s2P p i) (.x21, 1024 * (p.ℓ + i)) 1024) s
      fun t => PositiveID p S σ p.ℓ (i + 1) 0 t ∧ SecretCache p S σ t := by
  obtain ⟨hd, _⟩ := (dChk_spec hc).2.1 i hi
  simp only [decChk, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hbu, _⟩, hid⟩, _⟩ := hd
  have hw := (rw_parts hbu).2.2
  refine WP.mono (copy_secret_ok (by omega) hw hid h cache) fun t ⟨ht, hcache, hpoly⟩ => ?_
  rw [VG.Proof.MlDsa.PreparedKey.secret_s2 p (skOf p σ) hi] at hpoly
  exact ⟨⟨ht.im, ht.roots, ht.s1, ht.s2.snoc hpoly, ht.t0⟩, hcache⟩

theorem copy_t0 {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hc : dChk p = true) (hi : i < p.k)
    (h : PositiveID p S σ p.ℓ p.k i s) (cache : SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.copy (t0P p i) (.x21, 1024 * (p.ℓ + p.k + i)) 1024) s
      fun t => PositiveID p S σ p.ℓ p.k (i + 1) t ∧ SecretCache p S σ t := by
  obtain ⟨hd, _⟩ := (dChk_spec hc).2.2.1 i hi
  simp only [decChk, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hbu, _⟩, hid⟩, _⟩ := hd
  have hw := (rw_parts hbu).2.2
  refine WP.mono (copy_secret_ok (by omega) hw hid h cache) fun t ⟨ht, hcache, hpoly⟩ => ?_
  rw [VG.Proof.MlDsa.PreparedKey.secret_t0 p (skOf p σ) hi] at hpoly
  exact ⟨⟨ht.im, ht.roots, ht.s1, ht.s2, ht.t0.snoc hpoly⟩, hcache⟩

theorem restoreSecrets_ok {p : Params} {S : Nat} {σ s : State}
    (hc : dChk p = true) (h : PositiveID p S σ 0 0 0 s) (cache : SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets p) s fun t =>
      PositiveID p S σ p.ℓ p.k p.k t ∧ SecretCache p S σ t := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Sign.restoreSecrets
  refine WP.seq (WP.mono (seqR_ok
    (I := fun i s => PositiveID p S σ i 0 0 s ∧ SecretCache p S σ s) p.ℓ 0
    (fun i _ hi s hs => copy_s1 hc (by omega) hs.1 hs.2) s ⟨h, cache⟩) fun a ha => ?_)
  simp only [Nat.zero_add] at ha
  refine WP.seq (WP.mono (seqR_ok
    (I := fun i s => PositiveID p S σ p.ℓ i 0 s ∧ SecretCache p S σ s) p.k 0
    (fun i _ hi s hs => copy_s2 hc (by omega) hs.1 hs.2) a ha) fun b hb => ?_)
  simp only [Nat.zero_add] at hb
  simpa only [Nat.zero_add] using seqR_ok
    (I := fun i s => PositiveID p S σ p.ℓ p.k i s ∧ SecretCache p S σ s) p.k 0
    (fun i _ hi s hs => copy_t0 hc (by omega) hs.1 hs.2) b hb

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignRest -/
/-! ## SignInit -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem initialization_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {σ s : State} (h : IM p S σ s) (roots : StaticRoots S s)
    (hcache : s.gpr .x22 ≠ 0 → SecretCache p S σ s) :
    WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization keccak.callee P p) s
      (PositiveIK p S σ) := by
  unfold Impl.MlDsa.AArch64.PreparedKey.Sign.initialization
  refine WP.ite (M := isa) (s.gpr .x22 != 0) rfl (fun hne => ?_) (fun _ => ?_)
  · have cache := hcache (bne_iff_ne.mp hne)
    refine WP.seq (WP.mono (restoreSecrets_ok (dChk_ok hp)
      ⟨h, roots, by simp [PosFam], by simp [PosFam], by simp [PosFam]⟩ cache)
      fun t ht => positiveSeed_ok hP hp ht.1)
  · exact positiveInitialization_ok hP hp h roots

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignDepth -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Proof.MlDsa.AArch64.Message

theorem copy_dle (dst src : Ptr) (bytes : Nat) : DLe 1 (copy dst src bytes) := by
  unfold copy
  split <;> dle_tac

theorem restore_dle (p : Params) : DLe 1 (Sign.restoreSecrets p) := by
  unfold Sign.restoreSecrets
  exact DLe.seq (DLe.seqR (fun _ => copy_dle _ _ _) _ _)
    (DLe.seq (DLe.seqR (fun _ => copy_dle _ _ _) _ _)
      (DLe.seqR (fun _ => copy_dle _ _ _) _ _))

theorem initialization_dle (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) :
    DLe 1 (Sign.initialization v.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith v.callee) p) := by
  have hd := pairedInitialization_dle v p
  have hs : DLe 1 (Impl.MlDsa.AArch64.Sign.shakeAtWith v.callee
      [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩]
      ⟨.x28, Impl.MlDsa.AArch64.Sign.oMS, 64⟩) :=
    ⟨(Nat.max_le.mp hd.le).2⟩
  unfold Sign.initialization
  exact DLe.ite (DLe.seq (restore_dle p) hs) hd

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignRest -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

def selectedLoop (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 && p.k != 4 then
    Impl.MlDsa.AArch64.Sign.Cached.signLoop (primsWith v.callee) p (Optimized.pairedChecks p)
  else Optimized.signLoopWith v.callee (primsWith v.callee) p (Optimized.pairedChecks p)

theorem selectedLoop_ok (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {σ s : State} (h : PositiveIK p 16 σ s) (rp : PairedRoots 16 s) :
    WP isa (selectedLoop v p) s fun t => PositiveXS p 16 σ t ∧ PairedRoots 16 t := by
  unfold selectedLoop
  split
  · rename_i hpair
    simp only [Bool.and_eq_true] at hpair
    have hk : p.k ≠ 4 := bne_iff_ne.mp hpair.2
    have hp' : p = mlDsa65 ∨ p = mlDsa87 := by
      rcases hp with h44 | h65 | h87
      · subst p
        exact absurd rfl hk
      · exact .inl h65
      · exact .inr h87
    apply Cached.signLoop_concrete_ok (prims_okWith (keccak := v)) hp' _ h rp
    have hd := (Message.cachedCommit_dle v hp').le
    change 16 * _ ≤ 16
    omega
  · exact selectedPairedSignLoop_ok v hp h rp

theorem afterInitialization_ok (v : VG.Proof.Sha3.AArch64.Permutation)
    {p : Params} (hp : Ok3 p) {σ s : State} (h : PositiveIK p 16 σ s) (rp : PairedRoots 16 s) :
    WP isa (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))) s (FS p 16 σ) := by
  have hA := expandA_max h.d.im.ok
  refine WP.seq (WP.mono (selectedLoop_ok v hp h rp) fun b ⟨hb, _⟩ => ?_)
  unfold ifOk
  refine ifOkElse_ok (fun hne => ?_) fun he => ?_
  · have h1 := x24_one hb.r01 hne
    obtain ⟨t, hlt, hrej, hsampled, hpass, hct, hz, hh⟩ := hb.pass h1
    have ready : AcceptedConversion p 16 σ (p.ℓ * t) (-(q : Int) + 1) ((q : Int) - 1) 0 b :=
      ⟨⟨⟨hb.k.d.im.st, hb.k.d.roots⟩, by intro j hj; omega, fun j _ hj => hz j hj, h1⟩, hct, hh⟩
    refine WP.mono (optimizedOutput_ok (prims_okWith (keccak := v)) hp ready (by omega) (by omega) hpass)
      fun u ⟨hu, hbytes, hflag⟩ => ?_
    exact ⟨hu, .inr hflag,
      fun _ => by rw [hbytes]; exact signMu_max (paramsOk hp) hA hlt hrej hsampled hpass,
      fun h0 => absurd (h0.symm.trans hflag) (by decide)⟩
  · have h0 := x24_zero hb.r01 he
    exact WP.block_nil ⟨hb.k.d.im.st, .inl h0,
      fun h1 => absurd (h1.symm.trans h0) (by decide), fun _ => signMu_min_L hA (hb.fail h0)⟩

theorem rest_ok (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    {σ s : State} (h : IM p 16 σ s) (roots : StaticRoots 16 s) (rp : PairedRoots 16 s)
    (hcache : s.gpr .x22 ≠ 0 → SecretCache p 16 σ s) :
    WP isa (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p)))) s (FS p 16 σ) := by
  have hd : 16 * (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee
      (primsWith v.callee) p).aarch64Depth ≤ 16 := by
    have := (initialization_dle v p).le
    omega
  refine WP.seq (WP.mono (WP.pairedRoots
    (initialization_ok (keccak := v) (prims_okWith (keccak := v)) hp h roots hcache)
    rp hd (by decide)) fun t ⟨ht, rt⟩ => afterInitialization_ok v hp ht rt)

end VG.Proof.MlDsa.AArch64.PreparedKey
