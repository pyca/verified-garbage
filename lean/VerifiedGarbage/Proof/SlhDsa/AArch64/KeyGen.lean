module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.KeyGenPro
public import VerifiedGarbage.Spec.SlhDsa.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.SlhDsa.Fld

/-!
# SLH-DSA (SHAKE) on AArch64: key generation, correct

`keygen(seeds = x0, sk = x1, pk = x2, scratch = x3)`
(`Impl.SlhDsa.AArch64.Shake.keyGen`): the prologue (`pro_ok`), the call of
`xmssTree` on the top layer's tree with no key pair to sign with, whose root
is `PK.root`, then the keys copied out and the caller's registers restored
(`tail_ok`): `slh_keygen_internal` (Algorithm 18), as `kgK` states it
(`keyGen_wp`), for any implementation of `xmssTree` verified against its
contract.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.KeyGen

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Shake (topSaved)

/-! ## The contract, as the proof uses it -/

/-- `keyGenContract`'s precondition, a fact at a time. -/
structure KG (p : Params) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 3 * p.n⟩]
  wr : s.wr = [⟨s.gpr .x1, p.skLen⟩, ⟨s.gpr .x2, p.pkLen⟩, ⟨s.gpr .x3, scratchLen⟩]
  d_seed_sk : Region.Disjoint ⟨s.gpr .x0, 3 * p.n⟩ ⟨s.gpr .x1, p.skLen⟩
  d_seed_pk : Region.Disjoint ⟨s.gpr .x0, 3 * p.n⟩ ⟨s.gpr .x2, p.pkLen⟩
  d_seed_scr : Region.Disjoint ⟨s.gpr .x0, 3 * p.n⟩ ⟨s.gpr .x3, scratchLen⟩
  d_sk_pk : Region.Disjoint ⟨s.gpr .x1, p.skLen⟩ ⟨s.gpr .x2, p.pkLen⟩
  d_sk_scr : Region.Disjoint ⟨s.gpr .x1, p.skLen⟩ ⟨s.gpr .x3, scratchLen⟩
  d_pk_scr : Region.Disjoint ⟨s.gpr .x2, p.pkLen⟩ ⟨s.gpr .x3, scratchLen⟩
  f_seed : (s.gpr .x0).toNat + 3 * p.n ≤ 2 ^ 64
  f_sk : (s.gpr .x1).toNat + p.skLen ≤ 2 ^ 64
  f_pk : (s.gpr .x2).toNat + p.pkLen ≤ 2 ^ 64
  f_scr : (s.gpr .x3).toNat + scratchLen ≤ 2 ^ 64

/-- The keys of `slh_keygen_internal` of the seeds at `x0`. -/
abbrev kgOut (p : Params) (s : State) : List Byte × List Byte :=
  let x := bytesAt s.mem (s.gpr .x0) (3 * p.n)
  keyGenInternal p (chunk x p.n 0) (chunk x p.n 1) (chunk x p.n 2)

def kgK (p : Params) : Contract isa where
  pre s := KG p s
  post s s' := (bytesAt s'.mem (s.gpr .x1) p.skLen, bytesAt s'.mem (s.gpr .x2) p.pkLen) = kgOut p s
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-! ## Bytes -/

/-- `S + o` reads as a number. -/
theorem toNat_at {S : Addr} {o : Nat} (h : S.toNat + o < 2 ^ 64) : (at' S o).toNat = S.toNat + o := by
  rw [at', BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-! ## The call of `xmssTree` -/

/-- The SHAKE parameter sets the code is built for: the heights of their trees. -/
abbrev Hps (hp : Nat) : Prop := hp = 3 ∨ hp = 4 ∨ hp = 8 ∨ hp = 9

theorem sigLen_le {p : Params} (hz : Sz p) (hh : Hps p.hp) : p.xmssSigLen ≤ 2432 := by
  rcases hz.nv with e | e | e <;> rcases hh with h | h | h | h <;>
    (simp only [Params.xmssSigLen, hz.len, e, h]; decide)

/-- The regions of the call: `scratch` and the signature it discards. -/
abbrev callW (p : Params) (S : Addr) : List Region :=
  [⟨S, scratchLen⟩, ⟨at' S Layout.oSigTmp, p.xmssSigLen⟩]

theorem call_pre {p : Params} (hz : Sz p) (hh : Hps p.hp) {σ u : State} {S X : Addr} (hK : KG p σ)
    (hS : σ.gpr .x3 = S) (hu : KPro p σ S X u) :
    (xmssContract p).pre (u.callEntry.withRegions [] (callW p S)) ∧
      Covers ([] ++ callW p S) (u.rd ++ u.wr) ∧ Covers (callW p S) u.wr := by
  have hL := sigLen_le hz hh
  have eT : Layout.oSigTmp = 30144 := rfl
  have fS : S.toNat + scratchLen ≤ 2 ^ 64 := by rw [← hS]; exact hK.f_scr
  have hsc : scratchLen = 65536 := rfl
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [] (callW p S)).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have hcov : Covers (callW p S) u.wr := by
    rw [hu.wr, hK.wr, hS]
    refine Covers.cons (Covers.one ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      by simp [scratchLen, Region.contains_self]⟩) (Covers.cons (Covers.one ⟨_,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        Offset.contains_base _ (by omega) (by omega)⟩) Covers.nil)
  refine ⟨⟨?_, ⟨bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n, Proof.SlhDsa.layerTree (p.d - 1) 0, ?_⟩, ?_⟩,
    by rw [List.nil_append]; exact Covers.right hcov, hcov⟩
  · rw [hg _ (by decide), hg _ (by decide), hu.x0, hu.x2]
    refine ⟨rfl, rfl, fS, ?_, Offset.disjoint_base S (by omega) (by omega), fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
    show (at' S Layout.oSigTmp).toNat + p.xmssSigLen ≤ 2 ^ 64
    rw [toNat_at (by omega)]; omega
  · rw [hg _ (by decide), hu.x0, State.withRegions_mem, State.callEntry_mem]
    exact hu.env
  · rw [hg _ (by decide), hu.x1]; decide

/-- The root of the top layer's tree, at the address the code sets. -/
theorem root_adrs (p : Params) (skSeed pkSeed : List Byte) :
    xmssNode p skSeed 0 p.hp pkSeed (treeAdrs (Proof.SlhDsa.layerTree (p.d - 1) 0)) =
      xmssNode p skSeed 0 p.hp pkSeed (setLayerAddress adrsZero (p.d - 1)) := by
  refine Proof.SlhDsa.xmssNode_congr (p := p) skSeed pkSeed ?_ ?_ ?_ p.hp 0
  · simp [treeAdrs, Proof.SlhDsa.layerTree, toByte]
  · simp [setLayerAddress, setBytes, adrsZero, toByte]
  · simp [treeAdrs, Proof.SlhDsa.layerTree, setLayerAddress, setBytes, adrsZero, Proof.SlhDsa.toByte_zero,
      Proof.SlhDsa.toByte_length]

/-- The keys and `oTop` are outside what the internal functions change. -/
theorem keys_disj {p : Params} (hz : Sz p) (S : Addr) {o l : Nat}
    (h₁ : Layout.oTop ≤ o) (h₂ : o + l ≤ Layout.oDigest) : ∀ r ∈ changes p S, Region.Disjoint ⟨at' S o, l⟩ r := by
  have hn := hz.n32
  have eT : Layout.oTop = 1536 := rfl
  have eD : Layout.oDigest = 1792 := rfl
  have hsc : scratchLen = 65536 := rfl
  intro r hr
  simp only [changes, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((h | h) | ⟨k, hk, h | h⟩) | (h | h | h | h | h) <;> subst h
  · exact (Offset.disjoint_base S (d := o) (k := workUsed) (by simp only [workUsed]; omega) (by omega))
  · exact Offset.disjoint S (by simp only [Layout.oVars, Layout.frameLen]; omega) (by omega)
      (by simp only [Layout.oVars, Layout.frameLen]; omega)
  · exact Offset.disjoint S (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega) (by omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
  · exact Offset.disjoint S (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega) (by omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
  · exact Offset.disjoint S (by simp only [Layout.oDigits]; omega) (by omega) (by simp only [Layout.oDigits]; omega)
  · exact Offset.disjoint S (by simp only [Layout.oN]; omega) (by omega)
      (by simp only [Layout.oN, Layout.nodeSlots]; omega)
  · exact Offset.disjoint S (by simp only [Layout.oRoots, Layout.oN, Layout.nodeSlots]; omega) (by omega)
      (by simp only [Layout.oRoots, Layout.oN, Layout.nodeSlots]; omega)
  · exact Offset.disjoint S (by simp only [Layout.oMsg]; omega) (by omega) (by simp only [Layout.oMsg]; omega)
  · exact Offset.disjoint S (by simp only [Layout.oFidx]; omega) (by omega) (by simp only [Layout.oFidx]; omega)

/-! ## The function -/

/-- `Impl.SlhDsa.AArch64.Shake.keyGen` from `kgK`'s precondition: its
postcondition and the calling convention, for any `xmssTree` verified
against its contract. -/
theorem keyGen_wp {p : Params} (hz : Sz p) (hh : Hps p.hp) (hd : p.d - 1 < 2 ^ 16)
    {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true) {σ : State} (hK : KG p σ) :
    WP isa (Impl.SlhDsa.AArch64.Shake.keyGen p f) σ fun s' => abiPreserved σ s' ∧ (kgK p).post σ s' := by
  have hn32 := hz.n32
  have hsc : scratchLen = 65536 := rfl
  obtain ⟨S, hS⟩ : ∃ S, σ.gpr .x3 = S := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, σ.gpr .x0 = X := ⟨_, rfl⟩
  have fS : S.toNat + scratchLen ≤ 2 ^ 64 := by rw [← hS]; exact hK.f_scr
  have hw : (⟨S, scratchLen⟩ : Region) ∈ σ.wr := by rw [hK.wr, hS]; simp
  have hr : (⟨X, 3 * p.n⟩ : Region) ∈ σ.rd := by rw [hK.rd, hX]; simp
  have hdis : Region.Disjoint ⟨X, 3 * p.n⟩ ⟨S, scratchLen⟩ := by rw [← hX, ← hS]; exact hK.d_seed_scr
  rw [keyGen_eq]
  refine WP.seq (WP.mono (pro_ok hz hd hS hX hw hr (by rw [← hX]; exact hK.f_seed) fS hdis) fun u hu => ?_)
  obtain ⟨hpre, hc, hw'⟩ := call_pre hz hh hK hS hu
  refine WP.seq (WP.callV hx.1 hpre hc hw' (fun s' hrd hwr hsp hfr hpres _ hv hpost => ?_) hxn)
  have hvx0 : (u.callEntry.withRegions [] (callW p S)).gpr .x0 = S := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hu.x0]
  dsimp only [xmssContract] at hpost
  rw [hvx0] at hpost
  obtain ⟨-, hroot, -, hF⟩ := hpost _ _ _ hu.env rfl
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at hF hroot
  -- what the call keeps
  have hkd : ∀ {o l : Nat}, Layout.oTop ≤ o → o + l ≤ Layout.oDigest →
      ∀ r ∈ changes p S ++ [⟨u.gpr .x2, p.xmssSigLen⟩], Region.Disjoint ⟨at' S o, l⟩ r := fun {o l} h₁ h₂ r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact keys_disj hz S h₁ h₂ r hr
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hu.x2]
      have eS : Layout.oSigTmp = 30144 := rfl
      have eD : Layout.oDigest = 1792 := rfl
      have := sigLen_le hz hh
      exact Offset.disjoint S (d := o) (n := l) (e := Layout.oSigTmp) (k := p.xmssSigLen) (by omega) (by omega)
        (by omega)
  rw [State.callEntry_gpr _ (by decide)] at hF
  have hkeys : ∀ c < 3, bytesAt s'.mem (at' S (Layout.oKeys + 32 * c)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n := fun c hc => by
    rw [bytesAt_frame hF (hkd (by simp only [Layout.oKeys, Layout.oTop]; omega)
      (by simp only [Layout.oKeys, Layout.oDigest]; omega)) (by omega)]
    exact hu.keys c hc
  have hsv : ∀ i < 8, s'.mem.readW (at' S (Layout.oTop + 8 * i)) 64 = σ.gpr (topSaved.getD i .x19) := fun i hi => by
    rw [Frame.readW hF (r := ⟨at' S (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
      (hkd (by omega) (by simp only [Layout.oTop, Layout.oDigest]; omega)) (by decide)]
    exact hu.saved i hi
  have hp' : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r := hpres
  have hb' : s'.gpr .x19 = S := by rw [hp' _ (by decide) (by decide), hu.x19]
  have h20 : s'.gpr .x20 = σ.gpr .x1 := by rw [hp' _ (by decide) (by decide), hu.x20]
  have h21 : s'.gpr .x21 = σ.gpr .x2 := by rw [hp' _ (by decide) (by decide), hu.x21]
  have hwS : (⟨S, scratchLen⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr]; exact hw
  have hsk : (⟨σ.gpr .x1, 4 * p.n⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr, hK.wr]; simp [Params.skLen]
  have hpk : (⟨σ.gpr .x2, 2 * p.n⟩ : Region) ∈ s'.wr := by rw [hwr, hu.wr, hK.wr]; simp [Params.pkLen]
  have dsk : Region.Disjoint ⟨σ.gpr .x1, 4 * p.n⟩ ⟨S, scratchLen⟩ := by rw [← hS]; exact hK.d_sk_scr
  have dpk : Region.Disjoint ⟨σ.gpr .x2, 2 * p.n⟩ ⟨S, scratchLen⟩ := by rw [← hS]; exact hK.d_pk_scr
  have hsk0 : bytesAt u.mem (at' S Layout.oSkSeed) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 0)) p.n :=
    hu.keys 0 (by decide)
  refine WP.mono (tail_ok hz hb' h20 h21 hwS hsk hpk fS hK.f_sk hK.f_pk dsk dpk hK.d_sk_pk hsv) fun t ht => ?_
  refine ⟨⟨fun r hr => ?_, by rw [ht.sp, hsp, hu.sp], fun r hr => by rw [ht.vcs r hr, hv r hr, hu.vcs r hr]⟩, ?_⟩
  · by_cases hr' : r ∈ topSaved
    · exact ht.cs r hr'
    · have hu' : r ∈ untouched := by revert r; decide
      rw [ht.keep r hu', hp' r (by revert r; decide) (by revert r hu'; decide), hu.keep r hu']
  · show (bytesAt t.mem (σ.gpr .x1) (4 * p.n), bytesAt t.mem (σ.gpr .x2) (2 * p.n)) = kgOut p σ
    have k0 := hkeys 0 (by decide)
    have k1 := hkeys 1 (by decide)
    have k2 := hkeys 2 (by decide)
    rw [show Layout.oKeys + 32 * 0 = Layout.oKeys from rfl] at k0
    rw [show Layout.oKeys + 32 * 1 = Layout.oKeys + 32 from rfl] at k1
    rw [show Layout.oKeys + 32 * 2 = Layout.oKeys + 64 from rfl] at k2
    rw [ht.sk, ht.pk, k0, k1, k2, hroot, hsk0, root_adrs]
    simp only [kgOut, hX, keyGenInternal]
    rw [chunk_bytesAt _ _ (c := 3) (by decide), chunk_bytesAt _ _ (c := 3) (by decide),
      chunk_bytesAt _ _ (c := 3) (by decide)]

end VG.Proof.SlhDsa.AArch64.KeyGen
