module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.SignRest
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsPrologue
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsExec
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedExpansion
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttVerified
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Entry
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry

-- separate module: isolates memory framing, input snapshots, and ABI restoration from the independently iterated two-run timing proof.

@[expose] public section

/-! ## SignCore -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Sign

def selectedExpansion (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 && p.k != 4 then CachedMatrix.expandA (primsWith v.callee) p
  else expandA (primsWith v.callee) p

theorem selectedExpansion_depth (v : VG.Proof.Sha3.AArch64.Permutation) (p : Params) :
    16 * (selectedExpansion v p).aarch64Depth ≤ 16 := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.expandA_depth (prims_okWith (keccak := v)) p
  · exact expandA_depth (prims_okWith (keccak := v)) p

theorem selectedExpansion_ok (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : Ok3 p) (hc : aChk p = true) {σ s : State} (h : RootedSt p 16 σ s)
    (h1 : s.gpr .x24 = 1) :
    WP isa (selectedExpansion v p) s fun t => IA p 16 σ (p.k * p.ℓ) t ∧ StaticRoots 16 t := by
  unfold selectedExpansion
  split
  · exact CachedMatrix.rooted_expandA_ok (prims_okWith (keccak := v)) hp hc h h1
  · exact rooted_expandA_ok (prims_okWith (keccak := v)) hp hc h h1

theorem core_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (σ : State) (hpre : (signK p 16).pre σ) (roots : StaticRoots 16 σ) (rp : PairedRoots 16 σ)
    (hcache : σ.gpr .x22 ≠ 0 → SecretCache p 16 σ σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (signK p 16).post σ t := by
  have hc := allChk_ok hp
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hf⟩ := hc
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf
  obtain ⟨hsv, _⟩ := hf
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ ∃ u, FS p 16 σ u ∧ t.gpr .x0 = u.gpr .x24 ∧ t.mem = u.mem := by
    change WP isa (.seq (.block pro) (.seq (selectedExpansion v p)
      (.seq (ifOk (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
        (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) (.block epi)))) σ _
    refine WP.seq (WP.mono (WP.optionalCache
      (paired_prologue hp (by decide) hpre roots rp) hcache (Nat.zero_le _) (by decide)
      (fun t ht => ht.1.1.1.top.cs .x21 (by decide))
      (fun t ht => ht.1.1.1.top.cs .x22 (by decide)))
      fun s1 ⟨⟨⟨h1, hflag⟩, r1⟩, c1⟩ => ?_)
    refine WP.seq (WP.mono (WP.optionalCache (WP.pairedRoots
      (selectedExpansion_ok v hp ha h1 hflag) r1 (selectedExpansion_depth v p) (by decide))
      c1 (selectedExpansion_depth v p) (by decide)
      (fun t ht => (ht.1.1.st.top.cs .x21 (by decide)).trans (h1.1.top.cs .x21 (by decide)).symm)
      (fun t ht => (ht.1.1.st.top.cs .x22 (by decide)).trans (h1.1.top.cs .x22 (by decide)).symm))
      fun s2 ⟨⟨⟨h2, hr2⟩, r2⟩, c2⟩ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (.seq
      (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) s2 (FS p 16 σ) from ?_)
      fun s4 h4 => ?_)
    · unfold ifOk
      refine ifOkElse_ok (fun hn => ?_) fun hz => ?_
      · have hflag := x24_one h2.r01 hn
        obtain ⟨ok, fam⟩ := h2.ok hflag
        exact rest_ok v hp ⟨h2.st, ok, fam⟩ hr2 r2 c2
      · have hzero := x24_zero h2.r01 hz
        exact WP.block_nil ⟨h2.st, .inl hzero,
          fun hflag => absurd (hflag.symm.trans hzero) (by decide), fun _ => signMu_min_A (h2.bad hzero)⟩
    · exact WP.mono (epi_ok h4.st.top fun k hk => h4.st.lay.inR (hsv k hk))
        fun t ⟨habi, hret, hmem⟩ => ⟨habi, s4, h4, hret, hmem⟩
  obtain ⟨tr, t, he, habi, u, hu, hret, hmem⟩ := main
  refine ⟨tr, t, he, habi, ?_⟩
  have e23 : pa u (.x23, 0) = σ.gpr .x3 := by
    rw [pa, hu.st.top.regs (.x23, .x3) (by decide), BitVec.add_zero]
  show Outcome _ _ _
  rcases hu.r01 with h0 | h1
  · exact .inr ⟨by rw [hret, h0]; rfl, hu.bad h0⟩
  · exact .inl ⟨by rw [hret, h1]; rfl, maxBounds, by rw [hmem, ← e23]; exact hu.ok h1⟩

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignCorrect -/
/-! ## SignCoreDepth -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Sign

theorem left_dle {d : Nat} {a b : Prog isa} (h : DLe d (.seq a b)) : DLe d a :=
  ⟨(Nat.max_le.mp h.le).1⟩

theorem right_dle {d : Nat} {a b : Prog isa} (h : DLe d (.seq a b)) : DLe d b :=
  ⟨(Nat.max_le.mp h.le).2⟩

theorem then_dle {d : Nat} {c : isa.Cond} {a b : Prog isa} (h : DLe d (.ite c a b)) : DLe d a :=
  ⟨(Nat.max_le.mp h.le).1⟩

theorem selectedLoop_dle (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    DLe 1 (selectedLoop v p) := by
  unfold selectedLoop
  split
  · rename_i hpair
    simp only [Bool.and_eq_true] at hpair
    have hk : p.k ≠ 4 := bne_iff_ne.mp hpair.2
    have hp' : p = mlDsa65 ∨ p = mlDsa87 := by
      rcases hp with h44 | h65 | h87
      · subst p; exact absurd rfl hk
      · exact .inl h65
      · exact .inr h87
    have h := cachedPairedSignWith_dle v hp'
    exact left_dle (right_dle (then_dle (left_dle (right_dle (right_dle h)))))
  · have h := pairedSignWith_dle v hp
    exact left_dle (right_dle (then_dle (left_dle (right_dle (right_dle h)))))

theorem core_dle (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Sign.core v.callee (primsWith v.callee) p) := by
  have he : DLe 1 (selectedExpansion v p) := .of_fd (selectedExpansion_depth v p)
  have hl := selectedLoop_dle v hp
  have hi := initialization_dle v p
  have old := pairedSignWith_dle v hp
  have hout := right_dle (right_dle (then_dle (left_dle (right_dle (right_dle old)))))
  change DLe 1 (.seq (.block pro) (.seq (selectedExpansion v p)
    (.seq (ifOk (.seq (Impl.MlDsa.AArch64.PreparedKey.Sign.initialization v.callee (primsWith v.callee) p)
      (.seq (selectedLoop v p) (ifOk (Optimized.output (primsWith v.callee) p))))) (.block epi))))
  exact .seq (.block _) (.seq he (.seq (.ite (.seq hi (.seq hl hout)) (.block _)) (.block _)))

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignEntry -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Optimized

def signingMetadata (s : State) : State :=
  (s.write .x .x21 (s.gpr .x5)).write .x .x22 (s.gpr .x6)

theorem shared_sign_input {p : Params} (hp : Ok3 p) {s : State}
    (h : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre s) :
    (signK p 48).pre s ∧ StaticRoots 48 s ∧ PairedRoots 48 s ∧
      (s.gpr .x6 ≠ 0 → SecretCache p 48 s (signingMetadata s)) := by
  sig_pre [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs, Abi.withConsts,
    pairedSignRootConsts_eq, nttConsts_eq, Inverse.inverseConsts_eq,
    Abi.constRegions, Abi.constsHeld, TableConstants.staticNttWords_length,
    InverseTable.expandedWords_length, PairedTable.expandedWords_length, stackBelow] at h
  obtain ⟨hsp, hdrop, hf, hi, hpair, hff, hfw, hfs, hif, hiw, his, hpf, hpw, hps,
    hfa, hia, hpa, htake, hwr, d1, d2, d3, d4, d5, d6, d7, dc1, dc2,
    k1, k2, k3, k4, k5, kc, n1, n2, n3, n4, n5, _nc, hcache⟩ := h
  have hrd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩,
      ⟨s.gpr .x5, (s.gpr .x6).toNat⟩] ++
      [⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩,
        ⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩] := by
    rw [← List.take_append_drop (s.rd.length - 3) s.rd, htake, hdrop]
  refine ⟨?_, ⟨⟨hf, hff, ?_, hfw, hfs, hfa⟩, ⟨hi, hif, ?_, hiw, his, hia⟩⟩,
    ⟨hpair, hpf, ?_, hpw, hps, hpa⟩, ?_⟩
  · have hsub : [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩] ⊆ s.rd := by
      intro R hR
      rw [hrd]
      exact List.mem_append_left _ (List.mem_append_left _ hR)
    dsimp only [signK, scrLen]
    rw [Nat.mul_comm 8 (scratchWords p)]
    exact ⟨hsub, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5,
      n1, n2, n3, n4, n5, hsp⟩
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED", 3904⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_FOLDED", 3904⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · apply Covers.one
    refine ⟨⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩, ?_, Region.contains_self _ _⟩
    rw [hrd]
    simp
  · intro hne
    rcases hcache with hz | ⟨hlen, hvalues⟩
    · exact absurd hz hne
    change (s.gpr .x6).toNat = 1024 * (p.ℓ + 2 * p.k) at hlen
    have e21 : (signingMetadata s).gpr .x21 = s.gpr .x5 := by simp [signingMetadata, State.write]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases hp with rfl | rfl | rfl <;> decide
    · rw [e21, ← hlen]
      apply Covers.one
      refine ⟨⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ?_, Region.contains_self _ _⟩
      change _ ∈ s.rd ++ s.wr
      rw [hrd]
      simp
    · intro R hR
      change R ∈ s.wr at hR
      rw [hwr] at hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rw [e21, ← hlen]
      rcases hR with rfl | rfl
      exacts [dc1.symm, dc2.symm]
    · rw [e21, ← hlen]
      exact kc.symm
    · intro i hii
      rw [pa, e21]
      exact hvalues i hii

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignFrames -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem cache_reframe {count S T : Nat} {f : Nat → Poly} {s t : State} {W : List Region}
    (h : ReadCache count S f s) (hf : Frame W s.mem t.mem)
    (hd : ∀ R ∈ W, (⟨s.gpr .x21, 1024 * count⟩ : Region).Disjoint R)
    (h21 : t.gpr .x21 = s.gpr .x21) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : ReadCache count T f t := by
  refine ⟨h.small, ?_, ?_, ?_, ?_⟩
  · simpa only [h21, hr, hw] using h.readable
  · simpa only [h21, hw] using h.writable
  · rw [h21]
    exact h.stack.sub_right hst
  · intro i hi
    simp only [pa, h21]
    exact VG.Proof.MlDsa.Verify.polyIs_frame hf
      (fun R hR => (hd R hR).sub_left (h.slice_sub hi)) (h.values i hi)

theorem staticTable_reframe {S T : Nat} {name : String} {words : List (BitVec 64)}
    {s t : State} {W : List Region} (h : StaticTable S name words s)
    (hf : Frame W s.mem t.mem) (hd : ∀ R ∈ W, (⟨s.syms name, 3904⟩ : Region).Disjoint R)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hy : t.syms = s.syms)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : StaticTable T name words t := by
  refine ⟨?_, by simpa only [hy] using h.fit, ?_, ?_, ?_, by simpa only [hy] using h.aligned⟩
  · intro i hi
    rw [hy, hf.readW (r := ⟨s.syms name, 3904⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact h.held i hi
  · simpa only [hy, hr, hw] using h.readable
  · simpa only [hy, hw] using h.writable
  · rw [hy]
    exact h.stack.sub_right hst

theorem pairedRoots_reframe {S T : Nat} {s t : State} {W : List Region} (h : PairedRoots S s)
    (hf : Frame W s.mem t.mem)
    (hd : ∀ R ∈ W, (⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩ : Region).Disjoint R)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hy : t.syms = s.syms)
    (hst : Region.Sub (below t.sp T) (below s.sp S)) : PairedRoots T t := by
  refine ⟨?_, by simpa only [hy] using h.fit, ?_, ?_, ?_, by simpa only [hy] using h.aligned⟩
  · intro i hi
    rw [hy, hf.readW (r := ⟨s.syms "VG_MLDSA_INV_PAIR", 4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact h.held i hi
  · simpa only [hy, hr, hw] using h.readable
  · simpa only [hy, hw] using h.writable
  · rw [hy]
    exact h.stack.sub_right hst

def signInner (s : State) : State := pushState .x22 (pushState .x21 s)

theorem signInner_sp (s : State) : (signInner s).sp = s.sp - 32 := by
  simp only [signInner, pushState, BitVec.sub_sub]
  rfl

theorem signInner_frame (s : State) : Frame [below s.sp 32] s.mem (signInner s).mem := by
  have h1 : Frame [below s.sp 32] s.mem (pushState .x21 s).mem :=
    Frame.write (r := below s.sp 32) (Frame.refl _ _) (by simp) _
      (below_frame_contains s.sp 16 (by decide))
  refine Frame.write (r := below s.sp 32) h1 (by simp) _ ?_
  change (below s.sp 32).Contains ((s.sp - 16) - 16) 8
  rw [BitVec.sub_sub]
  change (below s.sp 32).Contains (s.sp - 32) 8
  simp [Region.Contains]

theorem metadata_setup (s : State) :
    WP isa (.block [.addImm .x .x21 .x5 0, .addImm .x .x22 .x6 0]) s fun t =>
      VG.Proof.MlKem.AArch64.Only [.x21, .x22] s t ∧
      t.gpr .x21 = s.gpr .x5 ∧ t.gpr .x22 = s.gpr .x6 := by
  open VG.Proof.MlKem.AArch64 in
  refine wp_addImm (by decide) fun u hu h21 => wp_addImm (by decide) fun t ht h22 => wp_nil ?_
  exact ⟨(hu.trans ht).mono (by simp), by rw [ht.get .x21, h21, BitVec.add_zero],
    by rw [h22, BitVec.add_zero, hu.get .x6]⟩

theorem sign_frame_guards {p : Params} {σ s : State} (pre : (signK p 48).pre σ)
    {offset : Nat} (ho : offset ≤ 32) (hw : s.wr = σ.wr)
    (hsp : s.sp = σ.sp - BitVec.ofNat 64 offset) :
    16 ≤ s.sp.toNat ∧ ∀ R ∈ s.wr, Region.Disjoint ⟨s.sp - 16, 16⟩ R := by
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, k4, k5, _, _, _, _, _, hstack⟩ := pre
  have hsub : Region.Sub (⟨s.sp - 16, 16⟩ : Region) (below σ.sp 48) := by
    have h1 := below_below σ.sp offset 16
    have h2 := below_sub (sp := σ.sp) (a := 16 + offset) (b := 48) (by omega) (by decide)
    rw [hsp]
    exact fun a ha => h2 a (h1 a ha)
  refine ⟨?_, ?_⟩
  · rw [hsp, toNat_sub_ofNat' (by omega)]
    omega
  · intro R hR
    rw [hw, hwr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [k4.sub_left hsub, k5.sub_left hsub]

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignSetup -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem setup_sign_inputs {p : Params} (hp : Ok3 p) {σ s : State}
    (hpre : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ)
    (hs : VG.Proof.MlKem.AArch64.Only [.x21, .x22] (signInner σ) s)
    (h21 : s.gpr .x21 = σ.gpr .x5) (h22 : s.gpr .x22 = σ.gpr .x6)
    (hy : s.syms = σ.syms) :
    (signK p 16).pre s ∧ StaticRoots 16 s ∧ PairedRoots 16 s ∧
      (s.gpr .x22 ≠ 0 → SecretCache p 16 s s) ∧
      skOf p s = skOf p σ ∧ muOf s = muOf σ ∧ rndOf s = rndOf σ ∧ s.gpr .x3 = σ.gpr .x3 := by
  obtain ⟨pre, roots, paired, cached⟩ := shared_sign_input hp hpre
  have e0 : s.gpr .x0 = σ.gpr .x0 := hs.get .x0
  have e1 : s.gpr .x1 = σ.gpr .x1 := hs.get .x1
  have e2 : s.gpr .x2 = σ.gpr .x2 := hs.get .x2
  have e3 : s.gpr .x3 = σ.gpr .x3 := hs.get .x3
  have e4 : s.gpr .x4 = σ.gpr .x4 := hs.get .x4
  have er : s.rd = σ.rd := hs.rd
  have ew : s.wr = σ.wr := hs.wr
  have esp : s.sp = σ.sp - 32 := hs.sp.trans (signInner_sp σ)
  have hframe : Frame [below σ.sp 32] σ.mem s.mem := by
    rw [hs.mem]
    exact signInner_frame σ
  have hsmall : Region.Sub (below σ.sp 32) (below σ.sp 48) := below_sub (by decide) (by decide)
  have hstack : Region.Sub (below s.sp 16) (below σ.sp 48) := by
    rw [esp]
    exact below_below σ.sp 32 16
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5,
    n1, n2, n3, n4, n5, hsp⟩ := pre
  have hkey : skOf p s = skOf p σ := by
    rw [skOf, skOf, e0]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k1.sub_left hsmall).symm) (by omega)
  have hmu : muOf s = muOf σ := by
    rw [muOf, muOf, e1]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k2.sub_left hsmall).symm) (by decide)
  have hrnd : rndOf s = rndOf σ := by
    rw [rndOf, rndOf, e2]
    exact MlKem.bytesAt_frame hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact (k3.sub_left hsmall).symm) (by decide)
  refine ⟨?_, ?_, ?_, ?_, hkey, hmu, hrnd, e3⟩
  · dsimp only [signK]
    rw [er, ew, e0, e1, e2, e3, e4]
    refine ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7,
      k1.sub_left hstack, k2.sub_left hstack, k3.sub_left hstack,
      k4.sub_left hstack, k5.sub_left hstack, n1, n2, n3, n4, n5, ?_⟩
    rw [esp]
    change 16 ≤ (σ.sp - BitVec.ofNat 64 32).toNat
    rw [toNat_sub_ofNat' (by omega)]
    omega
  · exact ⟨staticTable_reframe roots.forward hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact roots.forward.stack.sub_right hsmall) er ew hy hstack,
      staticTable_reframe roots.inverse hframe (fun R hR => by
        obtain rfl := List.mem_singleton.mp hR
        exact roots.inverse.stack.sub_right hsmall) er ew hy hstack⟩
  · exact pairedRoots_reframe paired hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact paired.stack.sub_right hsmall) er ew hy hstack
  · intro hn
    have hn' : σ.gpr .x6 ≠ 0 := by rwa [h22] at hn
    have hc := cached hn'
    have e21 : s.gpr .x21 = (signingMetadata σ).gpr .x21 := by
      simpa [signingMetadata, State.write] using h21
    have hc' : SecretCache p 16 σ s := cache_reframe hc hframe (fun R hR => by
      obtain rfl := List.mem_singleton.mp hR
      exact hc.stack.sub_right hsmall) e21 er ew hstack
    change ReadCache (p.ℓ + 2 * p.k) 16
      (fun i => (preparedSecretPolys p (skOf p s))[i]!) s
    rw [hkey]
    exact hc'

end VG.Proof.MlDsa.AArch64.PreparedKey

/-! ## SignCorrect -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign

theorem common_frame_bounds {d : Nat} (hd : d ≤ 1) :
    16 * (d + 1) + 16 < 2 ^ 64 ∧ 16 * d + 16 < 2 ^ 64 := by omega

theorem withCache_correct (v : VG.Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Ok3 p)
    (σ : State) (hpre : (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t := by
  have pre := (shared_sign_input hp hpre).1
  have hd := common_frame_bounds (core_dle v hp).le
  have g0 := sign_frame_guards (s := σ) pre (offset := 0) (by decide) rfl (by simp)
  have g1 := sign_frame_guards (s := pushState .x21 σ) pre (offset := 16) (by decide) rfl rfl
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Sign.withCache v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (signWithCacheContract p (abi.withConsts pairedSignRootConsts) 48).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Sign.withCache
    refine WP.frameReg g0.1 g0.2 ?_ (by
      simpa only [Code.aarch64Depth, Instr.frameUnits, Nat.zero_max] using hd.1)
    refine WP.frameReg g1.1 g1.2 ?_ (by
      simpa only [Code.aarch64Depth, Nat.zero_max] using hd.2)
    refine WP.seq (WP.mono_syms (metadata_setup (signInner σ)) fun s ⟨hs, h21, h22⟩ hy => ?_)
    obtain ⟨hcore, roots, paired, cache, hkey, hmu, hrnd, e3⟩ :=
      setup_sign_inputs hp hpre hs h21 h22 hy
    obtain ⟨tr, t, he, habi, hpost⟩ := core_correct v hp s hcore roots paired cache
    refine ⟨tr, t, he, ⟨?_, rfl, ?_⟩, ?_⟩
    · intro r hr
      by_cases e21 : r = .x21
      · subst r; simp [State.write]
      by_cases e22 : r = .x22
      · subst r; simp [State.write]
      simp only [State.write, e21, e22, ite_false]
      rw [habi.1 r hr, hs.get r (by simp [e21, e22])]
      rfl
    · intro r hr
      exact (habi.2.2 r hr).trans (hs.vcs r hr)
    · change Outcome (fun b => signMu p b (skOf p s) (muOf s) (rndOf s))
        ((t.gpr .x0).setWidth 32) (VG.Spec.Sha3.bytesAt t.mem (s.gpr .x3) p.sigLen) at hpost
      rw [hkey, hmu, hrnd, e3] at hpost
      sig_post [signWithCacheContract, signWithCacheSig, signSig, abi, argRegs, Abi.withConsts]
      simpa [skOf, muOf, rndOf, State.write] using hpost
  obtain ⟨tr, t, he, habi, hpost⟩ := main
  exact ⟨tr, t, he, habi, hpost⟩

end VG.Proof.MlDsa.AArch64.PreparedKey
