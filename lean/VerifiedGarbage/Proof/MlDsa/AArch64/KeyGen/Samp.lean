module

public import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `MlDsa.AArch64.KeyGen.Seeds`, which only this module used -/

section

/-!
# ML-DSA key generation on AArch64: the prologue and the seeds

The prologue saves the caller's registers and keeps the pointers
(`pro_piece`); then `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed
of `RejNTTPoly` and `ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`,
`K1`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep pbytes)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

theorem PPostB.app {S : Nat} {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPostB S s s₁ ws₁)
    (h₂ : PPostB S s₁ s₂ ws₂) (hc : ∀ w ∈ ws₂, w.1.1 ∈ keptRegs) : PPostB S s s₂ (ws₁ ++ ws₂) :=
  PPostB.trans h₁ h₂ hc (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)

theorem sc_bases (ws : List (Ptr × Nat)) (h : ∀ w ∈ ws, w.1.1 = .x28) : ∀ w ∈ ws, w.1.1 ∈ keptRegs :=
  fun w hw => by rw [h w hw]; decide

/-! ## The prologue -/

theorem scr_ge {p : Params} (hF : PFacts p) : 1024 * 32 ≤ scrLen p := by rw [scr_eq]; have := hF.k; omega_arith

theorem pro_piece {p : Params} (hF : PFacts p) {S : Nat} :
    Piece p S (fun σ s => s = σ) (fun σ s => KC p σ s ∧ s.gpr .x24 = 1) (.block pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp.1
    sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp'
    obtain ⟨_, hwr, _, _, d03, _⟩ := hp'
    have hsc : 1024 * 32 ≤ Spec.MlDsa.scratchWords p * 8 := scr_ge hF
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp, Offset.contains_base _ (by simp only [SV]; omega_arith) (by simp only [SV]; omega_arith)⟩
    refine WP.mono (pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_⟩, h24⟩
    rw [pa, ht.x25, BitVec.add_zero]
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact d03.sub_right (Offset.sub_base _ (by simp only [SV]; omega_arith))) (by decide)
  · subst h₁ h₂
    obtain ⟨esp, _, e0, e1, e2, e3⟩ := kgPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The seeds -/

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (σ s : State) : Prop where
  kc : KC p σ s
  hx : bytesAt s.mem (pa s (sc oHX)) 128 = hxOf p σ
  sa : bytesAt s.mem (pa s (sc oSA)) 32 = rhoOf p σ
  sb : bytesAt s.mem (pa s (sc oSB)) 64 = rho'Of p σ
  z : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]

/-- A piece that writes `ws` keeps `K1`. -/
def k1Chk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  kcChk p ws && keepB kgR (kgW p) ws (sc oHX) 128 && keepB kgR (kgW p) ws (sc oSA) 32 &&
    keepB kgR (kgW p) ws (sc oSB) 64 && keepB kgR (kgW p) ws (sc (oSB + 65)) 1

theorem K1.step {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ) {s s' : State}
    (h : K1 p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : k1Chk p ws = true) : K1 p σ s' := by
  simp only [k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP h0, by rw [L.keepBytes hP h1]; exact h.hx, by rw [L.keepBytes hP h2]; exact h.sa,
    by rw [L.keepBytes hP h3]; exact h.sb, by rw [L.keepBytes hP h4]; exact h.z⟩

theorem rho_eq (p : Params) (σ : State) : rhoOf p σ = (hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : rho'Of p σ = ((hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : kOf p σ = ((hxOf p σ).drop 96).take 32 := rfl

theorem bytesAt_two (m : Mem) (a : Addr) (x y : Byte) :
    bytesAt ((m.writeW a x).writeW (a + BitVec.ofNat 64 1) y) a 2 = [x, y] := by
  have hne : a + BitVec.ofNat 64 0 ≠ a + BitVec.ofNat 64 1 :=
    Offset.add_ofNat_ne a (by decide) (by decide) (by decide)
  show [_, _] = _
  dsimp only
  rw [Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply,
    Proof.MlDsa.KeyGen.ifn hne, Proof.MlDsa.KeyGen.ifp (Proof.MlKem.AArch64.ptr_zero a),
    Proof.MlDsa.KeyGen.ifp rfl]

theorem setTwo_ok {p : Params} {S : Nat} {s : State} (L : Lay S kgR (kgW p) s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : inB (kgW p) (sc o) 1 = true) (h2 : inB (kgW p) (sc (o + 1)) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(sc o, 1), (sc (o + 1), 1)] ∧ Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := sc o) (v := a) (by simp only; omega_arith) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := sc (o + 1)) (v := b) ho h2 (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (sc (o + 1)) = pa s (sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact bytesAt_two _ _ _ _

theorem hx_eq (p : Params) (σ : State) :
    hxOf p σ = Spec.MlDsa.H (xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ]) 128 := by
  rw [hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

theorem bytes64 (m : Mem) (a : Addr) : bytesAt m a 64 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 32 :=
  Proof.MlKem.bytesAt_add m a 32 32

theorem sc_pa {S : Nat} {s s' : State} {W : List Region} (hP : PostB S s s' W) (o : Nat) :
    pa s' (sc o) = pa s (sc o) := hP.pa (show Reg.x28 ∈ keptRegs by decide)

theorem seeds_ok {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {σ : State}
    (hp : kgPre p S σ) {s : State} (h : KC p σ s) (h24 : s.gpr .x24 = 1) :
    WP isa ((seedsWith keccak.callee) p) s fun s' => K1 p σ s' ∧ s'.gpr .x24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := scr_eq p
  have L := h.lay hF hp
  unfold seedsWith
  refine WP.seq (WP.mono (setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by layd) (by layd))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ := h.step hF hp hP₁ (by unfold kcChk; layd)
  have L₁ := h₁.lay hF hp
  refine WP.seq (WP.mono (shake_ok h16 hSl L₁ (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
    (by simp) (by unfold hashChk pieceChk; layd)) fun s₂ ⟨hP₂, x₂, ho₂⟩ => ?_)
  have h₂ := h₁.step hF hp hP₂ (by unfold kcChk; layd)
  have L₂ := h₂.lay hF hp
  have hmsg : ([⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩].map (pbytes s₁) : List (List Byte)).flatten =
      xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    have e1 : pbytes s₁ ⟨.x25, 0, 32⟩ = xiOf σ := h₁.xi
    have e2 : pbytes s₁ ⟨.x28, oKL, 2⟩ = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
      show bytesAt s₁.mem (pa s₁ (sc oKL)) 2 = _
      rw [sc_pa hP₁]; exact hb₁
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, e1, e2]
  rw [hmsg, ← hx_eq] at ho₂
  have ho₂' : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = hxOf p σ := by rw [sc_pa hP₂]; exact ho₂
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyP_ok L₂ (dst := sc oSA) (src := sc oHX) (by unfold copyPChk; layd)) fun s₃ ⟨hP₃, k₃, b₃⟩ => ?_
  have h₃ := h₂.step hF hp hP₃ (by unfold kcChk; layd)
  have L₃ := h₃.lay hF hp
  have hx3 : bytesAt s₃.mem (pa s₃ (sc oHX)) 128 = hxOf p σ := by rw [L₂.keepBytes hP₃ (by layd)]; exact ho₂'
  have sa3 : bytesAt s₃.mem (pa s₃ (sc oSA)) 32 = rhoOf p σ := by
    rw [sc_pa hP₃, b₃, rho_eq, ← ho₂', Proof.MlKem.bytesAt_take _ _ (by decide)]
  refine WP.mono (copyP_ok L₃ (dst := sc oSB) (src := sc (oHX + 32)) (by unfold copyPChk; layd))
    fun s₄ ⟨hP₄, k₄, b₄⟩ => ?_
  have h₄ := h₃.step hF hp hP₄ (by unfold kcChk; layd)
  have L₄ := h₄.lay hF hp
  refine WP.mono (copyP_ok L₄ (dst := sc (oSB + 32)) (src := sc (oHX + 64)) (by unfold copyPChk; layd))
    fun s₅ ⟨hP₅, k₅, b₅⟩ => ?_
  have h₅ := h₄.step hF hp hP₅ (by unfold kcChk; layd)
  have L₅ := h₅.lay hF hp
  refine WP.mono (setB_ok L₅ (p := sc (oSB + 65)) (v := 0) (by decide) (by layd) (show Reg.x28 ∈ keptRegs by decide))
    fun s₆ ⟨hP₆, k₆, m₆⟩ => ⟨⟨h₅.step hF hp hP₆ (by unfold kcChk; layd), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₅.keepBytes hP₆ (by layd), L₄.keepBytes hP₅ (by layd), L₃.keepBytes hP₄ (by layd)]; exact hx3
  · rw [L₅.keepBytes hP₆ (by layd), L₄.keepBytes hP₅ (by layd), L₃.keepBytes hP₄ (by layd)]; exact sa3
  · rw [L₅.keepBytes hP₆ (by layd)]
    have add32 : ∀ (t : State) (o : Nat), pa t (sc o) + BitVec.ofNat 64 32 = pa t (sc (o + 32)) := fun t o => by
      rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
    have A : bytesAt s₅.mem (pa s₅ (sc oSB)) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 := by
      rw [L₄.keepBytes hP₅ (by layd), sc_pa hP₄, b₄]
    have B : bytesAt s₅.mem (pa s₅ (sc (oSB + 32))) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [sc_pa hP₅, b₅, L₃.keepBytes hP₄ (by layd)]
    have C : rho'Of p σ = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 ++ bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [rho'_eq, ← hx3, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide),
        bytes64, add32, add32]
    rw [bytes64, add32, A, B, C]
  · rw [sc_pa hP₆, m₆, bytesAt_one, writeW8_self]; rfl
  · rw [k₆.get .x24, k₅.get .x24, k₄.get .x24, k₃.get .x24, x₂, k₁.get .x24, h24]

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_tr {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    RelCT isa (Two p S) ((seedsWith keccak.callee) p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := scr_eq p
  unfold seedsWith
  refine RelCT.seq (Two.step (taintRel [.x28] (fun x y h => h.x28) (setKL_taint p.k (by omega_arith) p.ℓ (by omega_arith)))
    fun x L => WP.mono (setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by layd) (by layd))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (Two.step (VectorTaint.relRegs [.x25, .x26, .x27, .x28] (fun x y h => h.bases) keccak.mldsaSeedsTaint.choose_spec)
    fun x L => WP.mono (shake_ok h16 hSl L (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
      (by simp) (by unfold hashChk pieceChk; layd)) fun _ h => ⟨_, h.1⟩) ?_
  exact taintRel [.x28] (fun x y h => h.x28) (by taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    Piece p S (fun σ s => KC p σ s ∧ s.gpr .x24 = 1) (fun σ s => K1 p σ s ∧ s.gpr .x24 = 1) ((seedsWith keccak.callee) p) :=
  ⟨fun _ _ hp h => seeds_ok hF h16 hSl hp h.1 h.2,
    rel_of (seeds_tr hF h16 hSl) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_two hF p₁ p₂ pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.AArch64.KeyGen

end

end

/-!
# ML-DSA key generation on AArch64: the samplers

The entries of `Â` (`expA_piece`; those of `s₁ ‖ s₂` are in
`OptimizedSecrets.lean`): after the first `e` entries of `Â` and `r` of
`s₁ ‖ s₂` (`KSamp`), each polynomial is reduced (and those of `s₁ ‖ s₂`
small), and `x24` is 1 if every sampler
succeeded, with the polynomials those of the standard for some bounds, or 0 if
key generation fails within the least bounds (`Good`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Params keyGenSeeds Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Bounds.Le bmax Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## What the samplers leave -/

/-- `x24` after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1 if they
are those of the standard, `A` and `S`, for some bounds; 0 if key generation
fails within the least bounds. -/
def Good (p : Params) (σ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 64) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (rhoOf p σ) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p σ) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (xiOf σ) = none)

theorem good_01 {p : Params} {σ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 64}
    (h : Good p σ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (pa s (aP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (pa s (sP p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧ Good p σ e r A S (s.gpr .x24)

theorem KSamp.keep {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ) {e r : Nat} {s s' : State}
    (h : KSamp p σ e r s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : k1Chk p ws = true)
    (ha : ∀ e' < e, keepB kgR (kgW p) ws (aP e') 1024 = true)
    (hs : ∀ r' < r, keepB kgR (kgW p) ws (sP p r') 1024 = true) (h24 : s'.gpr .x24 = s.gpr .x24) :
    KSamp p σ e r s' := by
  have L := h.k1.kc.lay hF hp
  obtain ⟨A, S', hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.step hF hp hP hc, A, S', fun e' he' => L.keepPoly hP (ha e' he') (hA e' he'),
    fun r' hr' => ⟨L.keepPoly hP (hs r' hr') (hS r' hr').1, (hS r' hr').2⟩, by rw [h24]; exact hG⟩

theorem KSamp.zero {p : Params} {σ s : State} (h : K1 p σ s) (h24 : s.gpr .x24 = 1) : KSamp p σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _),
    .inl ⟨h24, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem bytes34 (m : Mem) (a : Addr) : bytesAt m a 34 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 2 :=
  Proof.MlKem.bytesAt_add m a 32 2

theorem sc_add (t : State) (o k : Nat) : pa t (sc o) + BitVec.ofNat 64 k = pa t (sc (o + k)) := by
  rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## An entry of `Â` -/

theorem expA_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S σ) {e : Nat} (he : e < p.k * p.ℓ) {s : State} (h : KSamp p σ e 0 s) :
    WP isa (expA P p e) s (KSamp p σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.k1.kc.lay hF hp
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  unfold expA sampled
  refine WP.seq (WP.mono (setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by layd) (by layd))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ : KSamp p σ e 0 s₁ :=
    h.keep hF hp hP₁ (by unfold k1Chk kcChk; layd) (fun e' he' => by layd) (fun _ h => absurd h (Nat.not_lt_zero _))
      (k₁.get .x24)
  have L₁ := h₁.k1.kc.lay hF hp
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSA)) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [bytes34, h₁.k1.sa, sc_add, sc_pa hP₁, hb₁, Proof.MlDsa.KeyGen.seedA_eq]
  refine WP.seq (WP.mono (rejNttInline_ok hP.s64 hP.rejNtt L₁ (seed := sc oSA) (a := aP e) (ss := sc oSS)
    (by unfold rejNttChk; layd)) fun s₂ ⟨hP₂, x₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have L₂ := L₁.post hP₂
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L₂ (a := aP e) (by layd) (by layd) hr01) fun s₃ ⟨hP₃, x₃, hco⟩ => ?_
  have hP₁₃ := PPostB.app hP₂ hP₃ (sc_bases _ (by simp))
  have e₂ : pa s₂ (aP e) = pa s₁ (aP e) := sc_pa hP₂ _
  have e₃ : pa s₃ (aP e) = pa s₂ (aP e) := sc_pa hP₃ _
  rw [e₂] at hco
  obtain ⟨A, S', hA, _, hG⟩ := h₁.ex
  rw [x₂, Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01] at x₃
  refine ⟨h₁.k1.step hF hp hP₁₃ (by unfold k1Chk kcChk; layd), fun e' => if e' = e then polyAt s₃.mem (pa s₃ (aP e))
    else A e', S', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega_using [he'])]
      exact L₁.keepPoly hP₁₃ (by lay) (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rw [e₃, e₂]
      by_cases h1 : (s₂.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x₃]
    have hq' : e = p.ℓ * (e / p.ℓ) + e % p.ℓ := (Nat.div_add_mod e p.ℓ).symm
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
        · rw [ifn (by omega_using [he'])]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, e₃, e₂, (Proof.MlDsa.KeyGen.masked_one ho hco).1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

/-! ## Constant time -/

theorem rho_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : kgPub p S σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (kgPub_eq pub).2.1).1

theorem rej_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : kgPub p S σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (kgPub_eq pub).2.1).2 r hr

theorem Two.post {p : Params} {S : Nat} {x y x' y' : State} (T : Two p S x y) {W₁ W₂ : List Region}
    (hx : PostB S x x' W₁) (hy : PostB S y y' W₂) : Two p S x' y' :=
  ⟨T.lx.post hx, T.ly.post hy, fun r hr => by rw [hx.bs r (bases_kept r hr), hy.bs r (bases_kept r hr)]; exact T.same.1 r hr,
    by rw [hx.sp, hy.sp]; exact T.same.2⟩

/-- A piece that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {p : Params} {S : Nat} {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two p S x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB S x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB S y y' W)) :
    RelCT isa P c (Two p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB S x x' W) hok fun x y _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (hP x y h).post hx hy

/-- The check is the same for every offset: its hint is computed once, for offset 0. -/
theorem mask_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (mask (sc (oP j)))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (mask (sc 0)))).isSome = true := by decide +kernel

/-- The AND of a sampler's result and the mask of its output. -/
theorem tail_tr {p : Params} {S : Nat} {j : Nat} (hj : j < 80) :
    RelCT isa (Two p S) (.seq (.block and24) (mask (sc (oP j)))) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by simp only [and24, List.mem_singleton] at hi; subst hi; rfl)
      fun x _ => WP.mono (and24_ok x) fun _ ⟨o, _⟩ =>
        ⟨[], postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (mask_taint j hj))

theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

theorem expA_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : RelCT isa (R p S (KSamp p · e 0)) (expA P p e) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_using [hl])
  refine rel_of (Q := fun x y => Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 32 = bytesAt y.mem (pa y (sc oSA)) 32)
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, by
      rw [h₁.k1.sa, h₂.k1.sa, rho_pub pub]⟩
  unfold expA sampled
  -- The seed, then the call and the mask.
  let F := fun (x x' : State) => (∃ W, PostB S x x' W) ∧
    bytesAt x'.mem (pa x' (sc oSA)) 34 = bytesAt x.mem (pa x (sc oSA)) 32 ++ [BitVec.ofNat 8 (e % p.ℓ),
      BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, Lay S kgR (kgW p) x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x L =>
    WP.mono (setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by layd) (by layd))
      fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁⟩, by rw [bytes34, L.keepBytes hP₁ (by layd), sc_add, sc_pa hP₁, hb]⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.x28] (fun x y h => h.1.x28) (setIJ_taint _ (by omega_using [hl, hr]) _ (by omega_using [hk, hq])))
    (F := F) (fun x y h => ⟨hF1 x h.1.lx, hF1 y h.1.ly⟩)
    (Q := fun x y => Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    fun x y x' y' ⟨T, e32⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ => ⟨T.post hx hy, by rw [bx, by', e32]⟩) ?_
  have hc : rejNttChk kgR (kgW p) (sc oSA) (aP e) (sc oSS) = true := by unfold rejNttChk; layd
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rejNttInline_ok hP.s64 hP.rejNtt L hc)
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejNttInline_tr hP.rejNtt (kgOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (tail_tr (j := e) (by omega_using [he, hkl]))

/-! ## The pieces -/

theorem expA_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : Piece p S (KSamp p · e 0) (KSamp p · (e + 1) 0) (expA P p e) :=
  ⟨fun _ _ hp h => expA_ok hP hF hp he h, expA_tr hP hF he⟩

end VG.Proof.MlDsa.AArch64.KeyGen
