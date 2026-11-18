module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MlDsa.Arith.Zq
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Rel
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA4
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.X86_64.Round
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Rel
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA4
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-! ### `MlDsa.X86_64.Sign.PhaseACT`, which only this module used -/

section

/-!
# ML-DSA signing on x86-64: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly` and `vg_mldsa_rej_ntt_poly4`, so they agree on `r15`
(`RA`), and leak the same (`expandA_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `r15`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  RR p D (fun σ s => IA p D σ e s) fun x y => x.gpr .r15 = y.gpr .r15

theorem callE_ok' {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (callP "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (aBase p + e)), .ptr (sc oPS)]) s
      fun s' => JE p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3 _ (by decide)⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem sampleE_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (he : eChk p e = true) :
    RelCT isa (RA p D e) (sampleE P p e) (RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  rw [sampleE_eq]
  refine RelCT.seq (R := RR p D (fun σ s => IA p D σ e s ∧ bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e)
    fun x y => x.gpr .r15 = y.gpr .r15) ?_ (RelCT.seq (R := RR p D (JE p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_)
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => blkE_ok he h)
      (block_tr (rs := [.rbx]) rfl fun x y h r hr => ?_) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.lrel fun _ _ h => h.st).regs (.rbx, scrLen p) (by simp [sgR, sgW])
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => callE_ok' hP he h.1 h.2)
      ((rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, seedE, seedE, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (andE_ok he h) (WP.mono (and15_ok s) fun _ h => h.1))
      (block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

/-! ## Four entries at a time -/

/-- Two runs in a group, after the seeds of its first `j` entries, with the same `r15`. -/
abbrev RG (p : Params) (D e j : Nat) : State → State → Prop :=
  RR p D (fun σ s => GS p D σ e j s) fun x y => x.gpr .r15 = y.gpr .r15

theorem slot_tr {p : Params} {D e j : Nat} (hj4 : j < 4) (hc : slotChk p e j = true) :
    RelCT isa (RG p D e j) (.block (setSR p e j)) (RG p D e (j + 1)) :=
  stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => slot_ok hj4 hc h)
    (block_tr (rs := [.rbx]) rfl fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.lrel fun _ _ h => h.ia4.ia.st).regs (.rbx, scrLen p) (by simp [sgR, sgW]))
    fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]

theorem call4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (hc : callChk p e = true) :
    RelCT isa (RG p D e 4) (rej4At P (pS (aBase p + e)) (r4P p))
      (RR p D (fun σ s => IA4 p D σ (e + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  have hc' := hc
  simp only [callChk, Bool.and_eq_true] at hc'
  unfold rej4At
  refine RelCT.seq (R := RR p D (J4 p D e)
      fun x y => x.gpr .r15 = y.gpr .r15 ∧ (x.gpr .rax).setWidth 32 = (y.gpr .rax).setWidth 32) ?_ ?_
  · refine stepRR (F := fun s s' => s'.gpr .r15 = s.gpr .r15) (fun σ s _ h => callG_ok hP hc h)
      ((rej4Call_tr hP hc'.2).mono (fun x y h => ⟨h.lrel fun _ _ h => h.ia4.ia.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, g₁, g₂⟩, _⟩ := h
    rw [g₁.seeds, g₂.seeds, pub_rho hpub]
  · refine stepRR (F := fun s s' => s'.gpr .r15 =
        BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32))
      (fun σ s _ h => WP.conj (and4_ok hc h) (WP.mono (and15_ok s) fun _ h => h.1))
      (block_nomem_tr (fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
      fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]

theorem sample4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat} (hc : g4Chk p (4 * g) = true) :
    RelCT isa (RR p D (fun σ s => IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (sample4 P p g)
      (RR p D (fun σ s => IA4 p D σ (4 * g + 4) s) fun x y => x.gpr .r15 = y.gpr .r15) := by
  simp only [g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine RelCT.seq (RelCT.mono (slot_tr (by decide) s0) (fun x y h => RR.mono h
    (fun σ s h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) id) fun _ _ h => h) ?_
  refine RelCT.seq (slot_tr (by decide) s1) (RelCT.seq (slot_tr (by decide) s2) (RelCT.seq (slot_tr (by decide) s3) ?_))
  exact call4_tr hP cc

/-! ## The matrix -/

theorem cpR4_tr {p : Params} {D j : Nat} (hj : j < 4) (hc : cpChk p j = true) (hsk : 32 ≤ p.skLen) :
    RelCT isa (RR p D (fun σ s => ICopy p D σ j s) fun _ _ => True) (cpR4 j)
      (RR p D (fun σ s => ICopy p D σ (j + 1) s) fun _ _ => True) :=
  stepRR (F := fun _ _ => True) (fun σ s _ h => WP.mono (cpR4_ok hc hsk h) fun _ h => ⟨h, trivial⟩)
    (copy_tr (by decide) (by decide) (show oRS4 + 34 * j < 2 ^ 31 by simp only [oRS4]; omega_using [hj]) (by decide) (by decide)
      fun x y h => ⟨(h.lrel fun _ _ h => h.st).regs (.rbx, scrLen p) (by simp [sgR, sgW]),
        (h.lrel fun _ _ h => h.st).regs (.rbp, p.skLen) (by simp [sgR, sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) :
    RelCT isa (RR p D (fun σ s => St p D σ s ∧ s.gpr .r15 = 1) fun _ _ => True)
      (Impl.MlDsa.X86_64.Sign.expandA P p) (RA p D (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine RelCT.seq (R := RR p D (fun σ s => ICopy p D σ 0 s) fun _ _ => True) (stepRR (F := fun _ _ => True)
    (fun σ s _ h => WP.mono (copyRho_ok hcp hst hsk h.1) fun s1 ⟨S1, _, hb, e15⟩ =>
      ⟨⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h.2⟩, trivial⟩)
    (copy_tr (by decide) (by decide) (by decide) (by decide) (by decide) fun x y h =>
      ⟨(h.lrel fun _ _ h => h.1).regs (.rbx, scrLen p) (by simp [sgR, sgW]),
        (h.lrel fun _ _ h => h.1).regs (.rbp, p.skLen) (by simp [sgR, sgW])⟩)
    fun _ _ _ _ _ _ _ _ => trivial) ?_
  have hC := seqR_tr (f := cpR4) (R := fun j => RR p D (fun σ s => ICopy p D σ j s) fun _ _ => True) 4 0
    fun j _ hj => cpR4_tr (by omega_using [hj]) (hc4 j (by omega_using [hj])) hsk
  refine RelCT.seq (R := RR p D (fun σ s => ICopy p D σ 4 s) fun _ _ => True) hC ?_
  have hG := seqR_tr (f := sample4 P p)
    (R := fun g => RR p D (fun σ s => IA4 p D σ (4 * g) s) fun x y => x.gpr .r15 = y.gpr .r15) (p.k * p.ℓ / 4) 0
    fun g _ hg' => sample4_tr hP (hg g (by omega_using [hg']))
  rw [Nat.zero_add] at hG
  refine RelCT.seq (RelCT.mono hG (fun x y h => ?_) fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
    exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁.ia4, i₂.ia4⟩, i₁.r15.trans i₂.r15.symm⟩
  have hE := seqR_tr (f := sampleE P p) (R := fun k => RA p D k) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    fun k h1 hk => sampleE_tr hP (he k (by omega_using [hk]))
  rw [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega_using []] at hE
  exact RelCT.mono hE (fun x y h => RR.mono h (fun σ s h => h.ia) id) fun _ _ h => h

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: constant time

Two runs whose entry states agree on `signK`'s public data (`signLeak` among
them) leak the same: the prologue and the return only the pointers, `ExpandA`
only `ρ` (`expandA_tr`), and the rest what `signLeak` says after `ρ`, on
which they agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Rel2 relStart)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : (signK p D).pub σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2.1
  rw [signLeak_eq hA₁, signLeak_eq hA₂] at e
  have hρ : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 := pub_rho hpub
  rw [hρ] at e
  exact List.append_cancel_left e

theorem rr_rs {I E : State → State → Prop} {x y : State} (h : RR p D I E x y) : RS p D (fun _ _ => True) I x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, trivial, i₁, i₂⟩

theorem sign_ct {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) :
    ConstantTime isa (signK p D).pre (signK p D).pub (Impl.MlDsa.X86_64.Sign.sign P p) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsz⟩ := hf'
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.X86_64.Sign.sign
  refine RelCT.seq (RelCT.mono (relInvE (J := fun σ s => St p D σ s ∧ s.gpr .r15 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (pro_ok hp hsz.1) fun s₁ ⟨h₁, _, hf₁, h15⟩ => ⟨entry_st hP h3 hp h₁ hf₁, h15⟩)
    (block_tr (rs := [.r8]) rfl fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr h₁ h₂
      exact hpub.2.2.2.2.1)) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) ?_
    (VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine ifOkElse_tr (D := D) (P := RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (rest_tr hP h3)
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, ⟨hPx, _, _⟩, ⟨hPy, _, _⟩, hne⟩ => ?_)
    fun x y h => lrel_rbx (h.lrel fun _ _ h => h.st))
    (RelCT.mono nil_tr (fun _ _ h => h) fun x y h =>
      ifOk_rbx (I := fun σ s => IA p D σ (p.k * p.ℓ) s) (fun _ _ h => h.st) (E := fun _ _ => True)
        (C := fun x₀ => (x₀.gpr .r15).setWidth 32 = 0)
        (by obtain ⟨x₀, y₀, R, hx, hy, h0⟩ := h; exact ⟨x₀, y₀, rr_rs R, hx, hy, h0⟩))
  have e₁ := r15_one i₁.r01 hne
  have e₂ : y₀.gpr .r15 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, pub_leq hpub (expandA_max ok₁) (expandA_max ok₂),
    ⟨i₁.st.step hPx st0, ok₁, Fam.keep i₁.st.lay hPx fa0 fam₁⟩,
    ⟨i₂.st.step hPy st0, ok₂, Fam.keep i₂.st.lay hPy fa0 fam₂⟩⟩

end

end VG.Proof.MlDsa.X86_64.Sign
