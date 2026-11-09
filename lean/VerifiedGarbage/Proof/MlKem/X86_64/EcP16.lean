module

public import VerifiedGarbage.Proof.MlKem.X86_64.EcTop16
public import VerifiedGarbage.Proof.MlKem.X86_64.KgH16CT
public import VerifiedGarbage.Proof.MlKem.X86_64.Sel16
public import VerifiedGarbage.Impl.MlKem.X86_64.EncapsHP16
public import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Proof.MlKem.X86_64.Top16Ctl
public meta import VerifiedGarbage.Impl.MlKem.X86_64.EncapsHP16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFrag16
import VerifiedGarbage.Proof.MlKem.X86_64.KgCT

/-!
# ML-KEM-768 on x86-64: encapsulation with `H(ek)` given, `PRF₂` in the matrix's fragments

`kemEncapsHP16 K c p` (`Impl/MlKem/X86_64/EncapsHP16.lean`) is
`kemEncapsH16` but for K-PKE.Encrypt's matrix and noise
(`EncapsHP16.encrypt`): before the fragment of row `i` (`FP i`), `ρ` is at
`SB`, the first `3 i` entries of `Â` are sampled (`MatB16`), and the
polynomials `dnL i` of `y ‖ e₁ ‖ e₂`. The fragment copies `r` to the
samplers' working space, writes the seeds, and inlines `p (pf i) (pn i)`,
which meets `samplePNKW (pf i) (pn i)` (`BatchPOk16`): three entries of `Â`,
and `PRF₂(r, pf i + j)` for `j < pn i` at `PO + 128 j`, from which `cbdP i j`
samples polynomial `pf i + j` (`FM`). After the three rows, every entry and
every polynomial is sampled, and K-PKE.Encrypt's tail runs as for
`kemEncapsH16` (`Enc16.tail_okT`) if every `SampleNTT` succeeded:
`kemEncapsHP16_correct`. The layout's checks (`EcP16Wf`) are evaluated for
ML-KEM-768.

Constant time (`kemEncapsHP16_ct`): every piece but the fragments and the
branch on their results leaks only the pointers; the fragments sample from
the seeds of `ρ` (`sampleHAtP16_tr`), and the branch tests `r15`, which only
`ρ` decides. `r` flows only to fixed addresses.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace EncP16

open Encaps (ecR ecW ecB ecB_bases eckChk EcWfB ecC ecCA EC ECK ecEk ecMs ecG EIn.any)
open Enc (EIn inKeep rhoE)
open VG.Impl.MlKem.X86_64.Top16 (aP rP)
open VG.Impl.MlKem.X86_64.EncapsHP16 (pf pn cbdP frag)

variable (K : Kem16)

/-- `r` in the samplers' working space. -/
abbrev psP : Ptr := sc (K.oW + Sample4.oPS)
/-- Output `j` of `PRF₂` of the fragment. -/
abbrev poP (j : Nat) : Ptr := sc (K.oW + Sample4.oPO + 128 * j)

/-- The polynomials of `y ‖ e₁ ‖ e₂` the fragments before row `i ≤ 3` sampled:
1 to `3 i` before the last row, and all seven after it. -/
def dnL (i : Nat) : List Nat := if i < 3 then (List.range (3 * i)).map (· + 1) else List.range 7

/-- ... and the first `j` of row `i`. -/
def dl (i j : Nat) : List Nat := dnL i ++ (List.range j).map (pf i + ·)

/-! ## The checks of the layout -/

/-- A piece writing `ws` keeps the inputs, `ρ` at `SB`, the first `e` entries
of `Â` and the polynomials `ns` of `y ‖ e₁ ‖ e₂`. -/
def pkeep (ws : List (Ptr × Nat)) (e : Nat) (ns : List Nat) : Bool :=
  inKeep K.L (ecB K.L) (eckChk K.L) (.r14, 0) ws && keepB (ecB K.L) ws (sc oSB) 32 &&
    ((List.range e).all fun e' => keepB (ecB K.L) ws (aP K e') 512) &&
    ns.all fun N => keepB (ecB K.L) ws (rP K N) 512

/-- The copy of `r` of row `i`. -/
def psChk (i : Nat) : Bool :=
  copyChk (ecB K.L) (ecW K.L) (psP K) sigP 32 && pkeep K [(psP K, 32)] (3 * i) (dnL i)

/-- The seeds of row `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (ecB K.L) (ecW K.L) J && pkeep K (seedW J) (3 * i) (dnL i) &&
    keepB (ecB K.L) (seedW J) (psP K) 32

/-- The fragment of row `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (ecB K.L) (ecW K.L) (K.oA + 512 * (3 * i)) K.oW &&
    pkeep K [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)] (3 * i) (dnL i)

/-- Polynomial `pf i + j`, from output `j`. -/
def cbChk (i j : Nat) : Bool :=
  twoChk (ecB K.L) (ecW K.L) (poP K j) 128 (rP K (pf i + j)) 512 &&
    pkeep K [(rP K (pf i + j), 512)] (3 * i + 3) (dl i j) &&
    (List.range 3).all fun j' => keepB (ecB K.L) [(rP K (pf i + j), 512)] (poP K j') 128

/-- What the matrix and the noise need of the layout, evaluated for ML-KEM-768. -/
structure EcP16Wf : Prop extends Encaps16.Ec16Wf K where
  k3 : K.L.k = 3
  ps : ∀ i < 3, psChk K i = true
  sd : ∀ i < 3, sdChk K i = true
  sm : ∀ i < 3, smChk K i = true
  cb : ∀ i < 3, ∀ j < pn i, cbChk K i j = true
  fK : pkeep K [] 9 (dnL 3) = true
  rT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (sc oSB) (.r14, 0 + 384 * K.L.k) 32)
    h).isSome = true
  psT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (psP K) sigP 32)
    h).isSome = true

variable {K}

theorem pn_spec : ∀ i < 3, pn i ≤ 3 ∧ (pf i, pn i) ∈ Sample4.pnUses ∧ pf i + pn i ≤ 7 ∧
    (∀ N ∈ dnL (i + 1), N ∈ dl i (pn i)) ∧ ∀ j < pn i, pf i + j ∉ dl i j := by
  decide

theorem dl_succ (i j : Nat) : dl i (j + 1) = dl i j ++ [pf i + j] := by
  simp only [dl, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem dnL_three : ∀ N < 7, N ∈ dnL 3 := by decide

theorem seed_idx {i J : Nat} (hJ : J < 4) :
    (if J = 3 then i + 1 else i) = (3 * i + J) / 3 ∧ (if J = 3 then 0 else J) = (3 * i + J) % 3 := by
  rcases (by omega : J = 0 ∨ J = 1 ∨ J = 2 ∨ J = 3) with rfl | rfl | rfl | rfl <;> simp <;> omega

/-! ## Before each row -/

section
variable (W : EcWfB K.L) (σ : State)

/-- The inputs, from a run from `σ`. -/
abbrev EI (s : State) : Prop := EIn K.L (ecC W σ) (.r14, 0) (ecEk K.L σ) (ecMs σ) (ecG K.L σ).2 s

/-- `ρ` of the key. -/
abbrev ρE (K : Kem16) (σ : State) : List Byte := rhoE K.L (ecEk K.L σ)

/-- Before the fragment of row `i`. -/
structure FP (i : Nat) (s : State) : Prop where
  ei : EI W σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = ρE K σ
  mat : MatB16 K.L.k K.oA (ρE K σ) (3 * i) s
  rr : ∀ N ∈ dnL i, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (ecG K.L σ).2 N)

/-- After the copy of `r` and the first `J` seeds of row `i`. -/
structure FS (i J : Nat) (s : State) : Prop where
  fp : FP W σ i s
  ps : bytesAt s.mem (pa s (psP K)) 32 = (ecG K.L σ).2
  sd : SeedsIs (ρE K σ) K.L.k (3 * i) J s

/-- After the fragment of row `i` and the first `j` of its polynomials. -/
structure FM (i j : Nat) (s : State) : Prop where
  ei : EI W σ s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = ρE K σ
  mat : MatB16 K.L.k K.oA (ρE K σ) (3 * i + 3) s
  rr : ∀ N ∈ dl i j, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (ecG K.L σ).2 N)
  po : ∀ j' < pn i, bytesAt s.mem (pa s (poP K j')) 128 = prf 2 (ecG K.L σ).2 (BitVec.ofNat 8 (pf i + j'))

end

section
variable {W : EcWfB K.L} {σ : State}

theorem pkeep_spec {ws : List (Ptr × Nat)} {e : Nat} {ns : List Nat} (hc : pkeep K ws e ns = true) :
    inKeep K.L (ecB K.L) (eckChk K.L) (.r14, 0) ws = true ∧ keepB (ecB K.L) ws (sc oSB) 32 = true ∧
      (∀ e' < e, keepB (ecB K.L) ws (aP K e') 512 = true) ∧ ∀ N ∈ ns, keepB (ecB K.L) ws (rP K N) 512 = true := by
  simp only [pkeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

/-- A piece writing `ws` and keeping `r15` keeps `FP`. -/
theorem FP.keep {i : Nat} {s s' : State} (h : FP W σ i s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hc : pkeep K ws (3 * i) (dnL i) = true) : FP W σ i s' := by
  obtain ⟨hE, hS, hA, hR⟩ := pkeep_spec hc
  have L₀ := (ecC W σ).lay h.ei.out
  exact ⟨h.ei.keep hP hE, by rw [L₀.keepBytes hP hS]; exact h.sb,
    ⟨by rw [h15]; exact h.mat.r15, fun e he f hf => L₀.keepPoly16 hP (hA e he) (h.mat.mat e he f hf)⟩,
    fun N hN => L₀.keepPoly16 hP (hR N hN) (h.rr N hN)⟩

end

/-! ## A row -/

section
variable (V : EcP16Wf K) {σ : State}
include V

theorem ps_ok {i : Nat} (hi : i < 3) {s : State} (h : FP V.toEcWfB σ i s) :
    WP isa (copy (psP K) (sc (oG + 32)) 32) s (FS V.toEcWfB σ i 0) := by
  have hc := V.ps i hi
  simp only [psChk, Bool.and_eq_true] at hc
  have L₀ := (ecC V.toEcWfB σ).lay h.ei.out
  refine WP.mono (copy_okL L₀ (dst := psP K) (src := sigP) (n := 32) (by decide) hc.1) fun s' ⟨hP, hb⟩ => ?_
  have f := h.keep hP.b (hP.cs .r15 (by decide)) hc.2
  exact ⟨f, by rw [hP.pa rbx_cs, hb, h.ei.r], ⟨f.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem seedP_ok {i : Nat} (hi : i < 3) {J : Nat} (hJ : J < 4) {s : State} (h : FS V.toEcWfB σ i J s) :
    WP isa (seedAt J ((3 * i + J) / K.L.k) ((3 * i + J) % K.L.k)) s (FS V.toEcWfB σ i (J + 1)) := by
  have hsd := V.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  obtain ⟨⟨hs, hk⟩, hB⟩ := hsd J hJ
  have L₀ := (ecC V.toEcWfB σ).lay h.fp.ei.out
  refine WP.mono (seed_step L₀ (ecB_bases K.L) (by omega) hs h.sd) fun s' ⟨hP, hS⟩ =>
    ⟨h.fp.keep hP.b (hP.cs .r15 (by decide)) hk, ?_, hS⟩
  rw [L₀.keepBytes hP.b hB]; exact h.ps

/-- Seed `J` of row `i`, as `frag` writes it. -/
theorem seedP_ok' {i : Nat} (hi : i < 3) {J : Nat} (hJ : J < 4) {s : State} (h : FS V.toEcWfB σ i J s) :
    WP isa (seedAt J (if J = 3 then i + 1 else i) (if J = 3 then 0 else J)) s (FS V.toEcWfB σ i (J + 1)) := by
  have := seedP_ok V hi hJ h
  rw [V.k3] at this
  rcases (by omega : J = 0 ∨ J = 1 ∨ J = 2 ∨ J = 3) with rfl | rfl | rfl | rfl
  · rwa [show (3 * i + 0) / 3 = i by omega, show (3 * i + 0) % 3 = 0 by omega] at this
  · rwa [show (3 * i + 1) / 3 = i by omega, show (3 * i + 1) % 3 = 1 by omega] at this
  · rwa [show (3 * i + 2) / 3 = i by omega, show (3 * i + 2) % 3 = 2 by omega] at this
  · rwa [show (3 * i + 3) / 3 = i + 1 by omega, show (3 * i + 3) % 3 = 0 by omega] at this

theorem sampP_ok (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) {i : Nat}
    (hi : i < 3) {s : State} (h : FS V.toEcWfB σ i 4 s) :
    WP isa (Encaps.sampleHAt (p (pf i) (pn i)) (aP K (3 * i)) (sc K.oW)) s (FM V.toEcWfB σ i 0) := by
  obtain ⟨_, hU, _⟩ := pn_spec i hi
  have hsm := V.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  obtain ⟨hE, hS, hA, hR⟩ := pkeep_spec hsm.2
  have L₀ := (ecC V.toEcWfB σ).lay h.fp.ei.out
  refine WP.mono (sampleHAtP16_ok (v.batchP16 p hpb _ hU) (SHH16.of L₀ hsm.1)) fun s' h' => ?_
  refine ⟨h.fp.ei.keep h'.b hE, by rw [L₀.keepBytes h'.b hS]; exact h.fp.sb, ?_, fun N hN => ?_, fun j hj => ?_⟩
  · refine EkF16.MatB16.three (K := K) h.fp.mat L₀ h'.b hA ?_ fun t ht f hf => ?_
    · rw [h'.r15, all3_16, range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
        (seed4_eq h.sd (k := k) (by omega))]
    · have := h'.res t ht f (by rw [seed4_eq h.sd (by omega)]; exact hf)
      rwa [poly4W, pBytes_true, pa, off_add] at this
  · have hN' : N ∈ dnL i := by simpa [dl] using hN
    exact L₀.keepPoly16 h'.b (hR N hN') (h.fp.rr N hN')
  · have e := h'.pout j hj
    rw [KeyGenH.pa_off, KeyGenH.pa_off, h.ps] at e
    rw [h'.b.pa rbx_bases, poP, Nat.add_assoc]; exact e

theorem cbdP_ok {A : Arith} (hA : ArithOk A) {i : Nat} (hi : i < 3) {j : Nat} (hj : j < pn i) {s : State}
    (h : FM V.toEcWfB σ i j s) : WP isa (cbdP K A i j) s (FM V.toEcWfB σ i (j + 1)) := by
  obtain ⟨hp3, _⟩ := pn_spec i hi
  have hc := V.cb i hi j hj
  simp only [cbChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hcb, hk⟩, hkp⟩ := hc
  obtain ⟨hE, hS, hAk, hR⟩ := pkeep_spec hk
  have L₀ := (ecC V.toEcWfB σ).lay h.ei.out
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hcb) fun s' ⟨hP, hp'⟩ => ?_
  refine ⟨h.ei.keep hP.b hE, by rw [L₀.keepBytes hP.b hS]; exact h.sb,
    ⟨by rw [hP.cs .r15 (by decide)]; exact h.mat.r15, fun e he f hf => L₀.keepPoly16 hP.b (hAk e he) (h.mat.mat e he f hf)⟩,
    fun N hN => ?_, fun j' hj' => by rw [L₀.keepBytes hP.b (hkp j' (by omega))]; exact h.po j' hj'⟩
  rw [dl_succ, List.mem_append, List.mem_singleton] at hN
  rcases hN with hN' | rfl
  · exact L₀.keepPoly16 hP.b (hR N hN') (h.rr N hN')
  · rw [h.po j hj, ← hP.pa rbx_cs] at hp'; exact hp'

theorem fragP_ok (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) {i : Nat}
    (hi : i < 3) {s : State} (h : FP V.toEcWfB σ i s) :
    WP isa (frag K v.callee.arith p i) s (FP V.toEcWfB σ (i + 1)) := by
  obtain ⟨_, _, _, hnN', _⟩ := pn_spec i hi
  unfold frag
  refine WP.seq (WP.mono (ps_ok V hi h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seedP_ok' V hi (J := 0) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seedP_ok' V hi (J := 1) (by decide) h₂) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seedP_ok' V hi (J := 2) (by decide) h₂) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seedP_ok' V hi (J := 3) (by decide) h₂) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (sampP_ok V v hpb hi h₂) fun s₃ h₃ => ?_)
  refine WP.mono (seqR_ok (I := FM V.toEcWfB σ i) (pn i) 0
    (fun j _ hj s hs => cbdP_ok V v.arith hi (by omega) hs) s₃ h₃) fun s₄ h₄ => ?_
  rw [Nat.zero_add] at h₄
  exact ⟨h₄.ei, h₄.sb, by rw [show 3 * (i + 1) = 3 * i + 3 by omega]; exact h₄.mat,
    fun N hN => h₄.rr N (hnN' N hN)⟩

theorem rowsP_ok (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) {s : State}
    (h : FP V.toEcWfB σ 0 s) :
    WP isa (seqR (frag K v.callee.arith p) 0 K.L.k) s (FP V.toEcWfB σ 3) := by
  have := seqR_ok (I := FP V.toEcWfB σ) K.L.k 0 (fun i _ hi s hs => fragP_ok V v hpb (by rw [V.k3] at hi; omega) hs) s h
  rw [Nat.zero_add] at this
  exact WP.mono this fun _ h => by rwa [V.k3] at h

/-- `ρ` to `SB`, from the inputs. -/
theorem rho_ok {s : State} (h : Encaps.EncI V.toEcWfB σ s) :
    WP isa (copy (sc oSB) (.r14, 0 + 384 * K.L.k) 32) s (FP V.toEcWfB σ 0) := by
  have hc := V.enc.mat
  simp only [Enc.matChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have L₀ := (ecC V.toEcWfB σ).lay h.1.out
  refine WP.mono (copy_okL L₀ hc.1.2 hc.1.1) fun s' ⟨hP, hb⟩ => ?_
  exact ⟨h.1.keep hP.b hc.2, by rw [hP.pa rbx_cs, hb]; exact h.1.rho,
    MatB16.zero _ _ _ (by rw [hP.cs .r15 (by decide), h.2]), fun _ h => absurd h (by simp [dnL])⟩

/-- After the rows, the test of `r15`. -/
theorem FP.flag {s s' : State} (h : FP V.toEcWfB σ 3 s) (hP : PPost s s' []) : FP V.toEcWfB σ 3 s' := by
  exact h.keep hP.b (hP.cs .r15 (by decide)) V.fK

/-- K-PKE.Encrypt with the noise in the matrix's fragments, to `ct`. -/
theorem encryptP_ok (hK : KpkeOk K.L) (v : Sample4Impl) {p : Nat → Nat → Prog isa}
    (hpb : v.callee.batchP16 = some p) {s : State} (h : Encaps.EncI V.toEcWfB σ s) :
    WP isa (EncapsHP16.encrypt K v.callee p (.r14, 0) (.r13, 0)) s (Encaps16.EncO16 V.toEc16Wf σ) := by
  have e9 : 3 * 3 = K.L.k * K.L.k := by rw [V.k3]
  have e7 : ∀ N < 2 * K.L.k + 1, N ∈ dnL 3 := fun N hN => dnL_three N (by rw [V.k3] at hN; exact hN)
  unfold EncapsHP16.encrypt
  refine WP.seq (WP.mono (rho_ok V h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (rowsP_ok V v hpb h₁) fun s₂ h₂ => ?_)
  have m₂ : MatB16 K.L.k K.oA (ρE K σ) (K.L.k * K.L.k) s₂ := e9 ▸ h₂.mat
  refine ifOk_ok (fun s₃ hP hne => ?_) fun s₃ hP he => ?_
  · have h₃ := h₂.flag V hP
    have m₃ : MatB16 K.L.k K.oA (ρE K σ) (K.L.k * K.L.k) s₃ := e9 ▸ h₃.mat
    have ho := KeyGen.r15_ne m₂.r15 hne
    refine WP.mono (Enc16.tail_okT hK (C := ecC V.toEcWfB σ) (show Reg.r14 ∉ argRegs by decide) (by decide) V.tl
      (s := s₃) ⟨h₃.ei, by rw [m₃.r15, ifp ho], ho,
        fun e he => m₃.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he)),
        fun N hN => h₃.rr N (e7 N hN)⟩) fun _ ⟨_, hout, h15, hct⟩ =>
      ⟨hout, by rw [h15, ifp ho], fun _ => hct⟩
  · have h₃ := h₂.flag V hP
    have m₃ : MatB16 K.L.k K.oA (ρE K σ) (K.L.k * K.L.k) s₃ := e9 ▸ h₃.mat
    exact ⟨h₃.ei.out, m₃.r15, fun ho => absurd ho (KeyGen.r15_eq m₂.r15 he)⟩

end

/-! ## Constant time -/

section
variable (V : EcP16Wf K)
include V

open Encaps (R ec_lrel rho_pub trL) in
/-- Two runs from `I`, each keeping `EC`, are in the layout. -/
theorem lrelP {I : State → State → Prop} (hI : ∀ σ s, I σ s → (encapsK K.L).pre σ ∧ EC K.L σ s) :
    ∀ σ₁ σ₂ x y, (encapsK K.L).pre σ₁ → (encapsK K.L).pre σ₂ → (encapsK K.L).pub σ₁ σ₂ → I σ₁ x → I σ₂ y →
      LRel (ecR K.L) (ecW K.L) x y :=
  fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ec_lrel V.toEcWfB p₁ p₂ pub (hI _ _ h₁).2 (hI _ _ h₂).2

open Encaps (R rho_pub) in
theorem fragP_tr (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) {i : Nat}
    (hi : i < 3) : RelCT isa (R K.L (FP V.toEcWfB · i)) (frag K v.callee.arith p i) fun _ _ => True := by
  have Wb := V.toEcWfB
  obtain ⟨_, hU, _⟩ := pn_spec i hi
  have hB := v.batchP16 p hpb _ hU
  have hsd := V.sd i hi
  simp only [sdChk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hsd
  have hsm := V.sm i hi
  simp only [smChk, Bool.and_eq_true] at hsm
  have c4 := hsm.1
  have k3 := V.k3
  have eI : ∀ {Q : State → State → Prop}, (∀ σ s, Q σ s → EI V.toEcWfB σ s) →
      ∀ σ s, Q σ s → (encapsK K.L).pre σ ∧ EC K.L σ s := fun hQ σ s h => ⟨(hQ σ s h).out.1, (hQ σ s h).out.2.ec⟩
  unfold frag
  -- `r` to the samplers' working space.
  obtain ⟨_, psT⟩ := V.psT
  refine RelCT.seq (relInv (I' := fun σ s => FS V.toEcWfB σ i 0 s) (fun σ s _ h => ps_ok V hi h)
    (rel2_of (Encaps.trL Wb psT) (lrelP V (eI fun _ _ (h : FP V.toEcWfB _ i _) => h.ei)))) ?_
  -- The seeds.
  have st : ∀ J < 4, RelCT isa (R K.L (FS V.toEcWfB · i J))
      (seedAt J (if J = 3 then i + 1 else i) (if J = 3 then 0 else J)) (R K.L (FS V.toEcWfB · i (J + 1))) := by
    intro J hJ
    refine relInv (fun σ s _ h => seedP_ok' V hi hJ h) ?_
    rw [(seed_idx hJ).1, (seed_idx hJ).2, show (3 * i + J) / 3 = (3 * i + J) / K.L.k by rw [k3],
      show (3 * i + J) % 3 = (3 * i + J) % K.L.k by rw [k3]]
    refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => RQ (ecR K.L) (ecW K.L) ρ K.L.k (3 * i) J x y)
      (Q := fun _ _ => True) fun ρ => RelCT.mono (seed_tr (ecB_bases K.L) (ρ := ρ) (n := K.L.k) (e₀ := 3 * i)
        (K := J) (by omega) hJ (by rw [k3]; omega) (by rw [k3]; omega) (hsd J hJ).1.1) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ h => h
    · intro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
      refine ⟨ρE K σ₁, lrelP V (eI fun _ _ (h : FS V.toEcWfB _ i J _) => h.fp.ei) σ₁ σ₂ x y p₁ p₂ pub h₁ h₂, h₁.sd, ?_⟩
      have := h₂.sd
      rwa [ρE, ← rho_pub pub] at this
  have s0 := st 0 (by decide)
  rw [ifn (by decide), ifn (by decide)] at s0
  have s1 := st 1 (by decide)
  rw [ifn (by decide), ifn (by decide)] at s1
  have s2 := st 2 (by decide)
  rw [ifn (by decide), ifn (by decide)] at s2
  have s3 := st 3 (by decide)
  rw [ifp rfl, ifp rfl] at s3
  refine RelCT.seq s0 (RelCT.seq s1 (RelCT.seq s2 (RelCT.seq s3 ?_)))
  -- The fragment.
  refine RelCT.seq (relInv (I' := fun σ s => FM V.toEcWfB σ i 0 s) (fun σ s _ h => sampP_ok V v hpb hi h) ?_) ?_
  · refine RelCT.mono (sampleHAtP16_tr hB) (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
    have l := lrelP V (eI fun _ _ (h : FS V.toEcWfB _ i 4 _) => h.fp.ei) σ₁ σ₂ x y p₁ p₂ pub h₁ h₂
    have sd₂ := h₂.sd
    rw [ρE, ← rho_pub pub] at sd₂
    refine ⟨SHH16.of l.1 c4, SHH16.of l.2.1 c4, l.eq Wb.inBs.1, l.2.2.2, ?_⟩
    rw [bytesAt136, bytesAt136, seed4_eq h₁.sd (k := 0) (by decide), seed4_eq h₁.sd (k := 1) (by decide),
      seed4_eq h₁.sd (k := 2) (by decide), seed4_eq h₁.sd (k := 3) (by decide), seed4_eq sd₂ (k := 0) (by decide),
      seed4_eq sd₂ (k := 1) (by decide), seed4_eq sd₂ (k := 2) (by decide), seed4_eq sd₂ (k := 3) (by decide)]
  -- The polynomials of its outputs.
  · have := seqR_tr (f := cbdP K v.callee.arith i) (R := fun j => R K.L (FM V.toEcWfB · i j)) (pn i) 0
      fun j _ hj => by
        have hc := V.cb i hi j (by omega)
        simp only [cbChk, Bool.and_eq_true] at hc
        exact relInv (fun σ s _ h => cbdP_ok V v.arith hi (by omega) h)
          (rel2_of (cbd2_16At_trL v.arith rbx_na hc.1.1) (lrelP V (eI fun _ _ (h : FM V.toEcWfB _ i j _) => h.ei)))
    exact RelCT.mono this (fun _ _ h => h) fun _ _ _ => trivial

open Encaps (R) in
theorem rowsP_tr (v : Sample4Impl) {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) :
    RelCT isa (R K.L (FP V.toEcWfB · 0)) (seqR (frag K v.callee.arith p) 0 K.L.k) (R K.L (FP V.toEcWfB · 3)) := by
  have := seqR_tr (R := fun i => R K.L (FP V.toEcWfB · i)) K.L.k 0 fun i _ hi =>
    relInv (fun σ s _ h => fragP_ok V v hpb (by rw [V.k3] at hi; omega) h)
      (fragP_tr V v hpb (by rw [V.k3] at hi; omega))
  rw [Nat.zero_add] at this
  exact RelCT.mono this (fun _ _ h => h) fun _ _ h => by rwa [V.k3] at h

open Encaps (R ec_lrel rho_pub) in
theorem encryptP_tr (hK : KpkeOk K.L) (v : Sample4Impl) {p : Nat → Nat → Prog isa}
    (hpb : v.callee.batchP16 = some p) :
    RelCT isa (R K.L (Encaps.EncI V.toEcWfB)) (EncapsHP16.encrypt K v.callee p (.r14, 0) (.r13, 0)) fun _ _ => True := by
  have Wb := V.toEcWfB
  have e9 : 3 * 3 = K.L.k * K.L.k := by rw [V.k3]
  have e7 : ∀ N < 2 * K.L.k + 1, N ∈ dnL 3 := fun N hN => dnL_three N (by rw [V.k3] at hN; exact hN)
  unfold EncapsHP16.encrypt
  obtain ⟨_, rT⟩ := V.rT
  refine RelCT.seq (relInv (I' := fun σ s => FP V.toEcWfB σ 0 s) (fun σ s _ h => rho_ok V h)
    (rel2_of (Encaps.trL Wb rT) (lrelP V fun σ s (h : Encaps.EncI Wb σ s) => ⟨h.1.out.1, h.1.out.2.ec⟩))) ?_
  refine RelCT.seq (rowsP_tr V v hpb) ?_
  refine ifOk_tr (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      rw [h₁.mat.r15, h₂.mat.r15, ρE, ρE, rho_pub pub]) ?_ fun _ _ _ => trivial
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (ecR K.L) (ecW K.L) x y ∧
      Enc16.ERT16ρ K (ecCA Wb) (.r14, 0) ρ x ∧ Enc16.ERT16ρ K (ecCA Wb) (.r14, 0) ρ y)
    (Q := fun _ _ => True) fun ρ => RelCT.mono (Enc16.tail_trT hK (C := ecCA Wb) (show Reg.r14 ∉ argRegs by decide)
      (by decide) V.tl (ρ := ρ)) (fun _ _ h => h) fun _ _ _ => trivial) ?_ fun _ _ h => h
  rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩
  have m₁ : MatB16 K.L.k K.oA (ρE K σ₁) (K.L.k * K.L.k) x₀ := e9 ▸ h₁.mat
  have m₂ : MatB16 K.L.k K.oA (ρE K σ₂) (K.L.k * K.L.k) y₀ := e9 ▸ h₂.mat
  have o₁ := KeyGen.r15_ne m₁.r15 hne
  have o₂ : allOk K.L.k (ρE K σ₂) (K.L.k * K.L.k) := by rw [ρE, ← rho_pub pub]; exact o₁
  have k₁ := h₁.flag V hx
  have k₂ := h₂.flag V hy
  have n₁ : MatB16 K.L.k K.oA (ρE K σ₁) (K.L.k * K.L.k) x := e9 ▸ k₁.mat
  have n₂ : MatB16 K.L.k K.oA (ρE K σ₂) (K.L.k * K.L.k) y := e9 ▸ k₂.mat
  have l := (ec_lrel Wb p₁ p₂ pub h₁.ei.out.2.ec h₂.ei.out.2.ec).post (ecB_bases K.L) hx.b hy.b
  refine ⟨ρE K σ₁, l, ⟨_, _, _, rfl, ⟨EIn.any k₁.ei, by rw [n₁.r15, ifp o₁], o₁,
      fun e he => n₁.mat e he _ (aHat_eq o₁ (div_lt_k he) (mod_lt_k he)), fun N hN => k₁.rr N (e7 N hN)⟩⟩,
    ⟨_, _, _, (rho_pub pub).symm, ⟨EIn.any k₂.ei, by rw [n₂.r15, ifp o₂], o₂,
      fun e he => n₂.mat e he _ (aHat_eq o₂ (div_lt_k he) (mod_lt_k he)), fun N hN => k₂.rr N (e7 N hN)⟩⟩⟩

end

end EncP16

open Encaps Encaps16 in
theorem kemEncapsHP16_ct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (V : EncP16.EcP16Wf K)
    {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) :
    ConstantTime isa (encapsK K.L).pre (encapsK K.L).pub (kemEncapsHP16 K v.callee p) := by
  have W := V.toEc16Wf
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncapsHP16
  refine RelCT.seq (relInv (I' := ProOut K.L) (fun σ s hp hs => by subst hs; exact pro_ok W.toEcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => EC K.L σ s ∧ bytesAt s.mem (pa s (sc oH)) 32 = H (ecEk K.L σ) ∧
    s.gpr .r15 = 1) (fun σ s hp hs => hCopy_ok W.toEcWfB hp hs) hCopy_tr) ?_
  refine RelCT.seq (relInv (I' := EncI W.toEcWfB) (fun σ s hp hs => hashes_ok W.toEcWfB hp hs.1 hs.2.1 hs.2.2)
    (hashes_tr W.toEcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO16 W) (fun σ s _ hi => EncP16.encryptP_ok V hK v hpb hi)
    (EncP16.encryptP_tr V hK v hpb)) ?_
  refine RelCT.seq (relInv (I' := ECEnd K.L) (fun σ s _ hi => out_ok W hi) (out_tr W)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

open Encaps Encaps16 in
theorem kemEncapsHP16_correct {K : Kem16} (hK : KpkeOk K.L) (v : Sample4Impl) (V : EncP16.EcP16Wf K)
    {p : Nat → Nat → Prog isa} (hpb : v.callee.batchP16 = some p) (hctl : ctlOk (kemEncapsHP16 K v.callee p) = true)
    (σ : State) (hp : (encapsK K.L).pre σ) :
    ∃ t s', Exec isa (kemEncapsHP16 K v.callee p) σ t s' ∧ abiPreserved σ s' ∧ (encapsK K.L).post σ s' := by
  have W := V.toEc16Wf
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toEcWfB hp) fun s₁ h₁ =>
    WP.seq (WP.mono (hCopy_ok W.toEcWfB hp h₁) fun s₂ ⟨h₂, hH, h15⟩ =>
      WP.seq (WP.mono (hashes_ok W.toEcWfB hp h₂ hH h15) fun s₃ h₃ =>
        WP.seq (WP.mono (EncP16.encryptP_ok V hK v hpb h₃) fun s₄ h₄ =>
          WP.seq (WP.mono (out_ok W h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.ec.top (h₅.hin W.toEcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toEcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (encapsK K.L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Each implementation -/

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v` or `p`, or a part that calls
the K-PKE functions: the kernel evaluates only the parts that call neither
the fragments nor those functions. -/
elab "closedP_in " v:ident p:ident : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  for x in [v, p] do
    let e ← elabTerm x none
    if g.containsFVar e.fvarId! then throwError "the goal mentions {e}"
  let calls := [``Impl.MlKem.X86_64.kemEncapsHP16, ``Impl.MlKem.X86_64.EncapsHP16.encrypt,
    ``Impl.MlKem.X86_64.Kem.kpkeEncAt, ``Impl.MlKem.X86_64.kpkeEnc]
  if (g.find? fun e => e.isConst && calls.contains e.constName!).isSome then
    throwError "the goal calls the K-PKE functions"

/-- `ctlOk` of the encapsulation computing `PRF₂` in the fragments `p`
(`P`) of the implementation `v`, calling the K-PKE functions (`hK`). -/
tactic_template "ecp_ctl " v:ident p:ident P:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($P (_, _) (by decide)).ctl | with_reducible exact ($hK).enc.ctl
    | (closedP_in $v $p; decide +kernel) | (code_whnf; closedP_in $v $p; decide +kernel)
    | with_reducible exact ($v).arith.cbd16.ctl
    | (code_whnf; with_reducible apply ctlOk_seq) | (code_whnf; with_reducible apply ctlOk_ite)
    | (code_whnf; with_reducible apply ctlOk_call)))

/-- That the encapsulation computing `PRF₂` in the fragments never writes the stack pointer. -/
tactic_template "ecp_sp " v:ident p:ident P:ident hK:ident : tactic =>
  `(tactic| repeat' (first
    | with_reducible exact ($P (_, _) (by decide)).sp | with_reducible exact ($hK).enc.sp
    | (closedP_in $v $p; exact Code.all_of_allInstrs (by decide +kernel))
    | (code_whnf; closedP_in $v $p; exact Code.all_of_allInstrs (by decide +kernel))
    | with_reducible exact ($v).arith.cbd16.sp
    | (code_whnf; with_reducible apply all_seq) | (code_whnf; with_reducible apply all_ite)
    | (code_whnf; with_reducible apply all_call)))

theorem encapsHPSel_verified (hK : KpkeOk kem768w.L) (v : Sample4Impl) (V : EncP16.EcP16Wf kem768w)
    (W16 : Encaps16.Ec16Wf (narrowK kem768w kem768w.L.scr)) (W : Encaps.EcWf kem768w.L) {wc wd : List Nat}
    (C : KemCalls kem768w.L wc wd) {k : Contract isa} (hk : (encapsK kem768w.L).Implies k)
    (hctlP : ∀ p : Nat → Nat → Prog isa, (∀ q ∈ Sample4.pnUses, BatchPOk16 q.1 q.2 (p q.1 q.2)) →
      ctlOk (kemEncapsHP16 kem768w v.callee p) = true)
    (hctl16 : ∀ n c, S16Ok c → ctlOk (kemEncapsH16 kem768w v.callee (n, c)) = true)
    (hctl : ctlOk (kemEncapsH kem768w.L v.callee) = true) :
    Verified X86_64.target (kemEncapsHPSel v.callee) k := by
  unfold kemEncapsHPSel
  match hs : v.callee.s16, hpb : v.callee.batchP16 with
  | some _, some p =>
    exact Verified.of_correct (kemEncapsHP16_correct hK v V hpb (hctlP p (v.batchP16 p hpb)))
      (kemEncapsHP16_ct hK v V hpb) hk
  | none, _ => exact encapsHSel_verified (n := kem768w.L.scr) (Nat.le_refl _) hK v W16 W C hk hctl16 hctl
  | some _, none => exact encapsHSel_verified (n := kem768w.L.scr) (Nat.le_refl _) hK v W16 W C hk hctl16 hctl

/-- No instruction of `kemEncapsHPSel c` writes the stack pointer, if none of
the functions it may run does. -/
theorem encapsHPSel_sp (v : Sample4Impl) {q : Instr → Bool}
    (hP : ∀ p : Nat → Nat → Prog isa, (∀ q ∈ Sample4.pnUses, BatchPOk16 q.1 q.2 (p q.1 q.2)) →
      (kemEncapsHP16 kem768w v.callee p).all q = true)
    (h : (kemEncapsHSel kem768w v.callee).all q = true) : (kemEncapsHPSel v.callee).all q = true := by
  unfold kemEncapsHPSel
  match hs : v.callee.s16, hpb : v.callee.batchP16 with
  | some _, some p => exact hP p (v.batchP16 p hpb)
  | none, _ => exact h
  | some _, none => exact h

end VG.Proof.MlKem.X86_64
