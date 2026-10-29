module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKgRows
import VerifiedGarbage.Proof.MlKem.X86_64.Kg16
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4_16
public import VerifiedGarbage.Proof.MlKem.X86_64.KgA16
public import VerifiedGarbage.Proof.MlKem.X86_64.KgB
public import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
public import VerifiedGarbage.Proof.MlKem.HSponge
public import VerifiedGarbage.Impl.MlKem.X86_64.KeyGenH16
import VerifiedGarbage.Proof.MlKem.X86_64.EkFused16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop

/-!
# ML-KEM-768 on x86-64: key generation hashing `ek` while it samples `Â`, before the rows

`kemKeyGenH16` (`KeyGenH16.lean`) up to its rows: what it needs of the layout
(`KgH16Wf`, evaluated for each parameter set), what holds while it samples
the noise (`KN`) and from the noise's transforms on (`KH`), and the pieces:
the outputs of `PRF₂` and `s ‖ e` (`noise_ok`), `vg_mlkem768_kpke_keygen_ntt`
(`ntt_ok`) and the sponge's state zeroed (`hz_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

namespace KeyGenH

open KeyGen KeyGen16 VG.Impl.MlKem.X86_64.Top16 VG.Impl.MlKem.X86_64.KeyGenH16

variable (K : Kem16)

/-! ## The regions -/

/-- `ŝ[j]` and `ê[j]` (`u32`s), row `j` of `ek`, and the sponge's state and blocks. -/
abbrev shP (j : Nat) : Ptr := sc (oSH + 1024 * j)
abbrev ehP (j : Nat) : Ptr := sc (oEH + 1024 * j)
abbrev ekP (j : Nat) : Ptr := (.r12, 384 * j)
abbrev hsP : Ptr := sc (Encaps16.oHS K)
abbrev hbP : Ptr := sc (Encaps16.oHB K)

/-- `ρ` (twice) and `σ`. -/
abbrev baseR : List (Ptr × Nat) := [(sc oG, 32), (sigP, 32), (sc oSB, 32)]
abbrev shR : List (Ptr × Nat) := (List.range 3).map fun j => (shP j, 1024)
/-- `ê[j]` for `i ≤ j < 3`. -/
abbrev ehR (i : Nat) : List (Ptr × Nat) := (List.range (3 - i)).map fun j => (ehP (i + j), 1024)
abbrev dkR : List (Ptr × Nat) := [((.r13, 0), 1152)]
abbrev ekR (i : Nat) : List (Ptr × Nat) := (List.range i).map fun j => (ekP j, 384)
abbrev aR (e : Nat) : List (Ptr × Nat) := (List.range e).map fun e' => (aP K e', 512)
abbrev prR : List (Ptr × Nat) := (List.range 6).map fun N => (prfO K N, 128)
abbrev rR (n : Nat) : List (Ptr × Nat) := (List.range n).map fun N => (rP K N, 512)
/-- The polynomials of `s ‖ e` but `N`. -/
abbrev rRx (N : Nat) : List (Ptr × Nat) := ((List.range 6).filter (· ≠ N)).map fun N' => (rP K N', 512)
/-- `σ`, copied for the fragment of row 0, and its outputs of `PRF₂`. -/
abbrev psP : Ptr := sc (K.oW + Sample4.oPS)
abbrev poP (N : Nat) : Ptr := sc (K.oW + Sample4.oPO + 128 * N)
abbrev poR : List (Ptr × Nat) := (List.range 2).map fun N => (poP K N, 128)

/-- What the matrix's fragments and rows keep: `ê[j]` from `ie` on, the
first `ik` rows of `ek` and the first `e` entries of `Â`. -/
abbrev liveG (ie ik e : Nat) : List (Ptr × Nat) := baseR ++ shR ++ ehR ie ++ dkR ++ ekR ik ++ aR K e
abbrev liveR (i e : Nat) : List (Ptr × Nat) := liveG K i i e

/-- A piece writing `ws` keeps `KC` and every region of `rs`. -/
def keepAll (ws rs : List (Ptr × Nat)) : Bool :=
  kcChk K.L ws && rs.all fun r => keepB (kgB K.L) ws r.1 r.2

/-- What `vg_mlkem768_kpke_keygen_ntt` and `vg_mlkem768_kpke_keygen_row` write. -/
abbrev ntW : List (Ptr × Nat) := [((.r13, 0), 384 * 3), (sc oSH, 1024 * 3), (sc oEH, 1024 * 3), (sc oZK, 4096)]
abbrev rowW (i : Nat) : List (Ptr × Nat) := [(ekP i, 384), (ehP i, 1024), (sc oZK, 4096)]
abbrev smW (i : Nat) : List (Ptr × Nat) := [(sc (K.oA + 512 * (3 * i)), 2048), (sc K.oW, 8192)]

/-- The blocks of `ek` the fragment of row `i` copies. -/
def cpChk (i : Nat) : Bool :=
  (hm i).1 == 0 || (copyChk (kgB K.L) (kgW K.L) (hbP K) (.r12, 136 * (hm i).2) (136 * (hm i).1) &&
    keepAll K [(hbP K, 136 * (hm i).1)] (liveR K i (3 * i) ++ [(hsP K, 200)]))

/-- The seeds of the fragment of row `i`. -/
def sdChk (i : Nat) : Bool :=
  (List.range 4).all fun J => seedsChk (kgB K.L) (kgW K.L) J &&
    keepAll K (seedW J) (liveR K i (3 * i) ++ [(hsP K, 200), (hbP K, 136 * (hm i).1)])

/-- The sampling of the fragment of row `i`. -/
def smChk (i : Nat) : Bool :=
  s4_16Chk (kgB K.L) (kgW K.L) (K.oA + 512 * (3 * i)) K.oW && keepAll K (smW K i) (liveR K i (3 * i))

/-- Row `i` of `t̂`. -/
def rwChk (i : Nat) : Bool :=
  krChk (kgB K.L) (kgW K.L) 3 (ekP i) (aP K (3 * i)) (sc oSH) (ehP i) (sc oZK) &&
    keepAll K (rowW i) (liveG K (i + 1) i (3 * i + 3) ++ [(hsP K, 200)])

/-- What key generation hashing `ek` in the matrix's fragments needs of the
layout, evaluated for each parameter set. -/
structure KgH16Wf : Prop extends KgWfB K.L where
  k3 : K.L.k = 3
  ek : K.L.ekLen = 1184
  -- the noise but `PRF₂(σ, 0)` and `PRF₂(σ, 1)`
  pr : (prfsChk (kgB K.L) (kgW K.L) 4 (K.oPR + 256) (K.oW / 32) &&
    keepAll K (prfsW 4 (K.oPR + 256) (K.oW / 32)) baseR) = true
  se : ∀ N < 6, (twoChk (kgB K.L) (kgW K.L) (prfO K N) 128 (rP K N) 512 &&
    keepAll K [(rP K N, 512)] (baseR ++ prR K ++ rR K N)) = true
  -- row 0 of `Â` with `PRF₂(σ, 0)` and `PRF₂(σ, 1)`
  c0 : (copyChk (kgB K.L) (kgW K.L) (psP K) sigP 32 && keepAll K [(psP K, 32)] (baseR ++ rR K 6)) = true
  sd0 : ((List.range 4).all fun J => seedsChk (kgB K.L) (kgW K.L) J &&
    keepAll K (seedW J) (baseR ++ rR K 6 ++ [(psP K, 32)])) = true
  sm0 : (s4_16Chk (kgB K.L) (kgW K.L) K.oA K.oW && keepAll K (smW K 0) (baseR ++ rR K 6)) = true
  hz : (inB (kgW K.L) (hsP K) 200 && keepAll K [(hsP K, 200)] (baseR ++ rR K 6 ++ aR K 3 ++ poR K)) = true
  cP : ∀ N < 2, (twoChk (kgB K.L) (kgW K.L) (poP K N) 128 (rP K N) 512 &&
    keepAll K [(rP K N, 512)] (baseR ++ rRx K N ++ aR K 3 ++ poR K ++ [(hsP K, 200)])) = true
  -- the transforms
  nt : (knChk (kgB K.L) (kgW K.L) 3 (.r13, 0) (sc oSH) (sc oEH) (sc K.oR) (sc oZK) &&
    keepAll K ntW (baseR ++ aR K 3 ++ [(hsP K, 200)])) = true
  -- the rows
  cp : ∀ i < 3, cpChk K i = true
  sd : ∀ i < 3, sdChk K i = true
  sm : ∀ i < 3, smChk K i = true
  rw : ∀ i < 3, rwChk K i = true
  flg : ∀ i < 3, (keepAll K [] (liveR K i (3 * i + 3)) && keepB (kgB K.L) [] (hsP K) 200) = true
  -- the tail: the sponge's state kept by the copies of `ρ` and `ek`, copied to
  -- the sponge functions' state, and the rest of `ek` absorbed
  tS : (keepB (kgB K.L) (finW₁ K.L) (hsP K) 200 && keepB (kgB K.L) (finW₂ K.L) (hsP K) 200) = true
  tC : (copyChk (kgB K.L) (kgW K.L) (sc 0) (hsP K) 200 &&
    keepAll K [(sc 0, 200)] [((.r12, 0), 1184), ((.r13, 0), 1152), ((.r13, 1152), 1184)]) = true
  tH : hashChk (kgB K.L) (kgW K.L) [((.r12, 680), 504)] 136 (.r13, 384 * K.L.k + K.L.ekLen) 32 = true

variable {K}

theorem keepAll_spec {ws rs : List (Ptr × Nat)} (h : keepAll K ws rs = true) :
    kcChk K.L ws = true ∧ ∀ r ∈ rs, keepB (kgB K.L) ws r.1 r.2 = true := by
  simp only [keepAll, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem pa_off (s : State) (o d : Nat) : pa s (sc o) + BitVec.ofNat 64 d = pa s (sc (o + d)) := by
  simp only [pa]; rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## While the noise is sampled -/

/-- After `G(d ‖ k)`, the outputs of `PRF₂` from `PRF₂(σ, 2)` on, and the
polynomials of `s ‖ e` from 2 to `n`. -/
structure KN (K : Kem16) (n : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  r15 : s.gpr .r15 = 1
  prf : ∀ N < 6, 2 ≤ N → bytesAt s.mem (pa s (prfO K N)) 128 = prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ N < n, 2 ≤ N → PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

/-! ## From the transforms on -/

/-- Row `j` of `t̂`, encoded. -/
abbrev tRow (L : Kem) (σ : State) (j : Nat) : List Byte := encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) j)

/-- The blocks of `pad(ek)` the sponge has absorbed before the fragment of row `i`. -/
def hAbs : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | _ => 5

/-- Before row `i` of `t̂`, with the first `e` entries of `Â` sampled. -/
structure KH (K : Kem16) (σ : State) (i e : Nat) (s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  sh : ∀ j < 3, PolyIs s.mem (pa s (shP j)) (KPke.kgS K.L.p (kgD σ) j)
  eh : ∀ j < 3, i ≤ j → PolyIs s.mem (pa s (ehP j)) (KPke.kgE K.L.p (kgD σ) j)
  dk : bytesAt s.mem (pa s (.r13, 0)) 1152 = KPke.dkPKE K.L.p (kgD σ)
  mat : MatB16 K.L.k K.oA (rhoK K.L σ) e s
  ok : allOk K.L.k (rhoK K.L σ) e → (∀ j < i, bytesAt s.mem (pa s (ekP j)) 384 = tRow K.L σ j) ∧
    stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) (hAbs (e / 3))

/-- What holds of the regions besides `Â`, `ek` and the sponge, from `ê[i]` on. -/
structure KS (K : Kem16) (σ : State) (i : Nat) (s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoK K.L σ
  sh : ∀ j < 3, PolyIs s.mem (pa s (shP j)) (KPke.kgS K.L.p (kgD σ) j)
  eh : ∀ j < 3, i ≤ j → PolyIs s.mem (pa s (ehP j)) (KPke.kgE K.L.p (kgD σ) j)
  dk : bytesAt s.mem (pa s (.r13, 0)) 1152 = KPke.dkPKE K.L.p (kgD σ)

theorem KH.ks {i e : Nat} {σ s : State} (h : KH K σ i e s) : KS K σ i s := ⟨h.kc, h.rho, h.sb, h.sh, h.eh, h.dk⟩

theorem KH.of {i e : Nat} {σ s : State} (h : KS K σ i s) (hm : MatB16 K.L.k K.oA (rhoK K.L σ) e s)
    (ho : allOk K.L.k (rhoK K.L σ) e → (∀ j < i, bytesAt s.mem (pa s (ekP j)) 384 = tRow K.L σ j) ∧
      stateAt s.mem (pa s (hsP K)) = HSponge.hstate (ekK K.L σ) (hAbs (e / 3))) : KH K σ i e s :=
  ⟨h.kc, h.rho, h.sb, h.sh, h.eh, h.dk, hm, ho⟩

/-- `ρ`, `ŝ`, `ê` from `ie` on, and `dk_PKE`. -/
abbrev statR (ie : Nat) : List (Ptr × Nat) := baseR ++ shR ++ ehR ie ++ dkR

section
variable (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- A piece that writes `ws`, keeps the regions of `rs` and `r15`, keeps
the facts about them. -/
theorem KH.keepG {i i' e : Nat} (hi : i ≤ i') {s s' : State} (h : KH K σ i e s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (h15 : s'.gpr .r15 = s.gpr .r15) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ liveG K i' i e, keepB (kgB K.L) ws r.1 r.2 = true)
    (hrow : allOk K.L.k (rhoK K.L σ) e → ∀ j, i ≤ j → j < i' → bytesAt s'.mem (pa s' (ekP j)) 384 = tRow K.L σ j)
    (hhs : allOk K.L.k (rhoK K.L σ) e → keepB (kgB K.L) ws (hsP K) 200 = true) : KH K σ i' e s' := by
  have L₀ := h.kc.lay W.toKgWfB hp
  have m : ∀ r, r ∈ liveG K i' i e → keepB (kgB K.L) ws r.1 r.2 = true := hk
  have mB : ∀ r ∈ baseR, r ∈ liveG K i' i e := fun r h =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ h))))
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, fun j hj => ?_, fun j hj hij => ?_, ?_,
    ⟨by rw [h15]; exact h.mat.r15, fun e' he' f hf => L₀.keepPoly16 hP
      (m _ (List.mem_append_right _ (List.mem_map.2 ⟨e', List.mem_range.2 he', rfl⟩))) (h.mat.mat e' he' f hf)⟩,
    fun ho => ⟨fun j hj => ?_, ?_⟩⟩
  · rw [L₀.keepBytes hP (m (sc oG, 32) (mB _ (by simp)))]; exact h.rho
  · rw [L₀.keepBytes hP (m (sc oSB, 32) (mB _ (by simp)))]; exact h.sb
  · exact L₀.keepPoly hP (m _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))))))
      (h.sh j hj)
  · have hm : (ehP j, 1024) ∈ liveG K i' i e := List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨j - i', List.mem_range.2 (by omega),
        by rw [Nat.add_sub_cancel' hij]⟩))))
    exact L₀.keepPoly hP (m _ hm) (h.eh j hj (by omega))
  · rw [L₀.keepBytes hP (m _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton_self _)))))]; exact h.dk
  · by_cases hji : j < i
    · rw [L₀.keepBytes hP (m _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨j, List.mem_range.2 hji, rfl⟩))))]; exact (h.ok ho).1 j hji
    · exact hrow ho j (by omega) hj
  · rw [EkF.stateAt_keep L₀ hP (hhs ho)]; exact (h.ok ho).2

theorem KS.keep {i i' : Nat} (hi : i ≤ i') {s s' : State} (h : KS K σ i s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ statR i', keepB (kgB K.L) ws r.1 r.2 = true) : KS K σ i' s' := by
  have L₀ := h.kc.lay W.toKgWfB hp
  refine ⟨h.kc.step W.toKgWfB hp hP hkc, ?_, ?_, fun j hj => ?_, fun j hj hij => ?_, ?_⟩
  · rw [L₀.keepBytes hP (hk (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP (hk (sc oSB, 32) (by simp))]; exact h.sb
  · exact L₀.keepPoly hP (hk _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))))) (h.sh j hj)
  · exact L₀.keepPoly hP (hk (ehP j, 1024) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨j - i', List.mem_range.2 (by omega), by rw [Nat.add_sub_cancel' hij]⟩)))) (h.eh j hj (by omega))
  · rw [L₀.keepBytes hP (hk _ (List.mem_append_right _ (List.mem_singleton_self _)))]; exact h.dk

theorem KH.keep {i e : Nat} {s s' : State} (h : KH K σ i e s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hkc : kcChk K.L ws = true)
    (hk : ∀ r ∈ liveR K i e, keepB (kgB K.L) ws r.1 r.2 = true)
    (hhs : allOk K.L.k (rhoK K.L σ) e → keepB (kgB K.L) ws (hsP K) 200 = true) : KH K σ i e s' :=
  h.keepG W hp (Nat.le_refl _) hP h15 hkc hk (fun _ _ h₁ h₂ => absurd h₂ (by omega)) hhs

end

section
variable (W : KgH16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

/-- The outputs of `PRF₂` from `PRF₂(σ, 2)` on. -/
theorem prfs_ok (v : Sample4Impl) {s : State} (h : KA K.L σ s) (h15 : s.gpr .r15 = 1) :
    WP isa (v.callee.prfs 2 4 (K.oPR + 256) (K.oW / 32)) s (KN K 2 σ) := by
  have hc := W.pr
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases K.L) (by omega) hc.1) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b (hr (sigP, 32) (.tail _ (.head _)))
  refine ⟨h.kc.step W.toKgWfB hp hP.b hkc, by rw [L₀.keepBytes hP.b (hr (sc oG, 32) (by simp))]; exact h.rho,
    hσ.trans h.sig, by rw [L₀.keepBytes hP.b (hr (sc oSB, 32) (by simp))]; exact h.sb,
    by rw [hP.cs .r15 (by decide)]; exact h15, fun N hN h2 => ?_, fun _ h h2 => absurd h (by omega)⟩
  have := hb (N - 2) (by omega)
  rw [show K.oPR + 256 + 128 * (N - 2) = K.oPR + 128 * N by omega, show 2 + (N - 2) = N by omega] at this
  rw [Top16.prfO, hP.pa rbx_cs, this, h.sig]

/-- `s ‖ e`, polynomial `N`. -/
theorem se_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 6) (h2 : 2 ≤ N) {s : State} (h : KN K N σ s) :
    WP isa (cbdN K A N) s (KN K (N + 1) σ) := by
  have hc := W.se N hN
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hkc, hr⟩ := keepAll_spec hc.2
  have L₀ := h.kc.lay W.toKgWfB hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.prf N hN h2, ← hP₁.pa rbx_cs] at hp₁
  have k : ∀ r ∈ baseR ++ prR K ++ rR K N, keepB (kgB K.L) [(rP K N, 512)] r.1 r.2 = true := hr
  refine ⟨h.kc.step W.toKgWfB hp hP₁.b hkc, ?_, ?_, ?_, by rw [hP₁.cs .r15 (by decide)]; exact h.r15,
    fun N' hN' h2' => ?_, fun N' hN' h2' => ?_⟩
  · rw [L₀.keepBytes hP₁.b (k (sc oG, 32) (by simp))]; exact h.rho
  · rw [L₀.keepBytes hP₁.b (k (sigP, 32) (List.mem_append_left _ (List.mem_append_left _ (.tail _ (.head _)))))]; exact h.sig
  · rw [L₀.keepBytes hP₁.b (k (sc oSB, 32) (by simp))]; exact h.sb
  · rw [L₀.keepBytes hP₁.b (k (prfO K N', 128) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))))]; exact h.prf N' hN' h2'
  · rcases (by omega : N' < N ∨ N' = N) with hN' | rfl
    · exact L₀.keepPoly16 hP₁.b (k (rP K N', 512) (List.mem_append_right _
        (List.mem_map.2 ⟨N', List.mem_range.2 hN', rfl⟩))) (h.se N' hN' h2')
    · exact hp₁

/-- The noise but `PRF₂(σ, 0)` and `PRF₂(σ, 1)`: the outputs of `PRF₂` and
`s ‖ e` from 2 on. -/
theorem noise_ok (v : Sample4Impl) {s : State} (h : KA K.L σ s) (h15 : s.gpr .r15 = 1) :
    WP isa (.seq (v.callee.prfs 2 4 (K.oPR + 256) (K.oW / 32)) (seqR (cbdN K v.callee.arith) 2 4)) s (KN K 6 σ) :=
  WP.seq (WP.mono (prfs_ok W hp v h h15) fun s₀ h₀ =>
    seqR_ok (I := fun k => KN K k σ) 4 2 (fun k hk hk' s hs => se_ok W hp v.arith (by omega) hk hs) s₀ h₀)

end

theorem vecIs_get {m : Mem} {p : Addr} {f : Nat → Poly} (h : VecIs m p 3 ((List.range 3).map f)) {j : Nat}
    (hj : j < 3) : PolyIs m (p + BitVec.ofNat 64 (1024 * j)) (f j) := by
  have := h.2 j hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this

end KeyGenH

end VG.Proof.MlKem.X86_64
