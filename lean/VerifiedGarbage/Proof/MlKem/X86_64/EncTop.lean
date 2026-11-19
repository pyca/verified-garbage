module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncBase

/-! ### `MlKem.X86_64.KgTop`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.KgCT`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.KgB`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: key generation, the keys

When every entry of `Â` was sampled (`allOk`): `s` and `e` (`se_ok`; `KRest
n`: the first `n` of `s ‖ e` are done), `ŝ` and `t̂` (`kgm_ok`, by
`vg_mlkem*_keygen_mul`), `t̂` encoded to `ek` (`encT_ok`), `ŝ` encoded to `dk`
(`encS_ok`), and `ρ`, `ek`, `H(ek)` and `z` to the keys (`fin_ok`). After
`vg_mlkem*_keygen_mul`, `KRestT r e`: `r` rows of `ek` and `e` of `dk` are
done.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem bytesAt_split (m : Mem) (s : State) (r : Reg) (o a b : Nat) :
    bytesAt m (pa s (r, o)) (a + b) = bytesAt m (pa s (r, o)) a ++ bytesAt m (pa s (r, o + a)) b := by
  rw [bytesAt_add, pa, pa, off_add]

/-- `k` consecutive pieces of `c` bytes. -/
theorem bytesAt_catK (m : Mem) (s : State) (r : Reg) (o c : Nat) (f : Nat → List Byte) :
    ∀ k, (∀ i < k, bytesAt m (pa s (r, o + c * i)) c = f i) → bytesAt m (pa s (r, o)) (c * k) = KPke.catK f k
  | 0, _ => rfl
  | k + 1, h => by
    rw [KPke.catK, KPke.foldK_succ List.nil_append, ← KPke.catK, Nat.mul_succ, bytesAt_split,
      bytesAt_catK m s r o c f k fun i hi => h i (by omega_using [hi]), h k (by omega_using [])]

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `ρ` of `σ`. -/
abbrev rhoK (L : Kem) (σ : State) : List Byte := KPke.kgRho L.p (kgD σ)

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KRest0 (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoK L σ) (e / L.k) (e % L.k))

/-- The steps done after the outputs of `PRF₂`. -/
structure KRest (L : Kem) (n r e : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoK L σ) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k, bytesAt s.mem (pa s (prfO L N)) 128 = prf 2 (KPke.kgSigma L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ k < n, PolyIs s.mem (pa s (pS k)) (cbd (KPke.kgSigma L.p (kgD σ)) k)
  ek : ∀ i < r, bytesAt s.mem (pa s (.r12, 384 * i)) 384 = encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i)
  dk : ∀ j < e, bytesAt s.mem (pa s (.r13, 384 * j)) 384 = encode12 (KPke.kgS L.p (kgD σ) j)

theorem KRest.keep {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {n r e : Nat} {s s' : State}
    (h : KRest L n r e σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : restChk L n r e ws = true) :
    KRest L n r e σ s' := by
  simp only [restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩, kE⟩, kD⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, by rw [L₀.keepBytes hP.b kS]; exact h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kP k hk) (h.se k hk),
    fun i hi => by rw [L₀.keepBytes hP.b (kE i hi)]; exact h.ek i hi,
    fun j hj => by rw [L₀.keepBytes hP.b (kD j hj)]; exact h.dk j hj⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
theorem KRest0.start {L : Kem} {σ : State} {s : State} (h : KB L (L.k * L.k) σ s) (ho : allOk L.k (rhoK L σ) (L.k * L.k)) :
    KRest0 L σ s :=
  ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.m.r15, ifp ho], fun e he =>
    h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

/-- `Â[i, j]`, from the entries. -/
theorem KRest.matIJ {L : Kem} {n r e : Nat} {σ s : State} (h : KRest L n r e σ s) {i j : Nat} (hi : i < L.k)
    (hj : j < L.k) : PolyIs s.mem (pa s (L.aS i j)) (aHat (rhoK L σ) i j) := by
  have := h.mat (L.k * i + j) (ij_lt hi hj)
  rwa [(divmod_ij hj).1, (divmod_ij hj).2, ← aS_ij] at this

/-! ## The outputs of `PRF₂` -/

theorem prfs_okK (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KRest0 L σ s) : WP isa (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW) s (KRest L 0 0 0 σ) := by
  have hc := W.prfs
  simp only [prfsKChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases L) (by have := W.k; omega_using [this]) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b kS
  refine ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

/-! ## `ŝ` and `ê` -/

theorem se_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {N : Nat}
    (hN : N < 2 * L.k) {s : State} (h : KRest L N 0 0 σ s) : WP isa (se L A N) s (KRest L (N + 1) 0 0 σ) := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  obtain ⟨htw, hrc⟩ := hc
  have L₀ := h.kc.lay W hp
  unfold se
  refine WP.mono (cbd2At_okL hA L₀ rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  have hk := h.keep W hp hP₁ hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega_using [hk'] : k < N ∨ k = N) with hk' | rfl
  · exact hk.se k hk'
  · exact hp₁

theorem r12_na : Reg.r12 ∉ argRegs := by decide
theorem r13_na : Reg.r13 ∉ argRegs := by decide
theorem r12_cs : Reg.r12 ∈ calleeSaved := by decide
theorem r13_cs : Reg.r13 ∈ calleeSaved := by decide

/-! ## `ŝ` and `t̂` -/

/-- The steps done after `vg_mlkem*_keygen_mul`. -/
structure KRestT (L : Kem) (r e : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  r15 : s.gpr .r15 = 1
  shat : ∀ j < L.k, PolyIs s.mem (pa s (pS j)) (KPke.kgS L.p (kgD σ) j)
  that : ∀ i < L.k, PolyIs s.mem (pa s (pS (L.pU + i))) (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i)
  ek : ∀ i < r, bytesAt s.mem (pa s (.r12, 384 * i)) 384 = encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i)
  dk : ∀ j < e, bytesAt s.mem (pa s (.r13, 384 * j)) 384 = encode12 (KPke.kgS L.p (kgD σ) j)

theorem KRestT.keep {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {r e : Nat} {s s' : State}
    (h : KRestT L r e σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : restTChk L r e ws = true) :
    KRestT L r e σ s' := by
  simp only [restTChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kT⟩, kE⟩, kD⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun j hj => L₀.keepPoly hP.b (kS j hj) (h.shat j hj),
    fun i hi => L₀.keepPoly hP.b (kT i hi) (h.that i hi),
    fun i hi => by rw [L₀.keepBytes hP.b (kE i hi)]; exact h.ek i hi,
    fun j hj => by rw [L₀.keepBytes hP.b (kD j hj)]; exact h.dk j hj⟩

theorem pS_add (s : State) (a j : Nat) : pa s (pS a) + BitVec.ofNat 64 (1024 * j) = pa s (pS (a + j)) := by
  simp only [pa, oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4096 + 1024 * a + 1024 * j = 4096 + 1024 * (a + j) by omega_using []]

/-- `t̂[i]`, from the polynomials in memory. -/
theorem kgT_of {L : Kem} {σ : State} {m : Mem} {s : State} {i : Nat} (hi : i < L.k)
    (hA : ∀ j < L.k, polyAt m (pa s (pS (L.pA + L.k * i + j))) = aHat (rhoK L σ) i j)
    (hS : ∀ j < L.k, polyAt m (pa s (pS j)) = cbd (KPke.kgSigma L.p (kgD σ)) j)
    (hE : polyAt m (pa s (pS (L.k + i))) = cbd (KPke.kgSigma L.p (kgD σ)) (L.k + i)) :
    (addVec (mulMatVec (matAt m (pa s (pS L.pA)) L.k) ((vecAt m (pa s (pS 0)) L.k).map ntt))
      ((vecAt m (pa s (pS L.k)) L.k).map ntt)).getD i zero = KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i := by
  rw [KgMul.tgt_eq _ _ hi _ _ (by rw [List.length_map, vecAt_length]), vecAt_map_get _ _ hi,
    pS_add s L.k i, hE]
  have e1 : vecAt m (pa s (pS L.pA) + BitVec.ofNat 64 (1024 * (L.k * i))) L.k =
      (List.range L.k).map (aHat (rhoK L σ) i) := by
    simp only [vecAt]
    refine List.map_congr_left fun j hj => ?_
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, pS_add, ← Nat.add_assoc]
    exact hA j (List.mem_range.mp hj)
  have e2 : (vecAt m (pa s (pS 0)) L.k).map ntt = (List.range L.k).map (KPke.kgS L.p (kgD σ)) := by
    simp only [vecAt, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, pS_add, Nat.zero_add, hS j (List.mem_range.mp hj)]
    rfl
  rw [e1, e2, KPke.dot_eq_dotK]
  rfl

theorem kgm_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KRest L (2 * L.k) 0 0 σ s) :
    WP isa (L.kgMulAt A (pS L.pU) (pS 0) (pS L.pA) (pS L.k) (pS L.pZ)) s (KRestT L 0 0 σ) := by
  have L₀ := h.kc.lay W hp
  have redS : VecReduced s.mem (pa s (pS 0)) L.k := fun j hj => by
    rw [pS_add, Nat.zero_add]; exact (h.se j (by omega_using [hj])).1
  have redA : VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) := fun e he => by rw [pS_add]; exact (h.mat e he).1
  have redE : VecReduced s.mem (pa s (pS L.k)) L.k := fun i hi => by rw [pS_add]; exact (h.se (L.k + i) (by omega_using [hi])).1
  refine WP.mono (kgMulAt_okL hA W.k34 L₀ rbx_na rbx_na rbx_na rbx_na W.km redS redA redE)
    fun s' ⟨hP, hS, hT⟩ => ⟨h.kc.step W hp hP.b W.kmK, by rw [L₀.keepBytes hP.b W.kmG]; exact h.rho,
      by rw [hP.cs .r15 (by decide)]; exact h.r15, fun j hj => ?_, fun i hi => ?_,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := hS.2 j hj
    rw [pS_add, Nat.zero_add, KgMul.getD_get _ (by rw [List.length_map, vecAt_length]; exact hj),
      vecAt_map_get _ _ hj, pS_add, Nat.zero_add, (h.se j (by omega_using [hj])).2] at this
    rw [hP.pa rbx_cs]; exact this
  · have := hT.2 i hi
    rw [pS_add, kgT_of hi (fun j hj => (h.matIJ hi hj).2) (fun j hj => (h.se j (by omega_using [hj])).2)
        (h.se (L.k + i) (by omega_using [hi])).2] at this
    rw [hP.pa rbx_cs]; exact this

/-! ## `t̂`, encoded to `ek` -/

theorem encT_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {i : Nat}
    (hi : i < L.k) {s : State} (h : KRestT L i 0 σ s) : WP isa (encT L A i) s (KRestT L (i + 1) 0 σ) := by
  have hc := W.encT i hi
  simp only [encTChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  have ht := h.that i hi
  refine WP.mono (enc12At_okL hA L₀ r12_na hc.1 ht.1) fun s' ⟨hP, hb⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.kc, hk.rho, hk.r15, hk.shat, hk.that, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.ek i' hi'
  · rw [hP.pa r12_cs, hb, ht.2]

/-! ## `ŝ`, encoded to `dk` -/

theorem encS_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {j : Nat}
    (hj : j < L.k) {s : State}
    (h : KRestT L L.k j σ s) : WP isa (encS A j) s (KRestT L L.k (j + 1) σ) := by
  have hc := W.encS j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  have hs := h.shat j hj
  refine WP.mono (enc12At_okL hA L₀ r13_na hc.1 hs.1) fun s' ⟨hP, hb⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.kc, hk.rho, hk.r15, hk.shat, hk.that, hk.ek, fun j' hj' => ?_⟩
  rcases (by omega_using [hj'] : j' < j ∨ j' = j) with hj' | rfl
  · exact hk.dk j' hj'
  · rw [hP.pa r13_cs, hb, hs.2]

/-! ## The rest of the keys -/

/-- `ek` and `dk_PKE`. -/
abbrev ekK (L : Kem) (σ : State) : List Byte := KPke.ekPKE L.p (aHat (rhoK L σ)) (kgD σ)
abbrev dkK (L : Kem) (σ : State) : List Byte := KPke.dkPKE L.p (kgD σ)

/-- The keys. -/
structure KFin (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = 1
  ek : bytesAt s.mem (pa s (.r12, 0)) L.ekLen = ekK L σ
  dk : bytesAt s.mem (pa s (.r13, 0)) L.dkLen = dkK L σ ++ ekK L σ ++ H (ekK L σ) ++ kgZ σ

/-- Before the keys' last pieces: `t̂` encoded to `ek` and `ŝ` to `dk`. -/
structure KFinPre (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK L σ
  r15 : s.gpr .r15 = 1
  ek : bytesAt s.mem (pa s (.r12, 0)) (384 * L.k) =
    KPke.catK (fun i => encode12 (KPke.kgT L.p (aHat (rhoK L σ)) (kgD σ) i)) L.k
  dk : bytesAt s.mem (pa s (.r13, 0)) (384 * L.k) = KPke.catK (fun j => encode12 (KPke.kgS L.p (kgD σ) j)) L.k

theorem KRestT.pre {L : Kem} {σ s : State} (h : KRestT L L.k L.k σ s) : KFinPre L σ s :=
  ⟨h.kc, h.rho, h.r15, bytesAt_catK _ _ _ _ _ _ L.k fun i hi => by rw [Nat.zero_add]; exact h.ek i hi,
    bytesAt_catK _ _ _ _ _ _ L.k fun j hj => by rw [Nat.zero_add]; exact h.dk j hj⟩

theorem fin_ok {L : Kem} (W : KgWfB L) {σ : State} (hp : (keyGenK L).pre σ) {s : State} (h : KFinPre L σ s) :
    WP isa (fin L) s (KFin L σ) := by
  have L₀ := h.kc.lay W hp
  unfold fin
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.kc.step W hp hP₁.b W.f₁K
  have L₁ := k₁.lay W hp
  have hek : bytesAt s₁.mem (pa s₁ (.r12, 0)) L.ekLen = ekK L σ := by
    rw [Kem.ekLen, Params.ekLen, bytesAt_split, show 0 + 384 * L.p.k = 384 * L.k from Nat.zero_add _,
      hP₁.pa (p := (.r12, 384 * L.k)) r12_cs, hb₁, h.rho, ekK, KPke.ekPKE, L₀.keepBytes hP₁.b W.f₁E]
    exact congrArg (· ++ _) h.ek
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step W hp hP₂.b W.f₂K
  have L₂ := k₂.lay W hp
  rw [hek] at hb₂
  have hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) L.ekLen = ekK L σ := by
    rw [L₁.keepBytes hP₂.b W.f₂E]; exact hek
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
    (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  have k₃ := k₂.step W hp hP₃.b W.f₃K
  have L₃ := k₃.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hek₂, sha3Suffix6] at hb₃
  rw [← H_eq] at hb₃
  -- `z`.
  refine WP.mono (copy_okL L₃ (dst := (.r13, 384 * L.k + L.ekLen + 32)) (src := (.rbp, 32)) (n := 32) (by decide) W.f₄)
    fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have k₄ := k₃.step W hp hP₄.b W.f₄K
  rw [k₃.z] at hb₄
  refine ⟨k₄, ?_, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [L₃.keepBytes hP₄.b W.f₄E, L₂.keepBytes hP₃.b W.f₃E]; exact hek₂
  · have hP := PPost.app (PPost.app (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hP₃ (by simp [calleeSaved])) hP₄
      (by simp [calleeSaved])
    have hP' := PPost.app hP₃ hP₄ (by simp [calleeSaved])
    rw [show L.dkLen = 384 * L.k + L.ekLen + 32 + 32 by
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega_using [],
      bytesAt_split, bytesAt_split, bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₄.pa (p := (.r13, 384 * L.k + L.ekLen + 32)) r13_cs, hb₄,
      L₃.keepBytes hP₄.b W.dkH, hP₃.pa (p := (.r13, 384 * L.k + L.ekLen)) r13_cs, hb₃,
      L₂.keepBytes hP'.b W.dkE, hP₂.pa (p := (.r13, 384 * L.k)) r13_cs, hb₂, dkK, KPke.dkPKE]
    rw [L₀.keepBytes hP.b W.dkS]
    exact congrArg (· ++ _ ++ _ ++ _) h.dk

end KeyGen

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: key generation, constant time of the pieces

Two runs from entry states that agree on the public data (`keyGenK.pub`: the
pointers, the stack pointer and `ρ`), each at the same step with its invariant
(`Rel2`), are in the same layout (`kc_lrel`), and each piece leaks the same in
both (`gRho_tr`, `samples_tr`, `se_tr`, `kgm_tr`, `encT_tr`, `encS_tr`, `fin_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A piece's constant time in a relation implied by the invariants of two runs. -/
theorem rel2_of {Pre : State → Prop} {Pub : State → State → Prop} {I : State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

section

variable {L : Kem} (W : KgWfB L)
include W

theorem kc_lrel {σ₁ σ₂ x y : State} (p₁ : (keyGenK L).pre σ₁) (p₂ : (keyGenK L).pre σ₂) (pub : (keyGenK L).pub σ₁ σ₂)
    (h₁ : KC σ₁ x) (h₂ : KC σ₂ y) : LRel kgR (kgW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (keyGenK L).pub σ₁ σ₂) : rhoK L σ₁ = rhoK L σ₂ := pub.2.2.2.2.2

/-! ## `G` -/

theorem gRho_trL : RelCT isa (LRel kgR (kgW L)) (gRho L) fun _ _ => True := by
  unfold gRho
  refine RelCT.seq (LRel.step (kgB_bases L) (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) W.nbT)
    fun x Lx => WP.mono (setB_okL Lx (by decide) (by have := W.k; omega_using [this]) (p := sc oNB) (v := L.k) W.nb)
      fun _ h => ⟨_, h.1⟩) (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L)
        (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG) (len := 64) W.gH (show 6 < 256 by decide))
    fun x Lx => WP.mono (hash_ok (kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
      (len := 64) W.gH (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) (by taint_decide)))

theorem gRho_tr : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub fun σ s => KC σ s ∧ s.gpr .r15 = 1) (gRho L)
    fun _ _ => True :=
  rel2_of (gRho_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.1 h₂.1

/-! ## The matrix -/

theorem fin_trL : RelCT isa (LRel kgR (kgW L)) (fin L) fun _ _ => True := by
  unfold fin
  have tr : ∀ {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T},
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true →
      RelCT isa (LRel kgR (kgW L)) c fun _ _ => True := fun ht => taintRel [.rbx, .rbp, .r12, .r13] (fun x y h =>
    fa4 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2)) ht
  obtain ⟨_, t₁⟩ := W.finT₁
  obtain ⟨_, t₂⟩ := W.finT₂
  obtain ⟨_, t₄⟩ := W.finT₄
  refine RelCT.seq (LRel.step (kgB_bases L) (tr t₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (tr t₂) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (kgB_bases L) (hash_tr (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
      (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136) (out := (.r13, 384 * L.k + L.ekLen))
        (len := 32) W.f₃ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (tr t₄)))

theorem fin_tr {I : State → State → Prop} (hI : ∀ {σ s}, I σ s → KC σ s) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub I) (fin L) fun _ _ => True :=
  rel2_of (fin_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub (hI h₁) (hI h₂)

end

section

variable {L : Kem} (W : KgWf L)
include W

theorem sample_tr {e : Nat} (he : e < L.k * L.k) (he' : 4 * (L.k * L.k / 4) ≤ e) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e)) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      fun _ _ => True := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  exact rel2_of (sampleIJ_tr (kgB_bases L) rbx_na (by have := div_lt_k he; omega_using [hk, this]) (by have := mod_lt_k he; omega_using [hk, this])
      hc.1.1.1.1.1 (W.ijT e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact rho_pub pub⟩

theorem quad_trK (v : Sample4Impl) {q : Nat} (hq : q < L.k * L.k / 4) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (4 * q)))
      (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) fun _ _ => True := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2
  exact rel2_of (RelCT.exists_ fun ρ => quad_tr (ρ := ρ) v (kgB_bases L) (by omega_using [hq, h16])
      (fun t ht => ⟨by have := div_lt_k (show 4 * q + t < L.k * L.k by omega_using [hq, ht]); omega_using [hk, this],
        by have := mod_lt_k (show 4 * q + t < L.k * L.k by omega_using [hq, ht]); omega_using [hk, this]⟩) hc.1.1.1.1.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨KPke.kgRho L.p (kgD σ₁), kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr (v : Sample4Impl) : RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L 0)) (L.samples v.callee)
    (Rel2 (keyGenK L).pre (keyGenK L).pub (KB L (L.k * L.k))) :=
  samples_tr' L v.callee (R := fun e => Rel2 (keyGenK L).pre (keyGenK L).pub (KB L e))
    (fun _ he he' => relInv (fun _ _ hp hs => sample_step W hp he he' hs) (sample_tr W he he'))
    (fun _ hq => relInv (fun _ _ hp hs => quad_step v W hp hq hs) (quad_trK W v hq))

/-! ## `ŝ` and `ê` -/

theorem prfs_trK (v : Sample4Impl) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest0 L)) (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW)
      fun _ _ => True := by
  have hc := W.prfs
  simp only [prfsKChk, Bool.and_eq_true] at hc
  exact rel2_of (v.prfs_tr (kgB_bases L) (by have := W.k; omega_using [this]) hc.1.1.1.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem se_tr {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L N 0 0)) (se L A N) fun _ _ => True := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  unfold se
  exact rel2_of (cbd2At_trL hA rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

/-! ## `ŝ` and `t̂` -/

theorem kgm_tr {A : Arith} (hA : ArithOk A) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRest L (2 * L.k) 0 0))
      (L.kgMulAt A (pS L.pU) (pS 0) (pS L.pA) (pS L.k) (pS L.pZ)) fun _ _ => True := by
  have red : ∀ {σ s : State}, KRest L (2 * L.k) 0 0 σ s → VecReduced s.mem (pa s (pS 0)) L.k ∧
      VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) ∧ VecReduced s.mem (pa s (pS L.k)) L.k := fun h =>
    ⟨fun j hj => by rw [pS_add, Nat.zero_add]; exact (h.se j (by omega_using [hj])).1,
      fun e he => by rw [pS_add]; exact (h.mat e he).1,
      fun i hi => by rw [pS_add]; exact (h.se (L.k + i) (by omega_using [hi])).1⟩
  exact rel2_of (kgMulAt_trL hA W.k34 rbx_na rbx_na rbx_na rbx_na W.km) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, red h₁, red h₂⟩

/-! ## The rows of `ek` -/

theorem encT_tr {A : Arith} (hA : ArithOk A) {i : Nat} (hi : i < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRestT L i 0)) (encT L A i) fun _ _ => True := by
  have hc := W.encT i hi
  simp only [encTChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL hA r12_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.that i hi).1, (h₂.that i hi).1⟩

/-! ## The rows of `dk` -/

theorem encS_tr {A : Arith} (hA : ArithOk A) {j : Nat} (hj : j < L.k) :
    RelCT isa (Rel2 (keyGenK L).pre (keyGenK L).pub (KRestT L L.k j)) (encS A j) fun _ _ => True := by
  have hc := W.encS j hj
  simp only [encSChk, Bool.and_eq_true] at hc
  exact rel2_of (enc12At_trL hA r13_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.shat j hj).1, (h₂.shat j hj).1⟩

/-! ## The rest of the keys -/

end

end KeyGen

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: key generation

The function, piece by piece (`KeyGen.*_ok`): it returns 1 with
`KeyGen_internal(d, z)` in `ek` and `dk` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`keyGen_correct`); it leaks only
the pointers and `ρ` (`keyGen_ct`). Each parameter set's file moves this to
its shared contract.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `KB` is kept by a piece that only sets flags. -/
theorem KB.flag {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {e : Nat} (he : e ≤ L.k * L.k)
    {s s' : State} (h : KB L e σ s) (hP : PPost s s' []) : KB L e σ s' := by
  have L₀ := h.a.kc.lay W hp
  exact ⟨h.a.keep W hp hP.b W.flag W.flagG W.flagS W.flagB, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e' he' f hf => L₀.keepPoly hP.b (W.flagA e' (by omega_using [he, he'])) (h.m.mat e' he' f hf)⟩

/-- At the end: `r15` as `allOk`, and the keys if it is 1. -/
structure KEnd (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = if allOk L.k (rhoK L σ) (L.k * L.k) then 1 else 0
  keys : allOk L.k (rhoK L σ) (L.k * L.k) → KFin L σ s

theorem r15_ne {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if allOk k ρ (k * k) then 1 else 0)
    (hne : r.setWidth 32 ≠ 0) : allOk k ρ (k * k) := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_eq {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if allOk k ρ (k * k) then 1 else 0)
    (he : r.setWidth 32 = 0) : ¬ allOk k ρ (k * k) := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

theorem rest_ok (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KRest0 L σ s) : WP isa (rest L v.callee) s (KFin L σ) := by
  unfold rest
  refine WP.seq (WP.mono (prfs_okK v W hp h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest L k 0 0 σ) (2 * L.k) 0
    (fun k _ hk s hs => se_ok v.arith W hp (by omega_using [hk]) hs) s₀ h₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (kgm_ok v.arith W hp (by rwa [Nat.zero_add] at h₁)) fun s₁' h₁' => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRestT L k 0 σ) L.k 0
    (fun k _ hk s hs => encT_ok v.arith W hp (by omega_using [hk]) hs) s₁' h₁') fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRestT L L.k k σ) L.k 0
    (fun k _ hk s hs => encS_ok v.arith W hp (by omega_using [hk]) hs) s₂ (by rwa [Nat.zero_add] at h₂)) fun s₃ h₃ => ?_)
  exact fin_ok W hp (by rw [Nat.zero_add] at h₃; exact h₃.pre)

theorem body_ok (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KB L (L.k * L.k) σ s) : WP isa (ifOk (rest L v.callee)) s (KEnd L σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := r15_ne h.m.r15 hne
    exact WP.mono (rest_ok v W hp (KRest0.start (h.flag W hp (Nat.le_refl _) hP) ho)) fun s' hf =>
      ⟨hf.kc, by rw [hf.r15, ifp ho], fun _ => hf⟩
  · have ho := r15_eq h.m.r15 he
    have h' := h.flag W hp (Nat.le_refl _) hP
    exact ⟨h'.a.kc, h'.m.r15, fun h => absurd h ho⟩

/-- The postcondition, from the keys. -/
theorem post_of {L : Kem} (W : KgWfB L) {σ s : State} (h : KEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (keyGenK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rsi := by
    rw [pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rdx := by
    rw [pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (rhoK L σ) (L.k * L.k)
  · have hf := h.keys ho
    refine .inl ⟨by rw [hr, hf.r15]; rfl, minIterations, ?_⟩
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some W.eta.1 (a := aHat (rhoK L σ))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, hf.ek, hf.dk]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none hi hj hn]
    rfl

theorem KEnd.hin {L : Kem} (W : KgWfB L) {σ s : State} (hp : (keyGenK L).pre σ) (h : KEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.kc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

end KeyGen

open KeyGen in
theorem kemKeyGen_correct (v : Sample4Impl) {L : Kem} (W : KgWf L) (hctl : ctlOk (kemKeyGen L v.callee) = true)
    (σ : State) (hp : (keyGenK L).pre σ) :
    ∃ t s', Exec isa (kemKeyGen L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (keyGenK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok W hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (samples_ok v W hp (KB.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok v W hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (keyGenK L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

/-- `relInv`, with a fact about the entry state carried along. -/
theorem relInvC {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop} {C : State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub fun σ s => I σ s ∧ C σ) c (Rel2 Pre Pub fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable {L : Kem} (W : KgWf L)
include W

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (keyGenK L).pre (keyGenK L).pub I

theorem rest_tr (v : Sample4Impl) :
    RelCT isa (R L fun σ s => KRest0 L σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k)) (rest L v.callee)
      (R L fun σ s => KFin L σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k)) := by
  unfold rest
  refine RelCT.seq (relInvC (fun σ s hp hs => prfs_okK v W hp hs) (prfs_trK W v)) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRest L k 0 0 σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    (2 * L.k) 0 fun k _ hk => relInvC (fun σ s hp hs => se_ok v.arith W hp (by omega_using [hk]) hs)
      (se_tr W v.arith (by omega_using [hk]))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (relInvC (fun σ s hp hs => kgm_ok v.arith W hp hs) (kgm_tr W v.arith)) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRestT L k 0 σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => relInvC (fun σ s hp hs => encT_ok v.arith W hp (by omega_using [hk]) hs) (encT_tr W v.arith (by omega_using [hk]))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRestT L L.k k σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => relInvC (fun σ s hp hs => encS_ok v.arith W hp (by omega_using [hk]) hs) (encS_tr W v.arith (by omega_using [hk]))) ?_
  rw [Nat.zero_add]
  exact relInvC (fun σ s hp hs => fin_ok W hp hs.pre) (fin_tr W fun h => h.kc)

omit W in
theorem r15_pub {σ₁ σ₂ x y : State} (pub : (keyGenK L).pub σ₁ σ₂) (h₁ : KB L (L.k * L.k) σ₁ x)
    (h₂ : KB L (L.k * L.k) σ₂ y) : x.gpr .r15 = y.gpr .r15 := by
  rw [h₁.m.r15, h₂.m.r15]; exact congrArg (fun ρ => if allOk L.k ρ (L.k * L.k) then (1 : BitVec 64) else 0) (rho_pub pub)

theorem body_tr (v : Sample4Impl) : RelCT isa (R L (KB L (L.k * L.k))) (ifOk (rest L v.callee)) (R L (KEnd L)) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono (rest_tr W v) (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.1.kc, by rw [h₁.1.r15, ifp h₁.2], fun _ => h₁.1⟩,
          ⟨h₂.1.kc, by rw [h₂.1.r15, ifp h₂.2], fun _ => h₂.1⟩⟩
    have o₁ := r15_ne h₁.m.r15 hne
    have o₂ : allOk L.k (rhoK L σ₂) (L.k * L.k) := by rw [← rho_pub pub]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest0.start (h₁.flag W p₁ (Nat.le_refl _) hx) o₁, o₁⟩,
      ⟨KRest0.start (h₂.flag W p₂ (Nat.le_refl _) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk L.k (rhoK L σ₂) (L.k * L.k) := by rw [← rho_pub pub]; exact o₁
    have k₁ := h₁.flag W p₁ (Nat.le_refl _) hx
    have k₂ := h₂.flag W p₂ (Nat.le_refl _) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.m.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.m.r15, fun h => absurd h o₂⟩⟩

omit W in
theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

omit W in
theorem epi_tr : RelCT isa (R L (KEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.kc.top.regs (.rbx, .rcx) (by decide), h₂.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end KeyGen

open KeyGen in
theorem kemKeyGen_ct (v : Sample4Impl) {L : Kem} (W : KgWf L) :
    ConstantTime isa (keyGenK L).pre (keyGenK L).pub (kemKeyGen L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemKeyGen
  refine RelCT.seq (relInv (I' := fun σ s => KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KA L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => gRho_ok W hp hs.1 hs.2) (gRho_tr W)) ?_
  refine RelCT.seq (RelCT.mono (samples_tr W v)
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KB.zero h₁.1 h₁.2, KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq (body_tr W v) (RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.EncRest`, which only this module used -/

section

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, the ciphertext

When every entry of `Â` was sampled: `y` (`y_ok`), `t̂` (`t_ok`), the
products `NTT⁻¹(Â^⊺ ∘ ŷ)` and `NTT⁻¹(t̂^⊺ ∘ ŷ)` (`mul_ok`), `u` to the
ciphertext (`u_ok`) and `v` to the ciphertext (`v_ok`). Between the steps,
`ER ny nt`: the first `ny` of `y` and `nt` of `t̂` are done; then `EU nu`:
the products, and the first `nu` of `u`. Each with its constant time, for a
given `ρ`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- The steps done after the matrix. -/
structure ER (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (ny nt : Nat) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k + 1, bytesAt s.mem (pa s (prfO L N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  y : ∀ k < ny, PolyIs s.mem (pa s (pS k)) (cbd r k)
  t : ∀ i < nt, PolyIs s.mem (pa s (pS (L.k + i))) (ekT ek i)

/-- A piece that writes `ws` keeps `ER ny nt`. -/
def erChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ny nt : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  inKeep L bs chk E ws && (List.range (L.k * L.k)).all (fun e => keepB bs ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k + 1)).all (fun N => keepB bs ws (prfO L N) 128) &&
    (List.range ny).all (fun k => keepB bs ws (pS k) 1024) &&
    (List.range nt).all (fun i => keepB bs ws (pS (L.k + i)) 1024)

theorem ER.keep {C : Ctx rbs wbs} {ek m r : List Byte} {ny nt : Nat} {s s' : State}
    (h : ER L C E ek m r ny nt s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : erChk L (rbs ++ wbs) C.chk E ny nt ws = true) : ER L C E ek m r ny nt s' := by
  simp only [erChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hin, kA⟩, kR⟩, kY⟩, kT⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.ok, h.i.keep hP.b hin, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kY k hk) (h.y k hk),
    fun i hi => L₀.keepPoly hP.b (kT i hi) (h.t i hi)⟩

/-- `Â[i, j]`, from the entries. -/
theorem ER.matIJ {C : Ctx rbs wbs} {ek m r : List Byte} {ny nt : Nat} {s : State}
    (h : ER L C E ek m r ny nt s) {i j : Nat} (hi : i < L.k) (hj : j < L.k) :
    PolyIs s.mem (pa s (L.aS i j)) (aHat (rhoE L ek) i j) := by
  have := h.mat (L.k * i + j) (ij_lt hi hj)
  rwa [(divmod_ij hj).1, (divmod_ij hj).2, ← aS_ij] at this

theorem EB.flag {C : Ctx rbs wbs} {ek m r : List Byte} {s s' : State} (h : EB L C E ek m r (L.k * L.k) s)
    (hP : PPost s s' []) (hc : inKeep L (rbs ++ wbs) C.chk E [] = true)
    (hk : ∀ e < L.k * L.k, keepB (rbs ++ wbs) [] (pS (L.pA + e)) 1024 = true)
    (hsb : keepB (rbs ++ wbs) [] (sc oSB) 32 = true) : EB L C E ek m r (L.k * L.k) s' := by
  have L₀ := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc, by rw [L₀.keepBytes hP.b hsb]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e he f hf => L₀.keepPoly hP.b (hk e he) (h.m.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : allOk L.k (rhoE L ek) (L.k * L.k)
  i : EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (aHat (rhoE L ek) (e / L.k) (e % L.k))

theorem ER0.start {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : EB L C E ek m r (L.k * L.k) s)
    (ho : allOk L.k (rhoE L ek) (L.k * L.k)) : ER0 L C E ek m r s :=
  ⟨ho, h.i, by rw [h.m.r15, ifp ho], fun e he => h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

/-- The steps, for the `ρ` of `ek`. -/
abbrev ERρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (ny nt : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER L C E ek m r ny nt s

/-! ## The outputs of `PRF₂` -/

def prfsEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  prfsChk bs wbs (2 * L.k + 1) L.oPR L.lPW && inKeep L bs chk E (prfsW (2 * L.k + 1) L.oPR L.lPW) &&
    (List.range (L.k * L.k)).all (fun e => keepB bs (prfsW (2 * L.k + 1) L.oPR L.lPW) (pS (L.pA + e)) 1024)

theorem prfsE_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ek m r : List Byte} {s : State} (h : ER0 L C E ek m r s) :
    WP isa (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW) s fun s' =>
      PPost s s' (prfsW (2 * L.k + 1) L.oPR L.lPW) ∧ ER L C E ek m r 0 0 s' := by
  simp only [prfsEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hpc, hin⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (v.prfs_ok L₀ C.bs (by omega_using [hk]) hpc) fun s' ⟨hP, hb⟩ => ⟨hP, h.ok, h.i.keep hP.b hin,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

/-- After the matrix, for the `ρ` of `ek`. -/
abbrev ER0ρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ ER0 L C E ek m r s

theorem prfsE_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hk : L.k ≤ 4) (hc : prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ L C E ρ x ∧ ER0ρ L C E ρ y) (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ 0 0 x ∧ ERρ L C E ρ 0 0 y) := by
  have hc' := hc
  simp only [prfsEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by omega_using [hk]) hc'.1.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (prfsE_ok v hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `y` -/

def yChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (N : Nat) : Bool :=
  twoChk bs wbs (prfO L N) 128 (pS N) 1024 && erChk L bs chk E N 0 [(pS N, 1024)]

theorem y_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r N 0 s) :
    WP isa (y L A N) s fun s' => PPost s s' [(pS N, 1024)] ∧ ER L C E ek m r (N + 1) 0 s' := by
  simp only [yChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (cbd2At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega_using [hk'] : k < N ∨ k = N) with hk' | rfl
  · exact hk.y k hk'
  · rw [h.prf k (by omega_using [hN]), ← hP.pa rbx_cs] at hp; exact hp

theorem y_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : yChk L (rbs ++ wbs) wbs C.chk E N = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ N 0 x ∧ ERρ L C E ρ N 0 y) (y L A N)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ (N + 1) 0 x ∧ ERρ L C E ρ (N + 1) 0 y) := by
  have hc' := hc
  simp only [yChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (cbd2At_trL hA rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (y_ok hA hN hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `t̂` -/

def tChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (E.1, E.2 + 384 * i) 384 (pS (L.k + i)) 1024 && erChk L bs chk E L.k i [(pS (L.k + i), 1024)]

theorem t_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k i s) :
    WP isa (t L A E i) s fun s' => PPost s s' [(pS (L.k + i), 1024)] ∧ ER L C E ek m r L.k (i + 1) s' := by
  simp only [tChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (dec12At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, fun i' hi' => ?_⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.t i' hi'
  · rw [hP.pa rbx_cs]
    have e : bytesAt s.mem (pa s (E.1, E.2 + 384 * i')) 384 = (ek.drop (384 * i')).take 384 := by
      rw [← h.i.ek]
      show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * i')).take 384
      rw [bytesAt_slice _ _ (show 384 * i' + 384 ≤ 384 * L.k + 32 by omega_using [hi]), pa, pa, off_add]
    rw [e] at hp
    exact hp

theorem t_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k i x ∧ ERρ L C E ρ L.k i y) (t L A E i)
      (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k (i + 1) x ∧ ERρ L C E ρ L.k (i + 1) y) := by
  have hc' := hc
  simp only [tChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (dec12At_trL hA rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (t_ok hA hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## The products -/

/-- `NTT⁻¹(Â^⊺ ∘ ŷ)[i]` for `i < k`, and `NTT⁻¹(t̂^⊺ ∘ ŷ)` for `i = k`. -/
def encW (L : Kem) (ek r : List Byte) (i : Nat) : Poly :=
  if i < L.k then nttInv (KPke.dotK (fun j => aHat (rhoE L ek) j i) (encY r) L.k)
  else nttInv (KPke.dotK (ekT ek) (encY r) L.k)

/-- After the products: the first `nu` of `u` are in the ciphertext, the
others of the products are in place. -/
structure EU (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (nu : Nat) (s : State) : Prop
    extends ER L C E ek m r L.k L.k s where
  w : ∀ i < L.k + 1, nu ≤ i → PolyIs s.mem (pa s (pS (L.pU + i))) (encW L ek r i)
  u : ∀ i < nu, bytesAt s.mem (pa s (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
    compressEncode L.du (KPke.encU L.p (aHat (rhoE L ek)) r i)

/-- A piece that writes `ws` keeps `ER k k`, the products from `nw` and the first `nu` of `u`. -/
def euChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (nw nu : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  erChk L bs chk E L.k L.k ws &&
    (List.range (L.k + 1)).all (fun i => !decide (nw ≤ i) || keepB bs ws (pS (L.pU + i)) 1024) &&
    (List.range nu).all (fun i => keepB bs ws (sc (L.oCT + 32 * L.du * i)) (32 * L.du))

theorem EU.keep {C : Ctx rbs wbs} {ek m r : List Byte} {nu nw : Nat} {s s' : State} (h : EU L C E ek m r nu s)
    (hn : nu ≤ nw) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : euChk L (rbs ++ wbs) C.chk E nw nu ws = true) :
    ER L C E ek m r L.k L.k s' ∧ (∀ i < L.k + 1, nw ≤ i → PolyIs s'.mem (pa s' (pS (L.pU + i))) (encW L ek r i)) ∧
      ∀ i < nu, bytesAt s'.mem (pa s' (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
        compressEncode L.du (KPke.encU L.p (aHat (rhoE L ek)) r i) := by
  simp only [euChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  obtain ⟨⟨hr, kw⟩, ku⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.toER.keep hP hr, fun i hi hi' => L₀.keepPoly hP.b ((kw i hi).resolve_left fun h' => h' hi')
    (h.w i hi (Nat.le_trans hn hi')), fun i hi => by rw [L₀.keepBytes hP.b (ku i hi)]; exact h.u i hi⟩

theorem ER.vred {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) :
    VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) ∧ VecReduced s.mem (pa s (pS L.k)) L.k ∧
      VecReduced s.mem (pa s (pS 0)) L.k :=
  ⟨vecReduced_pS fun e he => (h.mat e he).1, vecReduced_pS fun i hi => (h.t i hi).1,
    vecReduced_pS fun j hj => by rw [Nat.zero_add]; exact (h.y j hj).1⟩

/-- The outputs of `vg_mlkem*_encrypt_mul`, for the inputs of `ER k k`. -/
theorem ER.prods {C : Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) {i : Nat}
    (hi : i < L.k + 1) :
    ((((mulMatTVec L.k (matAt s.mem (pa s (pS L.pA)) L.k) ((vecAt s.mem (pa s (pS 0)) L.k).map ntt)).map nttInv) ++
      [nttInv (dot (vecAt s.mem (pa s (pS L.k)) L.k) ((vecAt s.mem (pa s (pS 0)) L.k).map ntt))]).getD i zero) =
      encW L ek r i := by
  have hy : (vecAt s.mem (pa s (pS 0)) L.k).map ntt = (List.range L.k).map (encY r) := by
    rw [vecAt_pS, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    rw [Function.comp_apply, Nat.zero_add, (h.y j (List.mem_range.mp hj)).2]
    rfl
  rw [hy]
  by_cases h' : i < L.k
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [EncMul.mulMatTVec_length]; exact h'),
      ← List.getD_eq_getElem?_getD, EncMul.mulMatTVec_getD _ _ _ _ h', encW, ifp h']
    refine congrArg nttInv ?_
    have hcol : EncMul.colE s.mem (pa s (pS L.pA)) L.k i = (List.range L.k).map fun j => aHat (rhoE L ek) j i := by
      simp only [EncMul.colE, matAt, List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.mp hj
      rw [Function.comp_apply, List.getD_eq_getElem?_getD, vecAt, List.getElem?_map, List.getElem?_range h',
        Option.map_some, Option.getD_some, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, ← pa_pS,
        show L.pA + (L.k * j + i) = L.pA + L.k * j + i by omega_using []]
      exact (h.matIJ hj h').2
    rw [hcol, KPke.dot_eq_dotK]
  · have hik : i = L.k := by omega_using [hi, h']
    subst hik
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [EncMul.mulMatTVec_length]),
      EncMul.mulMatTVec_length, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, encW,
      ifn (Nat.lt_irrefl _)]
    refine congrArg nttInv ?_
    have ht : vecAt s.mem (pa s (pS L.k)) L.k = (List.range L.k).map (ekT ek) := by
      rw [vecAt_pS]
      exact List.map_congr_left fun j hj => (h.t j (List.mem_range.mp hj)).2
    rw [ht, KPke.dot_eq_dotK]

/-- The products: `vg_mlkem*_encrypt_mul`. -/
def emEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  emChk bs wbs L.k (pS L.pU) (pS L.pA) (pS L.k) (pS 0) (pS L.pZ) &&
    erChk L bs chk E L.k L.k [(pS L.pU, 1024 * (L.k + 1)), (pS L.pZ, 4096)]

theorem mul_ok {A : Arith} (hA : ArithOk A) (hk : L.k = 3 ∨ L.k = 4) {C : Ctx rbs wbs}
    (hc : emEChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : ER L C E ek m r L.k L.k s) :
    WP isa (mul L A) s fun s' => PPost s s' [(pS L.pU, 1024 * (L.k + 1)), (pS L.pZ, 4096)] ∧
      EU L C E ek m r 0 s' := by
  simp only [emEChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  have hr := h.vred
  refine WP.mono (encMulAt_okL hA hk L₀ rbx_na rbx_na rbx_na rbx_na hc.1 hr.1 hr.2.1 hr.2.2) fun s' ⟨hP, hv⟩ => ?_
  refine ⟨hP, h.keep hP hc.2, fun i hi _ => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have e := hv.2 i hi
  rw [← pa_pS, ← hP.pa rbx_cs, h.prods hi] at e
  exact e

/-- `EU nu`, for the `ρ` of `ek`. -/
abbrev EUρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (nu : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EU L C E ek m r nu s

theorem mul_tr {A : Arith} (hA : ArithOk A) (hk : L.k = 3 ∨ L.k = 4) {C : Ctx rbs wbs}
    (hc : emEChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k x ∧ ERρ L C E ρ L.k L.k y) (mul L A)
      (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ 0 x ∧ EUρ L C E ρ 0 y) := by
  have hc' := hc
  simp only [emEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (encMulAt_trL hA hk rbx_na rbx_na rbx_na rbx_na hc'.1)
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ => ⟨hl, h₁.vred, h₂.vred⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (mul_ok hA hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `u` -/

abbrev uW (L : Kem) (i : Nat) : List (Ptr × Nat) :=
  [(pS 15, 1024)] ++ [(pS (L.pU + i), 1024)] ++ [(sc (L.oCT + 32 * L.du * i), 32 * L.du)]

def uChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (prfO L (L.k + i)) 128 (pS 15) 1024 && keepB bs [(pS 15, 1024)] (pS (L.pU + i)) 1024 &&
    accChk bs wbs (pS (L.pU + i)) (pS 15) &&
    twoChk bs wbs (pS (L.pU + i)) 1024 (sc (L.oCT + 32 * L.du * i)) (32 * L.du) &&
    euChk L bs chk E (i + 1) i (uW L i)

theorem u_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ek m r : List Byte} {s : State}
    (h : EU L C E ek m r i s) :
    WP isa (u L A i) s fun s' => PPost s s' (uW L i) ∧ EU L C E ek m r (i + 1) s' := by
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hpc, hkw⟩, hac⟩, htw⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold u
  refine WP.seq (WP.mono (cbd2At_okL hA L₀ rbx_na hpc) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf (L.k + i) (by omega_using [hi]), ← hP₁.pa rbx_cs] at hp₁
  have hw₁ := L₀.keepPoly hP₁.b hkw (h.w i (by omega_using [hi]) (Nat.le_refl _))
  refine WP.seq (WP.mono (addAt_ok hA L₁ rbx_na hac hw₁.1 hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b C.bs
  rw [hw₁.2, hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.mono (ceCall_okL (K.ce A.codecs) L₂ rbx_na htw K.du.1 hp₂.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have hP := PPost.app (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hP₃ (by simp [calleeSaved])
  obtain ⟨hk, hw, hu⟩ := h.keep (Nat.le_succ i) hP hrc
  refine ⟨hP, hk, hw, fun i' hi' => ?_⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact hu i' hi'
  · rw [hP₃.pa rbx_cs, hb₃, hp₂.2, encW, ifp hi]; rfl

theorem u_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : uChk L (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ i x ∧ EUρ L C E ρ i y) (u L A i)
      (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ (i + 1) x ∧ EUρ L C E ρ (i + 1) y) := by
  have hc' := hc
  simp only [uChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨hpc, hkw⟩, hac⟩, htw⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (u_ok hA K hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold u
  refine RelCT.mono (RelCT.seqL (I := fun x => Reduced x.mem (pa x (pS (L.pU + i))))
    (J := fun x => Reduced x.mem (pa x (pS (L.pU + i))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (cbd2At_trL hA rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL hA Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + i)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL (K.ce A.codecs) rbx_na htw K.du.1)))
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
      ⟨hl, (h₁.w i (by omega_using [hi]) (Nat.le_refl _)).1, (h₂.w i (by omega_using [hi]) (Nat.le_refl _)).1⟩) fun _ _ h => h

/-! ## `v` -/

abbrev vW (L : Kem) : List (Ptr × Nat) := [(pS 15, 1024)] ++ [(pS (L.pU + L.k), 1024)] ++ [(pS 15, 1024)] ++
  [(pS (L.pU + L.k), 1024)] ++ [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)]

def vChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  twoChk bs wbs (prfO L (2 * L.k)) 128 (pS 15) 1024 && keepB bs [(pS 15, 1024)] (pS (L.pU + L.k)) 1024 &&
    accChk bs wbs (pS (L.pU + L.k)) (pS 15) && twoChk bs wbs (sc oM) 32 (pS 15) 1024 &&
    inKeep L bs chk E ([(pS 15, 1024)] ++ [(pS (L.pU + L.k), 1024)]) &&
    twoChk bs wbs (pS (L.pU + L.k)) 1024 (sc (L.oCT + 32 * L.du * L.k)) (32 * L.dv) &&
    euChk L bs chk E (L.k + 1) L.k (vW L)

theorem v_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : EU L C E ek m r L.k s) :
    WP isa (v L A) s fun s' => PPost s s' (vW L) ∧ C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r := by
  simp only [vChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hpc, hkw⟩, hac⟩, hdd⟩, hi₂⟩, htw⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold v
  refine WP.seq (WP.mono (cbd2At_okL hA L₀ rbx_na hpc) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf (2 * L.k) (by omega_using []), ← hP₁.pa rbx_cs] at hp₁
  have hw₁ := L₀.keepPoly hP₁.b hkw (h.w L.k (by omega_using []) (Nat.le_refl _))
  refine WP.seq (WP.mono (addAt_ok hA L₁ rbx_na hac hw₁.1 hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have hP₁₂ := PPost.app hP₁ hP₂ (by simp [calleeSaved])
  have e₂ := h.i.keep hP₁₂.b hi₂
  have L₂ := C.lay e₂.out
  rw [hw₁.2, hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (ddCall_okL (Codecs.ddI A.codecs) L₂ (d := 1) rbx_na hdd (by decide)) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b C.bs
  rw [e₂.m, ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hkw hp₂
  refine WP.seq (WP.mono (addAt_ok hA L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b C.bs
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceCall_okL (K.ce A.codecs) L₄ (d := L.dv) rbx_na htw K.dv.1 hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP₄' := PPost.app (PPost.app hP₁₂ hP₃ (by simp [calleeSaved])) hP₄ (by simp [calleeSaved])
  have hP := PPost.app hP₄' hP₅ (by simp [calleeSaved])
  obtain ⟨hk, -, hu⟩ := h.keep (Nat.le_succ _) hP hrc
  rw [hP₄'.pa rbx_cs] at hb₅
  refine ⟨hP, hk.i.out, hk.r15, ?_⟩
  rw [Kem.ctLen, Params.ctLen, show 32 * (L.p.du * L.p.k + L.p.dv) = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc], hP.pa rbx_cs, sc, bytesAt_split,
    hb₅, hp₄.2, encW, ifn (Nat.lt_irrefl _), KPke.ct]
  refine congrArg (· ++ _) (bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
  rw [← hP.pa (p := sc (L.oCT + 32 * L.du * i)) rbx_cs]
  exact hu i hi

/-! ## The end of K-PKE.Encrypt -/

/-- The end: `r15` as `allOk`, and the ciphertext if it is 1. -/
structure EOut (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if allOk L.k (rhoE L ek) (L.k * L.k) then 1 else 0
  ct : allOk L.k (rhoE L ek) (L.k * L.k) →
    bytesAt s.mem (pa s (sc L.oCT)) L.ctLen = KPke.ct L.p (aHat (rhoE L ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EOρ (L : Kem) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE L ek = ρ ∧ EOut L C E ek m r s

theorem v_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : KemCalls L wc wd) {C : Ctx rbs wbs}
    (hc : vChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EUρ L C E ρ L.k x ∧ EUρ L C E ρ L.k y) (v L A)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  have hc' := hc
  simp only [vChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hpc, hkw⟩, hac⟩, hdd⟩, _⟩, htw⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (v_ok hA K hc hx) fun _ ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP.b⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩
  unfold v
  refine RelCT.mono (RelCT.seqL (I := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))))
    (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (cbd2At_trL hA rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL hA Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k))) ∧ Reduced x.mem (pa x (pS 15))) C.bs
      (RelCT.mono (ddCall_trL (Codecs.ddI A.codecs) (d := 1) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL (Codecs.ddI A.codecs) Lx (d := 1) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hkw hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS (L.pU + L.k)))) C.bs (addAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL (K.ce A.codecs) (d := L.dv) rbx_na htw K.dv.1)))))
    (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
      ⟨hl, (h₁.w L.k (by omega_using []) (Nat.le_refl _)).1, (h₂.w L.k (by omega_using []) (Nat.le_refl _)).1⟩) fun _ _ h => h

end Enc

end VG.Proof.MlKem.X86_64

end

end


/-!
# ML-KEM on x86-64: K-PKE.Encrypt

`encrypt L`, from its inputs and `r15 = 1`: `r15` is 1 exactly when every
`SampleNTT` succeeded, and then the ciphertext is `K-PKE.Encrypt(ek, m, r)`
(`encrypt_ok`); for a given `ρ`, it leaks the same in two runs (`encrypt_tr`).
Every check of the pieces is one Boolean (`encChk`), which the callers
evaluate in their layouts, for each parameter set.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- Every check of `encrypt`. -/
def encChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  matChk L bs wbs chk E && (List.range (L.k * L.k / 4)).all (fun q => quadEChk L bs wbs chk E (4 * q)) &&
    (List.range (L.k * L.k)).all (fun e => !decide (4 * (L.k * L.k / 4) ≤ e) || sampEChk L bs wbs chk E e) &&
    inKeep L bs chk E [] && prfsEChk L bs wbs chk E &&
    (List.range (L.k * L.k)).all (fun e => keepB bs [] (pS (L.pA + e)) 1024) && keepB bs [] (sc oSB) 32 &&
    (List.range L.k).all (yChk L bs wbs chk E) && (List.range L.k).all (tChk L bs wbs chk E) &&
    emEChk L bs wbs chk E && (List.range L.k).all (uChk L bs wbs chk E) && vChk L bs wbs chk E

structure EncChks (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : matChk L bs wbs chk E = true
  q : ∀ q < L.k * L.k / 4, quadEChk L bs wbs chk E (4 * q) = true
  s : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → sampEChk L bs wbs chk E e = true
  inK : inKeep L bs chk E [] = true
  prfs : prfsEChk L bs wbs chk E = true
  aK : ∀ e < L.k * L.k, keepB bs [] (pS (L.pA + e)) 1024 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  y : ∀ N < L.k, yChk L bs wbs chk E N = true
  t : ∀ i < L.k, tChk L bs wbs chk E i = true
  mul : emEChk L bs wbs chk E = true
  u : ∀ i < L.k, uChk L bs wbs chk E i = true
  v : vChk L bs wbs chk E = true

theorem encChk_spec {bs wbs : List (Reg × Nat)} {chk : List (Ptr × Nat) → Bool} {E : Ptr}
    (h : encChk L bs wbs chk E = true) : EncChks L bs wbs chk E := by
  simp only [encChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hq⟩, hs⟩, h3⟩, hp⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, hq, fun e he he' => (hs e he).resolve_left (fun h => h he'), h3, hp, h4, h5, h6, h7, h8, h9, h10⟩

theorem rest_ok (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L) {C : Ctx rbs wbs}
    (hc : EncChks L (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte} {s : State} (h : ER0 L C E ek m r s) :
    WP isa (rest L v.callee E) s (EOut L C E ek m r) := by
  unfold rest
  refine WP.seq (WP.mono (prfsE_ok v W.k.2 hc.prfs h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER L C E ek m r k 0) L.k 0
    (fun k _ hk' s hs => WP.mono (y_ok v.arith (by omega_using [hk']) (hc.y k (by omega_using [hk'])) hs) fun _ h => h.2) s₀ h₀.2)
    fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER L C E ek m r L.k k) L.k 0
    (fun k _ hk' s hs => WP.mono (t_ok v.arith (by omega_using [hk']) (hc.t k (by omega_using [hk'])) hs) fun _ h => h.2) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  refine WP.seq (WP.mono (mul_ok v.arith W.k34 hc.mul h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => EU L C E ek m r k) L.k 0
    (fun k _ hk' s hs => WP.mono (u_ok v.arith K (by omega_using [hk']) (hc.u k (by omega_using [hk'])) hs) fun _ h => h.2) s₃ h₃.2)
    fun s₄ h₄ => ?_)
  rw [Nat.zero_add] at h₄
  exact WP.mono (v_ok v.arith K hc.v h₄) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, by rw [h15, ifp h₄.ok], fun _ => hct⟩

theorem encrypt_ok (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L)
    {C : Ctx rbs wbs} (hc : encChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : EIn L C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (encrypt L v.callee E) s (EOut L C E ek m r) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine WP.seq (WP.mono (mat_ok v W.k.2 hc.mat hc.q hc.s h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · exact rest_ok v K W hc (ER0.start (h₁.flag hP hc.inK hc.aK hc.sbK) (KeyGen.r15_ne h₁.m.r15 hne))
  · have h₂ := h₁.flag hP hc.inK hc.aK hc.sbK
    exact ⟨h₂.i.out, h₂.m.r15, fun ho => absurd ho (KeyGen.r15_eq h₁.m.r15 he)⟩

theorem rest_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L)
    {C : Ctx rbs wbs} (hc : EncChks L (rbs ++ wbs) wbs C.chk E) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ L C E ρ x ∧ ER0ρ L C E ρ y) (rest L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  unfold rest
  refine RelCT.seq (prfsE_tr v W.k.2 hc.prfs) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ L C E ρ k 0 x ∧ ERρ L C E ρ k 0 y) L.k 0
    fun k _ hk' => y_tr v.arith (by omega_using [hk']) (hc.y k (by omega_using [hk']))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k k x ∧ ERρ L C E ρ L.k k y) L.k 0
    fun k _ hk' => t_tr v.arith (by omega_using [hk']) (hc.t k (by omega_using [hk']))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (mul_tr v.arith W.k34 hc.mul) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ EUρ L C E ρ k x ∧ EUρ L C E ρ k y) L.k 0
    fun k _ hk' => u_tr v.arith K (by omega_using [hk']) (hc.u k (by omega_using [hk']))) ?_
  rw [Nat.zero_add]
  exact v_tr v.arith K hc.v

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L) {C : Ctx rbs wbs}
    (hc : encChk L (rbs ++ wbs) wbs C.chk E = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ L C E ρ x ∧ EIρ L C E ρ y) (encrypt L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine RelCT.seq (mat_tr v W.k.2 hc.mat hc.q hc.s W.ijT ht) (ifOk_tr
    (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (rest_tr v K W hc) ?_ fun _ _ h => h) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk L.k (rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, ER0.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, ER0.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk L.k (rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc.inK hc.aK hc.sbK
    have k₂ := h₂.flag hy hc.inK hc.aK hc.sbK
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.m.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.m.r15, fun h => absurd h o₂⟩⟩

end Enc

end VG.Proof.MlKem.X86_64
