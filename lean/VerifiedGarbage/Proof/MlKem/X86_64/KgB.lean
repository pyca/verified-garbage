module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgA
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

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
      bytesAt_catK m s r o c f k fun i hi => h i (by omega), h k (by omega)]

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
  refine WP.mono (v.prfs_ok L₀ (kgB_bases L) (by have := W.k; omega) hpc) fun s' ⟨hP, hb⟩ => ?_
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
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
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
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4096 + 1024 * a + 1024 * j = 4096 + 1024 * (a + j) by omega]

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
    rw [pS_add, Nat.zero_add]; exact (h.se j (by omega)).1
  have redA : VecReduced s.mem (pa s (pS L.pA)) (L.k * L.k) := fun e he => by rw [pS_add]; exact (h.mat e he).1
  have redE : VecReduced s.mem (pa s (pS L.k)) L.k := fun i hi => by rw [pS_add]; exact (h.se (L.k + i) (by omega)).1
  refine WP.mono (kgMulAt_okL hA W.k34 L₀ rbx_na rbx_na rbx_na rbx_na W.km redS redA redE)
    fun s' ⟨hP, hS, hT⟩ => ⟨h.kc.step W hp hP.b W.kmK, by rw [L₀.keepBytes hP.b W.kmG]; exact h.rho,
      by rw [hP.cs .r15 (by decide)]; exact h.r15, fun j hj => ?_, fun i hi => ?_,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := hS.2 j hj
    rw [pS_add, Nat.zero_add, KgMul.getD_get _ (by rw [List.length_map, vecAt_length]; exact hj),
      vecAt_map_get _ _ hj, pS_add, Nat.zero_add, (h.se j (by omega)).2] at this
    rw [hP.pa rbx_cs]; exact this
  · have := hT.2 i hi
    rw [pS_add, kgT_of hi (fun j hj => (h.matIJ hi hj).2) (fun j hj => (h.se j (by omega)).2)
        (h.se (L.k + i) (by omega)).2] at this
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
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
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
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
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
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega,
      bytesAt_split, bytesAt_split, bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₄.pa (p := (.r13, 384 * L.k + L.ekLen + 32)) r13_cs, hb₄,
      L₃.keepBytes hP₄.b W.dkH, hP₃.pa (p := (.r13, 384 * L.k + L.ekLen)) r13_cs, hb₃,
      L₂.keepBytes hP'.b W.dkE, hP₂.pa (p := (.r13, 384 * L.k)) r13_cs, hb₂, dkK, KPke.dkPKE]
    rw [L₀.keepBytes hP.b W.dkS]
    exact congrArg (· ++ _ ++ _ ++ _) h.dk

end KeyGen

end VG.Proof.MlKem.X86_64
