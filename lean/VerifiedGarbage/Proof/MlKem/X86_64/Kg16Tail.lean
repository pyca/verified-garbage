module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
public import VerifiedGarbage.Proof.MlKem.X86_64.KgCT
public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: key generation with 16-bit polynomials, after the samples

When `Â`, `s` and `e` are sampled as `u16`s (`KRest16`): `vg_mlkem*_kpke_keygen`
writes `t̂` and `ŝ`, encoded, to the keys (`kgCore_eq`: as `K-PKE.KeyGen`
states them), and the rest of the keys is as with polynomials of `u32`s
(`KeyGen.fin_ok`): `tail_ok`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem w16_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 o + BitVec.ofNat 64 (32 * 16 * j) = p + BitVec.ofNat 64 (o + 512 * j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * 16 * j = 512 * j by omega]

/-- The matrix of `u16`s from `aP`, from its entries. -/
theorem matAtW_eq {k : Nat} {m : Mem} {aP : Addr} {a : Nat → Nat → Poly}
    (hA : ∀ i < k, ∀ j < k, polyAtW 16 m (aP + BitVec.ofNat 64 (512 * (k * i + j))) = a i j) :
    matAtW 16 m aP k = matrix k a := by
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  rw [w16_off, show 32 * 16 * (k * i) + 512 * j = 512 * (k * i + j) by omega]
  exact hA i (List.mem_range.mp hi) j (List.mem_range.mp hj)

/-- What `vg_mlkem*_kpke_keygen` writes, as `K-PKE.KeyGen` states it: `t̂` and `ŝ`, encoded. -/
theorem kgCore_eq {L : Kem} {m : Mem} {aP se : Addr} {a : Nat → Nat → Poly} {d : List Byte}
    (hA : ∀ i < L.k, ∀ j < L.k, polyAtW 16 m (aP + BitVec.ofNat 64 (512 * (L.k * i + j))) = a i j)
    (hS : ∀ N < 2 * L.k, polyAtW 16 m (se + BitVec.ofNat 64 (512 * N)) = cbd (KPke.kgSigma L.p d) N) :
    encodeVec (addVec (mulMatVec (matAtW 16 m aP L.k) (sHatW m se L.k)) (eHatW m se L.k)) =
        KPke.catK (fun i => encode12 (KPke.kgT L.p a d i)) L.k ∧
      encodeVec (sHatW m se L.k) = KPke.catK (fun j => encode12 (KPke.kgS L.p d j)) L.k := by
  have eS : sHatW m se L.k = (List.range L.k).map (KPke.kgS L.p d) := by
    simp only [sHatW, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgS]
    rw [show 32 * 16 * j = 512 * j by omega, hS j (by have := List.mem_range.mp hj; omega)]
  have eE : eHatW m se L.k = (List.range L.k).map (KPke.kgE L.p d) := by
    simp only [eHatW, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgE]
    rw [w16_off, ← Nat.mul_add, hS _ (by have := List.mem_range.mp hj; omega)]
  rw [matAtW_eq hA, eS, eE, KPke.mulMatVec_matrix, KPke.addVec_map, KPke.catK_eq, KPke.catK_eq]
  simp only [encodeVec, List.flatMap_map]
  exact ⟨rfl, trivial⟩

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

variable (K : Kem16)

/-- What `vg_mlkem*_kpke_keygen` writes. -/
abbrev kpW : List (Ptr × Nat) :=
  [((.r12, 0), 384 * K.L.k), ((.r13, 0), 384 * K.L.k), (sc K.oR, 1024 * K.L.k), (sc K.oZ, kScrE)]

/-- What key generation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Kg16Wf : Prop extends KgWfB K.L where
  kp : kpChk (kgB K.L) (kgW K.L) K.L (.r12, 0) (.r13, 0) (sc K.oA) (sc K.oR) (sc K.oZ) = true
  kpK : kcChk K.L (kpW K) = true
  kpG : keepB (kgB K.L) (kpW K) (sc oG) 32 = true

instance : CoeOut (Kg16Wf K) (KgWfB K.L) := ⟨Kg16Wf.toKgWfB⟩

/-- After the outputs of `PRF₂` and the first `n` of `s ‖ e`, as `u16`s. -/
structure KRest16 (n : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoK K.L σ) (e / K.L.k) (e % K.L.k))
  prf : ∀ N < 2 * K.L.k, bytesAt s.mem (pa s (prfO K N)) 128 =
    prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ N < n, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

theorem sc_w16 (s : State) (o e : Nat) :
    pa s (sc o) + BitVec.ofNat 64 (32 * 16 * e) = pa s (sc (o + 512 * e)) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * 16 * e = 512 * e by omega]

theorem sc_512 (s : State) (o e : Nat) : pa s (sc o) + BitVec.ofNat 64 (512 * e) = pa s (sc (o + 512 * e)) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

omit W hp in
theorem KRest16.redA {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    VecReducedW 16 s.mem (pa s (sc K.oA)) (K.L.k * K.L.k) := fun e he => by
  rw [sc_w16]; exact (h.mat e he).1

omit W hp in
theorem KRest16.redS {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k) := fun N hN => by
  rw [sc_w16]; exact (h.se N hN).1

/-- `t̂` and `ŝ`, encoded to the keys. -/
theorem core_ok (hK : KpkeOk K.L) {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    WP isa (K.L.kpkeKgAt (.r12, 0) (.r13, 0) (sc K.oA) (sc K.oR) (sc K.oZ)) s (KFinPre K.L σ) := by
  have L₀ := h.kc.lay W hp
  refine WP.mono (kpkeKgAt_okL hK L₀ r13_na rbx_na rbx_na rbx_na W.kp h.redA h.redS)
    fun s' ⟨hP, hek, hdk⟩ => ?_
  have hc := kgCore_eq (L := K.L) (m := s.mem) (aP := pa s (sc K.oA)) (se := pa s (sc K.oR))
    (a := aHat (rhoK K.L σ)) (d := kgD σ)
    (fun i hi j hj => by
      have := (h.mat (K.L.k * i + j) (ij_lt hi hj)).2
      rwa [(divmod_ij hj).1, (divmod_ij hj).2, aP, ← sc_512] at this)
    (fun N hN => by have := (h.se N hN).2; rwa [rP, ← sc_512] at this)
  refine ⟨h.kc.step W hp hP.b W.kpK, by rw [L₀.keepBytes hP.b W.kpG]; exact h.rho,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, ?_, ?_⟩
  · rw [hP.pa r12_cs, hek, hc.1]
  · rw [hP.pa r13_cs, hdk, hc.2]

/-- `ŝ`, `t̂` encoded to the keys, and the keys' last pieces. -/
theorem tail_ok (hK : KpkeOk K.L) {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    WP isa (kgTail K) s (KFin K.L σ) :=
  WP.seq (WP.mono (core_ok W hp hK h) fun _ h' => fin_ok W hp h')

end

theorem tail_tr {K : Kem16} (hK : KpkeOk K.L) (W : Kg16Wf K) :
    RelCT isa (Rel2 (keyGenK K.L).pre (keyGenK K.L).pub (KRest16 K (2 * K.L.k))) (kgTail K) fun _ _ => True := by
  unfold kgTail
  refine RelCT.seq (relInv (I' := KFinPre K.L) (fun σ s hp hs => core_ok W hp hK hs)
    (rel2_of (kpkeKgAt_trL hK r13_na rbx_na rbx_na rbx_na W.kp)
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, ⟨h₁.redA, h₁.redS⟩,
        ⟨h₂.redA, h₂.redS⟩⟩)) ?_
  exact RelCT.mono (fin_tr W fun h => h.kc) (fun _ _ h => h) fun _ _ _ => trivial

end KeyGen16

end VG.Proof.MlKem.X86_64
