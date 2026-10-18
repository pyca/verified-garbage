module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16Tail
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: K-PKE.Encrypt with 16-bit polynomials, after the samples

When `Â` and `y ‖ e₁ ‖ e₂` are sampled as `u16`s (`ER16`), in the layout of
encapsulation or decapsulation (`Ctx`), `vg_mlkem*_kpke_encrypt` writes the
ciphertext (`encCt_eq`: as `K-PKE.Encrypt` states it) to `Cp`: `tail_ok`,
and its constant time, `tail_tr`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What `vg_mlkem*_kpke_encrypt` writes, as `K-PKE.Encrypt` states it. -/
theorem encCt_eq {L : Kem} {m : Mem} {aP tP rP mP : Addr} {a : Nat → Nat → Poly} {ek msg r : List Byte}
    (hA : ∀ i < L.k, ∀ j < L.k, polyAtW 16 m (aP + BitVec.ofNat 64 (512 * (L.k * i + j))) = a i j)
    (hT : bytesAt m tP (384 * L.k) = ek.take (384 * L.k))
    (hR : ∀ N < 2 * L.k + 1, polyAtW 16 m (rP + BitVec.ofNat 64 (512 * N)) = cbd r N)
    (hM : bytesAt m mP 32 = msg) :
    encCt L m aP tP rP mP = KPke.ct L.p a ek msg r := by
  have eY : (vecAtW 16 m rP L.k).map ntt = (List.range L.k).map (encY r) := by
    simp only [vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, encY]
    rw [show 32 * 16 * j = 512 * j by omega, hR j (by have := List.mem_range.mp hj; omega)]
  have eE : vecAtW 16 m (rP + BitVec.ofNat 64 (512 * L.k)) L.k = (List.range L.k).map fun i => cbd r (L.k + i) := by
    simp only [vecAtW]
    refine List.map_congr_left fun j hj => ?_
    rw [w16_off, ← Nat.mul_add, hR _ (by have := List.mem_range.mp hj; omega)]
  have e2 : polyAtW 16 m (rP + BitVec.ofNat 64 (1024 * L.k)) = cbd r (2 * L.k) := by
    rw [show 1024 * L.k = 512 * (2 * L.k) by omega, hR _ (by omega)]
  simp only [encCt]
  rw [matAtW_eq hA, hT, hM, eY, eE, e2, KPke.decodeVec_take, KPke.mulMatTVec_matrix, List.map_map,
    KPke.addVec_map, KPke.dot_eq_dotK, KPke.ct, KPke.catK_eq, List.flatMap_map]
  simp only [Function.comp, KPke.encU, KPke.encV]

namespace Enc16

open Enc VG.Impl.MlKem.X86_64.Top16

variable {rbs wbs : List (Reg × Nat)} (K : Kem16)

/-- After the outputs of `PRF₂` and the first `n` of `y ‖ e₁ ‖ e₂`, as `u16`s,
when every `SampleNTT` succeeded. -/
structure ER16 (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (n : Nat) (s : State) : Prop where
  i : EIn K.L C E ek m r s
  r15 : s.gpr .r15 = 1
  ok : allOk K.L.k (rhoE K.L ek) (K.L.k * K.L.k)
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoE K.L ek) (e / K.L.k) (e % K.L.k))
  prf : ∀ N < 2 * K.L.k + 1, bytesAt s.mem (pa s (prfO K N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  rr : ∀ N < n, PolyIsW 16 s.mem (pa s (rP K N)) (cbd r N)

/-- What `vg_mlkem*_kpke_encrypt` writes. -/
abbrev keW (Cp : Ptr) : List (Ptr × Nat) :=
  [(Cp, K.L.ctLen), (sc K.oR, 512 * (2 * K.L.k + 1)), (sc K.oZ, kScrE)]

/-- The call of `vg_mlkem*_kpke_encrypt`, in the layout, keeping the context. -/
def tailChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E Cp : Ptr) : Bool :=
  keChk bs wbs K.L Cp (sc K.oA) E (sc K.oR) (sc oM) (sc K.oZ) && chk (keW K Cp)

variable {K}

theorem ER16.redA {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State} (h : ER16 K C E ek m r (2 * K.L.k + 1) s) :
    VecReducedW 16 s.mem (pa s (sc K.oA)) (K.L.k * K.L.k) := fun e he => by
  rw [KeyGen16.sc_w16]; exact (h.mat e he).1

theorem ER16.redR {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State} (h : ER16 K C E ek m r (2 * K.L.k + 1) s) :
    VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k + 1) := fun N hN => by
  rw [KeyGen16.sc_w16]; exact (h.rr N hN).1

/-- The ciphertext, to `Cp`. -/
theorem tail_ok (hK : KpkeOk K.L) {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E) (hCp : Cp.1 ∈ calleeSaved)
    (hc : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true) {ek m r : List Byte} {s : State}
    (h : ER16 K C E ek m r (2 * K.L.k + 1) s) :
    WP isa (K.L.kpkeEncAt Cp (sc K.oA) E (sc K.oR) (sc oM) (sc K.oZ)) s fun s' => PPostB s s' (keW K Cp) ∧
      C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' Cp) K.L.ctLen = KPke.ct K.L.p (aHat (rhoE K.L ek)) ek m r := by
  simp only [tailChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (kpkeEncAt_okL hK L₀ rbx_na hE rbx_na rbx_na rbx_na hc.1 h.redA h.redR) fun s' ⟨hP, hct⟩ =>
    ⟨hP.b, C.step h.i.out hP.b hc.2, by rw [hP.cs .r15 (by decide)]; exact h.r15, ?_⟩
  rw [hP.pa hCp, hct]
  refine encCt_eq (fun i hi j hj => ?_) ?_ (fun N hN => ?_) h.i.m
  · have := (h.mat (K.L.k * i + j) (ij_lt hi hj)).2
    rw [(divmod_ij hj).1, (divmod_ij hj).2, aP, ← KeyGen16.sc_512] at this
    exact this
  · rw [← bytesAt_take _ _ (show 384 * K.L.p.k ≤ 384 * K.L.p.k + 32 from Nat.le_add_right _ _)]
    exact congrArg (List.take (384 * K.L.k)) h.i.ek
  · have := (h.rr N hN).2
    rw [rP, ← KeyGen16.sc_512] at this
    exact this

/-- The end of K-PKE.Encrypt: `r15` as `allOk`, and the ciphertext at `Cp` if it is 1. -/
structure EOut16 (K : Kem16) (C : Ctx rbs wbs) (Cp : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if allOk K.L.k (rhoE K.L ek) (K.L.k * K.L.k) then 1 else 0
  ct : allOk K.L.k (rhoE K.L ek) (K.L.k * K.L.k) →
    bytesAt s.mem (pa s Cp) K.L.ctLen = KPke.ct K.L.p (aHat (rhoE K.L ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EO16ρ (K : Kem16) (C : Ctx rbs wbs) (Cp : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE K.L ek = ρ ∧ EOut16 K C Cp ek m r s

/-- After the samples, for the `ρ` of `ek`. -/
abbrev ER16ρ (K : Kem16) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (n : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE K.L ek = ρ ∧ ER16 K C E ek m r n s

theorem tail_tr (hK : KpkeOk K.L) {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E) (hCp : Cp.1 ∈ calleeSaved)
    (hc : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER16ρ K C E ρ (2 * K.L.k + 1) x ∧ ER16ρ K C E ρ (2 * K.L.k + 1) y)
      (K.L.kpkeEncAt Cp (sc K.oA) E (sc K.oR) (sc oM) (sc K.oZ))
      (fun x y => LRel rbs wbs x y ∧ EO16ρ K C Cp ρ x ∧ EO16ρ K C Cp ρ y) := by
  have hc' := hc
  simp only [tailChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (kpkeEncAt_trL hK rbx_na hE rbx_na rbx_na rbx_na hc'.1)
    (fun _ _ ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ => ⟨hl, ⟨h₁.redA, h₁.redR⟩, ⟨h₂.redA, h₂.redR⟩⟩)
    fun _ _ h => h) fun x ⟨ek, m, r, eρ, hx⟩ => ?_
  exact WP.mono (tail_ok hK hE hCp hc hx) fun x' ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩

end Enc16

end VG.Proof.MlKem.X86_64
