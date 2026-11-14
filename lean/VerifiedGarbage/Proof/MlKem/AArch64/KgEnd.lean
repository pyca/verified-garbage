module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgC
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlKem.AArch64.KgT`, which only this module used -/

section

/-! ### `MlKem.AArch64.KgC2`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `keygen`, `ŝ` and `t̂`

`ŝ[j]` and its encoding into `dk` (`s_step`), then `ê[i]` and `t̂[i]` and its
encodings into `ek` and `dk` (`t_step`), each keeping what the steps before
established (`CInv`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[e]`'s buffer. -/
abbrev AR (s₀ : State) (e : Nat) : Addr := kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e)

/-- What phase C keeps: `ρ`, `σ`, `x24`, and `Â` as the matrix left it
(in `mB`). -/
structure CInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  kb : KB P s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK P s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = KPke.kgSigma P.params (dB s₀)
  x24 : s.gpr .x24 = v
  ahat : ∀ e < P.k * P.k, Reduced s.mem (AR s₀ e) ∧ polyAt s.mem (AR s₀ e) = polyAt mB (AR s₀ e)

/-- Memory changed only in `W`, which is apart from `ρ`, `σ` and `Â`. -/
theorem CInv.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {s s' : State} (h : CInv P s₀ mB v s)
    (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) : CInv P s₀ mB v s' := by
  have ha : ∀ e < P.k * P.k, ∀ r ∈ W, (polyRegion (AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show AR s₀ e = kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact sub_offset' (by omega_using [he]))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], fun e he => ⟨reduced_frame hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · rw [polyAt_frame hf (ha e he)]; exact (h.ahat e he).2

/-- A buffer apart from everything `(kgCbdNttWith keccak.callee)` writes. -/
theorem cnW_apart {s₀ : State} (hp : Pre P s₀) {off b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h : b ≠ 3 ∨ (840 ≤ o ∧ (o + l ≤ 912 ∨ 913 ≤ o) ∧ (o + l ≤ 928 ∨ 1056 ≤ o) ∧
      (o + l ≤ off ∨ off + 1024 ≤ o) ∧ (o + l ≤ 3104 ∨ 4128 ≤ o))) (ho : off + 1024 ≤ kL P 3) :
    ∀ r ∈ cnW s₀ off, (R (kA s₀) b o l).Disjoint r := by
  intro r hr
  rcases mem7 hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.ST]; omega_using [h]
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.WK]; omega_using [h]
  · exact below_R hp hb f
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.SG]; omega_using [h]
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.PB]; omega_using [h]
  · refine hp.args.rdisj hb (by decide) f ho ?_; omega_using [h]
  · refine hp.args.rdisj hb (by decide) f (by kl) ?_; simp only [KG.NS]; omega_using [h]

/-- `ρ`, `σ` and `Â` are apart from what `(kgCbdNttWith keccak.callee)` writes, for a polynomial past `Â`. -/
theorem cnW_far {s₀ : State} (hp : Pre P s₀) {off : Nat} (ho : SH P ≤ off ∧ off + 1024 ≤ SV P) :
    ∀ r ∈ cnW s₀ off, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r := by
  obtain ⟨ho1, ho2⟩ := ho
  have hoL : off + 1024 ≤ kL P 3 := by kl
  intro r hr
  exact ⟨cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) hoL r hr⟩

/-- A single buffer of `ek`, `dk` or past `Â` in `scratch` is apart from `ρ`, `σ` and `Â`. -/
theorem one_far {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h : b ≠ 3 ∨ SH P ≤ o) :
    ∀ r ∈ [R (kA s₀) b o l], (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact ⟨hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl),
    hp.args.rdisj (by decide) hb (by kl) f (by kl)⟩

/-- After `ŝ[j']` for `j' < j`. -/
structure SInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (j : Nat) (s : State) : Prop where
  c : CInv P s₀ mB v s
  sp : ∀ j' < j, PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j')) (KPke.kgS P.params (dB s₀) j')
  dk : ∀ j' < j, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j')) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j')

theorem s_step {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {j : Nat} (hj : j < P.k) {s : State}
    (h : SInv P s₀ mB v j s) : WP isa (P.kgSWith keccak.callee j) s (SInv P s₀ mB v (j + 1)) := by
  have hj' : SH P + 1024 * j + 1024 ≤ SV P := by kl
  have hpo : PolyOff P (sOff P j) := ⟨by kl, hj'⟩
  have hoL : sOff P j + 1024 ≤ kL P 3 := by kl
  have fd : 384 * j + 384 ≤ kL P 2 := by kl
  refine WP.seq (WP.mono (cbdNtt_ok hp (N := j) (off := sOff P j) (by kl) hpo h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  refine WP.mono (enc_ok hp (off := sOff P j) (b := 2) (o := 384 * j) hpo (.inr rfl) fd kb₁ p₁.1)
    fun s₂ ⟨kb₂, f₂, b₂, x₂⟩ => ?_
  have c₂ := (h.c.frame kb₁ x₁ f₁ (cnW_far hp ⟨by kl, hj'⟩)).frame kb₂ x₂ f₂
    (one_far hp (by decide) fd (.inl (by decide)))
  refine ⟨c₂, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · have hS : ∀ r ∈ [R (kA s₀) 2 (384 * j) 384], (R (kA s₀) 3 (sOff P j') 1024).Disjoint r := fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) fd (.inl (by decide))
    rcases (by omega_using [hj'] : j' < j ∨ j' = j) with hj' | rfl
    · refine polyIs_frame f₂ hS (polyIs_frame f₁ (cnW_apart hp (by decide)
        (by kl) (.inr (by kl)) hoL)
        (h.sp j' hj'))
    · exact polyIs_frame f₂ hS p₁
  · rcases (by omega_using [hj'] : j' < j ∨ j' = j) with hj' | rfl
    · rw [bytesAt_frame f₂ (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact hp.args.rdisj (by decide) (by decide) (by kl) fd (by omega_using [hj']))
          (by decide),
        bytesAt_frame f₁ (cnW_apart hp (by decide) (by kl) (.inl (by decide)) hoL)
          (by decide)]
      exact h.dk j' hj'
    · rw [b₂, p₁.2, KPke.kgS]

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-!
# ML-KEM on AArch64: `keygen`, `t̂`

`ê[i]`, `t̂[i]` and its encodings (`t_step`), keeping the facts established
before (`TL`), which every buffer the step writes is apart from (`Apart`).
The sum of products in `t̂[i]` is a loop over `j < k` (`WPs.dot`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- `Â[i, j]` as the matrix left it. -/
abbrev aM (P : KemLay) (s₀ : State) (mB : Mem) (i j : Nat) : Poly := polyAt mB (AR s₀ (P.k * i + j))

/-- `t̂[i]`. -/
abbrev tV (P : KemLay) (s₀ : State) (mB : Mem) (i : Nat) : Poly := KPke.kgT P.params (aM P s₀ mB) (dB s₀) i

/-- After `t̂[i']` for `i' < i`. -/
structure TL (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop where
  c : CInv P s₀ mB v s
  sp : ∀ j < P.k, PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff P j)) (KPke.kgS P.params (dB s₀) j)
  dk : ∀ j < P.k, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j)) 384 =
    encode12 (KPke.kgS P.params (dB s₀) j)
  ek : ∀ i' < i, bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * i')) 384 = encode12 (tV P s₀ mB i') ∧
    bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * P.k + 384 * i')) 384 = encode12 (tV P s₀ mB i')

/-- A region apart from what `TL i` describes. -/
def Apart (P : KemLay) (s₀ : State) (i : Nat) (r : Region) : Prop :=
  (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
    (R (kA s₀) 3 AH (1024 * (P.k * P.k) + 1024 * P.k)).Disjoint r ∧
    (R (kA s₀) 1 0 (384 * i)).Disjoint r ∧ (R (kA s₀) 2 0 (384 * P.k + 384 * i)).Disjoint r

theorem TL.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} {s s' : State}
    (h : TL P s₀ mB v i s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Apart P s₀ i r) : TL P s₀ mB v i s' := by
  have hw := hp.wf
  refine ⟨h.c.frame hk hx hf fun r hr => ⟨(hW r hr).1, (hW r hr).2.1,
    (hW r hr).2.2.1.sub_left (R.sub2 (Nat.le_refl _) (by omega_using []))⟩, fun j hj => ?_, fun j hj => ?_,
    fun i' hi' => ⟨?_, ?_⟩⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))) (h.sp j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hj; omega_using [hj]))) (by decide)]
    exact h.dk j hj
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hi'; omega_using [hi']))) (by decide)]
    exact (h.ek i' hi').1
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.sub_left (R.sub2 (by omega_using [])
      (by have := mul_succ_le (a := 384) hi'; omega_using [hi']))) (by decide)]
    exact (h.ek i' hi').2

/-- A buffer of `scratch` past `ŝ`, or the NTT's working space. -/
theorem apart_scr {s₀ : State} (hp : Pre P s₀) {i o l : Nat} (hi : i < P.k) (f : o + l ≤ kL P 3)
    (h : EP P ≤ o ∨ (o = 3104 ∧ l = 1024)) : Apart P s₀ i (R (kA s₀) 3 o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) (by kl) f (by kl),
    hp.args.rdisj (by decide) (by decide) hi' f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) hi'' f (.inl (by decide))⟩

theorem apart_cnW {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ cnW s₀ (EP P), Apart P s₀ i r := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  have ho : EP P + 1024 ≤ kL P 3 := by kl
  intro r hr
  exact ⟨cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) (by kl) (.inr (by kl)) ho r hr,
    cnW_apart hp (by decide) hi' (.inl (by decide)) ho r hr,
    cnW_apart hp (by decide) hi'' (.inl (by decide)) ho r hr⟩

theorem apart_ek {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 1 (384 * i) 384) := by
  have f : 384 * i + 384 ≤ kL P 1 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega_using []))),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide))⟩

theorem apart_dk {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    Apart P s₀ i (R (kA s₀) 2 (384 * P.k + 384 * i) 384) := by
  have f : 384 * P.k + 384 * i + 384 ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inl (by decide)),
    hp.args.rdisj (by decide) (by decide) (by kl) f (.inr (.inl (by omega_using [])))⟩

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : PolyOff P (aOff P i j) :=
  have := ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_s (hP : P.Wf) {j : Nat} (hj : j < P.k) : PolyOff P (sOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : PolyOff P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : PolyOff P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : PolyOff P (EP P) := ⟨by lom, by lom⟩

/-- `ê[i]`'s polynomial and `t̂[i]`'s are apart from what a product into `PP` writes. -/
theorem far_PP {s₀ : State} (hp : Pre P s₀) {o : Nat} (ho : o = EP P ∨ o = TP P) :
    ∀ r ∈ [R (kA s₀) 3 (PP P) 1024, R (kA s₀) 3 NS 1024],
      (polyRegion (kA s₀ 3 + BitVec.ofNat 64 o)).Disjoint r := by
  intro r hr
  rcases ho with rfl | rfl <;> rcases mem2' hr with rfl | rfl <;> rdisj

theorem far_TP {s₀ : State} (hp : Pre P s₀) :
    ∀ r ∈ [R (kA s₀) 3 (TP P) 1024, R (kA s₀) 3 NS 1024],
      (polyRegion (kA s₀ 3 + BitVec.ofNat 64 (EP P))).Disjoint r := by
  intro r hr
  rcases mem2' hr with rfl | rfl <;> rdisj

theorem apart_mul {s₀ : State} (hp : Pre P s₀) {i o : Nat} (hi : i < P.k) (ho : o = TP P ∨ o = PP P) :
    ∀ r ∈ [R (kA s₀) 3 o 1024, R (kA s₀) 3 NS 1024], Apart P s₀ i r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · rcases ho with rfl | rfl
    · exact apart_scr hp hi (by kl) (.inl (by kl))
    · exact apart_scr hp hi (by kl) (.inl (by kl))
  · exact apart_scr hp hi (by kl) (.inr ⟨rfl, rfl⟩)

theorem apart_TP {s₀ : State} (hp : Pre P s₀) {i : Nat} (hi : i < P.k) :
    ∀ r ∈ [R (kA s₀) 3 (TP P) 1024], Apart P s₀ i r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact apart_scr hp hi (by kl) (.inl (by kl))

/-- During `t̂[i]`: `TL i`, and `ê[i]` at `EP`. -/
abbrev TE (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop :=
  TL P s₀ mB v i s ∧ PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (EP P)) (KPke.kgE P.params (dB s₀) i)

/-- `Â[i, j] ŝ[j]` into `h` (`TP` or `PP`). -/
theorem prod_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i j h : Nat} (hi : i < P.k)
    (hj : j < P.k) (hh : h = TP P ∨ h = PP P) {s : State} (e : TE P s₀ mB v i s) :
    WP isa (kgMul h (aOff P i j) (sOff P j)) s fun s' => TE P s₀ mB v i s' ∧
      (∀ a, h = PP P → PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a →
        PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a) ∧
      PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 h)
        (multiplyNTTs (aM P s₀ mB i j) (KPke.kgS P.params (dB s₀) j)) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have a₁ : Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) ∧
      polyAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) = polyAt mB (kA s₀ 3 + BitVec.ofNat 64 (aOff P i j)) :=
    e.1.c.ahat (P.k * i + j) hij
  have s₁ := e.1.sp j hj
  have ph : PolyOff P h := by rcases hh with rfl | rfl; exacts [po_TP hw, po_PP hw]
  refine WP.mono (mul_ok hp (h := h) (f := aOff P i j) (g := sOff P j) ph (po_a hw hi hj) (po_s hw hj)
    (.inr (by rcases hh with rfl | rfl <;> lom)) (.inr (by rcases hh with rfl | rfl <;> lom)) e.1.c.kb a₁.1 s₁.1)
    fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_
  rw [a₁.2, s₁.2] at t₂
  have ho : h = TP P ∨ h = PP P := hh
  refine ⟨⟨e.1.frame hp kb₂ x₂ f₂ (apart_mul hp hi hh),
    polyIs_frame f₂ (by rcases ho with rfl | rfl; exacts [far_TP hp, far_PP hp (.inl rfl)]) e.2⟩,
    fun a ep ta => ?_, t₂⟩
  subst ep
  exact polyIs_frame f₂ (far_PP hp (.inr rfl)) ta

theorem t_step {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) {s : State}
    (h : TL P s₀ mB v i s) : WP isa (P.kgTWith keccak.callee i) s (TL P s₀ mB v (i + 1)) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (List.cons_ne_nil _ _) (WPs.cons ?_)
  refine WP.mono (cbdNtt_ok hp (N := P.k + i) (off := EP P) (by lom) (po_EP hw) h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, e₁, x₁⟩ => ?_
  have te₁ : TE P s₀ mB v i s₁ := ⟨h.frame hp kb₁ x₁ f₁ (apart_cnW hp hi), e₁⟩
  refine WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P) (E := TE P s₀ mB v i)
      (term := fun j h => [kgMul h (aOff P i j) (sOff P j)])
      (T := fun s a => PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) a)
      (Q := fun s a => PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (PP P)) a)
      (v := fun j => multiplyNTTs (aM P s₀ mB i j) (KPke.kgS P.params (dB s₀) j)) (N := P.k)
      (fun s e => WPs.single (WP.mono (prod_ok hp hi k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩))
      (fun j _ hj s a e t => WPs.single (WP.mono (prod_ok hp hi hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩))
      (fun s a b e t q => WP.mono (add_ok hp (f := TP P) (g := PP P) (po_TP hw) (po_PP hw) (.inl (by lom))
        e.1.c.kb t.1 q.1) fun s' ⟨kb', f', t', x'⟩ => ⟨⟨e.1.frame hp kb' x' f' (apart_TP hp hi),
          polyIs_frame f' (fun r hr => by rw [List.mem_singleton.mp hr]; rdisj) e.2⟩, by rw [t.2, q.2] at t'; exact t'⟩)
      k1 (Nat.le_refl _) te₁) ?_)
  intro s₂ ⟨⟨tl₂, e₂⟩, t₂⟩
  refine WPs.cons (WP.mono (add_ok hp (f := TP P) (g := EP P) (po_TP hw) (po_EP hw) (.inr (by lom)) tl₂.c.kb
    t₂.1 e₂.1) fun s₇ ⟨kb₇, f₇, t₇, x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (apart_TP hp hi)
  rw [t₂.2, e₂.2] at t₇
  have tv : PolyIs s₇.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) (tV P s₀ mB i) := t₇
  refine WPs.cons (WP.mono (enc_ok hp (off := TP P) (b := 1) (o := 384 * i) (po_TP hw) (.inl rfl)
    (by kl) kb₇ tv.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_ek hp hi
  have tv₈ := polyIs_frame f₈ (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WPs.single (WP.mono (enc_ok hp (off := TP P) (b := 2) (o := 384 * P.k + 384 * i) (po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈.1) fun s₉ ⟨kb₉, f₉, b₉, x₉⟩ => ?_)
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr => by rw [List.mem_singleton.mp hr]; exact apart_dk hp hi
  refine ⟨tl₉.c, tl₉.sp, tl₉.dk, fun i' hi' => ?_⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact tl₉.ek i' hi'
  · refine ⟨?_, by rw [b₉, tv₈.2]⟩
    rw [bytesAt_frame f₉ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide), b₈, tv.2]

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-!
# ML-KEM on AArch64: `keygen`, the end

The copies of `ρ` into `ek` and `dk`, `H(ek)` into `dk`, the copy of `z`, and
our caller's registers back (`end_ok`); then the bytes of `ek` and `dk` as the
standard puts them together (`ek_at`, `dk_at`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-! ## The bytes of `ek` and `dk` -/

/-- `n` encoded polynomials at `p`. -/
theorem cat_at {m : Mem} {p : Addr} {T : Nat → Poly} : ∀ {n : Nat},
    (∀ i < n, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i)) →
    bytesAt m p (384 * n) = KPke.catK (fun i => encode12 (T i)) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [Nat.mul_succ, bytesAt_add, cat_at fun i hi => h i (by omega_using [hi]), h n (by omega_using [])]
    exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm

variable {P : KemLay}

/-- `ek`'s bytes: the `k` `t̂[i]` and `ρ`, at `p`. -/
theorem ek_at {m : Mem} {p : Addr} {T : Nat → Poly} {ρ : List Byte}
    (h : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (384 * i)) 384 = encode12 (T i))
    (hr : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) 32 = ρ) :
    bytesAt m p P.ekLen = KPke.catK (fun i => encode12 (T i)) P.k ++ ρ := by
  rw [KemLay.ekLen, bytesAt_add, cat_at h, hr]

/-- `dk`'s bytes: `dk_PKE ‖ ek ‖ h ‖ z`, at `p`. -/
theorem dk_at {m : Mem} {p : Addr} {a b c d : List Byte} (ha : bytesAt m p (384 * P.k) = a)
    (hb : bytesAt m (p + BitVec.ofNat 64 (384 * P.k)) P.ekLen = b)
    (hc : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 32)) 32 = c)
    (hd : bytesAt m (p + BitVec.ofNat 64 (768 * P.k + 64)) 32 = d) : bytesAt m p P.dkLen = a ++ b ++ c ++ d := by
  have hc' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen)) 32 = c := by
    rw [show 384 * P.k + P.ekLen = 768 * P.k + 32 by simp only [KemLay.ekLen]; omega_using []]; exact hc
  have hd' : bytesAt m (p + BitVec.ofNat 64 (384 * P.k + P.ekLen + 32)) 32 = d := by
    rw [show 384 * P.k + P.ekLen + 32 = 768 * P.k + 64 by simp only [KemLay.ekLen]; omega_using []]; exact hd
  rw [show P.dkLen = 384 * P.k + P.ekLen + 32 + 32 by simp only [KemLay.ekLen, KemLay.dkLen]; omega_using [],
    bytesAt_add, bytesAt_add, bytesAt_add, ha, hb, hc', hd']

/-! ## Regions -/

/-- A buffer apart from what `TL i` describes. -/
theorem apart_R {s₀ : State} (hp : Pre P s₀) {i b o l : Nat} (hi : i ≤ P.k) (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b = 1 → 384 * i ≤ o) (h2 : b = 2 → 384 * P.k + 384 * i ≤ o) :
    Apart P s₀ i (R (kA s₀) b o l) := by
  have hi' : 0 + 384 * i ≤ kL P 1 := by kl
  have hi'' : 0 + (384 * P.k + 384 * i) ≤ kL P 2 := by kl
  refine ⟨hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb (by kl) f ?_,
    hp.args.rdisj (by decide) hb (by kl) f ?_, hp.args.rdisj (by decide) hb hi' f ?_,
    hp.args.rdisj (by decide) hb hi'' f ?_⟩ <;>
  · by_cases e : b = 3
    · have := h3 e; subst e; kl
    · by_cases e1 : b = 1
      · have := h1 e1; subst e1; kl
      · by_cases e2 : b = 2
        · have := h2 e2; subst e2; kl
        · kl

theorem apart_below {s₀ : State} (hp : Pre P s₀) (i : Nat) (hi : i ≤ P.k) : Apart P s₀ i (below s₀.sp 16) :=
  ⟨below_R hp (by decide) (by kl), below_R hp (by decide) (by kl), below_R hp (by decide) (by kl),
    below_R hp (by decide) (by kl), below_R hp (by decide) (by kl)⟩

/-! ## The end -/

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  ek : bytesAt s.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)
  dk : bytesAt s.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
    KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) ++ zB s₀

theorem pres_own : ∀ r ∈ preserved, r ∉ own → r ∉ [Reg.x0, .x30, .x24, .x25, .x26, .x27, .x28] := by decide

/-- Our caller's registers back, and the result. -/
theorem restore_ok {s₀ : State} (hp : Pre P s₀) {u : State} (hk : KB P s₀ u) :
    WP isa (.block [mov .x0 .x24, .ldr .x .x30 .x28 (SV P + 40), .ldr .x .x24 .x28 (SV P),
      .ldr .x .x25 .x28 (SV P + 8), .ldr .x .x26 .x28 (SV P + 16), .ldr .x .x27 .x28 (SV P + 24),
      .ldr .x .x28 .x28 (SV P + 32)]) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  have hsv : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  have cv := cov_r hp hk (b := 3) (o := SV P) (l := 48) (by decide) hp.sv
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (own.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega_using [hk']) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ 3 →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = kA s₀ 3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 5)) (by kl) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 0)) (by kl) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 1)) (by kl) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 2)) (by kl) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 3)) (by kl) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := kA s₀ 3 + BitVec.ofNat 64 (SV P + 8 * 4)) (by kl) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ own
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · rw [o₇.get r (pres_own r hr ho), hk.cs r hr ho]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁]

/-- What holds from the copies of `ρ` on. -/
structure EndInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  tl : TL P s₀ mB v P.k s
  rek : bytesAt s.mem (kA s₀ 1 + BitVec.ofNat 64 (384 * P.k)) 32 = rhoK P s₀
  rdk : bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k)) 32 = rhoK P s₀

/-- A region apart from what `EndInv` describes. -/
abbrev Far (P : KemLay) (s₀ : State) (r : Region) : Prop :=
  Apart P s₀ P.k r ∧ (R (kA s₀) 1 (384 * P.k) 32).Disjoint r ∧ (R (kA s₀) 2 (768 * P.k) 32).Disjoint r

theorem EndInv.frame {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s s' : State}
    (h : EndInv P s₀ mB v s) (hk : KB P s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region}
    (hf : Frame W s.mem s'.mem) (hW : ∀ r ∈ W, Far P s₀ r) : EndInv P s₀ mB v s' :=
  ⟨h.tl.frame hp hk hx hf fun r hr => (hW r hr).1,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.rek,
    by rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2) (by decide)]; exact h.rdk⟩

theorem far_R {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (h3 : b = 3 → o + l ≤ 840 ∨ EP P ≤ o) (h1 : b ≠ 1) (h2 : b = 2 → 768 * P.k + 32 ≤ o) :
    Far P s₀ (R (kA s₀) b o l) :=
  ⟨apart_R hp (Nat.le_refl _) hb f h3 (fun e => absurd e h1) (fun e => by have := h2 e; omega_using [this]),
    hp.args.rdisj (by decide) hb (by kl) f (.inl (Ne.symm h1)),
    hp.args.rdisj (by decide) hb (by kl) f (by
      by_cases e : b = 2
      · have := h2 e; subst e; omega_using [this]
      · exact .inl (Ne.symm e))⟩

theorem far_below {s₀ : State} (hp : Pre P s₀) : Far P s₀ (below s₀.sp 16) :=
  ⟨apart_below hp P.k (Nat.le_refl _), below_R hp (by decide) (by kl), below_R hp (by decide) (by kl)⟩

/-- `ρ` into `ek` and `dk`. -/
theorem rho_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL P s₀ mB v P.k s) :
    WP isa (.block (copy32 .x28 SB .x26 (384 * P.k) ++ copy32 .x28 SB .x27 (768 * P.k))) s fun s' =>
      KB P s₀ s' ∧ EndInv P s₀ mB v s' := by
  have hw := hp.wf
  have kb := h.c.kb
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 1) (so := SB) (dO := 384 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x26 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 1) (by decide) (by kl))) fun sa ⟨ka, fa, ba⟩ => ?_
  have kba := kb.frame ka fa (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 1) (o := 384 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have tla := h.frame hp kba (ka.get .x24) fa fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 1) (o := 384 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (fun _ => Nat.le_refl _) (by kl)
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := SB) (dO := 768 * P.k) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kba.x28 kba.x27 (cov_r hp kba (b := 3) (by decide) (by kl))
    (cov_w hp kba (b := 2) (by decide) (by kl))) fun sb ⟨kb', fb, bb⟩ => ?_
  have kbb := kba.frame kb' fb (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  refine ⟨kbb, tla.frame hp kbb (kb'.get .x24) fb (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact apart_R hp (b := 2) (o := 768 * P.k) (l := 32) (Nat.le_refl _) (by decide) (by kl) (by kl)
      (by kl) (fun _ => by omega_using [])), ?_, ?_⟩
  · rw [bytesAt_frame fb (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide), ba]
    exact h.c.rho
  · rw [bb, bytesAt_frame fa (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact h.c.rho

/-- `H(ek)` into `dk`. -/
theorem hek_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (kb : KB P s₀ s)
    (h : EndInv P s₀ mB v s) :
    WP isa (hashWith keccak.callee .x28 ST WK 136 6 [⟨.x26, 0, P.ekLen⟩] [⟨.x27, 768 * P.k + 32, 32⟩]) s
      fun s' => KB P s₀ s' ∧ EndInv P s₀ mB v s' ∧
      bytesAt s'.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
        H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
  have hw := hp.wf
  have e28 : ∀ o, s.gpr .x28 + BitVec.ofNat 64 o = kA s₀ 3 + BitVec.ofNat 64 o := fun o => by rw [kb.x28]
  refine WP.mono (hashWith_ok keccak (hsetup hp kb (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x26, 0, P.ekLen⟩]) (outs := [⟨.x27, 768 * P.k + 32, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 1) hp kb (by decide) (by kl) (by decide) (by kl) (by decide))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (b := 2) hp kb (by decide) (by kl) (by kl) (by decide) (by decide))
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ?_
  have kb' := kb.hash hp k' fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨2, 768 * P.k + 32, 32, rfl, by decide, by decide, by kl, .inl (by decide)⟩
  have msg : (List.map (pbytes s) [⟨.x26, 0, P.ekLen⟩]).flatten = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      kb.x26, ptr_zero]
    exact ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.tl.ek i hi).1) h.rek
  obtain ⟨o, -⟩ := o'
  rw [msg, kb.x27] at o
  refine ⟨kb', h.frame hp kb' (k'.cs _ (by decide) (by decide)) k'.frame fun r hr => ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil] at hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · rw [VG.Proof.MlKem.AArch64.STr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [VG.Proof.MlKem.AArch64.WKr, e28]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
    · rw [kb.sp]; exact far_below hp
    · simp only [preg, kb.x27]
      exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  · rw [o, H_eq]; rfl

/-- `z` into `dk`, and the rest. -/
theorem end_ok {s₀ : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {s : State} (h : TL P s₀ mB v P.k s) :
    WP isa (P.kgEndWith keccak.callee) s (Done P s₀ mB v) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (rho_ok hp h) fun s₁ ⟨kb₁, h₁⟩ => WP.seq (WP.mono (hek_ok hp kb₁ h₁)
    fun s₂ ⟨kb₂, h₂, hh₂⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  have kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  have far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  have h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  have hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 =
      H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  have z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  have ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) :=
    ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  have dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      KPke.ekPKE P.params (aM P s₀ mB) (dB s₀) ++ H (KPke.ekPKE P.params (aM P s₀ mB) (dB s₀)) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tV P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega_using []]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

end VG.Proof.MlKem.AArch64.KeyGen
