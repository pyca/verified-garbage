module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps

import VerifiedGarbage.Proof.MlKem.AArch64.KemB

/-!
# ML-KEM on AArch64: K-PKE.Encrypt after the matrix

`ŷ`, `u` into the ciphertext, and `v` into it, with `r` at `RB`, `m` at `MB`,
`Â` as the matrix left it, `t̂` decoded from the bytes of `ek` in a buffer the
function only reads, and the ciphertext in a written buffer (`EncArgs`). What
each step establishes survives the steps after it (`EInvW`), as they write
only apart from it (`Far`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : Layout}

/-- `u[i]`'s bytes end within the first `k` ones. -/
theorem du_le {P : KemLay} {i : Nat} (hi : i < P.k) : 32 * P.du * i + 32 * P.du ≤ 32 * (P.du * P.k) := by
  rw [← Nat.mul_assoc]; exact mul_succ_le hi

/-- Where `ek` and the ciphertext are: bytes `[eo, eo + 384 k)` of the read
buffer in `slotReg kE`, and bytes `[co, co + ctLen)` of the written buffer in
`slotReg kC` (in `scratch`, at `CB`). -/
structure EncArgs (P : KemLay) (L : Layout) (kE eo kC co : Nat) : Prop where
  hkE : kE < 4
  rE : L.slot kE < L.nrd
  fE : eo + 384 * P.k ≤ L.len (L.slot kE)
  hkC : kC < 4
  wC : L.nrd ≤ L.slot kC
  fC : co + P.ctLen ≤ L.len (L.slot kC)
  sC : L.slot kC ≠ L.sc ∨ co = CB P

/-- `Â` as the matrix left it in `mB`, with 16-bit coefficients (`w16`) or 32-bit ones. -/
abbrev aMW (w16 : Bool) (P : KemLay) (L : Layout) (s₀ : State) (mB : Mem) (i j : Nat) : Poly :=
  polyAtW (cw w16) mB (sA L s₀ (aOff P i j))

/-- All that `K-PKE.Encrypt` writes: the Keccak state and working space,
`N`, `scratch` past `r ‖ N` and `K'` and `K̄`, the stack below the stack
pointer, and the ciphertext. -/
abbrev encW (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) : List Region :=
  [R (kA s₀) L.sc 0 840, R (kA s₀) L.sc (RB + 32) 1, R (kA s₀) L.sc PB (SV P - PB), below s₀.sp 16,
    R (kA s₀) (L.slot kC) co P.ctLen]

/-- After `ŷ[j]` for `j < nY` and `u[i]` for `i < nU`, from memory `mE`, with `Â` and `ŷ`
stored with 16-bit coefficients (`w16`) or 32-bit ones. -/
structure EInvW (w16 : Bool) (P : KemLay) (L : Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem)
    (v : BitVec 64) (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (sA L s₀ MB) 32 = mv
  a : ∀ i < P.k, ∀ j < P.k, ReducedW (cw w16) s.mem (sA L s₀ (aOff P i j)) ∧
    polyAtW (cw w16) s.mem (sA L s₀ (aOff P i j)) = aMW w16 P L s₀ mB i j
  y : ∀ j < nY, PolyIsW (cw w16) s.mem (sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (aMW w16 P L s₀ mB) rv i)
  fr : Frame (encW P L s₀ kC co) mE s.mem

/-- A region apart from what `EInvW` describes. -/
def Far (P : KemLay) (L : Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (kA s₀) L.sc RB 32).Disjoint r ∧ (R (kA s₀) L.sc MB 32).Disjoint r ∧
    (R (kA s₀) L.sc AH (1024 * (P.k * P.k))).Disjoint r ∧ (R (kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ encW P L s₀ kC co, Region.Sub r r'

theorem EInvW.frame {w16 : Bool} {s₀ : State} (hp : Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : EInvW w16 P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, Far P L s₀ kC co nY nU r) : EInvW w16 P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · have hij := ij_lt hi hj
    have hd : ∀ r ∈ W, (polyRegion (sA L s₀ (aOff P i j))).Disjoint r := fun r hr =>
      (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))
    exact ⟨reducedW_frame hf hd (h.a i hi j hj).1, by rw [polyAtW_frame hf hd]; exact (h.a i hi j hj).2⟩
  · exact polyIsW_frame_poly hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega_using []) (by simp only [yOff]; omega_using [hj]))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.1.sub_left
      (R.sub2 (by omega_using []) (by have := mul_succ_le (a := 32 * P.du) hi; omega_using [this]))) (by kom)]
    exact h.u i hi

/-- A buffer of `scratch` apart from what `EInvW` describes. -/
theorem far_s {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {nY nU o l : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) (f : o + l ≤ SV P)
    (h : (o + l ≤ RB ∨ RB + 32 ≤ o) ∧ (o + l ≤ MB ∨ MB + 32 ≤ o) ∧
      (o + l ≤ AH ∨ AH + 1024 * (P.k * P.k) ≤ o) ∧ (o + l ≤ YH P ∨ YH P + 1024 * nY ≤ o) ∧ (o + l ≤ CB P) ∧
      (o + l ≤ 840 ∨ (o = RB + 32 ∧ l = 1) ∨ PB ≤ o)) :
    Far P L s₀ kC co nY nU (R (kA s₀) L.sc o l) := by
  have hw := hp.wf
  have f' : o + l ≤ SV P + 48 := by omega_using [f]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  refine ⟨sdisj hp (by lom) f' (by omega_using [h1]), sdisj hp (by lom) f' (by omega_using [h2]),
    sdisj hp (by lom) f' (by omega_using [h3]), sdisj hp (by lom) f' (by omega_using [h4]),
    hp.args.rdisj (hp.lt A.hkC) hp.scb (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom)
      (hp.fs f') (.inr (.inr hp.scw)) ?_, ?_⟩
  · rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inr (by subst hC; omega_using [h5]))
  · rcases h6 with h6 | ⟨rfl, rfl⟩ | h6
    · exact ⟨_, List.mem_cons_self .., R.sub2 (by omega_using []) (by omega_using [h6])⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        R.sub2 h6 (by simp only [PB] at h6 ⊢; omega_using [f])⟩

theorem far_below {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co)
    {nY nU : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : Far P L s₀ kC co nY nU (below s₀.sp 16) := by
  have hw := hp.wf
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  exact ⟨below_R hp hp.scb (hp.fs (by lom)), below_R hp hp.scb (hp.fs (by lom)),
    below_R hp hp.scb (hp.fs (by lom)), below_R hp hp.scb (hp.fs (by lom)),
    below_R hp (hp.lt A.hkC) (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom),
    ⟨_, by simp, fun _ h => h⟩⟩

/-- Bytes of a buffer the function only reads, as they were. -/
theorem KB.ro_bytes {s₀ s : State} (h : KB P L s₀ s) {b o n : Nat} (hb : b < L.nrd) (f : o + n ≤ L.len b) :
    bytesAt s.mem (kA s₀ b + BitVec.ofNat 64 o) n = bytesAt s₀.mem (kA s₀ b + BitVec.ofNat 64 o) n := by
  rw [← bytesAt_slice _ _ f, ← bytesAt_slice _ _ f, h.ro b hb]

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : PO P (aOff P i j) :=
  have := ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_y (hP : P.Wf) {j : Nat} (hj : j < P.k) : PO P (yOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : PO P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : PO P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : PO P (EP P) := ⟨by lom, by lom⟩

/-- A polynomial buffer of `scratch` that `K-PKE.Encrypt` writes. -/
theorem far_w {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    Far P L s₀ kC co nY nU (R (kA s₀) L.sc off 1024) :=
  have := hp.wf
  far_s hp A hnY hnU (by lom) (by lom)

theorem far_ns {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : Far P L s₀ kC co nY nU (R (kA s₀) L.sc NS 1024) :=
  have := hp.wf
  far_s hp A hnY hnU (by lom) (by lom)

theorem far_pcW {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ pcW L s₀ off, Far P L s₀ kC co nY nU r := by
  have := hp.wf
  intro r hr
  rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_below hp A hnY hnU
  · exact far_s hp A hnY hnU (by lom) ⟨.inr (by decide), .inr (by decide), .inl (by decide), .inl (by lom),
      by lom, .inr (.inl ⟨rfl, rfl⟩)⟩
  · exact far_s hp A hnY hnU (by lom) (by lom)
  · exact far_w hp A hnY hnU h1 h2

theorem far_mul {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024, R (kA s₀) L.sc NS 1024], Far P L s₀ kC co nY nU r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · exact far_w hp A hnY hnU h1 h2
  · exact far_ns hp A hnY hnU

theorem far_one {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (kA s₀) L.sc off 1024], Far P L s₀ kC co nY nU r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact far_w hp A hnY hnU h1 h2

/-- Two polynomial buffers of `scratch` apart. -/
theorem papart {s₀ : State} (hp : Pre P L s₀) {o₁ o₂ : Nat} (h₁ : PO P o₁) (h₂ : PO P o₂)
    (h : o₁ + 1024 ≤ o₂ ∨ o₂ + 1024 ≤ o₁) : (polyRegion (sA L s₀ o₁)).Disjoint (R (kA s₀) L.sc o₂ 1024) :=
  sdisj hp h₁.le h₂.le h

/-! ## `u` and `v` -/

/-- Bytes of the ciphertext past those written so far. -/
theorem far_ct {s₀ : State} (hp : Pre P L s₀) {kE eo kC co : Nat} (A : EncArgs P L kE eo kC co) {nU o l : Nat}
    (h : co + 32 * P.du * nU ≤ o) (f : o + l ≤ co + P.ctLen) :
    Far P L s₀ kC co P.k nU (R (kA s₀) (L.slot kC) o l) := by
  have hw := hp.wf
  have hb := hp.lt A.hkC
  have fC := A.fC
  have f' : o + l ≤ L.len (L.slot kC) := by omega_using [f, fC]
  have hs : ∀ {o' l' : Nat}, o' + l' ≤ CB P → L.slot kC ≠ L.sc ∨ o' + l' ≤ o ∨ o + l ≤ o' := fun h' => by
    rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inl (by subst hC; omega_using [h', h]))
  have g : ∀ {o' l' : Nat}, o' + l' ≤ CB P → (R (kA s₀) L.sc o' l').Disjoint (R (kA s₀) (L.slot kC) o l) :=
    fun h' => hp.args.rdisj hp.scb hb (hp.fs (by lom)) f' (.inr (.inl hp.scw)) (by
      rcases hs h' with e | e
      · exact .inl (Ne.symm e)
      · exact .inr e)
  exact ⟨g (by lom), g (by lom), g (by lom), g (by lom),
    hp.args.rdisj hb hb (by omega_using [h, f, fC]) f' (.inl rfl) (.inr (.inl h)), ⟨_, by simp, R.sub2 (by omega_using [h]) f⟩⟩

/-- `v`. -/
abbrev vPoly (P : KemLay) (T : Nat → Poly) (rv mv : List Byte) : Poly :=
  add (add (nttInv (KPke.dotK T (encY rv) P.k)) (cbd rv (2 * P.k))) (decodeDecompress 1 mv)

/-- The ciphertext's bytes. -/
theorem ct_at {m : Mem} {p : Addr} {U : Nat → List Byte} {V : List Byte}
    (hu : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (32 * P.du * i)) (32 * P.du) = U i)
    (hv : bytesAt m (p + BitVec.ofNat 64 (32 * P.du * P.k)) (32 * P.dv) = V) :
    bytesAt m p P.ctLen = KPke.catK U P.k ++ V := by
  have cat : ∀ n, n ≤ P.k → bytesAt m p (32 * P.du * n) = KPke.catK U n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Nat.mul_succ, bytesAt_add, ih (by omega_using [hn]), hu n (by omega_using [hn])]
      exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm
  rw [show P.ctLen = 32 * P.du * P.k + 32 * P.dv by simp only [KemLay.ctLen]; rw [Nat.mul_add, Nat.mul_assoc],
    bytesAt_add, cat P.k (Nat.le_refl _), hv]

end VG.Proof.MlKem.AArch64.Kem
