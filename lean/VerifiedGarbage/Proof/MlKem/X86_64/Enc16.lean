module

public import VerifiedGarbage.Proof.MlKem.X86_64.Enc16Tail
public import VerifiedGarbage.Proof.MlKem.X86_64.Kg16Tail
public import VerifiedGarbage.Proof.MlKem.X86_64.KgA16
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem.X86_64.Kg16

/-!
# ML-KEM on x86-64: K-PKE.Encrypt with 16-bit polynomials

`Top16.encrypt K c E Cp` in the layout of encapsulation or decapsulation
(`Ctx`): `Â` from `ρ` (the last 32 bytes of the key at `E`), as `u16`s, and
if every `SampleNTT` succeeded, the outputs of `PRF₂`, `y ‖ e₁ ‖ e₂` from
them as `u16`s, and the ciphertext to `Cp` (`Enc16Tail.lean`):
`encrypt_ok`, and its constant time, `encrypt_tr`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc16

open Enc VG.Impl.MlKem.X86_64.Top16

variable {rbs wbs : List (Reg × Nat)} {K : Kem16}

/-- After the first `e` entries of `Â`. -/
structure EB16 (K : Kem16) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (e : Nat) (s : State) : Prop where
  i : EIn K.L C E ek m r s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = rhoE K.L ek
  m : MatB16 K.L.k K.oA (rhoE K.L ek) e s

variable (K) in
/-- Entry `e` of `Â`. -/
def sampEChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  ij16Chk bs wbs (aP K e) (sc K.oW) && inKeep K.L bs chk E (KeyGen16.ijW K e) &&
    keepB bs (KeyGen16.ijW K e) (sc oSB) 32 && (List.range e).all fun e' => keepB bs (KeyGen16.ijW K e) (aP K e') 512

variable (K) in
/-- Entries `e, …, e + 3` of `Â`. -/
def quadEChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  quad16Chk bs wbs (K.oA + 512 * e) K.oW && inKeep K.L bs chk E (quad16W (K.oA + 512 * e) K.oW) &&
    keepB bs (quad16W (K.oA + 512 * e) K.oW) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB bs (quad16W (K.oA + 512 * e) K.oW) (aP K e') 512

theorem sampE_step {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat} (hk : K.L.k ≤ 4)
    (he : e < K.L.k * K.L.k) (hc : sampEChk K (rbs ++ wbs) wbs C.chk E e = true) {s : State}
    (h : EB16 K C E ek m r e s) :
    WP isa (sampleIJ16 (sc (K.oA + 512 * e)) (e / K.L.k) (e % K.L.k) (sc K.oW)) s fun s' =>
      PPostB s s' (KeyGen16.ijW K e) ∧ EB16 K C E ek m r (e + 1) s' := by
  simp only [sampEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hij, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (sampleIJ16_ok L₀ C.bs rbx_na rbx_na (by have := div_lt_k he; omega)
    (by have := mod_lt_k he; omega) hij) fun s' ⟨hP, h15, hres⟩ => ⟨hP, h.i.keep hP hkc,
      by rw [L₀.keepBytes hP kB]; exact h.sb, h.m.single h.sb L₀ hP kA h15 hres⟩

theorem quadE_step {n : String} {c : Prog isa} (v : S16Ok c) {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte}
    {e : Nat} (he : e + 4 ≤ 256) (hc : quadEChk K (rbs ++ wbs) wbs C.chk E e = true) {s : State}
    (h : EB16 K C E ek m r e s) :
    WP isa (quad16 (n, c) K.L.k e (sc (K.oA + 512 * e)) (sc K.oW)) s fun s' =>
      PPostB s s' (quad16W (K.oA + 512 * e) K.oW) ∧ EB16 K C E ek m r (e + 4) s' := by
  simp only [quadEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hq, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (quad16_ok v L₀ C.bs he hq) fun s' ⟨hP, h15, hres⟩ =>
    ⟨hP, h.i.keep hP hkc, by rw [L₀.keepBytes hP kB]; exact h.sb, h.m.four h.sb L₀ hP kA h15 hres⟩

variable (K) in
/-- Every check of `Top16.encrypt`, but the call of the K-PKE function (`tailChk`). -/
structure EncChks (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : matChk K.L bs wbs chk E = true
  q : ∀ q < K.L.k * K.L.k / 4, quadEChk K bs wbs chk E (4 * q) = true
  s : ∀ e < K.L.k * K.L.k, 4 * (K.L.k * K.L.k / 4) ≤ e → sampEChk K bs wbs chk E e = true
  inK : inKeep K.L bs chk E [] = true
  aK : ∀ e < K.L.k * K.L.k, keepB bs [] (aP K e) 512 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  prfs : prfsChk bs wbs (2 * K.L.k + 1) K.oPR (K.oW / 32) = true
  prfsK : inKeep K.L bs chk E (prfsW (2 * K.L.k + 1) K.oPR (K.oW / 32)) = true
  prfsA : ∀ e < K.L.k * K.L.k, keepB bs (prfsW (2 * K.L.k + 1) K.oPR (K.oW / 32)) (aP K e) 512 = true
  y : ∀ N < 2 * K.L.k + 1, twoChk bs wbs (prfO K N) 128 (rP K N) 512 = true
  yK : ∀ N < 2 * K.L.k + 1, inKeep K.L bs chk E [(rP K N, 512)] = true
  yA : ∀ N < 2 * K.L.k + 1, ∀ e < K.L.k * K.L.k, keepB bs [(rP K N, 512)] (aP K e) 512 = true
  yP : ∀ N < 2 * K.L.k + 1, ∀ N' < 2 * K.L.k + 1, keepB bs [(rP K N, 512)] (prfO K N') 128 = true
  yR : ∀ N < 2 * K.L.k + 1, ∀ N' < N, keepB bs [(rP K N, 512)] (rP K N') 512 = true

theorem mat_ok {n : String} {c : Prog isa} (v : S16Ok c) {C : Ctx rbs wbs} {E : Ptr} (hk : K.L.k ≤ 4)
    (hc : EncChks K (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte} {s : State} (h : EIn K.L C E ek m r s)
    (h15 : s.gpr .r15 = 1) : WP isa (encMat K (n, c) E) s (EB16 K C E ek m r (K.L.k * K.L.k)) := by
  have hc₁ := hc.mat
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay h.out
  unfold encMat mat
  refine WP.seq (WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.keep hP₁.b hc₁.2
  refine samples16_ok' (n, c) K.L.k K.oA (sc K.oW) (I := EB16 K C E ek m r)
    (fun e he he' s hs' => WP.mono (sampE_step hk he (hc.s e he he') hs') fun _ h => h.2)
    (fun q hq' s hs' => WP.mono (quadE_step v (by
      have : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul hk hk
      omega) (hc.q q hq') hs') fun _ h => h.2)
    ⟨h₁, ?_, MatB16.zero _ _ _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.rho

theorem EB16.flag {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s s' : State}
    (h : EB16 K C E ek m r (K.L.k * K.L.k) s) (hP : PPost s s' []) (hc : EncChks K (rbs ++ wbs) wbs C.chk E) :
    EB16 K C E ek m r (K.L.k * K.L.k) s' := by
  have L₀ := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc.inK, by rw [L₀.keepBytes hP.b hc.sbK]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e he f hf => L₀.keepPoly16 hP.b (hc.aK e he) (h.m.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (K : Kem16) (C : Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : allOk K.L.k (rhoE K.L ek) (K.L.k * K.L.k)
  i : EIn K.L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoE K.L ek) (e / K.L.k) (e % K.L.k))

theorem ER0.start {C : Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : EB16 K C E ek m r (K.L.k * K.L.k) s) (ho : allOk K.L.k (rhoE K.L ek) (K.L.k * K.L.k)) : ER0 K C E ek m r s :=
  ⟨ho, h.i, by rw [h.m.r15, ifp ho], fun e he => h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

theorem prfs_ok (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} (hk : K.L.k ≤ 4) (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    {ek m r : List Byte} {s : State} (h : ER0 K C E ek m r s) :
    WP isa (v.callee.prfs 0 (2 * K.L.k + 1) K.oPR (K.oW / 32)) s fun s' =>
      PPost s s' (prfsW (2 * K.L.k + 1) K.oPR (K.oW / 32)) ∧ ER16 K C E ek m r 0 s' := by
  have L₀ := C.lay h.i.out
  refine WP.mono (v.prfs_ok L₀ C.bs (by omega) hc.prfs) fun s' ⟨hP, hb⟩ => ⟨hP, h.i.keep hP.b hc.prfsK,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, h.ok, fun e he => L₀.keepPoly16 hP.b (hc.prfsA e he) (h.mat e he),
    fun N hN => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [Top16.prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

theorem y_ok {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {E : Ptr} (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    {N : Nat} (hN : N < 2 * K.L.k + 1) {ek m r : List Byte} {s : State} (h : ER16 K C E ek m r N s) :
    WP isa (cbdN K A N) s fun s' => PPost s s' [(rP K N, 512)] ∧ ER16 K C E ek m r (N + 1) s' := by
  have L₀ := C.lay h.i.out
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na (hc.y N hN)) fun s' ⟨hP, hp'⟩ => ⟨hP, h.i.keep hP.b (hc.yK N hN),
    by rw [hP.cs .r15 (by decide)]; exact h.r15, h.ok, fun e he => L₀.keepPoly16 hP.b (hc.yA N hN e he) (h.mat e he),
    fun N' hN' => by rw [L₀.keepBytes hP.b (hc.yP N hN N' hN')]; exact h.prf N' hN', fun N' hN' => ?_⟩
  rcases (by omega : N' < N ∨ N' = N) with hN'' | rfl
  · exact L₀.keepPoly16 hP.b (hc.yR N hN N' hN'') (h.rr N' hN'')
  · rw [h.prf N' hN, ← hP.pa rbx_cs] at hp'; exact hp'

theorem rest_ok (hK : KpkeOk K.L) (v : Sample4Impl) {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E)
    (hCp : Cp.1 ∈ calleeSaved) (hk : K.L.k ≤ 4) (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    (ht : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true) {ek m r : List Byte} {s : State} (h : ER0 K C E ek m r s) :
    WP isa (encRest K v.callee E Cp) s (EOut16 K C Cp ek m r) := by
  unfold encRest noise
  refine WP.seq (WP.seq (WP.mono (prfs_ok v hk hc h) fun s₀ h₀ => WP.mono (seqR_ok (I := fun k => ER16 K C E ek m r k)
    (2 * K.L.k + 1) 0 (fun k _ hk' s hs => WP.mono (y_ok v.arith hc (by omega) hs) fun _ h => h.2) s₀ h₀.2)
    fun s₁ h₁ => ?_))
  rw [Nat.zero_add] at h₁
  exact WP.mono (tail_ok hK hE hCp ht h₁) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, by rw [h15, ifp h₁.ok], fun _ => hct⟩

theorem encrypt_ok (hK : KpkeOk K.L) (v : Sample4Impl) {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c))
    {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E) (hCp : Cp.1 ∈ calleeSaved) (hk : K.L.k ≤ 4)
    (hc : EncChks K (rbs ++ wbs) wbs C.chk E) (ht : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true)
    {ek m r : List Byte} {s : State} (h : EIn K.L C E ek m r s) (h15 : s.gpr .r15 = 1) :
    WP isa (Top16.encrypt K v.callee (n, c) E Cp) s (EOut16 K C Cp ek m r) := by
  unfold Top16.encrypt
  refine WP.seq (WP.mono (mat_ok (v.s16 n c hs) hk hc h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · exact rest_ok hK v hE hCp hk hc ht (ER0.start (h₁.flag hP hc) (KeyGen.r15_ne h₁.m.r15 hne))
  · have h₂ := h₁.flag hP hc
    exact ⟨h₂.i.out, h₂.m.r15, fun ho => absurd ho (KeyGen.r15_eq h₁.m.r15 he)⟩

/-! ## Constant time, for a given `ρ` -/

/-- The entries of `Â` sampled so far, for the `ρ` of `ek`. -/
abbrev EBρ (K : Kem16) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (e : Nat) (s : State) : Prop :=
  ∃ ek m r, rhoE K.L ek = ρ ∧ EB16 K C E ek m r e s

theorem sampE_tr {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (hk : K.L.k ≤ 4) (he : e < K.L.k * K.L.k)
    (hc : sampEChk K (rbs ++ wbs) wbs C.chk E e = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % K.L.k) ++ setB (sc (oSB + 33)) (e / K.L.k))) (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ K C E ρ e x ∧ EBρ K C E ρ e y)
      (sampleIJ16 (sc (K.oA + 512 * e)) (e / K.L.k) (e % K.L.k) (sc K.oW))
      (fun x y => LRel rbs wbs x y ∧ EBρ K C E ρ (e + 1) x ∧ EBρ K C E ρ (e + 1) y) := by
  have hc' := hc
  simp only [sampEChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (sampleIJ16_tr C.bs rbx_na rbx_na (by have := div_lt_k he; omega)
      (by have := mod_lt_k he; omega) hc'.1.1.1 ht)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, by rw [h₁.sb, h₂.sb, e₁, e₂]⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (sampE_step hk he hc hx) fun x' hx' => ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

theorem quadE_tr {n : String} {c : Prog isa} (v : S16Ok c) {C : Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat}
    (hk : K.L.k ≤ 4) (he : e + 4 ≤ K.L.k * K.L.k) (hc : quadEChk K (rbs ++ wbs) wbs C.chk E e = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EBρ K C E ρ e x ∧ EBρ K C E ρ e y)
      (quad16 (n, c) K.L.k e (sc (K.oA + 512 * e)) (sc K.oW))
      (fun x y => LRel rbs wbs x y ∧ EBρ K C E ρ (e + 4) x ∧ EBρ K C E ρ (e + 4) y) := by
  have hc' := hc
  simp only [quadEChk, Bool.and_eq_true] at hc'
  have h16 : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul hk hk
  refine RelCT.stepL C.bs (RelCT.mono (quad16_tr (ρ := ρ) v C.bs (by omega)
      (fun t ht => ⟨by have := div_lt_k (show e + t < K.L.k * K.L.k by omega); omega,
        by have := mod_lt_k (show e + t < K.L.k * K.L.k by omega); omega⟩) hc'.1.1.1)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, ⟨by rw [h₁.sb, e₁], fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨by rw [h₂.sb, e₂], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (quadE_step v (by omega) hc hx) fun x' hx' =>
      ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

theorem mat_tr {n : String} {c : Prog isa} (v : S16Ok c) {C : Ctx rbs wbs} {E : Ptr} (hk : K.L.k ≤ 4)
    (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    (hij : ∀ e < K.L.k * K.L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % K.L.k) ++ setB (sc (oSB + 33)) (e / K.L.k))) (.block [])).isSome = true)
    {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * K.L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ K.L C E ρ x ∧ EIρ K.L C E ρ y) (encMat K (n, c) E)
      (fun x y => LRel rbs wbs x y ∧ EBρ K C E ρ (K.L.k * K.L.k) x ∧ EBρ K C E ρ (K.L.k * K.L.k) y) := by
  have hc₁ := hc.mat
  have hc₁' := hc₁
  simp only [matChk, copyChk, wrOk, rdOk, Bool.and_eq_true] at hc₁'
  have hin₁ : inB (rbs ++ wbs) (sc oSB) 32 = true := hc₁'.1.1.1.1.1.1.1.1.2
  have hin₂ : inB (rbs ++ wbs) (E.1, E.2 + 384 * K.L.k) 32 = true := hc₁'.1.1.1.1.1.1.2.2
  unfold encMat mat
  refine RelCT.seq (RelCT.stepL (J := EBρ K C E ρ 0) C.bs (taintRel [.rbx, E.1] (fun x y h =>
      fa2 (h.1.eq hin₁) (h.1.eq (p := (E.1, E.2 + 384 * K.L.k)) hin₂)) ht) fun x ⟨ek, m, r, eρ, hx, h15⟩ => ?_)
    (samples16_tr' (n, c) K.L.k K.oA (sc K.oW) (R := fun e x y => LRel rbs wbs x y ∧ EBρ K C E ρ e x ∧ EBρ K C E ρ e y)
      (fun e he he' => sampE_tr hk he (hc.s e he he') (hij e he))
      (fun q hq' => quadE_tr v hk (by omega) (hc.q q hq')))
  simp only [matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay hx.out
  refine WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun x₁ ⟨hP₁, hb₁⟩ => ⟨⟨_, hP₁.b⟩, ek, m, r, eρ, ?_⟩
  refine ⟨hx.keep hP₁.b hc₁.2, ?_, MatB16.zero _ _ _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa x₁ (sc oSB) = pa x (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact hx.rho

abbrev ER0ρ (K : Kem16) (C : Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, rhoE K.L ek = ρ ∧ ER0 K C E ek m r s

theorem prfs_tr (v : Sample4Impl) {C : Ctx rbs wbs} {E : Ptr} (hk : K.L.k ≤ 4) (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ K C E ρ x ∧ ER0ρ K C E ρ y)
      (v.callee.prfs 0 (2 * K.L.k + 1) K.oPR (K.oW / 32))
      (fun x y => LRel rbs wbs x y ∧ ER16ρ K C E ρ 0 x ∧ ER16ρ K C E ρ 0 y) :=
  RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by omega) hc.prfs) (fun _ _ h => h.1) fun _ _ h => h)
    fun _ ⟨ek, m, r, eρ, hx⟩ => WP.mono (prfs_ok v hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

theorem y_tr {A : Arith} (hA : ArithOk A) {C : Ctx rbs wbs} {E : Ptr} (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    {N : Nat} (hN : N < 2 * K.L.k + 1) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER16ρ K C E ρ N x ∧ ER16ρ K C E ρ N y) (cbdN K A N)
      (fun x y => LRel rbs wbs x y ∧ ER16ρ K C E ρ (N + 1) x ∧ ER16ρ K C E ρ (N + 1) y) :=
  RelCT.stepL C.bs (RelCT.mono (cbd2_16At_trL hA rbx_na (hc.y N hN)) (fun _ _ h => h.1) fun _ _ h => h)
    fun _ ⟨ek, m, r, eρ, hx⟩ => WP.mono (y_ok hA hc hN hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

theorem rest_tr (hK : KpkeOk K.L) (v : Sample4Impl) {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E)
    (hCp : Cp.1 ∈ calleeSaved) (hk : K.L.k ≤ 4) (hc : EncChks K (rbs ++ wbs) wbs C.chk E)
    (ht : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ K C E ρ x ∧ ER0ρ K C E ρ y) (encRest K v.callee E Cp)
      (fun x y => LRel rbs wbs x y ∧ EO16ρ K C Cp ρ x ∧ EO16ρ K C Cp ρ y) := by
  unfold encRest noise
  refine RelCT.seq (RelCT.seq (prfs_tr v hk hc) ?_) (tail_tr hK hE hCp ht)
  have := seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ER16ρ K C E ρ k x ∧ ER16ρ K C E ρ k y) (2 * K.L.k + 1) 0
    fun k _ hk' => y_tr v.arith hc (by omega)
  rwa [Nat.zero_add] at this

theorem encrypt_tr (hK : KpkeOk K.L) (v : Sample4Impl) {n : String} {c : Prog isa} (hs : v.callee.s16 = some (n, c))
    {C : Ctx rbs wbs} {E Cp : Ptr} (hE : NA E) (hCp : Cp.1 ∈ calleeSaved) (hk : K.L.k ≤ 4)
    (hc : EncChks K (rbs ++ wbs) wbs C.chk E) (htl : tailChk K (rbs ++ wbs) wbs C.chk E Cp = true)
    (hij : ∀ e < K.L.k * K.L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % K.L.k) ++ setB (sc (oSB + 33)) (e / K.L.k))) (.block [])).isSome = true)
    {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * K.L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ K.L C E ρ x ∧ EIρ K.L C E ρ y) (Top16.encrypt K v.callee (n, c) E Cp)
      (fun x y => LRel rbs wbs x y ∧ EO16ρ K C Cp ρ x ∧ EO16ρ K C Cp ρ y) := by
  unfold Top16.encrypt
  refine RelCT.seq (mat_tr (v.s16 n c hs) hk hc hij ht) (ifOk_tr
    (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (rest_tr hK v hE hCp hk hc htl) ?_ fun _ _ h => h) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk K.L.k (rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, ER0.start (h₁.flag hx hc) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, ER0.start (h₂.flag hy hc) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk K.L.k (rhoE K.L ek₂) (K.L.k * K.L.k) := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc
    have k₂ := h₂.flag hy hc
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.m.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.m.r15, fun h => absurd h o₂⟩⟩

end Enc16

end VG.Proof.MlKem.X86_64
