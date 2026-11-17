module

public import VerifiedGarbage.Proof.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Lay
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
public import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Call
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mask32
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.Framework.Sig

/-! ### `MlDsa.X86.KeyGen.Base`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on x86 (32-bit): the setting

Key generation is proven for any implementations of the primitives it calls
that are verified against their contracts (`PrimsOk`), as ML-KEM's top-level
functions on x86 (`Proof/MlKem/X86/`): the contract's precondition gives the
layout of the arguments (`pre_of`), and its public data the pointers and what
key generation may leak, as bytes (`lkK`, `pub_of`). `ξ` gives `(ρ, ρ′, K)`
(`hxOf`), which the body keeps in `scratch` (`KB`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- Verified implementations of the primitives key generation calls. -/
structure PrimsOk (P : Prims) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract X86.abi stk)
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract X86.abi stk)
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract X86.abi stk)
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract X86.abi stk)
  add : Callee P.add (fun stk => Proof.MlDsa.addContract X86.abi stk)
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract X86.abi stk)
  rejBounded : Callee P.rejBounded (fun stk => Proof.MlDsa.rejBoundedContract X86.abi stk)
  power2Round : Callee P.power2Round (fun stk => Proof.MlDsa.power2RoundContract X86.abi stk)
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract X86.abi stk)
  bitPack : Callee P.bitPack (fun stk => Proof.MlDsa.bitPackContract X86.abi stk)

section
variable (p : Params) (s₀ : State)

/-- `ξ`. -/
abbrev xiOf : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32
/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf : List Byte := Spec.MlDsa.H (xiOf s₀ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf : List Byte := (keyGenSeeds p (xiOf s₀)).1
abbrev rho'Of : List Byte := (keyGenSeeds p (xiOf s₀)).2.1
abbrev kOf : List Byte := (keyGenSeeds p (xiOf s₀)).2.2
/-- What key generation may leak, as bytes. -/
def lkK : List Byte := (keyGenLeak p (xiOf s₀)).map (BitVec.ofNat 8)
/-- The AND of the samplers' results. -/
abbrev accV (s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (sb oACC 4)) 32

end

/-- A piece of key generation. -/
abbrev KP (p : Params) := Piece (TPre (YK p)) (TPub (YK p) (lkK p))

theorem addr0 (s₀ : State) (i : Nat) (l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-! ## The contract -/

theorem pre_of {p : Params} {s₀ : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pre s₀) :
    TPre (YK p) s₀ := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 96#64, 96⟩ : Region) = below (E0 s₀) 96 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h20 h21 h22 h23 h24
  have c4 : ∀ i, i < (YK p).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    rw [YK_n] at hi; omega_using [hi]
  refine ⟨h1, by rw [YK_stk]; omega_using [], by rw [YK_n]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h24, ?_, by rw [YK_sc, YK_n]; decide⟩
  · intro i hi hw
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · rw [h3]; exact List.mem_singleton_self _
    all_goals simp [YK, Lay.awr] at hw
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · simp [YK, Lay.awr] at hw
    all_goals simp [argR, Lay.alen, YK, scrLen]
  · rw [h4]; simp [gR, Lay.n, YK]
  · intro i hi j hj hne _
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hne | skip
    all_goals simp only [argR, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    exacts [h5, h6, h7, h5.symm, h9, h10, h6.symm, h9.symm, h12, h7.symm, h10.symm, h12.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, gR, YK_n, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h8.symm
    · exact h11.symm
    · exact h13.symm
    · exact h14.symm
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h15
    · exact h16
    · exact h17
    · exact h18
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [argR, YK_stk, YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> simp only [YK_alen0, YK_alen1, YK_alen2, YK_alen3, scrLen]
    · exact h25
    · exact h26
    · exact h27
    · exact h28

theorem pub_of {p : Params} {s₀ s₀' : State} (h : (Spec.MlDsa.keyGenContract p X86.abi 96).pub s₀ s₀') :
    TPub (YK p) (lkK p) s₀ s₀' := by
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · rw [YK_n] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_using [hi]
    exacts [e₃, e₄, e₅, e₆]
  · simp only [lkK, xiOf, addr0]
    rw [e₂]

/-- Two runs agree on `ρ`, and on what each `RejBoundedPoly` of `ExpandS` leaks. -/
theorem TPub.leak {p : Params} {s₀ s₀' : State} (hq : TPub (YK p) (lkK p) s₀ s₀') :
    rhoOf p s₀ = rhoOf p s₀' ∧ ∀ r < p.ℓ + p.k, Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (rho'Of p s₀) r) =
      Spec.MlDsa.rejBoundedLeak p.η (Proof.MlDsa.KeyGen.seedS (rho'Of p s₀') r) :=
  Proof.MlDsa.KeyGen.keyGenLeak_split (Proof.MlDsa.KeyGen.keyGenLeak_bytes hq.2.2)

end VG.Proof.MlDsa.X86.KeyGen

end

end

/-!
# ML-DSA key generation on x86 (32-bit): what holds between the pieces

After the seeds, `scratch` holds `(ρ, ρ′, K)` and the seeds of the samplers
(`KB`); after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`, the
polynomials sampled, reduced (and small), and the AND of the samplers'
results, which is 1 if they are those of the standard for some bounds, and 0
if key generation fails within the least bounds (`Good`, `KSamp`). Each is
kept by a piece that writes only buffers apart from those it describes
(`KB.keep`, `KSamp.keep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS)
open VG.Spec.Sha3 (bytesAt)

/-! ## Bytes -/

theorem st8_bytes (s₀ : State) (m : Mem) (sc o v : Nat) :
    bytesAt (m.writeW (Buf.addr s₀ ⟨sc, o, 1⟩) ((BitVec.ofNat 32 v).setWidth 8)) (Buf.addr s₀ ⟨sc, o, 1⟩) 1 =
      [BitVec.ofNat 8 v] := by
  refine Proof.MlKem.bytesAt_eq (L := [BitVec.ofNat 8 v]) rfl fun i hi => ?_
  obtain rfl : i = 0 := by omega_using [hi]
  simp only [BitVec.add_zero, Proof.MlKem.writeW8_apply, List.getElem_cons_zero, ite_true]
  rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- The bytes of a part of a buffer. -/
theorem bytes_sub {Y : Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o L k c : Nat} (hkc : k + c ≤ L)
    (h₁ : Y.ok ⟨a, o, L⟩ = true) (h₂ : Y.ok ⟨a, o + k, c⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o + k, c⟩) c = ((bytesAt m (Buf.addr s₀ ⟨a, o, L⟩) L).drop k).take c := by
  rw [Proof.MlKem.bytesAt_slice _ _ hkc, Buf.addr_eq hp h₁, Buf.addr_eq hp h₂, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- The bytes of two adjacent buffers. -/
theorem bytes_cat {Y : Lay} {s₀ : State} (hp : TPre Y s₀) (m : Mem) {a o l₁ l₂ : Nat}
    (h₂ : Y.ok ⟨a, o + l₁, l₂⟩ = true) (h : Y.ok ⟨a, o, l₁ + l₂⟩ = true) :
    bytesAt m (Buf.addr s₀ ⟨a, o, l₁ + l₂⟩) (l₁ + l₂) =
      bytesAt m (Buf.addr s₀ ⟨a, o, l₁⟩) l₁ ++ bytesAt m (Buf.addr s₀ ⟨a, o + l₁, l₂⟩) l₂ := by
  have e : Buf.addr s₀ ⟨a, o + l₁, l₂⟩ = Buf.addr s₀ ⟨a, o, l₁ + l₂⟩ + BitVec.ofNat 64 l₁ := by
    rw [Buf.addr_eq hp h₂, Buf.addr_eq hp h, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [Proof.MlKem.bytesAt_add, e]

/-- An ML-DSA polynomial apart from what a piece writes. -/
theorem keepPolyD {Y : Lay} {s₀ : State} (hp : TPre Y s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ Y.stk)
    {a o : Nat} (hs : Y.apart ⟨a, o, 1024⟩ bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m') {f : Poly}
    (h : PolyIs m (Buf.addr s₀ ⟨a, o, 1024⟩) f) : PolyIs m' (Buf.addr s₀ ⟨a, o, 1024⟩) f :=
  Proof.MlDsa.KeyGen.polyIs_congr (Top.keep hp hN hs fr) h

/-! ## After the seeds -/

section
variable (p : Params) (s₀ : State)

/-- `(ρ, ρ′, K)`, `ρ` and `ρ′ ‖ · ‖ 0` in `scratch`. -/
structure KB (s : State) : Prop where
  ctx : Ctx (YK p) s₀ s
  hx : bytesAt s.mem (Buf.addr s₀ (sb oHX 128)) 128 = hxOf p s₀
  sa : bytesAt s.mem (Buf.addr s₀ (sb oSA 32)) 32 = rhoOf p s₀
  sbb : bytesAt s.mem (Buf.addr s₀ (sb oSB 64)) 64 = rho'Of p s₀
  z : bytesAt s.mem (Buf.addr s₀ (sb (oSB + 65) 1)) 1 = [0]

/-- The buffers of `KB` are apart from `bs`. -/
def safeKB (bs : List Buf) : Bool :=
  (YK p).apart (sb oHX 128) bs && (YK p).apart (sb oSA 32) bs && (YK p).apart (sb oSB 64) bs &&
    (YK p).apart (sb (oSB + 65) 1) bs

end

theorem KB.keep {p : Params} {s₀ s s' : State} (h : KB p s₀ s) (hp : TPre (YK p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : safeKB p bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YK p) s₀ s') :
    KB p s₀ s' := by
  simp only [safeKB, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s₁, s₂⟩, s₃⟩, s₄⟩ := hs
  exact ⟨h', by rw [keepBytes hp hN s₁ fr]; exact h.hx, by rw [keepBytes hp hN s₂ fr]; exact h.sa,
    by rw [keepBytes hp hN s₃ fr]; exact h.sbb, by rw [keepBytes hp hN s₄ fr]; exact h.z⟩

/-! ## The samplers -/

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

/-- The AND `v` of the samplers' results after the first `e` entries of `Â` and
`r` of `s₁ ‖ s₂`: 1 if they are those of the standard, `A` and `S`, for some
bounds; 0 if key generation fails within the least bounds. -/
def Good (p : Params) (s₀ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (rhoOf p s₀) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p s₀) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (xiOf s₀) = none)

theorem good_01 {p : Params} {s₀ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 32}
    (h : Good p s₀ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (e r : Nat) (s₀ s : State) : Prop where
  kb : KB p s₀ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (Buf.addr s₀ (aB e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (Buf.addr s₀ (sB p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p s₀ e r A S (accV s₀ s)

/-- The buffers of `KSamp` are apart from `bs`. -/
structure SafeS (p : Params) (e r : Nat) (bs : List Buf) : Prop where
  kb : safeKB p bs = true
  acc : (YK p).apart (sb oACC 4) bs = true
  a : ∀ e' < e, (YK p).apart (aB e') bs = true
  s : ∀ r' < r, (YK p).apart (sB p r') bs = true

theorem KSamp.keep {p : Params} {e r : Nat} {s₀ s s' : State} (h : KSamp p e r s₀ s) (hp : TPre (YK p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (hs : SafeS p e r bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YK p) s₀ s') : KSamp p e r s₀ s' := by
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.kb.keep hp hN hs.kb fr h', A, S, fun e' he' => keepPolyD hp hN (hs.a e' he') fr (hA e' he'),
    fun r' hr' => ⟨keepPolyD hp hN (hs.s r' hr') fr (hS r' hr').1, (hS r' hr').2⟩, ?_⟩
  rw [show accV s₀ s' = accV s₀ s from keepW hp hN hs.acc fr]
  exact hG

end VG.Proof.MlDsa.X86.KeyGen
