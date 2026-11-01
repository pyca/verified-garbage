module

import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.RestRow
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.RestPack

/-!
# ML-DSA key generation on PPC64LE: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Top.lean`): the rows
(`row_piece`), the keys in memory (`pk_bytes`, `sk_bytes`), `tr = H(pk, 64)`
(`trHash_piece`), and the whole function, piece by piece, for any parameter
set of Table 1 and any verified implementations of the primitives
(`keyGen_piece`, `keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Impl.MlKem.PPC64LE (topEnd)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK Good)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat}
    (hS : S ≤ STK) {i : Nat} (hi : i < p.k) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (rowMul_piece hP hF hS hi).seq (Piece.seq ?_ ((rowInv_piece hP hF hS hi).seq ((rowAdd_piece hP hF hS hi).seq
    ((rowP2r_piece hP hF hS hi).seq ((rowSbp_piece hP hF hS hi).seq (rowBp_piece hP hF hS hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p STK i (tIs p STK fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => rowMulAdd_piece hP hF hS hi (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_arith] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {np nj : Nat} {s : State} (h : KR p STK σ A S R np nj p.k s) :
    bytesAt s.mem ((lay p STK σ).A 3 0) p.pkLen = pkK p A S (rhoOf p σ) := by
  have hp0 := h.pk0
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem ((lay p STK σ).ptr 3 + BitVec.ofNat 64 (32 + 320 * i)) 320 =
      simpleBitPack (t1K p A S i) 1023 := fun i hi => (h.rows i (List.mem_range.mp hi)).1
  simp only [Lay.A, BitVec.add_zero] at hp0 ⊢
  rw [hF.pk, Proof.MlKem.bytesAt_add, hp0, show (lay p STK σ).ptr 3 + BitVec.ofNat 64 32 =
      (lay p STK σ).ptr 3 + BitVec.ofNat 64 32 from rfl,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK, t1Max_eq, flatMap_congr_mem hr]

theorem sk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {nj : Nat} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem ((lay p STK σ).A 4 0) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 := h.sk0
  have h1 := h.sk1
  simp only [Lay.A, BitVec.add_zero] at h0 h1 htr ⊢
  have h2 : bytesAt s.mem ((lay p STK σ).ptr 4 + BitVec.ofNat 64 (32 + 32)) 64 =
    Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 := htr
  have hp : ∀ r ∈ List.range (p.ℓ + p.k), bytesAt s.mem ((lay p STK σ).ptr 4 +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η := fun r hr =>
    h.packs r (List.mem_range.mp hr)
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem ((lay p STK σ).ptr 4 +
      BitVec.ofNat 64 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096 := fun i hi =>
    (h.rows i (List.mem_range.mp hi)).2
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (oT0 p) 416 p.k, skK, flatMap_congr_mem hp,
    flatMap_congr_mem hr]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trPieces {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (hs : Site (lay p STK σ) kWb STK s) :
    (∀ pc ∈ ([⟨.r29, 0, p.pkLen⟩] : List Impl.MlKem.PPC64LE.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc) ∧
    PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r28, 64, 64⟩ : Impl.MlKem.PPC64LE.Piece) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hpk := hF.lens
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hashLay, Lay.size, hF.sk, hlen, ite_true]) (.inr rfl)
    fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) hpk.1 (show 0 < p.pkLen by rw [hF.pk]; omega_arith)
    (by lsep hF [hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)

theorem trHash_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 64} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s) :
    WP isa (trHash p) s (KFin p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  obtain ⟨hin, hq⟩ := trPieces hF hs
  unfold trHash
  refine WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨A, S, R, h.keep hF k' ?_, ?_⟩
  · have := hF.scr
    exact (KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide)) (by omega_arith)).append
      (W₁ := [_]) ((KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
      (by omega_arith)).append (W₁ := [_]) ((KRChk.stk hF (Nat.le_refl _) (Nat.le_refl _)).append (W₁ := [_])
      (KRChk.c4 (o := 64) (n := 64) hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega_arith)) (by rw [hF.sk, oT0]; omega_arith))))
  have o₃ : bytesAt s'.mem ((lay p STK σ).A 4 64) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e : bytesAt s.mem ((lay p STK σ).ptr (ix Reg.r29) + BitVec.ofNat 64 0) p.pkLen = pkK p A S (rhoOf p σ) :=
    pk_bytes hF h
  rw [e, shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem trHash_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ p.k) (KFin p STK) (trHash p) :=
  ⟨fun _ _ _ ⟨_, _, _, h⟩ => trHash_ok hF h,
    rel_of (ktwo fun σ => hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp)
      (fun s hs => (trPieces hF hs).1) (fun s hs => (trPieces hF hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (h : KFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.keyGenContract p PPC64LE.abi STK).post σ s' := by
  obtain ⟨A, S, R, h, htr⟩ := h
  have hs := h.kc.site
  have hscr := hF.scr
  have hin : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (pScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := lay p STK σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by rw [lay_size0]; omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.r31 h.kc.sav hin h.kc.pres)
    fun s' ⟨pr, lr, r3, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h.kc.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs]
  have e3 : σ.gpr .r4 = (lay p STK σ).A 3 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  have e4 : σ.gpr .r5 = (lay p STK σ).A 4 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  rw [r3, h.r24, m', e3, e4, pk_bytes hF h, sk_bytes hF h htr]
  exact Proof.MlDsa.KeyGen.outcome_keyGen (by have := hF.l; omega_arith) h.good

theorem ktaint31 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) c hc).isSome = true) : RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint31 (fun _ _ h => h) h

theorem epi_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KFin p STK)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p PPC64LE.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hF h, rel_of (ktaint31 (by taint_decide))
    fun _ _ _ _ _ _ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The function -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem rest_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p STK) (rest P p) := by
  unfold rest
  refine (copies_piece hF).seq (Piece.seq (J := KRx p STK (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p STK r 0 0) (p.ℓ + p.k) 0
      fun r _ hr => packS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p STK (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p STK (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece (hSTK : 48 ≤ STK) :
    KPiece p STK (fun σ s => s = σ)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p PPC64LE.abi STK).post σ s)
      (keyGen P p) :=
  (pro_piece hF hSTK).seq ((seeds_piece hF).seq ((sampA_piece hP hF hS).seq ((sampS_piece hP hF hS).seq
    ((rest_piece hP hF hS).seq (epi_piece hF)))))

end

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | .r6 => 0x10000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract with `S`
bytes of stack, for any verified implementations `P` of the primitives it
calls with at most `S` bytes of stack, and `S` at least the 48 bytes the
sponge needs. The contract's satisfiability (`hsat`, by `keyGenSat`) is
evaluated once `S` is known. -/
theorem keyGen_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (h48 : 48 ≤ S)
    (p : Spec.MlDsa.Params) (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : (Spec.MlDsa.keyGenContract p PPC64LE.abi S).pre (keyGenSat p)) :
    Verified PPC64LE.target (keyGen P p) (Spec.MlDsa.keyGenContract p PPC64LE.abi S) := by
  have hF := pfacts hp
  have hk := keyGen_piece hP hF (Nat.le_refl _) h48
  obtain ⟨n, rfl⟩ : ∃ n, S = n + 1 := ⟨S - 1, by omega_arith⟩
  refine ⟨fun s hs => hk.ok s s (pre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    ⟨keyGenSat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6⟩ := hpub
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of h₁) (pre_of h₂) ⟨hsp, h3, h4, h5, h6, hl⟩ e₁ e₂

end VG.Proof.MlDsa.PPC64LE.KeyGen
