module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Lay
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Lay
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA key generation on PPC64LE: what holds throughout, and the prologue

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Inv.lean`): what holds of the
state throughout (`KC`: the layout, the permissions and stack pointer of the
entry state, our caller's registers saved in `scratch` (ML-KEM's
`TopSaved`), the callee-saved registers we do not save as they were, and the
seed `ξ`), which a part keeps if it writes apart from the saved registers
and the seed (`kcChk`); the pieces of key generation (`KPiece`); and the
prologue, which saves our caller's registers and keeps the pointers
(`pro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (pSeed σ) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.2

/-- The public data of `keyGenContract`. -/
def kgPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ pSeed σ₁ = pSeed σ₂ ∧ pPk σ₁ = pPk σ₂ ∧ pSk σ₁ = pSk σ₂ ∧ pScr σ₁ = pScr σ₂ ∧
    keyGenLeak p (xiOf σ₁) = keyGenLeak p (xiOf σ₂)

/-- The pieces of key generation. -/
abbrev KPiece (p : Params) (STK : Nat) := Piece (Pre p STK) (kgPub p)

/-- Two runs of a key generation with public data that agree have the same layout. -/
theorem lay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : kgPub p σ₁ σ₂) : lay p STK σ₁ = lay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [lay, pSeed, pPk, pSk, pScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (lay p STK σ) kWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (pScr σ) σ
  xi : bytesAt s.mem ((lay p STK σ).A 2 0) 32 = xiOf σ

theorem xi_eq (p : Params) (STK : Nat) (σ : State) : bytesAt σ.mem ((lay p STK σ).A 2 0) 32 = xiOf σ := by
  simp only [Lay.A, BitVec.add_zero]; rfl

theorem saveR_lay (p : Params) (STK : Nat) (σ : State) : saveR (pScr σ) = (lay p STK σ).R 0 840 72 := rfl

/-- A part that writes the regions `W` keeps `KC`. -/
def kcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, 840, 72) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (2, 0, 32) W

theorem KC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : KC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : kcChk p STK W = true) : KC p STK σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 0 840 72).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp hc.1 w hw) (.inl (by decide))
  have hd2 : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 2 0 32).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      have hs := List.all_eq_true.mp hc.2 w hw
      refine disjW' hL hs (.inr ?_)
      have hb : w.1 < 5 := by
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq, List.length_cons, List.length_nil] at hs
        exact hs.1.1.1.2
      rcases (by omega : w.1 = 0 ∨ w.1 = 1 ∨ w.1 = 2 ∨ w.1 = 3 ∨ w.1 = 4) with e | e | e | e | e <;> rw [e]
      · exact .inl (by decide)
      · exact .inl (by decide)
      · exact .inr rfl
      · exact .inl (by decide)
      · exact .inl (by decide)
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp,
    fun r hr hs => (hk.cs r hr).trans (h.pres r hr hs), h.sav.keep hk.frame (by rw [saveR_lay p STK σ]; exact hd), ?_⟩
  rw [Proof.MlKem.bytesAt_frame hk.frame hd2 (by decide)]; exact h.xi

/-! ## The prologue -/

theorem pro_ok {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 48 ≤ STK) {σ : State} (hp : Pre p STK σ) :
    WP isa (.block pro) σ fun s => KC p STK σ s ∧ s.gpr .r24 = 1 := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (lay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (lay p STK σ).buf 0 = reg (pScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr (pScr σ + BitVec.ofNat 64 o) n := fun {o n} h =>
    Lay.covers (L := lay p STK σ) (o := o) (l := n) w0 (by rw [lay_size0]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (topSave_ok (.inl rfl) rfl fun o _ h₂ => wS (by omega))
    fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = pSeed σ := g₁ _ (by decide)
  have g4 : s₁.gpr .r4 = pPk σ := g₁ _ (by decide)
  have g5 : s₁.gpr .r5 = pSk σ := g₁ _ (by decide)
  have g6 : s₁.gpr .r6 = pScr σ := g₁ _ (by decide)
  have hmv : WP isa (.block [mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r31 .r6, .li .r24 1]) s₁ fun s =>
      s.gpr .r30 = pSeed σ ∧ s.gpr .r29 = pPk σ ∧ s.gpr .r28 = pSk σ ∧ s.gpr .r31 = pScr σ ∧
      s.gpr .r24 = 1 ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    prun [g3, g4, g5, g6]
    and_intros
    all_goals first
      | exact trivial
      | rfl
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [RegUpd.gpr_write, a24, a28, a29, a30, a31, ite_false])
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, g24, cs, m, rd, wr, sp⟩ => ⟨⟨⟨hL, rfl, by decide, by decide,
    by rw [lay_size0]; omega, rfl, by rw [sp, sp₁]; rfl, hSTK, by rw [sp, sp₁]; exact hp.stk, g31, g30, g29, g28,
    fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => (cs r hr hs).trans (g₁ r (by rintro rfl; simp [preserved] at hr)), by rw [m]; exact sav, ?_⟩, g24⟩
  · show _ ∈ s.wr
    rw [wr, wr₁, hp.wr]
    simp only [kWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [Lay.buf, lay]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay]
    · simp [Lay.buf, lay]
  · show _ ∈ s.rd ++ s.wr
    rw [rd, rd₁, wr, wr₁, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, lay]
  · rw [m, ← xi_eq p STK σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [saveR_lay p STK σ]
      exact disjW' (i := 2) (o := 0) (l := 32) (j := 0) (o' := 840) (l' := 72) hL (by lsep hF)
        (.inr (.inl (by decide)))) (by decide)

theorem pro_piece {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 48 ≤ STK) :
    KPiece p STK (fun σ s => s = σ) (fun σ s => KC p STK σ s ∧ s.gpr .r24 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hF hSTK hp,
    Sample.taint_block [.r3, .r4, .r5, .r6] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by taint_decide)⟩

end VG.Proof.MlDsa.PPC64LE.KeyGen
