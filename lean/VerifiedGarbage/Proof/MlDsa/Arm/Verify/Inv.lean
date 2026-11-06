module

public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
meta import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Contracts
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.SeedsCT
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlKem.Arm.NttInv
import VerifiedGarbage.Proof.MlKem.Arm.RowSum
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Contracts
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.SeedsCT
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Norm
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Squeeze

/-!
# ML-DSA verification on 32-bit ARM: what holds throughout, and the prologue

What holds of the state throughout (`VC`: the layout, the permissions and
stack pointer of the entry state, our caller's registers saved in `scratch`,
and the inputs), which a part keeps if it writes only `scratch` and the stack,
apart from the saved registers (`vcChk`); the pieces of verification
(`VPiece`); and the prologue (`vpro_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece disjW disjW' Rel2)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (pro)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params) (σ : State)

abbrev pkOf : List Byte := bytesAt σ.mem (State.addr (vPk σ)) p.pkLen
abbrev muOf : List Byte := bytesAt σ.mem (State.addr (vMu σ)) 64
abbrev sgOf : List Byte := bytesAt σ.mem (State.addr (vSg σ)) p.sigLen

end

/-- The public data of `verifyContract`. -/
def vPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ vPk σ₁ = vPk σ₂ ∧ vMu σ₁ = vMu σ₂ ∧ vSg σ₁ = vSg σ₂ ∧ vScr σ₁ = vScr σ₂ ∧
    pkOf p σ₁ = pkOf p σ₂ ∧ muOf σ₁ = muOf σ₂ ∧ sgOf p σ₁ = sgOf p σ₂ ∧ stackArg σ₁ 0 = stackArg σ₂ 0

/-- The pieces of verification. -/
abbrev VPiece (p : Params) (STK : Nat) := Piece (VPre p STK) (vPub p)

theorem vlay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : vPub p σ₁ σ₂) : vlay p STK σ₁ = vlay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [vlay, vPk, vMu, vSg, vScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- If the kernel was given prepared polynomials (`cache ≠ 0`): they lie apart
from `scratch` and the stack, and are where they were. -/
def CKV (p : Params) (STK : Nat) (σ s : State) : Prop :=
  stackArg σ 0 ≠ 0 → (cacheRV p σ).Disjoint ((vlay p STK σ).buf 0) ∧
    (cacheRV p σ).Disjoint ((vlay p STK σ).buf 1) ∧ 1024 * p.k ≤ 2 ^ 64 ∧
    bytesAt s.mem (State.addr (stackArg σ 0)) (1024 * p.k) = bytesAt σ.mem (State.addr (stackArg σ 0)) (1024 * p.k)

/-- What the prologue establishes: `VC` but for `cache`. -/
structure VC0 (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (vlay p STK σ) vWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : Saved s.mem ((vlay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((vlay p STK σ).A 0 872) 32 = σ.gpr .lr
  pk : bytesAt s.mem ((vlay p STK σ).A 2 0) p.pkLen = pkOf p σ
  mu : bytesAt s.mem ((vlay p STK σ).A 3 0) 64 = muOf σ
  sg : bytesAt s.mem ((vlay p STK σ).A 4 0) p.sigLen = sgOf p σ

/-- What holds throughout, from the entry state `σ`. -/
structure VC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (vlay p STK σ) vWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : Saved s.mem ((vlay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((vlay p STK σ).A 0 872) 32 = σ.gpr .lr
  pk : bytesAt s.mem ((vlay p STK σ).A 2 0) p.pkLen = pkOf p σ
  mu : bytesAt s.mem ((vlay p STK σ).A 3 0) 64 = muOf σ
  sg : bytesAt s.mem ((vlay p STK σ).A 4 0) p.sigLen = sgOf p σ
  r8 : s.gpr .r8 = stackArg σ 0
  ck : CKV p STK σ s

theorem inputs_eq (p : Params) (STK : Nat) (σ : State) :
    bytesAt σ.mem ((vlay p STK σ).A 2 0) p.pkLen = pkOf p σ ∧ bytesAt σ.mem ((vlay p STK σ).A 3 0) 64 = muOf σ ∧
      bytesAt σ.mem ((vlay p STK σ).A 4 0) p.sigLen = sgOf p σ := by
  simp only [Lay.A, add_ofNat_zero]; exact ⟨rfl, rfl, rfl⟩

/-- A part that writes the regions `W` keeps `VC`. -/
def vcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, 840, 36) W && W.all (fun w => w.1 == 0 || w.1 == 1) &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (2, 0, p.pkLen) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (3, 0, 64) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (4, 0, p.sigLen) W

/-- Bytes of a buffer only read, kept by a part that writes only buffers of `vWb`. -/
theorem bytes_keepR {L : Lay} (hL : OkW L vWb) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : W.all (fun w => w.1 == 0 || w.1 == 1) = true)
    (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    refine disjW hL (List.all_eq_true.mp h w hw') (.inr ?_)
    have := List.all_eq_true.mp hw w hw'
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [vWb, List.mem_cons, List.not_mem_nil, or_false]
    exact this) hl

theorem vfit {p : Params} {STK : Nat} {σ : State} (hL : OkW (vlay p STK σ) vWb) (i : Nat) (hi : i < 5) :
    (vlay p STK σ).size i ≤ 2 ^ 64 := by
  have := hL.fit i (by simp only [vlay, List.length_cons, List.length_nil]; omega_arith)
  omega_arith

theorem VC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true) : VC p STK σ s' := by
  simp only [vcChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, hw⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (vlay p STK σ).RL W, ((vlay p STK σ).R 0 840 36).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp h0 w hw') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_, ?_, ?_,
    (hk.cs .r8 (by decide) (by decide)).trans h.r8, fun hne => ?_⟩
  · rw [hk.frame.readW (r := (vlay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW (r := (vlay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith) hd (by decide)]
    exact h.lr
  · rw [bytes_keepR hL hk.frame h2 hw (by have := vfit hL 2 (by decide); exact this)]
    exact h.pk
  · rw [bytes_keepR hL hk.frame h3 hw (by decide)]; exact h.mu
  · rw [bytes_keepR hL hk.frame h4 hw (by have := vfit hL 4 (by decide); exact this)]
    exact h.sg
  · obtain ⟨c0, c1, cl, cb⟩ := h.ck hne
    refine ⟨c0, c1, cl, (Proof.MlKem.bytesAt_frame hk.frame (fun r hr => ?_) cl).trans cb⟩
    obtain ⟨⟨i, o, l⟩, hw', rfl⟩ := List.mem_map.mp hr
    have hs := List.all_eq_true.mp h0 _ hw'
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hb := hs.1.2
    have h01 := List.all_eq_true.mp hw _ hw'
    simp only [Bool.or_eq_true, beq_iff_eq] at h01
    rcases h01 with rfl | rfl
    · exact c0.sub_right (Lay.R_sub hb)
    · exact c1.sub_right (Lay.R_sub hb)

/-! ## The prologue -/

theorem vpro_ok {p : Params} (hF : VFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : VPre p STK σ) :
    WP isa (.block pro) σ fun s => VC0 p STK σ s ∧ s.gpr .r11 = 1 ∧
      Frame [(vlay p STK σ).R 0 840 36] σ.mem s.mem := by
  have hL := vlay_ok hp
  have hk := hF.k
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (vlay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (vlay p STK σ).buf 0 = regA (vScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_singleton_self _
  have eA : ∀ o, (vlay p STK σ).A 0 o = State.addr (σ.gpr .r3) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((vlay p STK σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by simp only [vlay, Lay.size, List.getD_cons_zero]; omega_arith) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega_arith) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega_arith)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = vScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (vlay p STK σ).A 0 872 := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega_arith)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have e1 : encodable (1 : BitVec 32) = true := by decide
  run_block [i872, o1, e1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((vlay p STK σ).A 0 872) v).readW
      ((vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW ((vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega_arith) (by decide)
  have fr : Frame [(vlay p STK σ).R 0 840 36] σ.mem (s₁.mem.writeW ((vlay p STK σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(vlay p STK σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (vlay p STK σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega_arith
    · simp only [Region.Contains, eA]; bv_omega_arith
  have hin : ∀ {i l : Nat}, i ≠ 0 → i < 5 → l = (vlay p STK σ).size i →
      bytesAt (s₁.mem.writeW ((vlay p STK σ).A 0 872) (s₁.gpr .lr)) ((vlay p STK σ).A i 0) l =
        bytesAt σ.mem ((vlay p STK σ).A i 0) l := fun {i l} h0 h5 hl => by
    refine Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by rw [hl]; exact vfit hL i h5)
    rw [List.mem_singleton] at hr; subst hr
    refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 840) (l' := 36) hL ?_ (.inr (.inl (by decide)))
    subst hl
    rcases (by omega_arith : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> vsep hF [vlay, Lay.size]
  obtain ⟨ep, em, es⟩ := inputs_eq p STK σ
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by simp only [vlay, Lay.size, List.getD_cons_zero]; omega_arith, rfl,
    show σ.sp - BitVec.ofNat 32 STK = s₁.sp - BitVec.ofNat 32 STK by rw [h₁.sp], hSTK,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [vWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Lay.buf, vlay]
    · exact absurd rfl hi1
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, vlay]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (vlay p STK σ).A 0 872 = (vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 2) (l := p.pkLen) (by decide) (by decide) rfl]; exact ep
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 3) (l := 64) (by decide) (by decide) rfl]; exact em
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 4) (l := p.sigLen) (by decide) (by decide) rfl]; exact es
  · refine ⟨trivial, ?_⟩
    show Frame _ σ.mem (s₁.mem.writeW _ _)
    rw [e872]; exact fr

/-- The prologue and the load of `cache` into `r8`. -/
theorem vproC_ok {p : Params} (hF : VFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : VPre p STK σ) :
    WP isa (.block (pro ++ ([.ldrSp .r8 0] : List Instr))) σ fun s => VC p STK σ s ∧ s.gpr .r11 = 1 := by
  rw [WP.block_append_iff]
  refine WP.mono (vpro_ok hF hSTK hp) fun s₁ ⟨h0, h11, fr⟩ => ?_
  have hL := vlay_ok hp
  have hA : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨⟨stackArgAddr σ 0, 4⟩, List.mem_append_left _ (by rw [h0.rd, hp.rd]; simp), by
      rw [h0.sp]; exact Region.contains_self _ _⟩
  have h0' : (0 : Nat) < 4096 := by decide
  have hl : WP isa (.block [.ldrSp .r8 0]) s₁ fun s => s.gpr .r8 = s₁.mem.readW (State.addr (s₁.sp + BitVec.ofNat 32 0)) 32 ∧
      (∀ r, r ≠ .r8 → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    run_block [hA, h0']
    exact ⟨trivial, fun r hr => by simp [hr], trivial⟩
  refine WP.mono hl fun s ⟨g8, g, hm, hrd, hwr, hsp⟩ => ?_
  have hsc : Region.Sub ((vlay p STK σ).R 0 840 36) (regA (vScr σ) (scrLen p)) :=
    Lay.R_sub (L := vlay p STK σ) (i := 0) (by have := hF.scr; simp only [vlay, Lay.size, List.getD_cons_zero]; omega_arith)
  have e8 : s.gpr .r8 = stackArg σ 0 := by
    rw [g8, h0.sp]
    exact fr.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.d_ac.sub_right hsc) (by decide)
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩ : Region) = below σ STK := by
    rw [addr_sub hp.stk]
  refine ⟨⟨⟨h0.site.ok, h0.site.len, h0.site.w0, h0.site.w1, h0.site.sz0, h0.site.sz1, by rw [hsp]; exact h0.site.p1,
    h0.site.s8, by rw [hsp]; exact h0.site.spk, by rw [g _ (by decide)]; exact h0.site.r7,
    by rw [g _ (by decide)]; exact h0.site.r4, by rw [g _ (by decide)]; exact h0.site.r5,
    by rw [g _ (by decide)]; exact h0.site.r6, by rw [hwr]; exact h0.site.cw, by rw [hwr, hrd]; exact h0.site.cr⟩,
    hrd.trans h0.rd, hwr.trans h0.wr, hsp.trans h0.sp, by rw [hm]; exact h0.sav, by rw [hm]; exact h0.lr,
    by rw [hm]; exact h0.pk, by rw [hm]; exact h0.mu, by rw [hm]; exact h0.sg, e8, fun hne => ?_⟩,
    by rw [g _ (by decide)]; exact h11⟩
  obtain ⟨c0, c1, cf, -⟩ := hp.cache hne
  refine ⟨c0, ?_, by omega, ?_⟩
  · show (cacheRV p σ).Disjoint ⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩
    rw [es]; exact c1.symm
  · rw [hm]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact c0.sub_right hsc) (by omega)

/-- A load from the stack leaks only its address. -/
theorem ldrSp_trace {r : Reg} {off : Nat} {s u : State} {a : List Leak}
    (h : execBlock isa [.ldrSp r off] s = some (u, a)) :
    a = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := by
  simp only [execBlock] at h
  split at h
  · cases h
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at h
    exact h.2.symm

theorem vpro_piece {p : Params} (hF : VFacts p) {STK : Nat} (hSTK : 8 ≤ STK) :
    VPiece p STK (fun σ s => s = σ) (fun σ s => VC p STK σ s ∧ s.gpr .r11 = 1)
      (.block (pro ++ ([.ldrSp .r8 0] : List Instr))) := by
  refine ⟨fun σ s hp hs => by subst hs; exact vproC_ok hF hSTK hp, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  have hpro := Sample.taint_block (P := Rel2 (VPre p STK) (vPub p) fun σ s => s = σ) (is := pro)
    [.r0, .r1, .r2, .r3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by native_taint_decide)
  rw [Exec.block_iff, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, a₁⟩, h₁, g₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, a₂⟩, h₂, g₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨v₁, b₁⟩, f₁, k₁⟩ := Option.map_eq_some_iff.mp g₁
  obtain ⟨⟨v₂, b₂⟩, f₂, k₂⟩ := Option.map_eq_some_iff.mp g₂
  simp only [Prod.mk.injEq] at k₁ k₂
  have ea := (hpro _ _ _ _ _ _ hr (Exec.block h₁) (Exec.block h₂)).1
  obtain ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩ := hr
  subst i₁ i₂
  refine ⟨?_, trivial⟩
  rw [← k₁.2, ← k₂.2, ea, ldrSp_trace f₁, ldrSp_trace f₂, (execBlock_regions h₁).2.2.1,
    (execBlock_regions h₂).2.2.1, pub.1]

end VG.Proof.MlDsa.Arm.Verify
