module

public import VerifiedGarbage.Impl.MlDsa.Arm.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.Arm.RowSum
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlKem.Arm.Reduce
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.MlDsa.Arm.PkTr
meta import VerifiedGarbage.Spec.MlDsa.PkTr
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Steps
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Reduce
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. The function
(`Impl/MlDsa/Arm/PkTr.lean`) in the setting of key generation's top-level
proof (`Proof/MlDsa/Arm/KeyGen/`): five buffers (`lay`: `scratch`, the 8
bytes of stack the sponge uses, `pk` twice, as key generation's read-only
argument and as the buffer of `r5`, and `tr`), of which `scratch`, the stack
and `tr` are written (`Wb`); what holds throughout (`KC`: the layout, our
caller's registers and `lr` saved in `scratch`, and the bytes of `pk`); the
prologue (`pro_piece`), the sponge (`hash_piece`, from `hashS`), and the
return (`epi_piece`, from `topEnd_ok`). It meets `pkTrContract p Arm.abi 8`
(`pkTr_verified`), and leaks nothing.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PkTr

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW disjW disjW' hashS hashS_tr pieceS hashLay hashLay_ptr ix ix_ne1 Two
  taint7 Piece rel_of relStart)
open VG.Impl.MlDsa.Arm.PkTr
open VG.Impl.MlKem.Arm (topEnd saveRegs oSave)
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

section
variable (σ : State)
abbrev pPk : BitVec 32 := σ.gpr .r0
abbrev pTr : BitVec 32 := σ.gpr .r1
abbrev pScr : BitVec 32 := σ.gpr .r2
end

/-- The precondition of `pkTrContract` with 8 bytes of stack. -/
structure Pre (p : Params) (σ : State) : Prop where
  stk : 8 ≤ σ.sp.toNat
  rd : σ.rd = [regA (pPk σ) p.pkLen]
  wr : σ.wr = [regA (pTr σ) 64, regA (pScr σ) (scrLen p)]
  d_pt : (regA (pPk σ) p.pkLen).Disjoint (regA (pTr σ) 64)
  d_pc : (regA (pPk σ) p.pkLen).Disjoint (regA (pScr σ) (scrLen p))
  d_tc : (regA (pTr σ) 64).Disjoint (regA (pScr σ) (scrLen p))
  b_p : (below σ 8).Disjoint (regA (pPk σ) p.pkLen)
  b_t : (below σ 8).Disjoint (regA (pTr σ) 64)
  b_c : (below σ 8).Disjoint (regA (pScr σ) (scrLen p))
  f_p : (pPk σ).toNat + p.pkLen ≤ 2 ^ 32
  f_t : (pTr σ).toNat + 64 ≤ 2 ^ 32
  f_c : (pScr σ).toNat + scrLen p ≤ 2 ^ 32

theorem pre_of {p : Params} {σ : State} (h : (Spec.MlDsa.pkTrContract p Arm.abi 8).pre σ) : Pre p σ := by
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The public data of `pkTrContract`: the stack pointer and the pointers. -/
def Pub (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ pPk σ₁ = pPk σ₂ ∧ pTr σ₁ = pTr σ₂ ∧ pScr σ₁ = pScr σ₂

/-! ## The buffers -/

/-- The sizes of the buffers. -/
def sizes (p : Params) : List Nat := [scrLen p, 8, p.pkLen, p.pkLen, 64]

/-- `scratch` (0), the stack (1), `pk` (2 and 3) and `tr` (4). -/
def lay (p : Params) (σ : State) : Lay :=
  ⟨fun i => [pScr σ, σ.sp - BitVec.ofNat 32 8, pPk σ, pPk σ, pTr σ].getD i 0, sizes p⟩

theorem lay_sizes (p : Params) (σ : State) : (lay p σ).sizes = sizes p := rfl

/-- The buffers written: `scratch`, the stack and `tr`. -/
abbrev Wb : List Nat := [0, 1, 4]

theorem lay_pub {p : Params} {σ₁ σ₂ : State} (h : Pub σ₁ σ₂) : lay p σ₁ = lay p σ₂ := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  simp only [lay, pPk, pTr, pScr] at *
  rw [e0, e1, e2, e3]

/-- What the proof uses of a parameter set: facts about the sizes, decided. -/
structure Chk (p : Params) : Prop where
  scr : 32768 ≤ scrLen p ∧ scrLen p < 2 ^ 31
  pk : 0 < p.pkLen ∧ p.pkLen < 32768
  encPk : encodable (BitVec.ofNat 32 p.pkLen) = true
  sav_pk : sepB (sizes p) (3, 0, p.pkLen) (0, 840, 36) = true
  p1 : sepAll ([scrLen p, 8, 0, p.pkLen, 64]) (3, 0, p.pkLen) kRegs = true
  q : sepAll ([scrLen p, 8, 0, p.pkLen, 64]) (4, 0, 64) kRegs = true
  w_sav : sepAll (sizes p) (0, 840, 36) [(0, 0, 200), (0, 200, 640), (1, 0, 8), (4, 0, 64)] = true
  w_pk : sepAll (sizes p) (3, 0, p.pkLen) [(0, 0, 200), (0, 200, 640), (1, 0, 8), (4, 0, 64)] = true

theorem chk {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : Chk p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem lay_ok {p : Params} {σ : State} (hp : Pre p σ) : OkW (lay p σ) Wb := by
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below σ 8 := by
    rw [addr_sub hp.stk]
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [lay, sizes, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_p
    · exact hp.f_p
    · exact hp.f_t
  · simp only [lay, sizes, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [lay, sizes, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first
      | exact absurd rfl hij
      | (rw [es]; exact hp.b_c.symm) | (rw [es]; exact hp.b_c) | (rw [es]; exact hp.b_p)
      | (rw [es]; exact hp.b_p.symm) | (rw [es]; exact hp.b_t) | (rw [es]; exact hp.b_t.symm)
      | exact hp.d_pt | exact hp.d_pt.symm | exact hp.d_pc | exact hp.d_pc.symm
      | exact hp.d_tc | exact hp.d_tc.symm
      | (exfalso; simp [Wb] at hw; done)

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  site : Site (lay p σ) Wb 8 s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : Saved s.mem ((lay p σ).A 0 840) σ.gpr
  lr : s.mem.readW ((lay p σ).A 0 872) 32 = σ.gpr .lr
  pk : bytesAt s.mem ((lay p σ).A 3 0) p.pkLen = bytesAt σ.mem (State.addr (pPk σ)) p.pkLen

theorem pk_A (p : Params) (σ : State) : (lay p σ).A 3 0 = State.addr (pPk σ) := by
  simp only [Lay.A, add_ofNat_zero]; rfl

/-! ## The prologue -/

theorem pro_ok {p : Params} (hC : Chk p) {σ : State} (hp : Pre p σ) :
    WP isa (.block pro) σ (KC p σ) := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hC.scr
  have w0 : (lay p σ).buf 0 ∈ σ.wr := by
    rw [show (lay p σ).buf 0 = regA (pScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have eA : ∀ o, (lay p σ).A 0 o = State.addr (σ.gpr .r2) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((lay p σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by show o + n ≤ scrLen p; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r2 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega)) fun s₁ h₁ => ?_
  have g2 : s₁.gpr .r2 = pScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (lay p σ).A 0 872 := by
    rw [g2]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r2 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  run_block [i872, o1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay p σ).A 0 872) v).readW
      ((lay p σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay p σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega_arith) (by decide)
  have fr : Frame [(lay p σ).R 0 840 36] σ.mem (s₁.mem.writeW ((lay p σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(lay p σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (lay p σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega_arith
    · simp only [Region.Contains, eA]; bv_omega_arith
  refine ⟨⟨hL, rfl, by decide, by decide, by show 32768 ≤ scrLen p; omega, rfl,
    show σ.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8 by rw [h₁.sp], Nat.le_refl _,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [Wb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Lay.buf, lay, sizes]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay, sizes]
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, lay, sizes]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (lay p σ).A 0 872 = (lay p σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, ← pk_A p σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disjW' (i := 3) (o := 0) (l := p.pkLen) (j := 0) (o' := 840) (l' := 36) hL
        (by rw [lay_sizes]; exact hC.sav_pk) (.inr (.inl (by decide))))
      (by obtain ⟨-, h⟩ := hC.pk; omega)

theorem pro_piece {p : Params} (hC : Chk p) :
    Piece (Pre p) Pub (fun σ s => s = σ) (KC p) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hC hp,
    Sample.taint_block [.r0, .r1, .r2] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [e0, e1, e2]) (by native_taint_decide)⟩

/-! ## `tr = H(pk, 64)` -/

/-- The sponge reads the buffers but `pk`'s first copy. -/
def K (i : Nat) : Bool := i != 2

theorem hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [K, bne_iff_ne, ne_eq] at hi hj
    simp only [Wb, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem hashLay_sizes (p : Params) (σ s : State) :
    (hashLay (lay p σ) s K).sizes = [scrLen p, 8, 0, p.pkLen, 64] := rfl

theorem trPieces {p : Params} (hC : Chk p) {σ s : State} (hs : Site (lay p σ) Wb 8 s) :
    (∀ pc ∈ ([⟨.r5, 0, p.pkLen⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (lay p σ) s K) ix s false pc) ∧
    PieceOk (hashLay (lay p σ) s K) ix s true (⟨.r6, 0, 64⟩ : Impl.MlKem.Arm.Piece) := by
  obtain ⟨h1, h2⟩ := hC.pk
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide) (by decide)
    (by rw [hashLay_sizes]; exact hC.q) (.inr rfl) fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide) hC.encPk h1
    (show 0 + p.pkLen < 2 ^ 32 by omega) (by rw [hashLay_sizes]; exact hC.p1) (.inr rfl)
    fun h => absurd h (by decide)

/-- After the sponge: `tr = H(pk, 64)`. -/
def KFin (p : Params) (σ s : State) : Prop :=
  KC p σ s ∧ bytesAt s.mem ((lay p σ).A 4 0) 64 = Spec.MlDsa.H (bytesAt σ.mem (State.addr (pPk σ)) p.pkLen) 64

theorem shake31 : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem trHash_ok {p : Params} (hC : Chk p) {σ s : State} (h : KC p σ s) :
    WP isa (trHash p) s (KFin p σ) := by
  have hs := h.site
  have hL := hs.ok
  obtain ⟨hin, hq⟩ := trPieces hC hs
  unfold trHash
  refine WP.mono (hashS hs hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · have hd : ∀ {i o l : Nat},
        sepAll (sizes p) (i, o, l) [(0, 0, 200), (0, 200, 640), (1, 0, 8), (4, 0, 64)] = true →
        ∀ r ∈ (lay p σ).RL [(0, 0, 200), (0, 200, 640), (1, 0, 8), (4, 0, 64)], ((lay p σ).R i o l).Disjoint r :=
      fun {i o l} hc r hr => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        refine disjW hL (List.all_eq_true.mp hc w hw) (.inr ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> decide
    refine ⟨hs.kept k', k'.rd.trans h.rd, k'.wr.trans h.wr, k'.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
    · rw [k'.frame.readW (r := (lay p σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith)
        (hd hC.w_sav) (by decide)]
      exact h.sav i hi
    · rw [k'.frame.readW (r := (lay p σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega_arith)
        (hd hC.w_sav) (by decide)]
      exact h.lr
    · rw [Proof.MlKem.bytesAt_frame k'.frame (hd hC.w_pk) (by obtain ⟨-, h⟩ := hC.pk; omega)]; exact h.pk
  · have o₃ : bytesAt s'.mem ((lay p σ).A 4 0) 64 = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e : bytesAt s.mem (State.addr ((lay p σ).ptr (ix Reg.r5)) + 0#64) p.pkLen =
        bytesAt σ.mem (State.addr (pPk σ)) p.pkLen := h.pk
    rw [e, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem two_of {p : Params} {σ₁ σ₂ x y : State} (pub : Pub σ₁ σ₂) (h₁ : KC p σ₁ x) (h₂ : KC p σ₂ y) :
    ∃ σ, Two (lay p σ) Wb 8 x y :=
  ⟨σ₁, h₁.site, lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem hash_piece {p : Params} (hC : Chk p) : Piece (Pre p) Pub (KC p) (KFin p) (trHash p) :=
  ⟨fun _ _ _ h => trHash_ok hC h,
    rel_of (RelCT.exists_ fun σ => hashS_tr hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
      (by simp) (fun s hs => (trPieces hC hs).1) (fun s hs => (trPieces hC hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁ h₂⟩

/-! ## The return -/

theorem epi_ok {p : Params} {σ s : State} (h : KFin p σ s) :
    WP isa (.block topEnd) s fun s' =>
      Arm.target.abiPreserved σ s' ∧ (Spec.MlDsa.pkTrContract p Arm.abi 8).post σ s' := by
  obtain ⟨h, htr⟩ := h
  have hs := h.site
  have e0 : ∀ o, (hashLay (lay p σ) s K).A 0 o = (lay p σ).A 0 o := fun o => by
    simp only [Lay.A, hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx hK) (by rw [e0]; exact h.sav) (by rw [e0]; exact h.lr))
    fun s' ⟨pr, _, m', sp'⟩ => ⟨⟨pr, sp'.trans h.sp⟩, ?_⟩
  sig_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e4 : BitVec.setWidth 64 (σ.gpr .r1) = (lay p σ).A 4 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  rw [m', e4, htr]
  rfl

theorem epi_tr (p : Params) (σ : State) : RelCT isa (Two (lay p σ) Wb 8) (.block topEnd) fun _ _ => True :=
  taint7 (fun _ _ h => h) (by native_taint_decide)

theorem epi_piece {p : Params} :
    Piece (Pre p) Pub (KFin p)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p Arm.abi 8).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok h, rel_of (RelCT.exists_ (epi_tr p))
    fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁.1 h₂.1⟩

/-! ## The function -/

theorem pkTr_piece {p : Params} (hC : Chk p) :
    Piece (Pre p) Pub (fun σ s => s = σ)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p Arm.abi 8).post σ s)
      (pkTr p) :=
  (pro_piece hC).seq ((hash_piece hC).seq epi_piece)

/-- A state satisfying `pkTrContract`'s precondition. -/
def pkTrSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x2000, 64⟩, ⟨0x10000, scrLen p⟩]

theorem pkTr_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) :
    Verified Arm.target (pkTr p) (Spec.MlDsa.pkTrContract p Arm.abi 8) := by
  have hk := pkTr_piece (chk hp)
  refine ⟨fun s hs => hk.ok s s (pre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of h₁) (pre_of h₂) hpub e₁ e₂
  · refine ⟨pkTrSat p, ?_⟩
    rcases hp with rfl | rfl | rfl <;>
    sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, pkTrSat]

theorem pkTr44_verified : Verified Arm.target (pkTr mlDsa44) (Spec.MlDsa.pkTrContract mlDsa44 Arm.abi 8) :=
  pkTr_verified _ (.inl rfl)
theorem pkTr65_verified : Verified Arm.target (pkTr mlDsa65) (Spec.MlDsa.pkTrContract mlDsa65 Arm.abi 8) :=
  pkTr_verified _ (.inr (.inl rfl))
theorem pkTr87_verified : Verified Arm.target (pkTr mlDsa87) (Spec.MlDsa.pkTrContract mlDsa87 Arm.abi 8) :=
  pkTr_verified _ (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.PkTr
