module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.PkTr
public import VerifiedGarbage.Spec.MlDsa.PkTr
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.PkTr
meta import VerifiedGarbage.Spec.MlDsa.PkTr
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on RISC-V: `vg_mldsa*_pk_tr`

Untrusted: everything here is checked by Lean. The function
(`Impl/MlDsa/RISCV64/PkTr.lean`) in the setting of key generation's top-level
proof (`Proof/MlDsa/RISCV64/KeyGen/`): five buffers (`lay`: `scratch`, the
1168 bytes of stack the sponge uses, `pk` twice, as key generation's
read-only argument and as the buffer of `s9`, and `tr`), of which `scratch`,
the stack and `tr` are written (`Wb`); what holds throughout (`KC`: the
layout, our caller's registers saved in `scratch`, and the bytes of `pk`);
the prologue (`pro_piece`), the sponge (`hash_piece`, from `hashS`), and the
return (`epi_piece`, from `topEnd_ok`). It meets
`pkTrContract p RISCV64.abi 1168` (`pkTr_verified`), and leaks nothing.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PkTr

open VG VG.RISCV64 VG.Proof.MlKem.RISCV64
open VG.Proof.MlDsa.RISCV64.KeyGen (Site OkW disjW disjW' hashS hashS_tr pieceS hashLay hashLay_ptr ix ix_ne1 Two
  taint31 Piece rel_of relStart)
open VG.Impl.MlDsa.RISCV64.PkTr
open VG.Impl.MlKem.RISCV64 (topEnd topSave)
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-- The `l` bytes at `a`. -/
abbrev reg (a : Addr) (l : Nat) : Region := ⟨a, l⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

section
variable (σ : State)
abbrev pPk : Addr := σ.gpr .a0
abbrev pTr : Addr := σ.gpr .a1
abbrev pScr : Addr := σ.gpr .a2
end

/-- The precondition of `pkTrContract` with 1168 bytes of stack. -/
structure Pre (p : Params) (σ : State) : Prop where
  al : σ.sp.toNat % 16 = 0
  stk : 1168 ≤ σ.sp.toNat
  rd : σ.rd = [reg (pPk σ) p.pkLen]
  wr : σ.wr = [reg (pTr σ) 64, reg (pScr σ) (scrLen p)]
  d_pt : (reg (pPk σ) p.pkLen).Disjoint (reg (pTr σ) 64)
  d_pc : (reg (pPk σ) p.pkLen).Disjoint (reg (pScr σ) (scrLen p))
  d_tc : (reg (pTr σ) 64).Disjoint (reg (pScr σ) (scrLen p))
  b_p : (below σ.sp 1168).Disjoint (reg (pPk σ) p.pkLen)
  b_t : (below σ.sp 1168).Disjoint (reg (pTr σ) 64)
  b_c : (below σ.sp 1168).Disjoint (reg (pScr σ) (scrLen p))
  f_p : (pPk σ).toNat + p.pkLen ≤ 2 ^ 64
  f_t : (pTr σ).toNat + 64 ≤ 2 ^ 64
  f_c : (pScr σ).toNat + scrLen p ≤ 2 ^ 64
  al_c : (pScr σ).toNat % 8 = 0

theorem pre_of {p : Params} {σ : State} (h : (Spec.MlDsa.pkTrContract p RISCV64.abi 1168).pre σ) : Pre p σ := by
  sig_pre [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The public data of `pkTrContract`: the stack pointer and the pointers. -/
def Pub (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ pPk σ₁ = pPk σ₂ ∧ pTr σ₁ = pTr σ₂ ∧ pScr σ₁ = pScr σ₂

/-! ## The buffers -/

/-- The sizes of the buffers. -/
def sizes (p : Params) : List Nat := [scrLen p, 1168, p.pkLen, p.pkLen, 64]

/-- `scratch` (0), the stack (1), `pk` (2 and 3) and `tr` (4). -/
def lay (p : Params) (σ : State) : Lay :=
  ⟨fun i => [pScr σ, σ.sp - BitVec.ofNat 64 1168, pPk σ, pPk σ, pTr σ].getD i 0, sizes p⟩

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
  pk : 1024 < p.pkLen ∧ p.pkLen - 1024 < 2048 ∧ p.pkLen < 32768
  sav_pk : sepB (sizes p) (3, 0, p.pkLen) (0, 1288, 80) = true
  p1 : sepAll ([scrLen p, 1168, 0, p.pkLen, 64]) (3, 0, 1024) kRegs = true
  p2 : sepAll ([scrLen p, 1168, 0, p.pkLen, 64]) (3, 1024, p.pkLen - 1024) kRegs = true
  q : sepAll ([scrLen p, 1168, 0, p.pkLen, 64]) (4, 0, 64) kRegs = true
  w_sav : sepAll (sizes p) (0, 1288, 80) [(0, 0, 200), (1, 0, 1168), (4, 0, 64)] = true
  w_pk : sepAll (sizes p) (3, 0, p.pkLen) [(0, 0, 200), (1, 0, 1168), (4, 0, 64)] = true

theorem chk {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : Chk p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem lay_ok {p : Params} {σ : State} (hp : Pre p σ) : OkW (lay p σ) Wb := by
  have es : (⟨σ.sp - BitVec.ofNat 64 1168, 1168⟩ : Region) = below σ.sp 1168 := rfl
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [lay, sizes, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 64 1168).toNat + 1168 ≤ 2 ^ 64
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_p
    · exact hp.f_p
    · exact hp.f_t
  · simp only [lay, sizes, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Lay.buf, lay, sizes, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first
      | exact absurd rfl hij
      | (exfalso; simp [Wb] at hw; done)
      | (rw [es]; exact hp.b_c.symm) | (rw [es]; exact hp.b_c) | (rw [es]; exact hp.b_p)
      | (rw [es]; exact hp.b_p.symm) | (rw [es]; exact hp.b_t) | (rw [es]; exact hp.b_t.symm)
      | exact hp.d_pt | exact hp.d_pt.symm | exact hp.d_pc | exact hp.d_pc.symm
      | exact hp.d_tc | exact hp.d_tc.symm

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  site : Site (lay p σ) Wb 1168 s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  pres : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = σ.gpr r
  sav : TopSaved s.mem (pScr σ) σ
  pk : bytesAt s.mem ((lay p σ).A 3 0) p.pkLen = bytesAt σ.mem (pPk σ) p.pkLen

theorem saveR_lay (p : Params) (σ : State) : saveR (pScr σ) = (lay p σ).R 0 1288 80 := rfl

theorem pk_A (p : Params) (σ : State) : (lay p σ).A 3 0 = pPk σ := by
  simp only [Lay.A, BitVec.add_zero]; rfl

/-! ## The prologue -/

theorem pro_ok {p : Params} (hC : Chk p) {σ : State} (hp : Pre p σ) :
    WP isa (.block pro) σ (KC p σ) := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hC.scr
  have w0 : (lay p σ).buf 0 ∈ σ.wr := by
    rw [show (lay p σ).buf 0 = reg (pScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr (pScr σ + BitVec.ofNat 64 o) n := fun {o n} h =>
    Lay.covers (L := lay p σ) (o := o) (l := n) w0 (by show o + n ≤ scrLen p; omega_arith) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.al_c fun o _ h₂ => wS (by omega_arith))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .a0 = pPk σ := by rw [g₁]
  have g4 : s₁.gpr .a1 = pTr σ := by rw [g₁]
  have g6 : s₁.gpr .a2 = pScr σ := by rw [g₁]
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a0, mov .s8 .a1, mov .s11 .a2]) s₁ fun s =>
      s.gpr .s10 = pPk σ ∧ s.gpr .s9 = pPk σ ∧ s.gpr .s8 = pTr σ ∧ s.gpr .s11 = pScr σ ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    mrun [mov, g3, g4, g6]
    intro r _ hs
    simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    obtain ⟨-, -, -, -, -, a8, a9, a10, a11⟩ := hs
    simp only [a8, a9, a10, a11, ite_false]
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, cs, m, rd, wr, sp⟩ => ⟨⟨hL, rfl, by decide, by decide,
    by show 32768 ≤ scrLen p; omega_arith, rfl, by rw [sp, sp₁]; rfl, Nat.le_refl _, by rw [sp, sp₁]; exact hp.stk,
    by rw [sp, sp₁]; exact hp.al, hp.al_c, g31, g30, g29, g28,
    fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => (cs r hr hs).trans (by rw [g₁]), by rw [m]; exact sav, ?_⟩
  · show _ ∈ s.wr
    rw [wr, wr₁, hp.wr]
    simp only [Wb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · simp [Lay.buf, lay, sizes]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay, sizes]
  · show _ ∈ s.rd ++ s.wr
    rw [rd, rd₁, wr, wr₁, hp.rd, hp.wr]
    rcases (by omega_arith : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;>
      simp [Lay.buf, lay, sizes]
  · rw [m, pk_A]
    rw [← pk_A p σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      rw [saveR_lay p σ]
      exact disjW' (i := 3) (o := 0) (l := p.pkLen) (j := 0) (o' := 1288) (l' := 80) hL
        (by rw [lay_sizes]; exact hC.sav_pk) (.inr (.inl (by decide))))
      (by obtain ⟨-, -, h⟩ := hC.pk; omega)

theorem pro_piece {p : Params} (hC : Chk p) :
    Piece (Pre p) Pub (fun σ s => s = σ) (KC p) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hC hp,
    Sample.taint_block [.a0, .a1, .a2] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
      subst h₁ h₂; exact pub.1)
      (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [e0, e1, e2]) (by taint_decide)⟩

/-! ## `tr = H(pk, 64)` -/

/-- The sponge reads the buffers but `pk`'s first copy. -/
def K (i : Nat) : Bool := i != 2

theorem hK : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → K i = true → K j = true → i ∈ Wb ∨ j ∈ Wb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [K, bne_iff_ne, ne_eq] at hi hj
    simp only [Wb, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem hashLay_sizes (p : Params) (σ s : State) :
    (hashLay (lay p σ) s K).sizes = [scrLen p, 1168, 0, p.pkLen, 64] := rfl

theorem trPieces {p : Params} (hC : Chk p) {σ s : State} (hs : Site (lay p σ) Wb 1168 s) :
    (∀ pc ∈ ([⟨.s9, 0, 1024⟩, ⟨.s9, 1024, p.pkLen - 1024⟩] : List Impl.MlKem.RISCV64.Piece),
      PieceOk (hashLay (lay p σ) s K) ix s false pc) ∧
    PieceOk (hashLay (lay p σ) s K) ix s true (⟨.s8, 0, 64⟩ : Impl.MlKem.RISCV64.Piece) := by
  obtain ⟨h1, h2, h3⟩ := hC.pk
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide)
    (by rw [hashLay_sizes]; exact hC.q) (.inr rfl) fun _ => by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (by decide) (by decide)
      (by rw [hashLay_sizes]; exact hC.p1) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show (1024 : Nat) < 32768 by decide) h2 (by dsimp only; omega)
      (by rw [hashLay_sizes]; exact hC.p2) (.inr rfl) fun h => absurd h (by decide)

/-- After the sponge: `tr = H(pk, 64)`. -/
def KFin (p : Params) (σ s : State) : Prop :=
  KC p σ s ∧ bytesAt s.mem ((lay p σ).A 4 0) 64 = Spec.MlDsa.H (bytesAt σ.mem (pPk σ) p.pkLen) 64

theorem shake31 : BitVec.ofNat 8 31 = Spec.Sha3.shakeSuffix := by decide

theorem trHash_ok {p : Params} (hC : Chk p) {σ s : State} (h : KC p σ s) :
    WP isa (trHash p) s (KFin p σ) := by
  have hs := h.site
  have hL := hs.ok
  obtain ⟨hin, hq⟩ := trPieces hC hs
  unfold trHash
  refine WP.mono (hashS hs hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · have hd : ∀ {i o l : Nat}, sepAll (sizes p) (i, o, l) [(0, 0, 200), (1, 0, 1168), (4, 0, 64)] = true →
        ∀ r ∈ (lay p σ).RL [(0, 0, 200), (1, 0, 1168), (4, 0, 64)], ((lay p σ).R i o l).Disjoint r :=
      fun {i o l} hc r hr => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        refine disjW hL (List.all_eq_true.mp hc w hw) (.inr ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> decide
    refine ⟨hs.kept k', k'.rd.trans h.rd, k'.wr.trans h.wr, k'.sp.trans h.sp,
      fun r hr hs' => (k'.cs r hr).trans (h.pres r hr hs'),
      h.sav.keep k'.frame (by rw [saveR_lay p σ]; exact hd hC.w_sav), ?_⟩
    rw [Proof.MlKem.bytesAt_frame k'.frame (hd hC.w_pk) (by obtain ⟨-, -, h⟩ := hC.pk; omega)]; exact h.pk
  · have o₃ : bytesAt s'.mem ((lay p σ).A 4 0) 64 = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    obtain ⟨h1024', -, -⟩ := hC.pk
    have h1024 : 1024 ≤ p.pkLen := Nat.le_of_lt h1024'
    have e' : bytesAt s.mem ((lay p σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0) 1024 ++
        bytesAt s.mem ((lay p σ).ptr (ix Reg.s9) + BitVec.ofNat 64 1024) (p.pkLen - 1024) =
        bytesAt σ.mem (pPk σ) p.pkLen := by
      rw [← h.pk, show (lay p σ).ptr (ix Reg.s9) + BitVec.ofNat 64 1024 =
        (lay p σ).ptr (ix Reg.s9) + BitVec.ofNat 64 0 + BitVec.ofNat 64 1024 by rw [BitVec.add_zero],
        ← Proof.MlKem.bytesAt_add, Nat.add_sub_cancel' h1024]
      rfl
    rw [e', shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem two_of {p : Params} {σ₁ σ₂ x y : State} (pub : Pub σ₁ σ₂) (h₁ : KC p σ₁ x) (h₂ : KC p σ₂ y) :
    ∃ σ, Two (lay p σ) Wb 1168 x y :=
  ⟨σ₁, h₁.site, lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem hash_piece {p : Params} (hC : Chk p) : Piece (Pre p) Pub (KC p) (KFin p) (trHash p) :=
  ⟨fun _ _ _ h => trHash_ok hC h,
    rel_of (RelCT.exists_ fun σ => hashS_tr hK (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp)
      (fun s hs => (trPieces hC hs).1) (fun s hs => (trPieces hC hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁ h₂⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hC : Chk p) {σ s : State} (h : KFin p σ s) :
    WP isa (.block topEnd) s fun s' =>
      RISCV64.target.abiPreserved σ s' ∧ (Spec.MlDsa.pkTrContract p RISCV64.abi 1168).post σ s' := by
  obtain ⟨h, htr⟩ := h
  have hs := h.site
  obtain ⟨hscr, -⟩ := hC.scr
  have hin : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (pScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := lay p σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by show o + 8 ≤ scrLen p; omega_arith) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.s11 hs.al0 h.sav hin h.pres)
    fun s' ⟨pr, lr, _, m', sp', _, _⟩ => ⟨⟨pr, sp'.trans h.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs]
  have e4 : σ.gpr .a1 = (lay p σ).A 4 0 := by simp only [Lay.A, BitVec.add_zero]; rfl
  rw [m', e4, htr]
  rfl

theorem epi_tr (p : Params) (σ : State) : RelCT isa (Two (lay p σ) Wb 1168) (.block topEnd) fun _ _ => True :=
  taint31 (fun _ _ h => h) (by taint_decide)

theorem epi_piece {p : Params} (hC : Chk p) :
    Piece (Pre p) Pub (KFin p)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p RISCV64.abi 1168).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hC h, rel_of (RelCT.exists_ (epi_tr p))
    fun _ _ _ _ _ _ pub h₁ h₂ => two_of pub h₁.1 h₂.1⟩

/-! ## The function -/

theorem pkTr_piece {p : Params} (hC : Chk p) :
    Piece (Pre p) Pub (fun σ s => s = σ)
      (fun σ s => RISCV64.target.abiPreserved σ s ∧ (Spec.MlDsa.pkTrContract p RISCV64.abi 1168).post σ s)
      (pkTr p) :=
  (pro_piece hC).seq ((hash_piece hC).seq (epi_piece hC))

/-- A state satisfying `pkTrContract`'s precondition. -/
def pkTrSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩]
  wr := [⟨0x2000, 64⟩, ⟨0x10000, scrLen p⟩]

theorem pkTr_verified (p : Params) (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    (hsat : (Spec.MlDsa.pkTrContract p RISCV64.abi 1168).pre (pkTrSat p)) :
    Verified RISCV64.target (pkTr p) (Spec.MlDsa.pkTrContract p RISCV64.abi 1168) := by
  have hk := pkTr_piece (chk hp)
  refine ⟨fun s hs => hk.ok s s (pre_of hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    ⟨pkTrSat p, hsat⟩⟩
  sig_pub [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs] at hpub
  exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of h₁) (pre_of h₂) hpub e₁ e₂

theorem pkTr44_verified :
    Verified RISCV64.target (pkTr mlDsa44) (Spec.MlDsa.pkTrContract mlDsa44 RISCV64.abi 1168) :=
  pkTr_verified _ (.inl rfl) (by
    sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs, pkTrSat])

theorem pkTr65_verified :
    Verified RISCV64.target (pkTr mlDsa65) (Spec.MlDsa.pkTrContract mlDsa65 RISCV64.abi 1168) :=
  pkTr_verified _ (.inr (.inl rfl)) (by
    sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs, pkTrSat])

theorem pkTr87_verified :
    Verified RISCV64.target (pkTr mlDsa87) (Spec.MlDsa.pkTrContract mlDsa87 RISCV64.abi 1168) :=
  pkTr_verified _ (.inr (.inr rfl)) (by
    sig_sat_check [Spec.MlDsa.pkTrContract, Spec.MlDsa.pkTrSig, RISCV64.abi, RISCV64.argRegs, pkTrSat])

end VG.Proof.MlDsa.RISCV64.PkTr
