module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
import VerifiedGarbage.Proof.MlKem.PPC64LE.EncryptCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowCT
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.RowSum
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encrypt
public import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.EncapsHSat
meta import VerifiedGarbage.Proof.MlKem.EncapsHSat
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Encrypt
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-! ### `MlKem.PPC64LE.Encaps`, which this module and modules that import it used -/

section

/-!
# ML-KEM on PPC64LE: encapsulation, correctness

As on 32-bit ARM (`Proof/MlKem/Arm/Encaps.lean`): `K.encaps` for any
parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch`, the 48 bytes below the stack
pointer, `ek`, `key` and `ct`; `m`, which may overlap `ek`, is only read by
its copy into `scratch`, with a layout of its own (`layM`). What every phase
keeps (`EnEnv`), and the phases: the setup, `m` copied, `H(ek)`,
`G(m ‖ H(ek))` into `K ‖ r`, `K` copied into `key`, and K-PKE.Encrypt
(`Enc.encrypt_ok`) into `ct`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Encaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Impl.Sha3.PPC64LE.Stream (mov)

section
variable (s₀ : State)

abbrev pEk : Addr := s₀.gpr .r3
abbrev pM : Addr := s₀.gpr .r4
abbrev pKey : Addr := s₀.gpr .r5
abbrev pCt : Addr := s₀.gpr .r6
abbrev pScr : Addr := s₀.gpr .r7

/-- The buffers: `scratch`, the 48 bytes below the stack pointer, `ek`, `key` and `ct`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 48, pEk s₀, pKey s₀, pCt s₀].getD i 0,
    [K.scratch, 48, K.ekLen, 32, K.ctLen]⟩

/-- The buffers of the copy of `m`: `scratch`, the stack and `m`. -/
def layM (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 48, pM s₀].getD i 0, [K.scratch, 48, 32]⟩

end

/-- The sizes of the buffers. -/
abbrev eSz (K : KemLay) : List Nat := [K.scratch, 48, K.ekLen, 32, K.ctLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = eSz K := rfl

theorem layM_sizes (K : KemLay) (s₀ : State) : (layM s₀ K).sizes = [K.scratch, 48, 32] := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp48 : 48 ≤ s.sp.toNat
  rdEk : (⟨pEk s, K.ekLen⟩ : Region) ∈ s.rd
  rdM : (⟨pM s, 32⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨pKey s, 32⟩, ⟨pCt s, K.ctLen⟩, ⟨pScr s, K.scratch⟩]
  d_ek_key : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_ek_ct : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pCt s, K.ctLen⟩
  d_ek_scr : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_m_key : (⟨pM s, 32⟩ : Region).Disjoint ⟨pKey s, 32⟩
  d_m_ct : (⟨pM s, 32⟩ : Region).Disjoint ⟨pCt s, K.ctLen⟩
  d_m_scr : (⟨pM s, 32⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_key_ct : (⟨pKey s, 32⟩ : Region).Disjoint ⟨pCt s, K.ctLen⟩
  d_key_scr : (⟨pKey s, 32⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_ct_scr : (⟨pCt s, K.ctLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  b_ek : (below s.sp 48).Disjoint ⟨pEk s, K.ekLen⟩
  b_m : (below s.sp 48).Disjoint ⟨pM s, 32⟩
  b_key : (below s.sp 48).Disjoint ⟨pKey s, 32⟩
  b_ct : (below s.sp 48).Disjoint ⟨pCt s, K.ctLen⟩
  b_scr : (below s.sp 48).Disjoint ⟨pScr s, K.scratch⟩
  f_ek : (pEk s).toNat + K.ekLen ≤ 2 ^ 64
  f_m : (pM s).toNat + 32 ≤ 2 ^ 64
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 64
  f_ct : (pCt s).toNat + K.ctLen ≤ 2 ^ 64
  f_scr : (pScr s).toNat + K.scratch ≤ 2 ^ 64

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_fit : (s₀.sp - BitVec.ofNat 64 48).toNat + 48 ≤ 2 ^ 64 := by
  have := hp.sp48
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]
  have := s₀.sp.isLt; omega_using []

theorem lay_ok : (lay s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_ek
    · exact hp.f_key
    · exact hp.f_ct
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega_using [hj, hij] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega_using [hj, hij] : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_scr.symm
    · exact hp.d_ek_scr.symm
    · exact hp.d_key_scr.symm
    · exact hp.d_ct_scr.symm
    · exact hp.b_ek
    · exact hp.b_key
    · exact hp.b_ct
    · exact hp.d_ek_key
    · exact hp.d_ek_ct
    · exact hp.d_key_ct

theorem layM_ok : (layM s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [layM, List.length_cons, List.length_nil] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_m
  · simp only [layM, List.length_cons, List.length_nil] at hi hj
    rcases (by omega_using [hj, hij] : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega_using [hj, hij] : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [layM, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_scr.symm
    · exact hp.d_m_scr.symm
    · exact hp.b_m

end

/-- What every phase keeps: the pointers, the callee-saved registers we do
not save, our caller's registers in `scratch`, and `ek`. -/
structure EnEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  r30 : s.gpr .r30 = pEk s₀
  r28 : s.gpr .r28 = pKey s₀
  r27 : s.gpr .r27 = pCt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  ek : bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen = bytesAt s₀.mem ((lay s₀ K).A 2 0) K.ekLen

/-- A region the phases may change: apart from the saved registers and `ek`. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := sepB (eSz K) (0, 840, 72) w && sepB (eSz K) (2, 0, K.ekLen) w

/-- The buffer of each pointer register. -/
def eidx : Reg → Nat
  | .r30 => 2 | .r28 => 3 | .r27 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
tactic_template "edecide" : tactic => `(tactic| first
                   | decide
                   | ((try simp only [lay_sizes, layM_sizes, eSz, okW, eidx, kRegs, List.all_cons, List.all_nil,
                         List.all_append, List.map_cons, List.map_nil, trip, Bool.and_true])
                      (try have := (‹KemLay.WF _›).scr)
                      kdecide))

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 840 72 := rfl

theorem EnEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .r30 ∧ x ≠ .r28 ∧ x ≠ .r27 ∧ x ≠ .r31) (hW : W.all (okW K) = true) :
    EnEnv K s₀ s' := by
  have hL := lay_ok hp
  have hK := hp.wf
  have h1 : sepAll (lay s₀ K).sizes (0, 840, 72) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (2, 0, K.ekLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .r30 ∨ r = .r28 ∨ r = .r27 ∨ r = .r31 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c, d⟩ := hx r hm
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨hk.ctx (nx _ (by simp)) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun r hr hs => ?_, h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_⟩
  · rw [hk.cs .r30 (by decide) (nx _ (by simp)), h.r30]
  · rw [hk.cs .r28 (by decide) (nx _ (by simp)), h.r28]
  · rw [hk.cs .r27 (by decide) (nx _ (by simp)), h.r27]
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [Lay.bytes_keep hL hk.frame h2 (by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])]; exact h.ek

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr]; simp [Lay.buf, lay, layM, hp.rdEk, hp.rdM]

theorem A_zero (L : Lay) (i : Nat) : L.A i 0 = L.ptr i := BitVec.add_zero _

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block encapsSetup) s₀ fun s => EnEnv K s₀ s ∧ s.gpr .r29 = pM s₀ ∧
      bytesAt s.mem ((layM s₀ K).A 2 0) 32 = bytesAt s₀.mem ((layM s₀ K).A 2 0) 32 := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hw : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) 8 := fun o h₁ h₂ =>
    Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [scr, h₂]) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok (.inr rfl) rfl hw) fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = pEk s₀ := g₁ _ (by decide)
  have g4 : s₁.gpr .r4 = pM s₀ := g₁ _ (by decide)
  have g5 : s₁.gpr .r5 = pKey s₀ := g₁ _ (by decide)
  have g6 : s₁.gpr .r6 = pCt s₀ := g₁ _ (by decide)
  have g7 : s₁.gpr .r7 = pScr s₀ := g₁ _ (by decide)
  have hmv : WP isa (.block [mov .r30 .r3, mov .r29 .r4, mov .r28 .r5, mov .r27 .r6, mov .r31 .r7]) s₁ fun s =>
      s.gpr .r30 = pEk s₀ ∧ s.gpr .r29 = pM s₀ ∧ s.gpr .r28 = pKey s₀ ∧ s.gpr .r27 = pCt s₀ ∧
      s.gpr .r31 = pScr s₀ ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    prun [g3, g4, g5, g6, g7]
    and_intros
    all_goals first
      | exact trivial
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [RegUpd.gpr_write, a27, a28, a29, a30, a31, ite_false])
  refine WP.mono hmv fun s ⟨g30, g29, g28, g27, g31, cs, m, rd, wr, sp⟩ => ?_
  have fr' : Frame ((lay s₀ K).RL [(0, 840, 72)]) s₀.mem s.mem := by rw [m]; exact fr
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this]
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp48, by rw [sp, sp₁]; rfl,
    by rw [wr, wr₁, hp.wr]; simp [lay]⟩, g30, g28, g27, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => ?_, by rw [m]; exact sav, ?_⟩, g29, ?_⟩
  · rw [cs r hr hs]; exact g₁ r (by rintro rfl; simp [preserved] at hr)
  · exact Lay.bytes_keep hL fr' (by edecide) ek
  · rw [m]; exact Lay.bytes_keep (layM_ok hp) (L := layM s₀ K) (W := [(0, 840, 72)]) fr (by edecide) (by decide)

/-! ## `m` copied -/

/-- `m`. -/
abbrev M (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((layM s₀ K).A 2 0) 32

/-- `ek`. -/
abbrev EK (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((lay s₀ K).A 2 0) K.ekLen

theorem layA0 (K : KemLay) (s₀ : State) (o : Nat) : (layM s₀ K).A 0 o = (lay s₀ K).A 0 o := rfl

theorem copyM_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) (h29 : s.gpr .r29 = pM s₀)
    (hm : bytesAt s.mem ((layM s₀ K).A 2 0) 32 = M K s₀) :
    WP isa (copy .r29 0 .r31 oMsg 32) s fun s' =>
      EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ ∧
        Kept ((lay s₀ K).RL [(0, oMsg, 32)]) s s' := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, wM, wM0⟩ := buf_wr hp
  refine WP.mono (copyL (layM_ok hp) (i := 2) (j := 0) (by decide) (by decide) h29
    h.ctx.r31 (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_, k⟩
  · have k' : Kept ((lay s₀ K).RL [(0, oMsg, 32)]) s s' := k
    exact h.keep hp (k'.x []) (by simp) (by edecide)
  · rw [← layA0, e, hm]

theorem ptr29_ok {s : State} :
    WP isa (.block [.addi .r29 .r31 oMsg]) s fun s' =>
      KeptX [.r29] [] s s' ∧ s'.gpr .r29 = s.gpr .r31 + BitVec.ofNat 64 oMsg ∧ s'.mem = s.mem := by
  have e1 : oMsg < 32768 := by decide
  prun [e1]
  refine ⟨⟨fun r _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  exact RegUpd.gpr_write_of_ne _ _ fun e => hx (by rw [e]; exact List.mem_singleton_self _)

/-! ## The hashes -/

theorem pieceE {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r30 ∨ p.base = .r31) (hw : w = true → p.base = .r31)
    (hoe : p.off < 32768) (hle : p.len < 32768) (hpos : 0 < p.len)
    (hsep : sepAll (eSz K) (eidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) eidx s w p := by
  obtain ⟨w0, -, -, w2, -, -⟩ := buf_wr hp
  rw [← h.wr] at w0
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.r30
    · exact h.ctx.r31
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

theorem hashH_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) :
    WP isa (hash 136 0x06 [⟨.r30, 0, K.ekLen⟩] [⟨.r31, oHek, 32⟩]) s fun s' =>
      EnEnv K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oHek, 32)])) s.mem s'.mem ∧
      s'.gpr .r29 = s.gpr .r29 ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.r30, 0, K.ekLen⟩ : Piece)], PieceOk (lay s₀ K) eidx s false p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inl rfl) (by simp) (by show 0 < 32768; decide)
      (by show K.ekLen < 32768; have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])
      (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega_using []) (by edecide)
  have hout : ∀ p ∈ [(⟨.r31, oHek, 32⟩ : Piece)], PieceOk (lay s₀ K) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)
  refine WP.mono (hash_ok (idx := eidx) VG.Proof.MlKem.rate136 (by decide) h.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k.frame, k.cs .r29 (by decide), ?_⟩
  have e := o.1
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
  refine e.trans ?_
  show _ = H (EK K s₀)
  have ek : bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen = EK K s₀ := h.ek
  rw [VG.Proof.MlKem.H_eq, ← ek]; rfl

theorem hashG_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩] [⟨.r31, oG, 64⟩]) s fun s' =>
      EnEnv K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧ s'.gpr .r29 = s.gpr .r29 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = (G (M K s₀ ++ H (EK K s₀))).1 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = (G (M K s₀ ++ H (EK K s₀))).2 := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.r31, oMsg, 32⟩ : Piece), ⟨.r31, oHek, 32⟩], PieceOk (lay s₀ K) eidx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
  have hout : ∀ p ∈ [(⟨.r31, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)
  have hin' : (List.map ((lay s₀ K).pb eidx s.mem) [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩]).flatten =
      M K s₀ ++ H (EK K s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 ++ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = _
    rw [hm, hh]
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) h.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ =>
    ⟨?_, k'.frame, k'.cs .r29 (by decide), ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by edecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀ K).A 0 oG) 64 =
        (G (M K s₀ ++ H (EK K s₀))).1 ++ (G (M K s₀ ++ H (EK K s₀))).2 :=
      e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀ K).A 0 oG) 32).length = (G (M K s₀ ++ H (EK K s₀))).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem ((lay s₀ K).ptr 0 + BitVec.ofNat 64 (920 + 32)) 32 = _
    rw [← ptr_add]; exact r2

theorem copyK_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) :
    WP isa (copy .r31 oG .r28 0 32) s fun s' => EnEnv K s₀ s' ∧ Kept ((lay s₀ K).RL [(3, 0, 32)]) s s' ∧
      bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = bytesAt s.mem ((lay s₀ K).A 0 oG) 32 := by
  have hK := hp.wf
  obtain ⟨w0, w3, -, -, -, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) (by decide) (by decide) h.ctx.r31 h.r28
    (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun s' ⟨k, e⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k, e⟩

/-! ## K-PKE.Encrypt -/

/-- The buffers of `encrypt`: `ek`, the copy of `m`, and `ct`. -/
abbrev eb : EB := ⟨2, 0, 0, oMsg, 4, 0⟩

theorem encPre {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (h29 : s.gpr .r29 = (lay s₀ K).A 0 oMsg) : EncPre K (lay s₀ K) eb s := by
  have hK := hp.wf
  obtain ⟨w0, -, w4, w2, -, -⟩ := buf_wr hp
  exact ⟨hK, hp.calls, h.ctx, by rw [h.r30, A_zero]; rfl, h29, by rw [h.r27, A_zero]; rfl, by edecide,
    by edecide, by edecide, by rw [h.rd, h.wr]; exact w2, by rw [h.rd, h.wr]; exact mem_rd_wr w0,
    by rw [h.wr]; exact w4⟩

theorem encW_ok {K : KemLay} (hK : K.WF) :
    (encW K eb).all (okW K) = true ∧ sepAll (eSz K) (3, 0, 32) (encW K eb) = true := by
  have := hK.scr
  constructor <;> edecide

/-! ## The phases, from the copy of `m` on -/

section
variable (K : KemLay) (s₀ : State)

/-- `K`, the first output of `G(m ‖ H(ek))`. -/
abbrev KK : List Byte := (G (M K s₀ ++ H (EK K s₀))).1

/-- `r`, the second output of `G(m ‖ H(ek))`. -/
abbrev RR : List Byte := (G (M K s₀ ++ H (EK K s₀))).2

/-- After the copy of `m`, with its pointer in `r29`. -/
abbrev F4 (s : State) : Prop := EnEnv K s₀ s ∧ s.gpr .r29 = (lay s₀ K).A 0 oMsg ∧
  bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀

end

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem s4_ok {s : State} (h : EnEnv K s₀ s) (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀) :
    WP isa (.block [.addi .r29 .r31 oMsg]) s (F4 K s₀) :=
  WP.mono ptr29_ok fun _ ⟨k, g29, m⟩ =>
    ⟨h.keep hp (W := []) k (by simp [savedTop]) rfl, by rw [g29, h.ctx.r31], by rw [m]; exact hm⟩

theorem s5_ok {s : State} (h : F4 K s₀ s) :
    WP isa (hash 136 0x06 [⟨.r30, 0, K.ekLen⟩] [⟨.r31, oHek, 32⟩]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) := by
  have hK := hp.wf
  exact WP.mono (hashH_ok hp h.1) fun _ ⟨e, f, g29, hh⟩ =>
    ⟨⟨e, by rw [g29, h.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.2.2⟩, hh⟩

theorem s6_ok {s : State} (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩] [⟨.r31, oG, 64⟩]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = KK K s₀ ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (hashG_ok hp h.1.1 h.1.2.2 h.2) fun _ ⟨e, f, g29, k, r⟩ =>
    ⟨⟨e, by rw [g29, h.1.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.1.2.2⟩, k, r⟩

theorem s7_ok {s : State}
    (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = KK K s₀ ∧
      bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀) :
    WP isa (copy .r31 oG .r28 0 32) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (copyK_ok hp h.1.1) fun _ ⟨e, k, key⟩ =>
    ⟨⟨e, by rw [k.cs .r29 (by decide), h.1.2.1],
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.1.2.2⟩, key.trans h.2.1,
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.2.2⟩

theorem s8_ok {s : State}
    (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀) :
    WP isa K.encrypt s fun s' => EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      s'.gpr .r24 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
      bytesAt s'.mem ((lay s₀ K).A 4 0) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀) := by
  have hK := hp.wf
  have eρ : ρE K (lay s₀ K) eb s = ekRho K.p (EK K s₀) := by
    show ekRho K.p (bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen) = _
    rw [h.1.1.ek]
  have er : rB (lay s₀ K) s = RR K s₀ := h.2.2
  have e1 : ekB K (lay s₀ K) eb s = EK K s₀ := h.1.1.ek
  have e2 : mB (lay s₀ K) eb s = M K s₀ := h.1.2.2
  refine WP.mono (encrypt_ok (encPre hp h.1.1 h.1.2.1)) fun s' ⟨K', r24, ct⟩ =>
    ⟨h.1.1.keep hp K' (by simp [savedTop]) (encW_ok hK).1,
      (Lay.bytes_keep (lay_ok hp) K'.frame (encW_ok hK).2 (by decide)).trans h.2.1, ?_, ?_⟩
  · rw [r24]; show (if okEnc K.k (ρE K (lay s₀ K) eb s) K.k = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)
    rw [← eρ, ← er]; exact ct

end

/-! ## The whole function -/

theorem end_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      s'.gpr .r3 = s.gpr .r24 ∧ s'.mem = s.mem ∧ s'.sp = s₀.sp := by
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hK := hp.wf
  refine WP.mono (topEnd_ok h.ctx.r31 h.sav (fun o h₁ h₂ => ?_) h.cs) fun s' ⟨pr, lr, r3, m, sp, _, _⟩ =>
    ⟨pr, lr, r3, m, sp.trans h.sp⟩
  rw [h.rd, h.wr]
  have scr := hK.scr
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [h₂, scr]
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

/-- What follows `H(ek)` (in `encaps`; its copy from `h` in `encapsH`): `G(m ‖ H(ek))`, `K` into `key`,
K-PKE.Encrypt and the end. -/
abbrev tail (K : KemLay) : Prog isa :=
  .seq (hash 72 0x06 [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩] [⟨.r31, oG, 64⟩]) <|
  .seq (copy .r31 oG .r28 0 32) <|
  .seq K.encrypt (.block topEnd)

/-- What the function ensures, of the arguments of `s₀`. -/
abbrev Post (K : KemLay) (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
    s.gpr .r3 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
    bytesAt s.mem (pKey s₀) 32 = KK K s₀ ∧
    bytesAt s.mem (pCt s₀) K.ctLen =
      VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀)
    (h₅ : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (tail K) s (Post K s₀) := by
  refine WP.seq (WP.mono (s6_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (s7_ok hp h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (s8_ok hp h₇) fun s₈ ⟨h₈, key₈, r24₈, ct₈⟩ => ?_)
  refine WP.mono (end_ok hp h₈) fun s ⟨pr, lr, r3, m', sp'⟩ => ⟨pr, sp', lr, by rw [r3, r24₈], ?_, ?_⟩
  · show bytesAt s.mem ((lay s₀ K).ptr 3) 32 = _
    rw [m', ← A_zero (lay s₀ K) 3]; exact key₈
  · show bytesAt s.mem ((lay s₀ K).ptr 4) K.ctLen = _
    rw [m', ← A_zero (lay s₀ K) 4]; exact ct₈

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) : WP isa K.encaps s₀ (Post K s₀) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₂ ⟨h₂, g29, m₂⟩ => ?_)
  refine WP.seq (WP.mono (copyM_ok hp h₂ g29 m₂) fun s₃ ⟨h₃, m₃, _⟩ => ?_)
  refine WP.seq (WP.mono (s4_ok hp h₃ m₃) fun s₄ h₄ => ?_)
  exact WP.seq (WP.mono (s5_ok hp h₄) fun s₅ h₅ => tail_ok hp h₅)

/-! ## `encapsH`: `H(ek)` given at `h`

`encapsH` takes `encaps`'s arguments with `h` after `ek`, so its phases are
`encaps`'s, of the arguments `args s₀` (`ek`, `m`, `key`, `ct` and `scratch`
in `a0`–`a4`): its setup (`setupH_ok`), the copy of `h` into `H(ek)`'s place
(`copyH_ok`), and then `encaps`'s phases from the copy of `m` on, but the
hash of `ek`. Its own buffer `h`, which it only reads, has a layout of its own
(`layH`), as `m`. -/

/-- The arguments of `encaps` from those of `encapsH` in `s₀`: `ek` in `r3`;
`m`, `key`, `ct` and `scratch`, in `r5`–`r8`, in `r4`–`r7`. -/
def args (s₀ : State) : State :=
  { s₀ with gpr := fun r => match r with
    | .r4 => s₀.gpr .r5 | .r5 => s₀.gpr .r6 | .r6 => s₀.gpr .r7 | .r7 => s₀.gpr .r8 | r => s₀.gpr r }

theorem args_preserved (s₀ : State) : ∀ r ∈ preserved, (args s₀).gpr r = s₀.gpr r := by
  intro r hr
  cases r <;> first | rfl | simp [preserved] at hr

abbrev pH (s₀ : State) : Addr := s₀.gpr .r4

/-- The buffers of the copy of `h`: `scratch`, the stack and `h`. -/
def layH (K : KemLay) (s₀ : State) : Lay :=
  ⟨fun i => [pScr (args s₀), s₀.sp - BitVec.ofNat 64 48, pH s₀].getD i 0, [K.scratch, 48, 32]⟩

theorem layH_sizes (K : KemLay) (s₀ : State) : (layH K s₀).sizes = [K.scratch, 48, 32] := rfl

/-- The precondition of `encapsH`'s contract: `encaps`'s, of `args s`, and `h`,
which holds `H(ek)`. -/
structure PreH (K : KemLay) (s : State) : Prop where
  pre : Pre K (args s)
  rdH : (⟨pH s, 32⟩ : Region) ∈ s.rd
  d_h_scr : (⟨pH s, 32⟩ : Region).Disjoint ⟨pScr (args s), K.scratch⟩
  b_h : (below s.sp 48).Disjoint ⟨pH s, 32⟩
  f_h : (pH s).toNat + 32 ≤ 2 ^ 64
  hh : bytesAt s.mem (pH s) 32 = H (EK K (args s))

section
variable {K : KemLay} {s₀ : State} (hq : PreH K s₀)
include hq

theorem layH_ok : (layH K s₀).Ok := by
  have hp := hq.pre
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [layH, List.length_cons, List.length_nil] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit (s₀ := args s₀) hp
    · exact hq.f_h
  · simp only [layH, List.length_cons, List.length_nil] at hi hj
    rcases (by omega_using [hj, hij] : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega_using [hj, hij] : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [layH, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_scr.symm
    · exact hq.d_h_scr.symm
    · exact hq.b_h

theorem setupH_ok :
    WP isa (.block encapsHSetup) s₀ fun s => EnEnv K (args s₀) s ∧ s.gpr .r29 = pM (args s₀) ∧
      s.gpr .r26 = pH s₀ ∧ bytesAt s.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀) ∧
      bytesAt s.mem ((layH K s₀).A 2 0) 32 = bytesAt s₀.mem ((layH K s₀).A 2 0) 32 := by
  have hp := hq.pre
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hw : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions s₀.wr (pScr (args s₀) + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ =>
      Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [scr, h₂]) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsHSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok' (.inr (.inr rfl)) rfl hw) fun s₁ ⟨sav, fr, g₁, lr₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .r3 = s₀.gpr .r3 := g₁ _ (by decide)
  have g4 : s₁.gpr .r4 = s₀.gpr .r4 := g₁ _ (by decide)
  have g5 : s₁.gpr .r5 = s₀.gpr .r5 := g₁ _ (by decide)
  have g6 : s₁.gpr .r6 = s₀.gpr .r6 := g₁ _ (by decide)
  have g7 : s₁.gpr .r7 = s₀.gpr .r7 := g₁ _ (by decide)
  have g8 : s₁.gpr .r8 = s₀.gpr .r8 := g₁ _ (by decide)
  have hmv : WP isa (.block [mov .r30 .r3, mov .r29 .r5, mov .r28 .r6, mov .r27 .r7, mov .r31 .r8, mov .r26 .r4])
      s₁ fun s =>
      s.gpr .r30 = s₀.gpr .r3 ∧ s.gpr .r29 = s₀.gpr .r5 ∧ s.gpr .r28 = s₀.gpr .r6 ∧ s.gpr .r27 = s₀.gpr .r7 ∧
      s.gpr .r31 = s₀.gpr .r8 ∧ s.gpr .r26 = s₀.gpr .r4 ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp := by
    prun [g3, g4, g5, g6, g7, g8]
    and_intros
    all_goals first
      | exact trivial
      | (intro r hr hs
         simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
         obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
         simp only [RegUpd.gpr_write, a26, a27, a28, a29, a30, a31, ite_false])
  refine WP.mono hmv fun s ⟨g30, g29, g28, g27, g31, g26, cs, m, rd, wr, sp⟩ => ?_
  have fr' : Frame ((lay (args s₀) K).RL [(0, 840, 72)]) s₀.mem s.mem := by rw [m]; exact fr
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this]
  have hwr : s₀.wr = (args s₀).wr := rfl
  have sav' : TopSaved s.mem (pScr (args s₀)) (args s₀) := by
    rw [m]; exact ⟨sav.s24, sav.s25, sav.s26, sav.s27, sav.s28, sav.s29, sav.s30, sav.s31, sav.slr⟩
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp48, by rw [sp, sp₁]; rfl,
    by rw [wr, wr₁, hwr, hp.wr]; simp [lay]⟩, g30, g28, g27, rd.trans rd₁, wr.trans wr₁, sp.trans sp₁,
    fun r hr hs => ?_, sav', ?_⟩, g29, g26, ?_, ?_⟩
  · rw [cs r hr hs, args_preserved s₀ r hr]; exact g₁ r (by rintro rfl; simp [preserved] at hr)
  · exact Lay.bytes_keep hL fr' (by edecide) ek
  · rw [m]; exact Lay.bytes_keep (layM_ok hp) (L := layM (args s₀) K) (W := [(0, 840, 72)]) fr (by edecide)
      (by decide)
  · rw [m]; exact Lay.bytes_keep (layH_ok hq) (L := layH K s₀) (W := [(0, 840, 72)]) fr
      (by rw [layH_sizes]; edecide) (by decide)

theorem copyH_ok {s : State} (h : EnEnv K (args s₀) s) (h26 : s.gpr .r26 = pH s₀)
    (hh : bytesAt s.mem ((layH K s₀).A 2 0) 32 = bytesAt s₀.mem ((layH K s₀).A 2 0) 32)
    (hm : bytesAt s.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀)) :
    WP isa (copy .r26 0 .r31 oHek 32) s fun s' => EnEnv K (args s₀) s' ∧ s'.gpr .r29 = s.gpr .r29 ∧
      bytesAt s'.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀) ∧
      bytesAt s'.mem ((lay (args s₀) K).A 0 oHek) 32 = H (EK K (args s₀)) := by
  have hp := hq.pre
  have hK := hp.wf
  obtain ⟨-, -, -, -, -, wM0⟩ := buf_wr hp
  have wH : (layH K s₀).buf 2 ∈ s.rd ++ s.wr := by rw [h.rd]; exact List.mem_append_left _ hq.rdH
  refine WP.mono (copyL (layH_ok hq) (i := 2) (j := 0) (by decide) (by decide) h26
    h.ctx.r31 (by decide) (by decide) (by decide) (by decide) (by rw [layH_sizes]; edecide) wH
    (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ?_
  have k' : Kept ((lay (args s₀) K).RL [(0, oHek, 32)]) s s' := k
  refine ⟨h.keep hp (k'.x []) (by simp) (by edecide), k'.cs .r29 (by decide), ?_, ?_⟩
  · have fM : Frame ((layM (args s₀) K).RL [(0, oHek, 32)]) s.mem s'.mem := k.frame
    rw [Lay.bytes_keep (layM_ok hp) fM (by edecide) (by decide)]; exact hm
  · show bytesAt s'.mem ((layH K s₀).A 0 oHek) 32 = _
    rw [e, hh, A_zero]; exact hq.hh

end

/-- The copy of `m`, keeping `H(ek)`. -/
theorem copyMh_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) (h29 : s.gpr .r29 = pM s₀)
    (hm : bytesAt s.mem ((layM s₀ K).A 2 0) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (copy .r29 0 .r31 oMsg 32) s fun s' => EnEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) :=
  have hK := hp.wf
  WP.mono (copyM_ok hp h h29 hm) fun _ ⟨e, m, k⟩ =>
    ⟨e, m, by rw [Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)]; exact hh⟩

/-- `s4_ok`, keeping `H(ek)`. -/
theorem s4h_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (.block [.addi .r29 .r31 oMsg]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) :=
  WP.mono ptr29_ok fun _ ⟨k, g29, m⟩ =>
    ⟨⟨h.keep hp (W := []) k (by simp [savedTop]) rfl, by rw [g29, h.ctx.r31], by rw [m]; exact hm⟩,
      by rw [m]; exact hh⟩

theorem correctH {K : KemLay} {s₀ : State} (hq : PreH K s₀) : WP isa K.encapsH s₀ (Post K (args s₀)) := by
  have hp := hq.pre
  refine WP.seq (WP.mono (setupH_ok hq) fun s₂ ⟨h₂, g29, g1, m₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (copyH_ok hq h₂ g1 hh₂ m₂) fun s₃ ⟨h₃, g29₃, m₃, hh₃⟩ => ?_)
  refine WP.seq (WP.mono (copyMh_ok hp h₃ (g29₃.trans g29) m₃ hh₃) fun s₄ ⟨h₄, m₄, hh₄⟩ => ?_)
  exact WP.seq (WP.mono (s4h_ok hp h₄ m₄ hh₄) fun _ h₅ => tail_ok hp h₅)

end VG.Proof.MlKem.PPC64LE.Encaps

end

end

/-!
# ML-KEM on PPC64LE: encapsulation, constant time and `Verified`

As on 32-bit ARM (`Proof/MlKem/Arm/CallWipe.lean`): two runs from states that
agree on the public data (the pointers, the stack pointer and `ρ` of `ek`,
which the contract lets the function leak) leak the same trace (`all_ct`),
phase by phase: the blocks by the taint analysis, from the pointers, or
because they access no memory; the hashes by `hash_ct`; and K-PKE.Encrypt by
`encrypt_ct`, whose `SampleNTT`s take the seeds of the same `ρ`. What each
run is at each point comes from its correctness (`Encaps.lean`).

All of it holds for any parameter set. Its `outcome` is the contract's,
which ML-KEM-768's `verified` (below) and ML-KEM-1024's use.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE.Encaps

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE.Enc
open VG.Proof.MlKem.PPC64LE.Sample (taint_block relct_wp)

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  r4 : s₁.gpr .r4 = s₂.gpr .r4
  r5 : s₁.gpr .r5 = s₂.gpr .r5
  r6 : s₁.gpr .r6 = s₂.gpr .r6
  r7 : s₁.gpr .r7 = s₂.gpr .r7
  rho : ekRho K.p (EK K s₁) = ekRho K.p (EK K s₂)

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.r3, two.r5, two.r6, two.r7, two.sp]

theorem Two.regs {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) :
    ∀ r ∈ [Reg.r27, .r28, .r30, .r31], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.r27, hb.r27]; exact two.r6
  · rw [ha.r28, hb.r28]; exact two.r5
  · rw [ha.r30, hb.r30]; exact two.r3
  · rw [ha.ctx.r31, hb.ctx.r31, two.layEq]

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.r27, .r28, .r30, .r31] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
  fun r hr => two.regs ha hb r (hs r hr)

theorem Two.spE {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) : a.sp = b.sp := by
  rw [ha.sp, hb.sp, two.sp]

theorem Two.hashOk {ins outs : List Piece} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hi : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ ins, PieceOk (lay s₀ K) eidx s false p)
    (ho : ∀ {s₀ s : State}, Pre K s₀ → EnEnv K s₀ s → ∀ p ∈ outs, PieceOk (lay s₀ K) eidx s true p) :
    HashOk (lay s₁ K) eidx ins outs a ∧ HashOk (lay s₁ K) eidx ins outs b ∧ a.sp = b.sp :=
  ⟨⟨ha.ctx, hi two.hp₁ ha, ho two.hp₁ ha⟩,
    by rw [← two.layEq]; exact ⟨hb.ctx, hi two.hp₂ hb, ho two.hp₂ hb⟩, two.spE ha hb⟩

/-- From `G(m ‖ H(ek))` on (`tail`), in both runs. -/
theorem tail_ct :
    RelCT isa (fun a b => (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂))) (tail K) fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- `G(m ‖ H(ek))`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oG) 32 = KK K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oG) 32 = KK K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate72 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.r31, oMsg, 32⟩, ⟨.r31, oHek, 32⟩]) (outs := [⟨.r31, oG, 64⟩])
          hab.1.1.1 hab.2.1.1
        (fun hp h p hp' => by
          have hK := hp.wf
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
          · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)))
      fun a b hab => ⟨s6_ok hp₁ hab.1, s6_ok hp₂ hab.2⟩) ?_
  -- `K` into `key`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 3 0) 32 = KK K s₁ ∧
        bytesAt a.mem ((lay s₁ K).A 0 oSigma) 32 = RR K s₁) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 3 0) 32 = KK K s₂ ∧
        bytesAt b.mem ((lay s₂ K).A 0 oSigma) 32 = RR K s₂))
    (relct_wp (taint_prog [.r28, .r31] (fun a b hab => two.spE hab.1.1.1 hab.2.1.1)
      (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt, and the end
  refine RelCT.seq (R := fun (a b : State) => EnEnv K s₁ a ∧ EnEnv K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.r31] (fun a b hab => two.spE hab.1 hab.2)
      (fun a b hab => two.sub' hab.1 hab.2) (by taint_decide))
  have ey : EncPre K (lay s₁ K) eb y := by rw [← two.layEq]; exact encPre hp₂ hxy.2.1.1 hxy.2.1.2.1
  refine encrypt_ct (encPre hp₁ hxy.1.1.1 hxy.1.1.2.1) ey ?_
  show ekRho K.p (bytesAt x.mem ((lay s₁ K).A 2 0) K.ekLen) =
    ekRho K.p (bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen)
  have e₂ : bytesAt y.mem ((lay s₁ K).A 2 0) K.ekLen = EK K s₂ := by
    rw [← two.layEq]; exact hxy.2.1.1.ek
  rw [hxy.1.1.1.ek, e₂]; exact two.rho


theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encaps fun _ _ => True := by
  have hp₁ := two.hp₁
  have hp₂ := two.hp₂
  have hK := hp₁.wf
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ a.gpr .r29 = pM s₁ ∧ bytesAt a.mem ((layM s₁ K).A 2 0) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ b.gpr .r29 = pM s₂ ∧ bytesAt b.mem ((layM s₂ K).A 2 0) 32 = M K s₂))
    (relct_wp (taint_block [.r3, .r4, .r5, .r6, .r7] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact two.r3
        · exact two.r4
        · exact two.r5
        · exact two.r6
        · exact two.r7) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = M K s₂))
    (relct_wp (taint_prog [.r29, .r31] (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r4
        · exact two.regs hab.1.1 hab.2.1 .r31 (by simp)) (by taint_decide))
      fun a b hab => ⟨WP.mono (copyM_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2) fun _ h => ⟨h.1, h.2.1⟩,
        WP.mono (copyM_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2) fun _ h => ⟨h.1, h.2.1⟩⟩) ?_
  refine RelCT.seq (R := fun (a b : State) => F4 K s₁ a ∧ F4 K s₂ b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨s4_ok hp₁ hab.1.1 hab.1.2, s4_ok hp₂ hab.2.1 hab.2.2⟩) ?_
  -- `H(ek)`
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oHek) 32 = H (EK K s₁)) ∧
      (F4 K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oHek) 32 = H (EK K s₂)))
    (relct_wp (hash_ct (L := lay s₁ K) (idx := eidx) VG.Proof.MlKem.rate136 (by decide)
      (List.cons_ne_nil _ _) fun a b hab =>
        two.hashOk (ins := [⟨.r30, 0, K.ekLen⟩]) (outs := [⟨.r31, oHek, 32⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) (by show 0 < 32768; decide)
            (by show K.ekLen < 32768; have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])
            (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega_using []) (by edecide))
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)))
      fun a b hab => ⟨s5_ok hp₁ hab.1, s5_ok hp₂ hab.2⟩) (tail_ct two)

end

/-! ## The outcome -/

theorem outcome {K : KemLay} (hK : K.WF) (s₀ : State) :
    Outcome (fun iters => encapsInternal K.p iters (EK K s₀) (M K s₀))
      (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0)
      (KK K s₀,
        VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀)
          (RR K s₀)) := by
  refine VG.Proof.MlKem.outcome_of_min ?_
  rw [show minIterations = 280 from rfl]
  cases hk : okEnc K.k (ekRho K.p (EK K s₀)) K.k
  · obtain ⟨i, hi, j, hj, hn⟩ := enc_none hk
    refine .inr ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq, VG.Proof.MlKem.KPke.kpkeEncrypt_none hi hj hn]; rfl
  · refine .inl ⟨rfl, ?_⟩
    rw [VG.Proof.MlKem.KPke.encapsInternal_eq,
      VG.Proof.MlKem.KPke.kpkeEncrypt_some ⟨hK.η₁, hK.η₂⟩ (enc_some (r := RR K s₀) hk)]
    rfl

theorem EK_eq (K : KemLay) (s₀ : State) : EK K s₀ = bytesAt s₀.mem (s₀.gpr .r3) K.ekLen := by
  simp only [EK, Lay.A, BitVec.add_zero]; rfl

theorem M_eq (K : KemLay) (s₀ : State) : M K s₀ = bytesAt s₀.mem (s₀.gpr .r4) 32 := by
  simp only [M, Lay.A, BitVec.add_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encapsBodyContract PPC64LE.abi 48).pre s) : Pre kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5⟩ := h
  exact ⟨kl768_wf, kl768_calls, h0, by rw [h1]; exact .head _, by rw [h1]; exact .tail _ (.head _), h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl768 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀)) :
    (Proof.MlKem.Scrubbed.encapsBodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1184 = EK kl768 s₀ := (EK_eq kl768 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r4) 32 = M kl768 s₀ := (M_eq kl768 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.encaps (Proof.MlKem.Scrubbed.encapsBodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 s₁) = ekRho kl768.p (EK kl768 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

/-! ## `encapsH` -/

/-- Two runs of `encapsH`, from states that agree on the public data. -/
structure TwoH (K : KemLay) (s₁ s₂ : State) : Prop where
  hq₁ : PreH K s₁
  hq₂ : PreH K s₂
  sp : s₁.sp = s₂.sp
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  r4 : s₁.gpr .r4 = s₂.gpr .r4
  r5 : s₁.gpr .r5 = s₂.gpr .r5
  r6 : s₁.gpr .r6 = s₂.gpr .r6
  r7 : s₁.gpr .r7 = s₂.gpr .r7
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  rho : ekRho K.p (EK K (args s₁)) = ekRho K.p (EK K (args s₂))

/-- What `encaps`'s runs of their arguments are. -/
theorem TwoH.two {K : KemLay} {s₁ s₂ : State} (t : TwoH K s₁ s₂) : Two K (args s₁) (args s₂) :=
  ⟨t.hq₁.pre, t.hq₂.pre, t.sp, t.r3, t.r5, t.r6, t.r7, t.r8, t.rho⟩

theorem all_ctH {K : KemLay} {s₁ s₂ : State} (two : TwoH K s₁ s₂) :
    RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encapsH fun _ _ => True := by
  have hq₁ := two.hq₁
  have hq₂ := two.hq₂
  have hp₁ := hq₁.pre
  have hp₂ := hq₂.pre
  have tw := two.two
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ a.gpr .r29 = pM (args s₁) ∧ a.gpr .r26 = pH s₁ ∧
        bytesAt a.mem ((layM (args s₁) K).A 2 0) 32 = M K (args s₁) ∧
        bytesAt a.mem ((layH K s₁).A 2 0) 32 = bytesAt s₁.mem ((layH K s₁).A 2 0) 32) ∧
      (EnEnv K (args s₂) b ∧ b.gpr .r29 = pM (args s₂) ∧ b.gpr .r26 = pH s₂ ∧
        bytesAt b.mem ((layM (args s₂) K).A 2 0) 32 = M K (args s₂) ∧
        bytesAt b.mem ((layH K s₂).A 2 0) 32 = bytesAt s₂.mem ((layH K s₂).A 2 0) 32))
    (relct_wp (taint_block [.r3, .r4, .r5, .r6, .r7, .r8] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact two.r3
        · exact two.r4
        · exact two.r5
        · exact two.r6
        · exact two.r7
        · exact two.r8) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setupH_ok hq₁, by rw [hab.2]; exact setupH_ok hq₂⟩) ?_
  -- `h` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ a.gpr .r29 = pM (args s₁) ∧
        bytesAt a.mem ((layM (args s₁) K).A 2 0) 32 = M K (args s₁) ∧
        bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (EnEnv K (args s₂) b ∧ b.gpr .r29 = pM (args s₂) ∧
        bytesAt b.mem ((layM (args s₂) K).A 2 0) 32 = M K (args s₂) ∧
        bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (taint_prog [.r26, .r31] (fun a b hab => tw.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.r4
        · exact tw.regs hab.1.1 hab.2.1 .r31 (by simp)) (by taint_decide))
      fun a b hab =>
        ⟨WP.mono (copyH_ok hq₁ hab.1.1 hab.1.2.2.1 hab.1.2.2.2.2 hab.1.2.2.2.1) fun _ h =>
          ⟨h.1, h.2.1.trans hab.1.2.1, h.2.2⟩,
        WP.mono (copyH_ok hq₂ hab.2.1 hab.2.2.2.1 hab.2.2.2.2.2 hab.2.2.2.2.1) fun _ h =>
          ⟨h.1, h.2.1.trans hab.2.2.1, h.2.2⟩⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ bytesAt a.mem ((lay (args s₁) K).A 0 oMsg) 32 = M K (args s₁) ∧
        bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (EnEnv K (args s₂) b ∧ bytesAt b.mem ((lay (args s₂) K).A 0 oMsg) 32 = M K (args s₂) ∧
        bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (taint_prog [.r29, .r31] (fun a b hab => tw.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.r5
        · exact tw.regs hab.1.1 hab.2.1 .r31 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyMh_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2,
        copyMh_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K (args s₁) a ∧ bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (F4 K (args s₂) b ∧ bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨s4h_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, s4h_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  exact tail_ct tw

/-! ## ML-KEM-768's `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract PPC64LE.abi 48).pre s) : PreH kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, d1, d2, d3, dh1, dh2, dh3, d4, d5, d6, d7, d8, d9, b1, bh, b2, b3, b4, b5,
    f1, fh, f2, f3, f4, f5, hh⟩ := h
  have r : (args s).rd = _ := h1
  exact ⟨⟨kl768_wf, kl768_calls, h0, by rw [r]; exact .head _, by rw [r]; exact .tail _ (.tail _ (.head _)),
    h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5⟩,
    by rw [h1]; exact .tail _ (.head _), dh3, bh, fh, by rw [EK_eq]; exact hh⟩

/-- `post_of` for `encapsH`, whose arguments after `ek` are one register later. -/
theorem post_ofH {s₀ s : State}
    (h3 : s.gpr .r3 = if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey (args s₀)) 32 = KK kl768 (args s₀))
    (hct : bytesAt s.mem (pCt (args s₀)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 (args s₀))) (RR kl768 (args s₀))) (EK kl768 (args s₀)) (M kl768 (args s₀))
      (RR kl768 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsHBodyContract PPC64LE.abi 48).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
    PPC64LE.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .r3) 1184 = EK kl768 (args s₀) := (EK_eq kl768 (args s₀)).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .r5) 32 = M kl768 (args s₀) := (M_eq kl768 (args s₀)).symm
  have hkey' : bytesAt s.mem (s₀.gpr .r6) 32 = KK kl768 (args s₀) := hkey
  have hct' : bytesAt s.mem (s₀.gpr .r7) 1088 = _ := hct
  rw [h3, e, hkey', hct', e0, e1]
  exact outcome kl768_wf (args s₀)

/-- A state satisfying `encapsH`'s precondition, with `H(ek)` at `h` (`hMem`). -/
def satStateH (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | .r7 => 0x5000 | .r8 => 0x10000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := VG.Proof.MlKem.hMem ekLen
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x4000, 32⟩, ⟨0x5000, ctLen⟩, ⟨0x10000, scr⟩]

theorem verifiedH :
    Verified PPC64LE.target Impl.MlKem.PPC64LE.encapsH (Proof.MlKem.Scrubbed.encapsHBodyContract PPC64LE.abi 48) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correctH (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp, hlr⟩, post_ofH h3 hkey hct⟩
  · have hq₁ := pre_ofH h₁
    have hq₂ := pre_ofH h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
      PPC64LE.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7, g8⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 (args s₁)) = ekRho kl768.p (EK kl768 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ctH ⟨hq₁, hq₂, hsp, g3, g4, g5, g6, g7, g8, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satStateH 1184 1088 32768, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h (by decide)
        | trivial
        | decide +kernel

end VG.Proof.MlKem.PPC64LE.Encaps
