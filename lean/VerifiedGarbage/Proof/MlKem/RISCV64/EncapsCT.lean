module

public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.RISCV64.EncryptCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.RowSum
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.MlKem.EncapsH
meta import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Proof.MlKem.EncapsHSat
meta import VerifiedGarbage.Proof.MlKem.EncapsHSat
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
meta import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-! ### `MlKem.RISCV64.Encaps`, which this module and modules that import it used -/

section

/-!
# ML-KEM on RISC-V: encapsulation, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/EncapsCT.lean`): `K.encaps` for any
parameter set `K` (`KemLay.WF`).

The buffers of the function (`lay`): `scratch`, the 1168 bytes below the stack
pointer, `ek`, `key` and `ct`; `m`, which may overlap `ek`, is only read by
its copy into `scratch`, with a layout of its own (`layM`). What every phase
keeps (`EnEnv`), and the phases: the setup, `m` copied, `H(ek)`,
`G(m ‖ H(ek))` into `K ‖ r`, `K` copied into `key`, and K-PKE.Encrypt
(`Enc.encrypt_ok`) into `ct`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.Encaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc
open VG.Impl.Sha3.RISCV64.Stream (mov)

section
variable (s₀ : State)

abbrev pEk : Addr := s₀.gpr .a0
abbrev pM : Addr := s₀.gpr .a1
abbrev pKey : Addr := s₀.gpr .a2
abbrev pCt : Addr := s₀.gpr .a3
abbrev pScr : Addr := s₀.gpr .a4

/-- The buffers: `scratch`, the 1168 bytes below the stack pointer, `ek`, `key` and `ct`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pEk s₀, pKey s₀, pCt s₀].getD i 0,
    [K.scratch, 1168, K.ekLen, 32, K.ctLen]⟩

/-- The buffers of the copy of `m`: `scratch`, the stack and `m`. -/
def layM (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pM s₀].getD i 0, [K.scratch, 1168, 32]⟩

end

/-- The sizes of the buffers. -/
abbrev eSz (K : KemLay) : List Nat := [K.scratch, 1168, K.ekLen, 32, K.ctLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = eSz K := rfl

theorem layM_sizes (K : KemLay) (s₀ : State) : (layM s₀ K).sizes = [K.scratch, 1168, 32] := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  al : s.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s.sp.toNat
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
  b_ek : (below s.sp 1168).Disjoint ⟨pEk s, K.ekLen⟩
  b_m : (below s.sp 1168).Disjoint ⟨pM s, 32⟩
  b_key : (below s.sp 1168).Disjoint ⟨pKey s, 32⟩
  b_ct : (below s.sp 1168).Disjoint ⟨pCt s, K.ctLen⟩
  b_scr : (below s.sp 1168).Disjoint ⟨pScr s, K.scratch⟩
  f_ek : (pEk s).toNat + K.ekLen ≤ 2 ^ 64
  f_m : (pM s).toNat + 32 ≤ 2 ^ 64
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 64
  f_ct : (pCt s).toNat + K.ctLen ≤ 2 ^ 64
  f_scr : (pScr s).toNat + K.scratch ≤ 2 ^ 64
  alS : (pScr s).toNat % 8 = 0

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem stack_fit : (s₀.sp - BitVec.ofNat 64 1168).toNat + 1168 ≤ 2 ^ 64 := by
  have := hp.sp1168
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
  s10 : s.gpr .s10 = pEk s₀
  s8 : s.gpr .s8 = pKey s₀
  s7 : s.gpr .s7 = pCt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  ek : bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen = bytesAt s₀.mem ((lay s₀ K).A 2 0) K.ekLen

/-- A region the phases may change: apart from the saved registers and `ek`. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := sepB (eSz K) (0, 1288, 80) w && sepB (eSz K) (2, 0, K.ekLen) w

/-- The buffer of each pointer register. -/
def eidx : Reg → Nat
  | .s10 => 2 | .s8 => 3 | .s7 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
tactic_template "edecide" : tactic => `(tactic| first
                   | decide
                   | ((try simp only [lay_sizes, layM_sizes, eSz, okW, eidx, kRegs, List.all_cons, List.all_nil,
                         List.all_append, List.map_cons, List.map_nil, trip, Bool.and_true])
                      (try have := (‹KemLay.WF _›).scr)
                      kdecide))

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 1288 80 := rfl

theorem EnEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .s10 ∧ x ≠ .s8 ∧ x ≠ .s7 ∧ x ≠ .s11) (hW : W.all (okW K) = true) :
    EnEnv K s₀ s' := by
  have hL := lay_ok hp
  have hK := hp.wf
  have h1 : sepAll (lay s₀ K).sizes (0, 1288, 80) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (2, 0, K.ekLen) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .s10 ∨ r = .s8 ∨ r = .s7 ∨ r = .s11 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c, d⟩ := hx r hm
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨hk.ctx (nx _ (by simp)) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun r hr hs => ?_, h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_⟩
  · rw [hk.cs .s10 (by decide) (nx _ (by simp)), h.s10]
  · rw [hk.cs .s8 (by decide) (nx _ (by simp)), h.s8]
  · rw [hk.cs .s7 (by decide) (nx _ (by simp)), h.s7]
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [Lay.bytes_keep hL hk.frame h2 (by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])]; exact h.ek

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr]; simp [Lay.buf, lay, layM, hp.rdEk, hp.rdM]

theorem A_zero (L : Lay) (i : Nat) : L.A i 0 = L.ptr i := BitVec.add_zero _

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block encapsSetup) s₀ fun s => EnEnv K s₀ s ∧ s.gpr .s9 = pM s₀ ∧
      bytesAt s.mem ((layM s₀ K).A 2 0) 32 = bytesAt s₀.mem ((layM s₀ K).A 2 0) 32 := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hw : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) 8 := fun o h₁ h₂ =>
    Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [scr, h₂]) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.alS hw) fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s7 .a3, mov .s11 .a4]) s₁ fun s =>
      s.gpr .s10 = pEk s₀ ∧ s.gpr .s9 = pM s₀ ∧ s.gpr .s8 = pKey s₀ ∧ s.gpr .s7 = pCt s₀ ∧
      s.gpr .s11 = pScr s₀ ∧ (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp :=
    wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_mv fun u₅ h₅ => WP.block_nil
      ⟨by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        fun r hr hs => by
          simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
          obtain ⟨-, -, -, -, a7, a8, a9, a10, a11⟩ := hs
          simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, a7, a8, a9, a10, a11, ↓reduceIte],
        by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
        by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  refine WP.mono hmv fun s ⟨g30, g29, g28, g27, g31, cs, m, rd, wr, sp⟩ => ?_
  have fr' : Frame ((lay s₀ K).RL [(0, 1288, 80)]) s₀.mem s.mem := by rw [m]; exact fr
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this]
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp1168, by rw [sp, sp₁]; exact hp.al,
    hp.alS, by rw [sp, sp₁]; rfl, by rw [wr, wr₁, hp.wr]; simp [lay]⟩, g30, g28, g27, rd.trans rd₁, wr.trans wr₁,
    sp.trans sp₁, fun r hr hs => ?_, by rw [m]; exact sav, ?_⟩, g29, ?_⟩
  · rw [cs r hr hs, g₁]
  · exact Lay.bytes_keep hL fr' (by edecide) ek
  · rw [m]; exact Lay.bytes_keep (layM_ok hp) (L := layM s₀ K) (W := [(0, 1288, 80)]) fr (by edecide) (by decide)

/-! ## `m` copied -/

/-- `m`. -/
abbrev M (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((layM s₀ K).A 2 0) 32

/-- `ek`. -/
abbrev EK (K : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem ((lay s₀ K).A 2 0) K.ekLen

theorem layA0 (K : KemLay) (s₀ : State) (o : Nat) : (layM s₀ K).A 0 o = (lay s₀ K).A 0 o := rfl

theorem copyM_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) (h29 : s.gpr .s9 = pM s₀)
    (hm : bytesAt s.mem ((layM s₀ K).A 2 0) 32 = M K s₀) :
    WP isa (copy .s9 0 .s11 oMsg 32) s fun s' =>
      EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ ∧
        Kept ((lay s₀ K).RL [(0, oMsg, 32)]) s s' := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, wM, wM0⟩ := buf_wr hp
  refine WP.mono (copyL (layM_ok hp) (i := 2) (j := 0) (by decide) (by decide) h29
    h.ctx.s11 (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_, k⟩
  · have k' : Kept ((lay s₀ K).RL [(0, oMsg, 32)]) s s' := k
    exact h.keep hp (k'.x []) (by simp) (by edecide)
  · rw [← layA0, e, hm]

theorem ptr29_ok {s : State} :
    WP isa (.block [.addi .s9 .s11 oMsg]) s fun s' =>
      KeptX [.s9] [] s s' ∧ s'.gpr .s9 = s.gpr .s11 + BitVec.ofNat 64 oMsg ∧ s'.mem = s.mem :=
  wp_addi (by decide) fun s' h => WP.block_nil
    ⟨⟨fun r _ hx => h.other r fun e => hx (by rw [e]; exact List.mem_singleton_self _), h.sp, h.rd, h.wr,
      by rw [h.mem]; exact Frame.refl _ _⟩, h.gpr, h.mem⟩

/-! ## The hashes -/

theorem pieceE {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .s10 ∨ p.base = .s11) (hw : w = true → p.base = .s11)
    (hoe : p.off < 32768) (hle : p.len < 2048) (hpos : 0 < p.len)
    (hsep : sepAll (eSz K) (eidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) eidx s w p := by
  obtain ⟨w0, -, -, w2, -, -⟩ := buf_wr hp
  rw [← h.wr] at w0
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.s10
    · exact h.ctx.s11
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

theorem hashH_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) :
    WP isa (hash 136 0x06 [⟨.s10, 0, K.ekLen⟩] [⟨.s11, oHek, 32⟩]) s fun s' =>
      EnEnv K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oHek, 32)])) s.mem s'.mem ∧
      s'.gpr .s9 = s.gpr .s9 ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.s10, 0, K.ekLen⟩ : Piece)], PieceOk (lay s₀ K) eidx s false p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inl rfl) (by simp) (by show 0 < 32768; decide)
      (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])
      (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega_using []) (by edecide)
  have hout : ∀ p ∈ [(⟨.s11, oHek, 32⟩ : Piece)], PieceOk (lay s₀ K) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)
  refine WP.mono (hash_ok (idx := eidx) VG.Proof.MlKem.rate136 (by decide) h.ctx
    (List.cons_ne_nil _ _) hin hout (List.pairwise_singleton _ _)) fun s' ⟨k, o⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k.frame, k.cs .s9 (by decide), ?_⟩
  have e := o.1
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
  refine e.trans ?_
  show _ = H (EK K s₀)
  have ek : bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen = EK K s₀ := h.ek
  rw [VG.Proof.MlKem.H_eq, ← ek]; rfl

theorem hashG_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩] [⟨.s11, oG, 64⟩]) s fun s' =>
      EnEnv K s₀ s' ∧ Frame ((lay s₀ K).RL (kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧ s'.gpr .s9 = s.gpr .s9 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = (G (M K s₀ ++ H (EK K s₀))).1 ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = (G (M K s₀ ++ H (EK K s₀))).2 := by
  have hK := hp.wf
  have hin : ∀ p ∈ [(⟨.s11, oMsg, 32⟩ : Piece), ⟨.s11, oHek, 32⟩], PieceOk (lay s₀ K) eidx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
    · exact pieceE hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by edecide)
  have hout : ∀ p ∈ [(⟨.s11, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) eidx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceE hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by edecide)
  have hin' : (List.map ((lay s₀ K).pb eidx s.mem) [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩]).flatten =
      M K s₀ ++ H (EK K s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 ++ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = _
    rw [hm, hh]
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) h.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ =>
    ⟨?_, k'.frame, k'.cs .s9 (by decide), ?_⟩
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
    WP isa (copy .s11 oG .s8 0 32) s fun s' => EnEnv K s₀ s' ∧ Kept ((lay s₀ K).RL [(3, 0, 32)]) s s' ∧
      bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = bytesAt s.mem ((lay s₀ K).A 0 oG) 32 := by
  have hK := hp.wf
  obtain ⟨w0, w3, -, -, -, -⟩ := buf_wr hp
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) (by decide) (by decide) h.ctx.s11 h.s8
    (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun s' ⟨k, e⟩ =>
    ⟨h.keep hp (k.x []) (by simp) (by edecide), k, e⟩

/-! ## K-PKE.Encrypt -/

/-- The buffers of `encrypt`: `ek`, the copy of `m`, and `ct`. -/
abbrev eb : EB := ⟨2, 0, 0, oMsg, 4, 0⟩

theorem encPre {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (h29 : s.gpr .s9 = (lay s₀ K).A 0 oMsg) : EncPre K (lay s₀ K) eb s := by
  have hK := hp.wf
  obtain ⟨w0, -, w4, w2, -, -⟩ := buf_wr hp
  exact ⟨hK, hp.calls, h.ctx, by rw [h.s10, A_zero]; rfl, h29, by rw [h.s7, A_zero]; rfl, by edecide,
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

/-- After the copy of `m`, with its pointer in `s9`. -/
abbrev F4 (s : State) : Prop := EnEnv K s₀ s ∧ s.gpr .s9 = (lay s₀ K).A 0 oMsg ∧
  bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀

end

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀)
include hp

theorem s4_ok {s : State} (h : EnEnv K s₀ s) (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀) :
    WP isa (.block [.addi .s9 .s11 oMsg]) s (F4 K s₀) :=
  WP.mono ptr29_ok fun _ ⟨k, g29, m⟩ =>
    ⟨h.keep hp (W := []) k (by simp [savedTop]) rfl, by rw [g29, h.ctx.s11], by rw [m]; exact hm⟩

theorem s5_ok {s : State} (h : F4 K s₀ s) :
    WP isa (hash 136 0x06 [⟨.s10, 0, K.ekLen⟩] [⟨.s11, oHek, 32⟩]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) := by
  have hK := hp.wf
  exact WP.mono (hashH_ok hp h.1) fun _ ⟨e, f, g29, hh⟩ =>
    ⟨⟨e, by rw [g29, h.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.2.2⟩, hh⟩

theorem s6_ok {s : State} (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩] [⟨.s11, oG, 64⟩]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = KK K s₀ ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (hashG_ok hp h.1.1 h.1.2.2 h.2) fun _ ⟨e, f, g29, k, r⟩ =>
    ⟨⟨e, by rw [g29, h.1.2.1], (Lay.bytes_keep (lay_ok hp) f (by edecide) (by decide)).trans h.1.2.2⟩, k, r⟩

theorem s7_ok {s : State}
    (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = KK K s₀ ∧
      bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀) :
    WP isa (copy .s11 oG .s8 0 32) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀ := by
  have hK := hp.wf
  exact WP.mono (copyK_ok hp h.1.1) fun _ ⟨e, k, key⟩ =>
    ⟨⟨e, by rw [k.cs .s9 (by decide), h.1.2.1],
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.1.2.2⟩, key.trans h.2.1,
      (Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)).trans h.2.2⟩

theorem s8_ok {s : State}
    (h : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = RR K s₀) :
    WP isa K.encrypt s fun s' => EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 3 0) 32 = KK K s₀ ∧
      s'.gpr .s4 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
      bytesAt s'.mem ((lay s₀ K).A 4 0) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀) := by
  have hK := hp.wf
  have eρ : ρE K (lay s₀ K) eb s = ekRho K.p (EK K s₀) := by
    show ekRho K.p (bytesAt s.mem ((lay s₀ K).A 2 0) K.ekLen) = _
    rw [h.1.1.ek]
  have er : rB (lay s₀ K) s = RR K s₀ := h.2.2
  have e1 : ekB K (lay s₀ K) eb s = EK K s₀ := h.1.1.ek
  have e2 : mB (lay s₀ K) eb s = M K s₀ := h.1.2.2
  refine WP.mono (encrypt_ok (encPre hp h.1.1 h.1.2.1)) fun s' ⟨K', s4, ct⟩ =>
    ⟨h.1.1.keep hp K' (by simp [savedTop]) (encW_ok hK).1,
      (Lay.bytes_keep (lay_ok hp) K'.frame (encW_ok hK).2 (by decide)).trans h.2.1, ?_, ?_⟩
  · rw [s4]; show (if okEnc K.k (ρE K (lay s₀ K) eb s) K.k = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)
    rw [← eρ, ← er]; exact ct

end

/-! ## The whole function -/

theorem end_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = s.gpr .s4 ∧ s'.mem = s.mem ∧ s'.sp = s₀.sp := by
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hK := hp.wf
  refine WP.mono (topEnd_ok h.ctx.s11 hp.alS h.sav (fun o h₁ h₂ => ?_) h.cs) fun s' ⟨pr, lr, a0, m, sp, _, _⟩ =>
    ⟨pr, lr, a0, m, sp.trans h.sp⟩
  rw [h.rd, h.wr]
  have scr := hK.scr
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [h₂, scr]
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

/-- What follows `H(ek)` (in `encaps`; its copy from `h` in `encapsH`): `G(m ‖ H(ek))`, `K` into `key`,
K-PKE.Encrypt and the end. -/
abbrev tail (K : KemLay) : Prog isa :=
  .seq (hash 72 0x06 [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩] [⟨.s11, oG, 64⟩]) <|
  .seq (copy .s11 oG .s8 0 32) <|
  .seq K.encrypt (.block topEnd)

/-- What the function ensures, of the arguments of `s₀`. -/
abbrev Post (K : KemLay) (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    s.gpr .a0 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
    bytesAt s.mem (pKey s₀) 32 = KK K s₀ ∧
    bytesAt s.mem (pCt s₀) K.ctLen =
      VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀)

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀)
    (h₅ : F4 K s₀ s ∧ bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (tail K) s (Post K s₀) := by
  refine WP.seq (WP.mono (s6_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (s7_ok hp h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (s8_ok hp h₇) fun s₈ ⟨h₈, key₈, r24₈, ct₈⟩ => ?_)
  refine WP.mono (end_ok hp h₈) fun s ⟨pr, lr, a0, m', sp'⟩ => ⟨pr, sp', lr, by rw [a0, r24₈], ?_, ?_⟩
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

/-- The arguments of `encaps` from those of `encapsH` in `s₀`: `ek` in `a0`;
`m`, `key`, `ct` and `scratch`, in `a2`–`a5`, in `a1`–`a4`. -/
def args (s₀ : State) : State :=
  { s₀ with gpr := fun r => match r with
    | .a1 => s₀.gpr .a2 | .a2 => s₀.gpr .a3 | .a3 => s₀.gpr .a4 | .a4 => s₀.gpr .a5 | r => s₀.gpr r }

theorem args_preserved (s₀ : State) : ∀ r ∈ preserved, (args s₀).gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

abbrev pH (s₀ : State) : Addr := s₀.gpr .a1

/-- The buffers of the copy of `h`: `scratch`, the stack and `h`. -/
def layH (K : KemLay) (s₀ : State) : Lay :=
  ⟨fun i => [pScr (args s₀), s₀.sp - BitVec.ofNat 64 1168, pH s₀].getD i 0, [K.scratch, 1168, 32]⟩

theorem layH_sizes (K : KemLay) (s₀ : State) : (layH K s₀).sizes = [K.scratch, 1168, 32] := rfl

/-- The precondition of `encapsH`'s contract: `encaps`'s, of `args s`, and `h`,
which holds `H(ek)`. -/
structure PreH (K : KemLay) (s : State) : Prop where
  pre : Pre K (args s)
  rdH : (⟨pH s, 32⟩ : Region) ∈ s.rd
  d_h_scr : (⟨pH s, 32⟩ : Region).Disjoint ⟨pScr (args s), K.scratch⟩
  b_h : (below s.sp 1168).Disjoint ⟨pH s, 32⟩
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
    WP isa (.block encapsHSetup) s₀ fun s => EnEnv K (args s₀) s ∧ s.gpr .s9 = pM (args s₀) ∧
      s.gpr .a1 = pH s₀ ∧ bytesAt s.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀) ∧
      bytesAt s.mem ((layH K s₀).A 2 0) 32 = bytesAt s₀.mem ((layH K s₀).A 2 0) 32 := by
  have hp := hq.pre
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -, -, -⟩ := buf_wr hp
  have hw : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions s₀.wr (pScr (args s₀) + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ =>
      Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega_using [scr, h₂]) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [encapsHSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok (b := .a5) rfl hp.alS hw) fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a2, mov .s8 .a3, mov .s7 .a4, mov .s11 .a5]) s₁ fun s =>
      s.gpr .s10 = s₀.gpr .a0 ∧ s.gpr .s9 = s₀.gpr .a2 ∧ s.gpr .s8 = s₀.gpr .a3 ∧ s.gpr .s7 = s₀.gpr .a4 ∧
      s.gpr .s11 = s₀.gpr .a5 ∧ s.gpr .a1 = s₀.gpr .a1 ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧ s.mem = s₁.mem ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp :=
    wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_mv fun u₅ h₅ => WP.block_nil
      ⟨by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g₁],
        fun r hr hs => by
          simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
          obtain ⟨-, -, -, -, a7, a8, a9, a10, a11⟩ := hs
          simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, a7, a8, a9, a10, a11, ↓reduceIte],
        by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd],
        by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr], by rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  refine WP.mono hmv fun s ⟨g30, g29, g28, g27, g31, g1, cs, m, rd, wr, sp⟩ => ?_
  have fr' : Frame ((lay (args s₀) K).RL [(0, 1288, 80)]) s₀.mem s.mem := by rw [m]; exact fr
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega_using [this]
  have hwr : s₀.wr = (args s₀).wr := rfl
  have sav' : TopSaved s.mem (pScr (args s₀)) (args s₀) := by
    rw [m]; exact ⟨sav.v3, sav.v4, sav.v5, sav.v6, sav.v7, sav.v8, sav.v9, sav.v10, sav.v11, sav.vra⟩
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp1168, by rw [sp, sp₁]; exact hp.al,
    hp.alS, by rw [sp, sp₁]; rfl, by rw [wr, wr₁, hwr, hp.wr]; simp [lay]⟩, g30, g28, g27, rd.trans rd₁,
    wr.trans wr₁, sp.trans sp₁, fun r hr hs => ?_, sav', ?_⟩, g29, g1, ?_, ?_⟩
  · rw [cs r hr hs, g₁, args_preserved s₀ r hr]
  · exact Lay.bytes_keep hL fr' (by edecide) ek
  · rw [m]; exact Lay.bytes_keep (layM_ok hp) (L := layM (args s₀) K) (W := [(0, 1288, 80)]) fr (by edecide)
      (by decide)
  · rw [m]; exact Lay.bytes_keep (layH_ok hq) (L := layH K s₀) (W := [(0, 1288, 80)]) fr
      (by rw [layH_sizes]; edecide) (by decide)

theorem copyH_ok {s : State} (h : EnEnv K (args s₀) s) (h1 : s.gpr .a1 = pH s₀)
    (hh : bytesAt s.mem ((layH K s₀).A 2 0) 32 = bytesAt s₀.mem ((layH K s₀).A 2 0) 32)
    (hm : bytesAt s.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀)) :
    WP isa (copy .a1 0 .s11 oHek 32) s fun s' => EnEnv K (args s₀) s' ∧ s'.gpr .s9 = s.gpr .s9 ∧
      bytesAt s'.mem ((layM (args s₀) K).A 2 0) 32 = M K (args s₀) ∧
      bytesAt s'.mem ((lay (args s₀) K).A 0 oHek) 32 = H (EK K (args s₀)) := by
  have hp := hq.pre
  have hK := hp.wf
  obtain ⟨-, -, -, -, -, wM0⟩ := buf_wr hp
  have wH : (layH K s₀).buf 2 ∈ s.rd ++ s.wr := by rw [h.rd]; exact List.mem_append_left _ hq.rdH
  refine WP.mono (copyL (layH_ok hq) (i := 2) (j := 0) (by decide) (by decide) h1
    h.ctx.s11 (by decide) (by decide) (by decide) (by decide) (by rw [layH_sizes]; edecide) wH
    (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ?_
  have k' : Kept ((lay (args s₀) K).RL [(0, oHek, 32)]) s s' := k
  refine ⟨h.keep hp (k'.x []) (by simp) (by edecide), k'.cs .s9 (by decide), ?_, ?_⟩
  · have fM : Frame ((layM (args s₀) K).RL [(0, oHek, 32)]) s.mem s'.mem := k.frame
    rw [Lay.bytes_keep (layM_ok hp) fM (by edecide) (by decide)]; exact hm
  · show bytesAt s'.mem ((layH K s₀).A 0 oHek) 32 = _
    rw [e, hh, A_zero]; exact hq.hh

end

/-- The copy of `m`, keeping `H(ek)`. -/
theorem copyMh_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s) (h29 : s.gpr .s9 = pM s₀)
    (hm : bytesAt s.mem ((layM s₀ K).A 2 0) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (copy .s9 0 .s11 oMsg 32) s fun s' => EnEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) :=
  have hK := hp.wf
  WP.mono (copyM_ok hp h h29 hm) fun _ ⟨e, m, k⟩ =>
    ⟨e, m, by rw [Lay.bytes_keep (lay_ok hp) k.frame (by edecide) (by decide)]; exact hh⟩

/-- `s4_ok`, keeping `H(ek)`. -/
theorem s4h_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : EnEnv K s₀ s)
    (hm : bytesAt s.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀)
    (hh : bytesAt s.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀)) :
    WP isa (.block [.addi .s9 .s11 oMsg]) s fun s' =>
      F4 K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oHek) 32 = H (EK K s₀) :=
  WP.mono ptr29_ok fun _ ⟨k, g29, m⟩ =>
    ⟨⟨h.keep hp (W := []) k (by simp [savedTop]) rfl, by rw [g29, h.ctx.s11], by rw [m]; exact hm⟩,
      by rw [m]; exact hh⟩

theorem correctH {K : KemLay} {s₀ : State} (hq : PreH K s₀) : WP isa K.encapsH s₀ (Post K (args s₀)) := by
  have hp := hq.pre
  refine WP.seq (WP.mono (setupH_ok hq) fun s₂ ⟨h₂, g29, g1, m₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (copyH_ok hq h₂ g1 hh₂ m₂) fun s₃ ⟨h₃, g29₃, m₃, hh₃⟩ => ?_)
  refine WP.seq (WP.mono (copyMh_ok hp h₃ (g29₃.trans g29) m₃ hh₃) fun s₄ ⟨h₄, m₄, hh₄⟩ => ?_)
  exact WP.seq (WP.mono (s4h_ok hp h₄ m₄ hh₄) fun _ h₅ => tail_ok hp h₅)

end VG.Proof.MlKem.RISCV64.Encaps

end

end

/-!
# ML-KEM on RISC-V: encapsulation, constant time and `Verified`

As on PPC64LE (`Proof/MlKem/PPC64LE/EncapsCT.lean`): two runs from states that
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

namespace VG.Proof.MlKem.RISCV64.Encaps

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc

/-- Two runs, from states that agree on the public data. -/
structure Two (K : KemLay) (s₁ s₂ : State) : Prop where
  hp₁ : Pre K s₁
  hp₂ : Pre K s₂
  sp : s₁.sp = s₂.sp
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  a4 : s₁.gpr .a4 = s₂.gpr .a4
  rho : ekRho K.p (EK K s₁) = ekRho K.p (EK K s₂)

section
variable {K : KemLay} {s₁ s₂ : State} (two : Two K s₁ s₂)
include two

theorem Two.layEq : lay s₂ K = lay s₁ K := by
  simp only [Encaps.lay, pScr, pEk, pKey, pCt, two.a0, two.a2, two.a3, two.a4, two.sp]

theorem Two.regs {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b) :
    ∀ r ∈ [Reg.s7, .s8, .s10, .s11], a.gpr r = b.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [ha.s7, hb.s7]; exact two.a3
  · rw [ha.s8, hb.s8]; exact two.a2
  · rw [ha.s10, hb.s10]; exact two.a0
  · rw [ha.ctx.s11, hb.ctx.s11, two.layEq]

theorem Two.sub' {rs : List Reg} {a b : State} (ha : EnEnv K s₁ a) (hb : EnEnv K s₂ b)
    (hs : ∀ r ∈ rs, r ∈ [Reg.s7, .s8, .s10, .s11] := by decide) : ∀ r ∈ rs, a.gpr r = b.gpr r :=
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
        two.hashOk (ins := [⟨.s11, oMsg, 32⟩, ⟨.s11, oHek, 32⟩]) (outs := [⟨.s11, oG, 64⟩])
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
    (relct_wp (taint_prog [.s8, .s11] (fun a b hab => two.spE hab.1.1.1 hab.2.1.1)
      (fun a b hab => two.sub' hab.1.1.1 hab.2.1.1) (by taint_decide))
      fun a b hab => ⟨s7_ok hp₁ hab.1, s7_ok hp₂ hab.2⟩) ?_
  -- K-PKE.Encrypt, and the end
  refine RelCT.seq (R := fun (a b : State) => EnEnv K s₁ a ∧ EnEnv K s₂ b)
    (relct_wp (RelCT.pointwise fun x y hxy => ?_) fun a b hab =>
      ⟨WP.mono (s8_ok hp₁ hab.1) fun _ h => h.1, WP.mono (s8_ok hp₂ hab.2) fun _ h => h.1⟩)
    (taint_block [.s11] (fun a b hab => two.spE hab.1 hab.2)
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
      (EnEnv K s₁ a ∧ a.gpr .s9 = pM s₁ ∧ bytesAt a.mem ((layM s₁ K).A 2 0) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ b.gpr .s9 = pM s₂ ∧ bytesAt b.mem ((layM s₂ K).A 2 0) 32 = M K s₂))
    (relct_wp (taint_block [.a0, .a1, .a2, .a3, .a4] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact two.a0
        · exact two.a1
        · exact two.a2
        · exact two.a3
        · exact two.a4) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  -- `m` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K s₁ a ∧ bytesAt a.mem ((lay s₁ K).A 0 oMsg) 32 = M K s₁) ∧
      (EnEnv K s₂ b ∧ bytesAt b.mem ((lay s₂ K).A 0 oMsg) 32 = M K s₂))
    (relct_wp (taint_prog [.s9, .s11] (fun a b hab => two.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.a1
        · exact two.regs hab.1.1 hab.2.1 .s11 (by simp)) (by taint_decide))
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
        two.hashOk (ins := [⟨.s10, 0, K.ekLen⟩]) (outs := [⟨.s11, oHek, 32⟩]) hab.1.1 hab.2.1
        (fun hp h p hp' => by
          have hK := hp.wf
          rw [List.mem_singleton] at hp'; subst hp'
          exact pieceE hp h (.inl rfl) (by simp) (by show 0 < 32768; decide)
            (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega_using [this])
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

theorem EK_eq (K : KemLay) (s₀ : State) : EK K s₀ = bytesAt s₀.mem (s₀.gpr .a0) K.ekLen := by
  simp only [EK, Lay.A, BitVec.add_zero]; rfl

theorem M_eq (K : KemLay) (s₀ : State) : M K s₀ = bytesAt s₀.mem (s₀.gpr .a1) 32 := by
  simp only [M, Lay.A, BitVec.add_zero]; rfl

/-! ## ML-KEM-768 -/

theorem pre_of {s : State} (h : (Proof.MlKem.Scrubbed.encapsBodyContract RISCV64.abi 1168).pre s) : Pre kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5,
    f1, f2, f3, f4, f5, alS⟩ := h
  exact ⟨kl768_wf, kl768_calls, al, h0, by rw [h1]; exact .head _, by rw [h1]; exact .tail _ (.head _), h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4,
    b5, f1, f2, f3, f4, f5, alS⟩

theorem post_of {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey s₀) 32 = KK kl768 s₀)
    (hct : bytesAt s.mem (pCt s₀) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 s₀)) (RR kl768 s₀)) (EK kl768 s₀) (M kl768 s₀) (RR kl768 s₀)) :
    (Proof.MlKem.Scrubbed.encapsBodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ekRho kl768.p (EK kl768 s₀)) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 1184 = EK kl768 s₀ := (EK_eq kl768 s₀).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a1) 32 = M kl768 s₀ := (M_eq kl768 s₀).symm
  rw [h3, e, hkey, hct, e0, e1]
  exact outcome kl768_wf s₀

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x10000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.encaps (Proof.MlKem.Scrubbed.encapsBodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correct (pre_of hs)
    exact ⟨t, s', he, ⟨hpres, hsp, hlr⟩, post_of h3 hkey hct⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 s₁) = ekRho kl768.p (EK kl768 s₂) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ct ⟨hp₁, hp₂, hsp, g3, g4, g5, g6, g7, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsBodyContract, Spec.MlKem.encapsSig, RISCV64.abi, RISCV64.argRegs]
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
  a0 : s₁.gpr .a0 = s₂.gpr .a0
  a1 : s₁.gpr .a1 = s₂.gpr .a1
  a2 : s₁.gpr .a2 = s₂.gpr .a2
  a3 : s₁.gpr .a3 = s₂.gpr .a3
  a4 : s₁.gpr .a4 = s₂.gpr .a4
  a5 : s₁.gpr .a5 = s₂.gpr .a5
  rho : ekRho K.p (EK K (args s₁)) = ekRho K.p (EK K (args s₂))

/-- What `encaps`'s runs of their arguments are. -/
theorem TwoH.two {K : KemLay} {s₁ s₂ : State} (t : TwoH K s₁ s₂) : Two K (args s₁) (args s₂) :=
  ⟨t.hq₁.pre, t.hq₂.pre, t.sp, t.a0, t.a2, t.a3, t.a4, t.a5, t.rho⟩

theorem all_ctH {K : KemLay} {s₁ s₂ : State} (two : TwoH K s₁ s₂) :
    RelCT isa (fun a b => a = s₁ ∧ b = s₂) K.encapsH fun _ _ => True := by
  have hq₁ := two.hq₁
  have hq₂ := two.hq₂
  have hp₁ := hq₁.pre
  have hp₂ := hq₂.pre
  have tw := two.two
  -- the setup
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ a.gpr .s9 = pM (args s₁) ∧ a.gpr .a1 = pH s₁ ∧
        bytesAt a.mem ((layM (args s₁) K).A 2 0) 32 = M K (args s₁) ∧
        bytesAt a.mem ((layH K s₁).A 2 0) 32 = bytesAt s₁.mem ((layH K s₁).A 2 0) 32) ∧
      (EnEnv K (args s₂) b ∧ b.gpr .s9 = pM (args s₂) ∧ b.gpr .a1 = pH s₂ ∧
        bytesAt b.mem ((layM (args s₂) K).A 2 0) 32 = M K (args s₂) ∧
        bytesAt b.mem ((layH K s₂).A 2 0) 32 = bytesAt s₂.mem ((layH K s₂).A 2 0) 32))
    (relct_wp (taint_block [.a0, .a1, .a2, .a3, .a4, .a5] (fun a b hab => by rw [hab.1, hab.2, two.sp])
      (fun a b hab r hr => by
        rw [hab.1, hab.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact two.a0
        · exact two.a1
        · exact two.a2
        · exact two.a3
        · exact two.a4
        · exact two.a5) (by taint_decide))
      fun a b hab => ⟨by rw [hab.1]; exact setupH_ok hq₁, by rw [hab.2]; exact setupH_ok hq₂⟩) ?_
  -- `h` copied
  refine RelCT.seq (R := fun (a b : State) =>
      (EnEnv K (args s₁) a ∧ a.gpr .s9 = pM (args s₁) ∧
        bytesAt a.mem ((layM (args s₁) K).A 2 0) 32 = M K (args s₁) ∧
        bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (EnEnv K (args s₂) b ∧ b.gpr .s9 = pM (args s₂) ∧
        bytesAt b.mem ((layM (args s₂) K).A 2 0) 32 = M K (args s₂) ∧
        bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (taint_prog [.a1, .s11] (fun a b hab => tw.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.2.1, hab.2.2.2.1]; exact two.a1
        · exact tw.regs hab.1.1 hab.2.1 .s11 (by simp)) (by taint_decide))
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
    (relct_wp (taint_prog [.s9, .s11] (fun a b hab => tw.spE hab.1.1 hab.2.1)
      (fun a b hab r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [hab.1.2.1, hab.2.2.1]; exact two.a2
        · exact tw.regs hab.1.1 hab.2.1 .s11 (by simp)) (by taint_decide))
      fun a b hab => ⟨copyMh_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2.1 hab.1.2.2.2,
        copyMh_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2.1 hab.2.2.2.2⟩) ?_
  refine RelCT.seq (R := fun (a b : State) =>
      (F4 K (args s₁) a ∧ bytesAt a.mem ((lay (args s₁) K).A 0 oHek) 32 = H (EK K (args s₁))) ∧
      (F4 K (args s₂) b ∧ bytesAt b.mem ((lay (args s₂) K).A 0 oHek) 32 = H (EK K (args s₂))))
    (relct_wp (relct_noMem (by rfl)) fun a b hab =>
      ⟨s4h_ok hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, s4h_ok hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  exact tail_ct tw

/-! ## ML-KEM-768's `encapsH` -/

theorem pre_ofH {s : State} (h : (Proof.MlKem.Scrubbed.encapsHBodyContract RISCV64.abi 1168).pre s) : PreH kl768 s := by
  sig_pre [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs] at h
  obtain ⟨al, h0, h1, h2, d1, d2, d3, dh1, dh2, dh3, d4, d5, d6, d7, d8, d9, b1, bh, b2, b3, b4, b5,
    f1, fh, f2, f3, f4, f5, hh, alS⟩ := h
  have r : (args s).rd = _ := h1
  exact ⟨⟨kl768_wf, kl768_calls, al, h0, by rw [r]; exact .head _, by rw [r]; exact .tail _ (.tail _ (.head _)),
    h2, d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, alS⟩,
    by rw [h1]; exact .tail _ (.head _), dh3, bh, fh, by rw [EK_eq]; exact hh⟩

/-- `post_of` for `encapsH`, whose arguments after `ek` are one register later. -/
theorem post_ofH {s₀ s : State}
    (h3 : s.gpr .a0 = if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then 1 else 0)
    (hkey : bytesAt s.mem (pKey (args s₀)) 32 = KK kl768 (args s₀))
    (hct : bytesAt s.mem (pCt (args s₀)) 1088 = VG.Proof.MlKem.KPke.ct kl768.p
      (aEnc (ekRho kl768.p (EK kl768 (args s₀))) (RR kl768 (args s₀))) (EK kl768 (args s₀)) (M kl768 (args s₀))
      (RR kl768 (args s₀))) :
    (Proof.MlKem.Scrubbed.encapsHBodyContract RISCV64.abi 1168).post s₀ s := by
  sig_post [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
    RISCV64.argRegs]
  have e : BitVec.setWidth 32
      (if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then (1 : BitVec 64) else 0) =
      if okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k then 1 else 0 := by
    cases okEnc kl768.k (ekRho kl768.p (EK kl768 (args s₀))) kl768.k <;> rfl
  have e0 : bytesAt s₀.mem (s₀.gpr .a0) 1184 = EK kl768 (args s₀) := (EK_eq kl768 (args s₀)).symm
  have e1 : bytesAt s₀.mem (s₀.gpr .a2) 32 = M kl768 (args s₀) := (M_eq kl768 (args s₀)).symm
  have hkey' : bytesAt s.mem (s₀.gpr .a3) 32 = KK kl768 (args s₀) := hkey
  have hct' : bytesAt s.mem (s₀.gpr .a4) 1088 = _ := hct
  rw [h3, e, hkey', hct', e0, e1]
  exact outcome kl768_wf (args s₀)

/-- A state satisfying `encapsH`'s precondition, with `H(ek)` at `h` (`hMem`). -/
def satStateH (ekLen ctLen scr : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x5000 | .a5 => 0x10000 | _ => 0
  sp := 0x8000
  mem := VG.Proof.MlKem.hMem ekLen
  rd := [⟨0x1000, ekLen⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x4000, 32⟩, ⟨0x5000, ctLen⟩, ⟨0x10000, scr⟩]

theorem verifiedH :
    Verified RISCV64.target Impl.MlKem.RISCV64.encapsH (Proof.MlKem.Scrubbed.encapsHBodyContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h3, hkey, hct⟩ := correctH (pre_ofH hs)
    exact ⟨t, s', he, ⟨fun r hr => (hpres r hr).trans (args_preserved s r hr), hsp, hlr⟩, post_ofH h3 hkey hct⟩
  · have hq₁ := pre_ofH h₁
    have hq₂ := pre_ofH h₂
    sig_pub [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
      RISCV64.argRegs] at hpub
    obtain ⟨hsp, hl, g3, g4, g5, g6, g7, g8⟩ := hpub
    have hr : ekRho kl768.p (EK kl768 (args s₁)) = ekRho kl768.p (EK kl768 (args s₂)) := by
      rw [EK_eq, EK_eq]
      unfold leakRho at hl
      exact (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hl
    exact (all_ctH ⟨hq₁, hq₂, hsp, g3, g4, g5, g6, g7, g8, hr⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satStateH 1184 1088 32768, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlKem.Scrubbed.encapsHBodyContract, Spec.MlKem.encapsHSig, Spec.MlKem.encapsHSigOf, RISCV64.abi,
        RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | exact VG.Proof.MlKem.hMem_h (by decide)
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.Encaps
