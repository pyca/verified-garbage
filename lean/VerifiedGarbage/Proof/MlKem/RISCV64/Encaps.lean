module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.RISCV64.Encrypt
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashTop
public import VerifiedGarbage.Proof.MlKem.RISCV64.TopSave
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: encapsulation, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/Encaps.lean`): `K.encaps` for any
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

theorem lay_ptr0 (K : KemLay) (s₀ : State) : (lay s₀ K).ptr 0 = pScr s₀ := rfl
theorem layM_ptr0 (K : KemLay) (s₀ : State) : (layM s₀ K).ptr 0 = pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  al : s.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s.sp.toNat
  rd : s.rd = [⟨pEk s, K.ekLen⟩, ⟨pM s, 32⟩]
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
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have := s₀.sp.isLt; omega

theorem lay_ok : (lay s₀ K).Ok := by
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_ek
    · exact hp.f_key
    · exact hp.f_ct
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
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
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_m
  · simp only [layM, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
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
  · rw [Lay.bytes_keep hL hk.frame h2 (by have := hK.k4; simp only [KemLay.ekLen]; omega)]; exact h.ek

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layM]

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
    Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
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
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega
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
      EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, wM, wM0⟩ := buf_wr hp
  refine WP.mono (copyL (layM_ok hp) (i := 2) (j := 0) (by decide) (by decide) h29
    h.ctx.s11 (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_⟩
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
      (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega)
      (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega) (by edecide)
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
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.encaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
      s.gpr .a0 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
      bytesAt s.mem (pKey s₀) 32 = KK K s₀ ∧
      bytesAt s.mem (pCt s₀) K.ctLen =
        VG.Proof.MlKem.KPke.ct K.p (aEnc (ekRho K.p (EK K s₀)) (RR K s₀)) (EK K s₀) (M K s₀) (RR K s₀) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₂ ⟨h₂, g29, m₂⟩ => ?_)
  refine WP.seq (WP.mono (copyM_ok hp h₂ g29 m₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (s4_ok hp h₃ m₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (s5_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s6_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (s7_ok hp h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (s8_ok hp h₇) fun s₈ ⟨h₈, key₈, r24₈, ct₈⟩ => ?_)
  refine WP.mono (end_ok hp h₈) fun s ⟨pr, lr, a0, m', sp'⟩ => ⟨pr, sp', lr, by rw [a0, r24₈], ?_, ?_⟩
  · show bytesAt s.mem ((lay s₀ K).ptr 3) 32 = _
    rw [m', ← A_zero (lay s₀ K) 3]; exact key₈
  · show bytesAt s.mem ((lay s₀ K).ptr 4) K.ctLen = _
    rw [m', ← A_zero (lay s₀ K) 4]; exact ct₈

end VG.Proof.MlKem.RISCV64.Encaps
