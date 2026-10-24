module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encrypt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashTop
public import VerifiedGarbage.Proof.MlKem.PPC64LE.TopSave
import VerifiedGarbage.Proof.MlKem.PPC64LE.Loops
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

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

theorem lay_ptr0 (K : KemLay) (s₀ : State) : (lay s₀ K).ptr 0 = pScr s₀ := rfl
theorem layM_ptr0 (K : KemLay) (s₀ : State) : (layM s₀ K).ptr 0 = pScr s₀ := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  sp48 : 48 ≤ s.sp.toNat
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
  · rw [Lay.bytes_keep hL hk.frame h2 (by have := hK.k4; simp only [KemLay.ekLen]; omega)]; exact h.ek

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layM s₀ K).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layM]

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
    Lay.covers w0 (o := o) (l := 8) (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
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
  have ek : K.ekLen ≤ 2 ^ 64 := by have := hK.k4; simp only [KemLay.ekLen]; omega
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
      EnEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oMsg) 32 = M K s₀ := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, wM, wM0⟩ := buf_wr hp
  refine WP.mono (copyL (layM_ok hp) (i := 2) (j := 0) (by decide) (by decide) h29
    h.ctx.r31 (by decide) (by decide) (by decide) (by decide) (by edecide)
    (by rw [h.rd, h.wr]; exact wM) (by rw [h.wr]; exact wM0)) fun s' ⟨k, e⟩ => ⟨?_, ?_⟩
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
      (by show K.ekLen < 32768; have := hK.k4; simp only [KemLay.ekLen]; omega)
      (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega) (by edecide)
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
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.encaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      s.gpr .r3 = (if okEnc K.k (ekRho K.p (EK K s₀)) K.k then 1 else 0) ∧
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
  refine WP.mono (end_ok hp h₈) fun s ⟨pr, lr, r3, m', sp'⟩ => ⟨pr, sp', lr, by rw [r3, r24₈], ?_, ?_⟩
  · show bytesAt s.mem ((lay s₀ K).ptr 3) 32 = _
    rw [m', ← A_zero (lay s₀ K) 3]; exact key₈
  · show bytesAt s.mem ((lay s₀ K).ptr 4) K.ctLen = _
    rw [m', ← A_zero (lay s₀ K) 4]; exact ct₈

end VG.Proof.MlKem.PPC64LE.Encaps
