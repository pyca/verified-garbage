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
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ML-KEM on RISC-V: key generation, correctness

As on PPC64LE (`Proof/MlKem/PPC64LE/KeyGen.lean`): `K.keygen` for any
parameter set `K` (`KemLay.WF`). The buffers of the function (`lay`):
`scratch`, the stack, `seed`, `ek` and `dk`; what every phase keeps (`KEnv`:
the pointers, our caller's registers in `scratch`, the seed); and the
phases: the setup, `G(d ‖ k)` into `ρ` and `σ`, the `PRF`s into `ŝ` and `ê`,
the rows of `t̂ = Â ∘ ŝ + ê` encoded into `ek`, `ŝ` encoded into `dk`, the
copies of `ρ`, `ek` and `z`, and `H(ek)`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.KeyGen

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.RISCV64.Wp
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64.Enc (bytes_catK catK_congr flagInit_ok ptrSlot_ok)
open VG.Impl.Sha3.RISCV64.Stream (mov)

section
variable (s₀ : State)

abbrev pSeed : Addr := s₀.gpr .a0
abbrev pEk : Addr := s₀.gpr .a1
abbrev pDk : Addr := s₀.gpr .a2
abbrev pScr : Addr := s₀.gpr .a3

/-- The buffers: `scratch`, the 1168 bytes below the stack pointer, `seed`,
`ek` and `dk`. -/
def lay (K : KemLay) : Lay :=
  ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 64 1168, pSeed s₀, pEk s₀, pDk s₀].getD i 0,
    [K.scratch, 1168, 64, K.ekLen, K.dkLen]⟩

end

/-- The sizes of the buffers. -/
abbrev kSz (K : KemLay) : List Nat := [K.scratch, 1168, 64, K.ekLen, K.dkLen]

theorem lay_sizes (K : KemLay) (s₀ : State) : (lay s₀ K).sizes = kSz K := rfl

/-- The precondition of the contract. -/
structure Pre (K : KemLay) (s : State) : Prop where
  wf : K.WF
  calls : K.CallsOk
  al : s.sp.toNat % 16 = 0
  sp1168 : 1168 ≤ s.sp.toNat
  rd : s.rd = [⟨pSeed s, 64⟩]
  wr : s.wr = [⟨pEk s, K.ekLen⟩, ⟨pDk s, K.dkLen⟩, ⟨pScr s, K.scratch⟩]
  d_se : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pEk s, K.ekLen⟩
  d_sd : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pDk s, K.dkLen⟩
  d_ss : (⟨pSeed s, 64⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_ed : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pDk s, K.dkLen⟩
  d_es : (⟨pEk s, K.ekLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  d_ds : (⟨pDk s, K.dkLen⟩ : Region).Disjoint ⟨pScr s, K.scratch⟩
  b_s : (below s.sp 1168).Disjoint ⟨pSeed s, 64⟩
  b_e : (below s.sp 1168).Disjoint ⟨pEk s, K.ekLen⟩
  b_d : (below s.sp 1168).Disjoint ⟨pDk s, K.dkLen⟩
  b_c : (below s.sp 1168).Disjoint ⟨pScr s, K.scratch⟩
  f_s : (pSeed s).toNat + 64 ≤ 2 ^ 64
  f_e : (pEk s).toNat + K.ekLen ≤ 2 ^ 64
  f_d : (pDk s).toNat + K.dkLen ≤ 2 ^ 64
  f_c : (pScr s).toNat + K.scratch ≤ 2 ^ 64
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
    · exact hp.f_c
    · exact stack_fit hp
    · exact hp.f_s
    · exact hp.f_e
    · exact hp.f_d
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · exact hp.b_c.symm
    · exact hp.d_ss.symm
    · exact hp.d_es.symm
    · exact hp.d_ds.symm
    · exact hp.b_s
    · exact hp.b_e
    · exact hp.b_d
    · exact hp.d_se
    · exact hp.d_sd
    · exact hp.d_ed

end

/-- What every phase keeps: the pointers, the callee-saved registers we do
not save, our caller's registers in `scratch`, and the seed. -/
structure KEnv (K : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀ K) s
  s10 : s.gpr .s10 = pSeed s₀
  s9 : s.gpr .s9 = pEk s₀
  s8 : s.gpr .s8 = pDk s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r
  sav : TopSaved s.mem (pScr s₀) s₀
  seed : bytesAt s.mem ((lay s₀ K).A 2 0) 64 = bytesAt s₀.mem ((lay s₀ K).A 2 0) 64

/-- A region the phases may change: apart from the saved registers and the seed. -/
def okW (K : KemLay) (w : Nat × Nat × Nat) : Bool := sepB (kSz K) (0, 1288, 80) w && sepB (kSz K) (2, 0, 64) w

/-- The buffer of each pointer register. -/
def kidx : Reg → Nat
  | .s10 => 2 | .s9 => 3 | .s8 => 4 | _ => 0

/-- Decides a fact about the offsets in the buffers. -/
tactic_template "ldecide" : tactic => `(tactic| first
                   | decide
                   | ((try simp only [lay_sizes, kSz, kidx, okW, kRegs, List.all_cons, List.all_nil, List.all_append,
                         List.map_cons, List.map_nil, trip, Bool.and_true])
                      (try have := (‹KemLay.WF _›).scr)
                      kdecide))

theorem saveR_eq (K : KemLay) (s₀ : State) : saveR (pScr s₀) = (lay s₀ K).R 0 1288 80 := rfl

theorem KEnv.keep {K : KemLay} {s₀ s s' : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (hk : KeptX xs ((lay s₀ K).RL W) s s')
    (hx : ∀ x ∈ xs, x ∈ savedTop ∧ x ≠ .s10 ∧ x ≠ .s9 ∧ x ≠ .s8 ∧ x ≠ .s11) (hW : W.all (okW K) = true) :
    KEnv K s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀ K).sizes (0, 1288, 80) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀ K).sizes (2, 0, 64) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have nx : ∀ r, r = .s10 ∨ r = .s9 ∨ r = .s8 ∨ r = .s11 → r ∉ xs := fun r hr hm => by
    obtain ⟨-, a, b, c, d⟩ := hx r hm
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all
  refine ⟨hk.ctx (nx _ (by simp)) h.ctx, ?_, ?_, ?_, hk.rd.trans h.rd, hk.wr.trans h.wr,
    hk.sp.trans h.sp, fun r hr hs => ?_, h.sav.keep hk.frame (by rw [saveR_eq K]; exact Lay.disjAll hL h1), ?_⟩
  · rw [hk.cs .s10 (by decide) (nx _ (by simp)), h.s10]
  · rw [hk.cs .s9 (by decide) (nx _ (by simp)), h.s9]
  · rw [hk.cs .s8 (by decide) (nx _ (by simp)), h.s8]
  · rw [hk.cs r hr (fun hm => hs (hx r hm).1), h.cs r hr hs]
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.seed

theorem buf_wr {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    (lay s₀ K).buf 0 ∈ s₀.wr ∧ (lay s₀ K).buf 3 ∈ s₀.wr ∧ (lay s₀ K).buf 4 ∈ s₀.wr ∧
      (lay s₀ K).buf 2 ∈ s₀.rd ++ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay]

/-! ## The setup -/

theorem setup_ok {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa (.block K.kgSetup) s₀ fun s => KEnv K s₀ s ∧ s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k := by
  have hL := lay_ok hp
  have hK := hp.wf
  have scr := hK.scr
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr (pScr s₀ + BitVec.ofNat 64 o) n := fun h =>
    Lay.covers w0 (by simp only [lay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [KemLay.kgSetup, WP.block_append_iff]
  refine WP.mono (topSave_ok rfl hp.alS fun o _ h₂ => wS (by omega))
    fun s₁ ⟨sav, fr, g₁, rd₁, wr₁, sp₁⟩ => ?_
  have g3 : s₁.gpr .a0 = pSeed s₀ := by rw [g₁]
  have g4 : s₁.gpr .a1 = pEk s₀ := by rw [g₁]
  have g5 : s₁.gpr .a2 = pDk s₀ := by rw [g₁]
  have g6 : s₁.gpr .a3 = pScr s₀ := by rw [g₁]
  have i1184 : InRegions s₁.wr (pScr s₀ + BitVec.ofNat 64 oK) 1 := by rw [wr₁]; exact wS (by decide)
  have ek : K.k < 2048 := by have := hK.k4; omega
  have sk := setWidth8_ofNat (N := K.k) (by omega)
  have hmv : WP isa (.block [mov .s10 .a0, mov .s9 .a1, mov .s8 .a2, mov .s11 .a3, .li .t0 K.k,
      .store .b .t0 .s11 oK]) s₁ fun s =>
      s.gpr .s10 = pSeed s₀ ∧ s.gpr .s9 = pEk s₀ ∧ s.gpr .s8 = pDk s₀ ∧ s.gpr .s11 = pScr s₀ ∧
      (∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₁.gpr r) ∧
      s.mem = s₁.mem.writeW (pScr s₀ + BitVec.ofNat 64 oK) (BitVec.ofNat 8 K.k) ∧
      s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp :=
    wp_mv fun u₁ h₁ => wp_mv fun u₂ h₂ => wp_mv fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_li ek fun u₅ h₅ =>
      wp_sb (a := pScr s₀ + BitVec.ofNat 64 oK) (by decide)
        (by simp only [h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g6])
        (by rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact i1184) fun u₆ m₆ => WP.block_nil
        ⟨by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g3],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g4],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g5],
          by simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, reduceCtorEq, ↓reduceIte, g6],
          fun r hr hs => by
            have h0 := (pres_ne hr).1
            simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
            obtain ⟨-, -, -, -, -, a8, a9, a10, a11⟩ := hs
            simp only [m₆.gpr, h₅.gpr_eq, h₄.gpr_eq, h₃.gpr_eq, h₂.gpr_eq, h₁.gpr_eq, a8, a9, a10, a11, h0,
              ↓reduceIte],
          by rw [m₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₅.gpr, sk],
          by rw [m₆.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [m₆.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
          by rw [m₆.sp, h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]⟩
  refine WP.mono hmv fun s ⟨g30, g29, g28, g31, cs, m, rd, wr, sp⟩ => ?_
  have c1184 : ((lay s₀ K).R 0 1184 1).Contains (pScr s₀ + BitVec.ofNat 64 oK) (8 / 8) :=
    Region.contains_self _ _
  have fr' : Frame ((lay s₀ K).RL [(0, 1288, 80), (0, 1184, 1)]) s₀.mem s.mem := by
    rw [m]
    exact (fr.mono (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [saveR_eq K])).writeW
      (by simp) _ c1184
  refine ⟨⟨⟨hL, scr, rfl, by simp [lay], g31, by rw [sp, sp₁]; exact hp.sp1168, by rw [sp, sp₁]; exact hp.al,
    hp.alS, by rw [sp, sp₁]; rfl, by rw [wr, wr₁, hp.wr]; simp [lay]⟩, g30, g29, g28, rd.trans rd₁, wr.trans wr₁,
    sp.trans sp₁, fun r hr hs => ?_, ?_, ?_⟩, ?_⟩
  · rw [cs r hr hs, g₁]
  · rw [m]
    exact sav.keep ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c1184) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [saveR_eq K]; exact Lay.disj hL (by ldecide))
  · exact Lay.bytes_keep hL fr' (by ldecide) (by decide)
  · show s.mem (pScr s₀ + BitVec.ofNat 64 oK) = _
    rw [m, writeW8_apply, ite_eq_left rfl]

/-! ## Pieces of the hashes -/

theorem pieceK {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .s10 ∨ p.base = .s9 ∨ p.base = .s8 ∨ p.base = .s11) (hw : w = true → p.base ≠ .s10)
    (hoe : p.off < 32768) (hle : p.len < 2048) (hpos : 0 < p.len)
    (hsep : sepAll (kSz K) (kidx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀ K) kidx s w p := by
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  rw [← h.wr] at w0 w3 w4
  rw [← h.wr, ← h.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hsep, ?_⟩
  · rcases hb with e | e | e | e <;> rw [e] <;> decide
  · rcases hb with e | e | e | e <;> rw [e]
    · exact h.s10
    · exact h.s9
    · exact h.s8
    · exact h.ctx.s11
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e | e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w3
      · exact mem_rd_wr w4
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rcases hb with e | e | e | e
      · exact absurd e (hw rfl)
      all_goals rw [e]
      · exact w3
      · exact w4
      · exact w0

/-! ## `G(d ‖ k)` -/

/-- `d`, the first half of the seed. -/
abbrev D (s₀ : State) : List Byte := bytesAt s₀.mem (pSeed s₀) 32

/-- `z`, the second half of the seed. -/
abbrev Z (s₀ : State) : List Byte := bytesAt s₀.mem (pSeed s₀ + BitVec.ofNat 64 32) 32

theorem g_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s10, 0, 32⟩ : Piece), ⟨.s11, oK, 1⟩], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact pieceK hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by ldecide)
  · exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by ldecide)

theorem g_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s11, oG, 64⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inr rfl))) (by simp) (by decide) (by decide) (by decide) (by ldecide)

theorem g_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (h3 : s.mem ((lay s₀ K).A 0 oK) = BitVec.ofNat 8 K.k) :
    WP isa (hash 72 0x06 [⟨.s10, 0, 32⟩, ⟨.s11, oK, 1⟩] [⟨.s11, oG, 64⟩]) s fun s' =>
      KEnv K s₀ s' ∧ bytesAt s'.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hK := hp.wf
  have hin := g_ins hp h
  have hout := g_outs hp h
  have hD : bytesAt s.mem ((lay s₀ K).A 2 0) 32 = D s₀ := by
    have := congrArg (List.take 32) h.seed
    rw [bytesAt_take _ _ (by decide), bytesAt_take _ _ (by decide)] at this
    rw [this]; show bytesAt s₀.mem (pSeed s₀ + BitVec.ofNat 64 0) 32 = _; rw [BitVec.add_zero]
  have hin' : (List.map ((lay s₀ K).pb kidx s.mem) [⟨.s10, 0, 32⟩, ⟨.s11, oK, 1⟩]).flatten =
      D s₀ ++ [BitVec.ofNat 8 K.k] := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀ K).A 2 0) 32 ++ bytesAt s.mem ((lay s₀ K).A 0 oK) 1 = _
    rw [hD, bytes_one, h3]
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) h.ctx (List.cons_ne_nil _ _) hin hout
    (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by ldecide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀ K).A 0 oG) 64 = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1 ++
        (G (D s₀ ++ [BitVec.ofNat 8 K.k])).2 := e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀ K).A 0 oG) 32).length = (G (D s₀ ++ [BitVec.ofNat 8 K.k])).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem ((lay s₀ K).ptr 0 + BitVec.ofNat 64 (920 + 32)) 32 = _
    rw [← ptr_add]; exact r2

theorem rho_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oG) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (copy .s11 oG .s11 oSeed 32) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀) := by
  have hL := lay_ok hp
  have hK := hp.wf
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  refine WP.mono (copyL hL (i := 0) (j := 0) (by decide) (by decide) h.ctx.s11 h.ctx.s11
    (by decide) (by decide) (by decide) (by decide) (by ldecide)
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w0)) fun s' ⟨k', b'⟩ =>
    ⟨h.keep hp (k'.x []) (by simp) (by ldecide), b'.trans hr,
      (Lay.bytes_keep hL k'.frame (by ldecide) (by decide)).trans hs⟩

/-! ## The `PRF`s -/

theorem prf_phase {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀))
    (hs : bytesAt s.mem ((lay s₀ K).A 0 oSigma) 32 = VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) :
    WP isa (K.prfLoop true 0 (2 * K.k)) s fun s' => KEnv K s₀ s' ∧
      bytesAt s'.mem ((lay s₀ K).A 0 oSeed) 32 = VG.Proof.MlKem.KPke.kgRho K.p (D s₀) ∧
      ∀ N < 2 * K.k, PolyIs s'.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
        (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N)) := by
  have hK := hp.wf
  exact WP.mono (prfLoop_ok hK h.ctx true (by have := hK.k1; omega) (by omega) hs) fun s' ⟨k', p'⟩ =>
    ⟨h.keep hp k' (by simp [savedTop]) (by ldecide),
      by rw [← hr]; exact Lay.bytes_keep (lay_ok hp) k'.frame (by ldecide) (by decide),
      fun N hN => p' N (Nat.zero_le _) hN⟩

/-! ## Pointers into `ek` and `dk` -/

/-- `a0` at polynomial `j` of `scratch`, `a1` at `b + 384 i`. -/
theorem ptrMul_ok {s : State} {P B : BitVec 64} {b : Reg} {i j : Nat} (hb : b = .s9 ∨ b = .s8)
    (h11 : s.gpr .s11 = P) (hB : s.gpr b = B) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hj : j + 2 < 2048) :
    WP isa (.block (polyAddr .a0 j ++ atMul .a1 b .s6 384)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly j) ∧ s'.gpr .a1 = B + BitVec.ofNat 64 (384 * i) := by
  have hb0 : b ≠ .t0 := by rcases hb with rfl | rfl <;> decide
  have hba : b ≠ .a0 := by rcases hb with rfl | rfl <;> decide
  rw [← List.append_nil (atMul .a1 b .s6 384)]
  refine wp_polyAddr hj (by decide) fun s₁ h₁ => wp_atMul (by decide) hb0 (by decide) fun s₂ u₂ => WP.block_nil
    ⟨⟨fun r hr => ?_, by rw [u₂.mem, h₁.mem], by rw [u₂.rd, h₁.rd], by rw [u₂.wr, h₁.wr], by rw [u₂.sp, h₁.sp]⟩,
      ?_, ?_⟩
  · obtain ⟨n0, n1, n2, -, -, -⟩ := pres_ne hr
    rw [u₂.other _ n2 n0, h₁.other _ n1]
  · rw [u₂.other _ (by decide) (by decide), h₁.gpr, h11]
  · rw [u₂.gpr, h₁.other _ hba, h₁.other _ (by decide), hB, h6, mul_eq]

/-- `a0` at polynomial `i` of the array from polynomial `j`, `a1` at `b + 384 i`. -/
theorem slotMul_ok {s : State} {P B : BitVec 64} {b : Reg} {i j : Nat} (hb : b = .s9 ∨ b = .s8)
    (h11 : s.gpr .s11 = P) (hB : s.gpr b = B) (h6 : s.gpr .s6 = BitVec.ofNat 64 i) (hj : j + 2 < 2048)
    (hi : i + j + 2 < 2 ^ 50) :
    WP isa (.block (slotAt .a0 .s6 j ++ atMul .a1 b .s6 384)) s fun s' =>
      Only s s' ∧ s'.gpr .a0 = P + BitVec.ofNat 64 (oPoly j + 1024 * i) ∧
      s'.gpr .a1 = B + BitVec.ofNat 64 (384 * i) := by
  have hb0 : b ≠ .t0 := by rcases hb with rfl | rfl <;> decide
  have hba : b ≠ .a0 := by rcases hb with rfl | rfl <;> decide
  rw [← List.append_nil (atMul .a1 b .s6 384)]
  refine wp_slotAt hj hi (by decide) h6 fun s₁ h₁ => wp_atMul (by decide) hb0 (by decide) fun s₂ u₂ =>
    WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₂.mem, h₁.mem], by rw [u₂.rd, h₁.rd], by rw [u₂.wr, h₁.wr],
      by rw [u₂.sp, h₁.sp]⟩, ?_, ?_⟩
  · obtain ⟨n0, n1, n2, -, -, -⟩ := pres_ne hr
    rw [u₂.other _ n2 n0, h₁.other _ n1]
  · rw [u₂.other _ (by decide) (by decide), h₁.gpr, h11]
  · rw [u₂.gpr, h₁.other _ hba, h₁.other _ (by decide), hB, h6, mul_eq]

/-! ## The rows of `t̂` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ρ`. -/
abbrev ρ₀ : List Byte := VG.Proof.MlKem.KPke.kgRho K.p (D s₀)

/-- `ŝ`. -/
abbrev sK : Nat → Poly := VG.Proof.MlKem.KPke.kgS K.p (D s₀)

/-- The entries of `Â` the products use. -/
abbrev aK (i j : Nat) : Poly := effA false (ρ₀ K s₀) i j (sK K s₀ j)

/-- Whether the `SampleNTT`s of the first `i` rows finished. -/
def okK (i : Nat) : Bool := (List.range i).all fun i' => okRow false (ρ₀ K s₀) i' K.k

/-- `t̂`. -/
abbrev tK : Nat → Poly := VG.Proof.MlKem.KPke.kgT K.p (aK K s₀) (D s₀)

end

theorem okK_succ (K : KemLay) (s₀ : State) (i : Nat) :
    okK K s₀ (i + 1) = (okK K s₀ i && okRow false (ρ₀ K s₀) i K.k) := by
  simp only [okK, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

/-- After the first `i` rows. -/
structure KRow (K : KemLay) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 i
  s4 : s.gpr .s4 = if okK K s₀ i then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  slots : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
    (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))
  ek : ∀ i' < i, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')

/-- What a row changes. -/
abbrev rowK (K : KemLay) (i : Nat) : List (Nat × Nat × Nat) :=
  [(0, 1280, 2), (0, K.oAcc, 3072), (0, K.oSample, 3072), (1, 0, 1168), (0, K.oAcc, 1024), (3, 384 * i, 384)]

/-- `rowK_ok` with the sizes `sz` of the buffers. -/
abbrev RowKF (K : KemLay) (sz : List Nat) : Prop := ∀ i < K.k,
    (rowK K i).all (fun w => sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll sz (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll sz (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB sz (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB sz (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true

theorem rowK_ok {K : KemLay} (hK : K.WF) {i : Nat} (hi : i < K.k) : (rowK K i).all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) (rowK K i) = true ∧
    (∀ N < 2 * K.k, sepAll (kSz K) (0, oPoly (K.k + N), 1024) (rowK K i) = true) ∧
    (∀ i' < K.k, i' ≠ i → sepAll (kSz K) (3, 384 * i', 384) (rowK K i) = true) ∧
    sepB (kSz K) (0, K.oAcc, 1024) (3, 384 * i, 384) = true ∧
    sepB (kSz K) (0, K.oAcc, 1024) (0, oPoly (K.k + (K.k + i)), 1024) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, RowKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) i hi
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun N hN => sepAll_scr (c3 N hN) scr,
    fun i' hi' hne => sepAll_scr (c4 i' hi' hne) scr, sepB_scr c5 scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

/-- The row's facts at its start `s`, for its `RowSum`. -/
theorem KRow.rowPre {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) : RowPre K (lay s₀ K) (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s :=
  ⟨hp.wf, h.env.ctx, hi, h.s6, h.s4, h.rho, fun j hj => h.slots j (by omega)⟩

section
variable (K : KemLay) (s₀ : State) (i : Nat) (s : State)

/-- After the arguments of `t̂[i] += ê[i]`. -/
structure KR2 (s₂ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₂
  s6 : s₂.gpr .s6 = BitVec.ofNat 64 i
  a0 : s₂.gpr .a0 = (lay s₀ K).A 0 K.oAcc
  a1 : s₂.gpr .a1 = (lay s₀ K).A 0 (oPoly (K.k + (K.k + i)))
  s4 : s₂.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₂.mem ((lay s₀ K).A 0 K.oAcc) (VG.Proof.MlKem.KPke.dotK (aK K s₀ i) (sK K s₀) K.k)

/-- After `t̂[i]`. -/
structure KR3 (s₃ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₃
  s6 : s₃.gpr .s6 = BitVec.ofNat 64 i
  s4 : s₃.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  acc : PolyIs s₃.mem ((lay s₀ K).A 0 K.oAcc) (tK K s₀ i)

/-- After the arguments of its encoding. -/
structure KR4 (s₄ : State) : Prop where
  a0 : KR3 K s₀ i s s₄
  a3 : s₄.gpr .a0 = (lay s₀ K).A 0 K.oAcc
  a4 : s₄.gpr .a1 = (lay s₀ K).A 3 (384 * i)

/-- After its encoding. -/
structure KR5 (s₅ : State) : Prop where
  kx : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s₅
  s6 : s₅.gpr .s6 = BitVec.ofNat 64 i
  s4 : s₅.gpr .s4 = if okK K s₀ (i + 1) then 1 else 0
  enc : bytesAt s₅.mem ((lay s₀ K).A 3 (384 * i)) 384 = encode12 (tK K s₀ i)

end

theorem KRow.ctxOf {K : KemLay} {s₀ : State} {i : Nat} {s : State} (h : KRow K s₀ i s) {x : State} {xs : List Reg}
    {W : List (Nat × Nat × Nat)} (k : KeptX xs ((lay s₀ K).RL W) s x) (h31 : Reg.s11 ∉ xs) : Ctx (lay s₀ K) x :=
  k.ctx h31 h.env.ctx

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State} (h : KRow K s₀ i s)
include hp hi h

theorem kr2_ok {s₁ : State}
    (r : RowInv K (lay s₀ K) false (ρ₀ K s₀) (sK K s₀) i (okK K s₀ i) s K.k s₁) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ slotAt .a1 .s6 (2 * K.k))) s₁ (KR2 K s₀ i s) := by
  have hK := hp.wf
  have hc₁ := h.ctxOf r.kx (by decide)
  have g26₁ : s₁.gpr .s6 = BitVec.ofNat 64 i := by rw [r.kx.cs .s6 (by decide) (by decide), h.s6]
  refine WP.mono (ptrSlot_ok (i := i) hc₁.s11 g26₁ (by offs) (by offs) (by offs)) fun s₂ ⟨o₂, a3, a4⟩ => ?_
  rw [show oPoly (2 * K.k) + 1024 * i = oPoly (K.k + (K.k + i)) by offs] at a4
  exact ⟨((r.kx.weaken (by simp)).monoL (by simp)).trans (o₂.x _ _),
    by rw [o₂.cs .s6 (by decide), g26₁], a3, a4,
    by rw [o₂.cs .s4 (by decide), r.s4, ← okK_succ],
    by rw [o₂.mem, ← rowAcc_eq]; exact r.acc⟩

theorem kr3_ok {s₂ : State} (r : KR2 K s₀ i s s₂) : WP isa callAdd s₂ (KR3 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₂ := h.ctxOf r.kx (by decide)
  obtain ⟨-, -, c_slots, -, -, c_add⟩ := rowK_ok hp.wf hi
  have sl₂ : PolyIs s₂.mem ((lay s₀ K).A 0 (oPoly (K.k + (K.k + i))))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) (K.k + i))) :=
    Lay.polyIs_keep hL r.kx.frame (c_slots (K.k + i) (by omega)) (h.slots (K.k + i) (by omega))
  exact addL hL r.a0 r.a1 c_add hc₂.cw (mem_rd_wr hc₂.cw) r.acc sl₂ (hc₂.alP _) (hc₂.alP _) fun s₃ k₃ p₃ =>
    ⟨r.kx.trans ((k₃.x _).monoL (by simp)), by rw [k₃.cs .s6 (by decide), r.s6],
      by rw [k₃.cs .s4 (by decide), r.s4], p₃⟩

omit hi in
theorem kr4_ok {s₃ : State} (r : KR3 K s₀ i s s₃) :
    WP isa (.block (polyAddr .a0 K.jAcc ++ atMul .a1 .s9 .s6 384)) s₃ (KR4 K s₀ i s) := by
  have hK := hp.wf
  have hc₃ := h.ctxOf r.kx (by decide)
  have g29₃ : s₃.gpr .s9 = pEk s₀ := by rw [r.kx.cs .s9 (by decide) (by decide), h.env.s9]
  refine WP.mono (ptrMul_ok (b := .s9) (.inl rfl) hc₃.s11 g29₃ r.s6 (by offs)) fun s₄ ⟨o₄, b3, b4⟩ =>
    ⟨⟨r.kx.trans (o₄.x _ _), by rw [o₄.cs .s6 (by decide), r.s6],
      by rw [o₄.cs .s4 (by decide), r.s4], by rw [o₄.mem]; exact r.acc⟩, b3, b4⟩

theorem kr5_ok {s₄ : State} (r : KR4 K s₀ i s s₄) : WP isa callEncode12 s₄ (KR5 K s₀ i s) := by
  have hL := lay_ok hp
  have hc₄ := h.ctxOf r.a0.kx (by decide)
  obtain ⟨-, -, -, -, c_enc, -⟩ := rowK_ok hp.wf hi
  obtain ⟨-, w3, -, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 3) (o' := 384 * i) r.a3 r.a4 c_enc (mem_rd_wr hc₄.cw)
    (by rw [r.a0.kx.wr, h.env.wr]; exact w3) r.a0.acc (hc₄.alP _) fun s₅ k₅ e₅ =>
    ⟨r.a0.kx.trans ((k₅.x _).monoL (by simp)), by rw [k₅.cs .s6 (by decide), r.a0.s6],
      by rw [k₅.cs .s4 (by decide), r.a0.s4], e₅⟩

theorem kr6_ok {s₅ : State} (r : KR5 K s₀ i s s₅) :
    WP isa (.block (count .s6 K.k)) s₅ fun s' =>
      KRow K s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_slots, c_ek, -, -⟩ := rowK_ok hK hi
  refine WP.mono (count_ok (by decide) (by omega) (by omega) r.s6) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.s6, .s5, .s4] ((lay s₀ K).RL (rowK K i)) s s' :=
    r.kx.trans ((k'.weaken (by simp)).mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp [savedTop]) c_ok
  · rw [k'.cs .s4 (by decide) (by decide), r.s4]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun N hN => Lay.polyIs_keep hL K'.frame (c_slots N hN) (h.slots N hN)
  · intro i' hi'
    by_cases e : i' = i
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · rw [← h.ek i' (by omega)]; exact Lay.bytes_keep hL K'.frame (c_ek i' (by omega) e) (by decide)

end

theorem kgRow_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {i : Nat} (hi : i < K.k) {s : State}
    (h : KRow K s₀ i s) :
    WP isa K.kgRowBody s fun s' => KRow K s₀ (i + 1) s' ∧ (s'.gpr .t0 != 0) = decide (i + 1 ≠ K.k) :=
  WP.seq (WP.mono (rowSum_ok (transpose := false) (h.rowPre hp hi)) fun _ r₁ =>
    WP.seq (WP.mono (kr2_ok hp hi h r₁) fun _ r₂ => WP.seq (WP.mono (kr3_ok hp hi h r₂) fun _ r₃ =>
    WP.seq (WP.mono (kr4_ok hp h r₃) fun _ r₄ => WP.seq (WP.mono (kr5_ok hp hi h r₄) fun _ r₅ =>
      kr6_ok hp hi h r₅)))))

theorem rows_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
    (hr : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀)
    (hs : ∀ N < 2 * K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + N)))
      (ntt (VG.Proof.MlKem.cbd (VG.Proof.MlKem.KPke.kgSigma K.p (D s₀)) N))) :
    WP isa (.block [.li .s4 1, .li .s6 0]) s (KRow K s₀ 0) :=
  WP.mono flagInit_ok fun _ ⟨k₁, g24, g26, m₁⟩ =>
    ⟨h.keep hp (xs := [.s6, .s4]) (W := []) k₁ (by simp [savedTop]) rfl, g26, by rw [g24]; rfl,
      by rw [m₁]; exact hr, by rw [m₁]; exact hs, fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

/-! ## `ŝ` into `dk` -/

/-- After encoding the first `j` polynomials of `ŝ`. -/
structure KS (K : KemLay) (s₀ : State) (j : Nat) (s : State) : Prop where
  env : KEnv K s₀ s
  s6 : s.gpr .s6 = BitVec.ofNat 64 j
  s4 : s.gpr .s4 = if okK K s₀ K.k then 1 else 0
  rho : bytesAt s.mem ((lay s₀ K).A 0 oSeed) 32 = ρ₀ K s₀
  ek : ∀ i' < K.k, bytesAt s.mem ((lay s₀ K).A 3 (384 * i')) 384 = encode12 (tK K s₀ i')
  slots : ∀ j' < K.k, PolyIs s.mem ((lay s₀ K).A 0 (oPoly (K.k + j'))) (sK K s₀ j')
  dk : ∀ j' < j, bytesAt s.mem ((lay s₀ K).A 4 (384 * j')) 384 = encode12 (sK K s₀ j')

/-- `sK_ok` with the sizes `sz` of the buffers. -/
abbrev SKF (K : KemLay) (sz : List Nat) : Prop := ∀ j < K.k,
    [((4 : Nat), 384 * j, (384 : Nat))].all (fun w => sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w) = true ∧
    sepAll sz (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll sz (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll sz (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll sz (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB sz (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true

theorem sK_ok {K : KemLay} (hK : K.WF) {j : Nat} (hj : j < K.k) :
    [((4 : Nat), 384 * j, (384 : Nat))].all (okW K) = true ∧
    sepAll (kSz K) (0, oSeed, 32) [(4, 384 * j, 384)] = true ∧
    (∀ i' < K.k, sepAll (kSz K) (3, 384 * i', 384) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, sepAll (kSz K) (0, oPoly (K.k + j'), 1024) [(4, 384 * j, 384)] = true) ∧
    (∀ j' < K.k, j' ≠ j → sepAll (kSz K) (4, 384 * j', 384) [(4, 384 * j, 384)] = true) ∧
    sepB (kSz K) (0, oPoly (K.k + j), 1024) (4, 384 * j, 384) = true := by
  have scr := hK.scr
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ :=
    (by decide : ∀ k < 5, SKF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega) j hj
  refine ⟨List.all_eq_true.mpr fun w hw => ?_, sepAll_scr c2 scr, fun i' hi' => sepAll_scr (c3 i' hi') scr,
    fun j' hj' => sepAll_scr (c4 j' hj') scr, fun j' hj' hne => sepAll_scr (c5 j' hj' hne) scr, sepB_scr c6 scr⟩
  have := List.all_eq_true.mp c1 w hw
  simp only [okW, Bool.and_eq_true] at this ⊢
  exact ⟨sepB_scr this.1 scr, sepB_scr this.2 scr⟩

theorem s_init {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KRow K s₀ K.k s) :
    WP isa (.block [.li .s6 0]) s (KS K s₀ 0) :=
  WP.mono (li_ok .s6 (N := 0) (by decide)) fun _ ⟨k₆, g26', m₆⟩ =>
    ⟨h.env.keep hp (xs := [.s6]) (W := []) k₆ (by simp [savedTop]) rfl, g26',
      by rw [k₆.cs .s4 (by decide) (by decide), h.s4], by rw [m₆]; exact h.rho,
      by rw [m₆]; exact h.ek, fun j' hj' => by rw [m₆]; exact h.slots j' (by omega),
      fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩

section
variable (K : KemLay) (s₀ : State) (j : Nat) (s : State)

/-- After the arguments of the encoding of `ŝ[j]`. -/
structure KS1 (s₁ : State) : Prop where
  o : Only s s₁
  a3 : s₁.gpr .a0 = (lay s₀ K).A 0 (oPoly (K.k + j))
  a4 : s₁.gpr .a1 = (lay s₀ K).A 4 (384 * j)

/-- After the encoding of `ŝ[j]`. -/
structure KS2 (s₂ : State) : Prop where
  kx : KeptX [.s6] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s₂
  s6 : s₂.gpr .s6 = BitVec.ofNat 64 j
  enc : bytesAt s₂.mem ((lay s₀ K).A 4 (384 * j)) 384 = encode12 (sK K s₀ j)

end

section
variable {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State} (h : KS K s₀ j s)
include hp hj h

theorem ks1_ok : WP isa (.block (slotAt .a0 .s6 K.k ++ atMul .a1 .s8 .s6 384)) s (KS1 K s₀ j s) := by
  have hK := hp.wf
  refine WP.mono (slotMul_ok (b := .s8) (.inr rfl) h.env.ctx.s11 h.env.s8 h.s6 (by offs) (by offs))
    fun s₁ ⟨o₁, a3, a4⟩ => ⟨o₁, ?_, a4⟩
  rw [a3, show oPoly K.k + 1024 * j = oPoly (K.k + j) by offs]

theorem ks2_ok {s₁ : State} (r : KS1 K s₀ j s s₁) : WP isa callEncode12 s₁ (KS2 K s₀ j s) := by
  have hL := lay_ok hp
  have hc₁ := h.env.ctx.only r.o
  obtain ⟨-, -, -, -, -, c_enc⟩ := sK_ok hp.wf hj
  obtain ⟨-, -, w4, -⟩ := buf_wr hp
  exact encode12L hL (i := 0) (j := 4) (o' := 384 * j) r.a3 r.a4 c_enc (mem_rd_wr hc₁.cw)
    (by rw [r.o.wr, h.env.wr]; exact w4) (by rw [r.o.mem]; exact h.slots j hj) (hc₁.alP _) fun s₂ k₂ e₂ =>
    ⟨(r.o.x _ _).trans ((k₂.x _).monoL (by simp)),
      by rw [k₂.cs .s6 (by decide), r.o.cs .s6 (by decide), h.s6], e₂⟩

theorem ks3_ok {s₂ : State} (r : KS2 K s₀ j s s₂) :
    WP isa (.block (count .s6 K.k)) s₂ fun s' => KS K s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨c_ok, c_rho, c_ek, c_slots, c_dk, -⟩ := sK_ok hK hj
  refine WP.mono (count_ok (by decide) (by omega) (by omega) r.s6) fun s' ⟨k', g', z'⟩ =>
    ⟨⟨?_, g', ?_, ?_, ?_, ?_, ?_⟩, z'⟩
  all_goals have K' : KeptX [.s6] ((lay s₀ K).RL [(4, 384 * j, 384)]) s s' :=
    r.kx.trans (k'.mono (fun _ h => absurd h List.not_mem_nil))
  · exact h.env.keep hp K' (by simp [savedTop]) c_ok
  · rw [K'.cs .s4 (by decide) (by decide), h.s4]
  · rw [← h.rho]; exact Lay.bytes_keep hL K'.frame c_rho (by decide)
  · exact fun i' hi' => (Lay.bytes_keep hL K'.frame (c_ek i' hi') (by decide)).trans (h.ek i' hi')
  · exact fun j' hj' => Lay.polyIs_keep hL K'.frame (c_slots j' hj') (h.slots j' hj')
  · intro j' hj'
    by_cases e : j' = j
    · subst e
      exact (bytesAt_frame k'.frame (fun _ h => absurd h List.not_mem_nil) (by decide)).trans r.enc
    · exact (Lay.bytes_keep hL K'.frame (c_dk j' (by omega) e) (by decide)).trans (h.dk j' (by omega))

end

theorem kgS_step {K : KemLay} {s₀ : State} (hp : Pre K s₀) {j : Nat} (hj : j < K.k) {s : State}
    (h : KS K s₀ j s) :
    WP isa K.kgSBody s fun s' => KS K s₀ (j + 1) s' ∧ (s'.gpr .t0 != 0) = decide (j + 1 ≠ K.k) :=
  WP.seq (WP.mono (ks1_ok hp hj h) fun _ r₁ => WP.seq (WP.mono (ks2_ok hp hj h r₁) fun _ r₂ => ks3_ok hp hj h r₂))

/-! ## The encapsulation key, `H(ek)` and `z` -/

section
variable (K : KemLay) (s₀ : State)

/-- `ek`. -/
abbrev EK : List Byte := VG.Proof.MlKem.KPke.ekPKE K.p (aK K s₀) (D s₀)

/-- `dk`. -/
abbrev DK : List Byte := VG.Proof.MlKem.KPke.dkPKE K.p (D s₀) ++ EK K s₀ ++ H (EK K s₀) ++ Z s₀

end

theorem ek_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.ekLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) 32 :=
  bytesAt_add _ _ (384 * K.k) 32

theorem dk_split (K : KemLay) (m : Mem) (q : Addr) :
    bytesAt m q K.dkLen = bytesAt m q (384 * K.k) ++ bytesAt m (q + BitVec.ofNat 64 (384 * K.k)) K.ekLen ++
      bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 32)) 32 ++ bytesAt m (q + BitVec.ofNat 64 (768 * K.k + 64)) 32 := by
  rw [show K.dkLen = 384 * K.k + (K.ekLen + (32 + 32)) by simp only [KemLay.dkLen, KemLay.ekLen]; omega,
    bytesAt_add _ _ (384 * K.k), bytesAt_add _ _ K.ekLen, bytesAt_add _ _ 32 32, VG.Offset.add_ofNat_add_ofNat,
    VG.Offset.add_ofNat_add_ofNat, show 384 * K.k + K.ekLen = 768 * K.k + 32 by simp only [KemLay.ekLen]; omega,
    show 768 * K.k + 32 + 32 = 768 * K.k + 64 by omega]
  simp only [List.append_assoc]

/-- What a region of `KEnv` must be apart from, with the sizes `sz` of the buffers. -/
abbrev okWz (sz : List Nat) (w : Nat × Nat × Nat) : Bool := sepB sz (0, 1288, 80) w && sepB sz (2, 0, 64) w

theorem okWz_scr {K : KemLay} {W : List (Nat × Nat × Nat)} (h : W.all (okWz (32768 :: (kSz K).tail)) = true)
    (hs : 32768 ≤ K.scratch) : W.all (okW K) = true :=
  List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp h w hw
    simp only [okWz, okW, Bool.and_eq_true] at this ⊢
    exact ⟨sepB_scr this.1 hs, sepB_scr this.2 hs⟩

/-- The separations of the copies and the hash of `tail_ok`, with the sizes `sz` of the buffers. -/
abbrev TailF (K : KemLay) (sz : List Nat) : Prop :=
  sepB sz (0, oSeed, 32) (3, 384 * K.k, 32) = true ∧ [(3, 384 * K.k, 32)].all (okWz sz) = true ∧
  (∀ i < K.k, sepAll sz (3, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepB sz (3, 0, K.ekLen) (4, 384 * K.k, K.ekLen) = true ∧ [(4, 384 * K.k, K.ekLen)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 384 * K.k, K.ekLen)] = true ∧
  (kRegs ++ [(4, 768 * K.k + 32, 32)]).all (okWz sz) = true ∧
  sepB sz (2, 32, 32) (4, 768 * K.k + 64, 32) = true ∧ [(4, 768 * K.k + 64, 32)].all (okWz sz) = true ∧
  sepAll sz (3, 0, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (3, 0, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  (∀ i < K.k, sepAll sz (4, 384 * i, 384) [(4, 768 * K.k + 64, 32)] = true ∧
    sepAll sz (4, 384 * i, 384) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
    sepAll sz (4, 384 * i, 384) [(4, 384 * K.k, K.ekLen)] = true ∧
    sepAll sz (4, 384 * i, 384) [(3, 384 * K.k, 32)] = true) ∧
  sepAll sz (4, 384 * K.k, K.ekLen) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (4, 384 * K.k, K.ekLen) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true ∧
  sepAll sz (4, 768 * K.k + 32, 32) [(4, 768 * K.k + 64, 32)] = true ∧
  sepAll sz (0, 1288, 80) (kRegs ++ [(4, 768 * K.k + 32, 32)]) = true

theorem tail_facts {K : KemLay} (hK : K.WF) : TailF K (kSz K) := by
  have s := hK.scr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    (by decide : ∀ k < 5, TailF (kOf k) (kSz (kOf k))) K.k (by have := hK.k4; omega)
  exact ⟨sepB_scr f1 s, okWz_scr f2 s, fun i hi => sepAll_scr (f3 i hi) s, sepB_scr f4 s, okWz_scr f5 s,
    sepAll_scr f6 s, okWz_scr f7 s, sepB_scr f8 s, okWz_scr f9 s, sepAll_scr f10 s, sepAll_scr f11 s,
    fun i hi => ⟨sepAll_scr (f12 i hi).1 s, sepAll_scr (f12 i hi).2.1 s, sepAll_scr (f12 i hi).2.2.1 s,
      sepAll_scr (f12 i hi).2.2.2 s⟩, sepAll_scr f13 s, sepAll_scr f14 s, sepAll_scr f15 s, sepAll_scr f16 s⟩

theorem h_ins {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s9, 0, K.ekLen⟩ : Piece)], PieceOk (lay s₀ K) kidx s false p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inl rfl)) (by simp) (by show 0 < 32768; decide)
    (by show K.ekLen < 2048; have := hK.k4; simp only [KemLay.ekLen]; omega)
    (by show 0 < K.ekLen; simp only [KemLay.ekLen]; omega) (by ldecide)

theorem h_outs {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    ∀ p ∈ [(⟨.s8, 768 * K.k + 32, 32⟩ : Piece)], PieceOk (lay s₀ K) kidx s true p := by
  have hK := hp.wf
  intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
  exact pieceK hp h (.inr (.inr (.inl rfl))) (by simp)
    (by show 768 * K.k + 32 < 32768; have := hK.k4; omega) (by show 32 < 2048; decide) (by show 0 < 32; decide)
    (by ldecide)

/-- The end: our caller's registers restored, and `a0` the flag. -/
theorem end_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = s.gpr .s4 ∧ s'.mem = s.mem ∧ s'.sp = s₀.sp := by
  obtain ⟨w0, -, -, -⟩ := buf_wr hp
  have hK := hp.wf
  refine WP.mono (topEnd_ok h.ctx.s11 hp.alS h.sav (fun o h₁ h₂ => ?_) h.cs) fun s' ⟨pr, lr, a0, m, sp, _, _⟩ =>
    ⟨pr, lr, a0, m, sp.trans h.sp⟩
  rw [h.rd, h.wr]
  have scr := hK.scr
  have hb : o + 8 ≤ (lay s₀ K).size 0 := by simp only [lay, Lay.size, List.getD_cons_zero]; omega
  exact mem_rd_wr' (Lay.covers w0 hb _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)

/-! What each step of the end keeps, for the proof of constant time. -/

section
variable {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KEnv K s₀ s)
include hp h

theorem cpRho_env : WP isa (copy .s11 oSeed .s9 (384 * K.k) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨w0, w3, -, -⟩ := buf_wr hp
  obtain ⟨f1, f2, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 0) (j := 3) (by decide) (by decide) h.ctx.s11 h.s9
    (by decide) (by show 384 * K.k < 32768; omega) (by decide) (by decide) f1
    (by rw [h.rd, h.wr]; exact mem_rd_wr w0) (by rw [h.wr]; exact w3)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f2

theorem cpEk_env : WP isa (copy .s9 0 .s8 (384 * K.k) K.ekLen) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨-, w3, w4, -⟩ := buf_wr hp
  obtain ⟨-, -, -, f4, f5, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen)
    (by decide) (by decide) h.s9 h.s8 (by decide) (by show 384 * K.k < 32768; omega)
    (by show K.ekLen < 2048; simp only [KemLay.ekLen]; omega) (by simp only [KemLay.ekLen]; omega) f4
    (by rw [h.rd, h.wr]; exact mem_rd_wr w3) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f5

theorem hashH_env :
    WP isa (hash 136 0x06 [⟨.s9, 0, K.ekLen⟩] [⟨.s8, 768 * K.k + 32, 32⟩]) s (KEnv K s₀) := by
  have hK := hp.wf
  obtain ⟨-, -, -, -, -, -, f7, -⟩ := tail_facts hK
  exact WP.mono (hash_ok (idx := kidx) VG.Proof.MlKem.rate136 (by decide) h.ctx
    (List.cons_ne_nil _ _) (h_ins hp h) (h_outs hp h) (List.pairwise_singleton _ _)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f7

theorem cpZ_env : WP isa (copy .s10 32 .s8 (768 * K.k + 64) 32) s (KEnv K s₀) := by
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨-, -, w4, w2⟩ := buf_wr hp
  obtain ⟨-, -, -, -, -, -, -, f8, f9, -⟩ := tail_facts hK
  exact WP.mono (copyL (lay_ok hp) (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    (by decide) (by decide) h.s10 h.s8 (by decide) (by show 768 * K.k + 64 < 32768; omega) (by decide)
    (by decide) f8 (by rw [h.rd, h.wr]; exact w2) (by rw [h.wr]; exact w4)) fun _ ⟨k, _⟩ =>
    h.keep hp (k.x []) (by simp) f9

end

theorem tail_ok {K : KemLay} {s₀ s : State} (hp : Pre K s₀) (h : KS K s₀ K.k s) :
    WP isa (.seq (copy .s11 oSeed .s9 (384 * K.k) 32) <| .seq (copy .s9 0 .s8 (384 * K.k) K.ekLen) <|
      .seq (hash 136 0x06 [⟨.s9, 0, K.ekLen⟩] [⟨.s8, 768 * K.k + 32, 32⟩]) <|
      .seq (copy .s10 32 .s8 (768 * K.k + 64) 32) (.block topEnd)) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.gpr .ra = s₀.gpr .ra ∧
        s'.gpr .a0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s'.mem (pEk s₀) K.ekLen = EK K s₀ ∧
        bytesAt s'.mem (pDk s₀) K.dkLen = DK K s₀ := by
  have hL := lay_ok hp
  have hK := hp.wf
  have k4 := hK.k4
  obtain ⟨w0, w3, w4, w2⟩ := buf_wr hp
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, -⟩ := tail_facts hK
  -- `ρ` into `ek`
  have h₀ := h.env
  refine WP.seq (WP.mono (copyL hL (i := 0) (j := 3) (by decide) (by decide) h₀.ctx.s11 h₀.s9
    (by decide) (by show 384 * K.k < 32768; omega) (by decide) (by decide) f1
    (by rw [h₀.rd, h₀.wr]; exact mem_rd_wr w0) (by rw [h₀.wr]; exact w3)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  have h₁ := h₀.keep hp (k₁.x []) (by simp) f2
  have ek₁ : bytesAt s₁.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ := by
    rw [ek_split, bytes_catK, VG.Offset.add_ofNat_add_ofNat, Nat.zero_add, b₁, h.rho]
    refine congrArg (· ++ _) (catK_congr fun i hi => ?_)
    rw [VG.Offset.add_ofNat_add_ofNat, Nat.zero_add]
    exact (Lay.bytes_keep hL k₁.frame (f3 i hi) (by decide)).trans (h.ek i hi)
  -- `ek` into `dk`
  refine WP.seq (WP.mono (copyL hL (i := 3) (j := 4) (so := 0) (dO := 384 * K.k) (len := K.ekLen) (by decide)
    (by decide) h₁.s9 h₁.s8 (by decide) (by show 384 * K.k < 32768; omega)
    (by show K.ekLen < 2048; simp only [KemLay.ekLen]; omega) (by simp only [KemLay.ekLen]; omega) f4
    (by rw [h₁.rd, h₁.wr]; exact mem_rd_wr w3) (by rw [h₁.wr]; exact w4)) fun s₂ ⟨k₂, b₂⟩ => ?_)
  rw [ek₁] at b₂
  have h₂ := h₁.keep hp (k₂.x []) (by simp) f5
  have ek₂ : bytesAt s₂.mem ((lay s₀ K).A 3 0) K.ekLen = EK K s₀ :=
    (Lay.bytes_keep hL k₂.frame f6 (by simp only [KemLay.ekLen]; omega)).trans ek₁
  -- `H(ek)`
  refine WP.seq (WP.mono (hash_ok (idx := kidx) VG.Proof.MlKem.rate136 (by decide) h₂.ctx
    (List.cons_ne_nil _ _) (h_ins hp h₂) (h_outs hp h₂) (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have h₃ := h₂.keep hp (k₃.x []) (by simp) f7
  have hek₃ : bytesAt s₃.mem ((lay s₀ K).A 4 (768 * K.k + 32)) 32 = H (EK K s₀) := by
    have e := o₃.1
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at e
    refine e.trans ?_
    show _ = H (EK K s₀)
    rw [VG.Proof.MlKem.H_eq, ← ek₂]; rfl
  -- `z`
  refine WP.seq (WP.mono (copyL hL (i := 2) (j := 4) (so := 32) (dO := 768 * K.k + 64) (len := 32)
    (by decide) (by decide) h₃.s10 h₃.s8 (by decide) (by show 768 * K.k + 64 < 32768; omega) (by decide) (by decide)
    f8 (by rw [h₃.rd, h₃.wr]; exact w2) (by rw [h₃.wr]; exact w4)) fun s₄ ⟨k₄, b₄⟩ => ?_)
  have h₄ := h₃.keep hp (k₄.x []) (by simp) f9
  have z₄ : bytesAt s₄.mem ((lay s₀ K).A 4 (768 * K.k + 64)) 32 = Z s₀ := by
    rw [b₄]
    have := congrArg (List.drop 32) h₃.seed
    rw [bytesAt_drop _ _ (by decide), bytesAt_drop _ _ (by decide)] at this
    rw [show (lay s₀ K).A 2 32 = (lay s₀ K).A 2 0 + BitVec.ofNat 64 32 by
      simp only [Lay.A, VG.Offset.add_ofNat_add_ofNat], this]
    simp only [Lay.A, BitVec.add_zero]; rfl
  have g24 : s₄.gpr .s4 = if okK K s₀ K.k then 1 else 0 := by
    rw [k₄.cs .s4 (by decide), k₃.cs .s4 (by decide), k₂.cs .s4 (by decide), k₁.cs .s4 (by decide), h.s4]
  refine WP.mono (end_ok hp h₄) fun s' ⟨pr, lr, a0, m', sp'⟩ => ⟨pr, sp', lr, a0.trans g24, ?_, ?_⟩
  · rw [m', show pEk s₀ = (lay s₀ K).A 3 0 from (BitVec.add_zero _).symm,
      Lay.bytes_keep hL k₄.frame f10 (by simp only [KemLay.ekLen]; omega),
      Lay.bytes_keep hL k₃.frame f11 (by simp only [KemLay.ekLen]; omega), ek₂]
  · have kd : ∀ i < K.k, bytesAt s₄.mem ((lay s₀ K).A 4 (384 * i)) 384 = bytesAt s.mem ((lay s₀ K).A 4 (384 * i)) 384 :=
      fun i hi => (Lay.bytes_keep hL k₄.frame (f12 i hi).1 (by decide)).trans
        ((Lay.bytes_keep hL k₃.frame (f12 i hi).2.1 (by decide)).trans
        ((Lay.bytes_keep hL k₂.frame (f12 i hi).2.2.1 (by decide)).trans
          (Lay.bytes_keep hL k₁.frame (f12 i hi).2.2.2 (by decide))))
    have e4 := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 384 * K.k) (l := K.ekLen) f13
      (by simp only [KemLay.ekLen]; omega)).trans ((Lay.bytes_keep hL k₃.frame f14
        (by simp only [KemLay.ekLen]; omega)).trans b₂)
    have hh := (Lay.bytes_keep hL k₄.frame (i := 4) (o := 768 * K.k + 32) (l := 32) f15 (by decide)).trans hek₃
    simp only [Lay.A] at e4 hh z₄ kd
    rw [m', show pDk s₀ = (lay s₀ K).ptr 4 from rfl, dk_split, bytes_catK, e4, hh, z₄]
    refine congrArg (· ++ _ ++ _ ++ _) (catK_congr fun i hi => ?_)
    exact (kd i hi).trans (h.dk i hi)

/-! ## The whole function -/

theorem correct {K : KemLay} {s₀ : State} (hp : Pre K s₀) :
    WP isa K.keygen s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
      s.gpr .a0 = (if okK K s₀ K.k then 1 else 0) ∧ bytesAt s.mem (pEk s₀) K.ekLen = EK K s₀ ∧
      bytesAt s.mem (pDk s₀) K.dkLen = DK K s₀ := by
  have hK := hp.wf
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, b₁⟩ => ?_)
  refine WP.seq (WP.mono (g_ok hp h₁ b₁) fun s₂ ⟨h₂, r₂, σ₂⟩ => ?_)
  refine WP.seq (WP.mono (rho_ok hp h₂ r₂ σ₂) fun s₂' ⟨h₂', r₂', σ₂'⟩ => ?_)
  refine WP.seq (WP.mono (prf_phase hp h₂' r₂' σ₂') fun s₃ ⟨h₃, r₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (rows_init hp h₃ r₃ p₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (KRow K s₀) (N := K.k) hK.k1 (fun i hi s h => kgRow_step hp hi h)
    (fun _ h => h) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (s_init hp h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (wp_loop_nz (KS K s₀) (N := K.k) hK.k1 (fun j hj s h => kgS_step hp hj h)
    (fun _ h => h) h₆) fun s₇ h₇ => ?_)
  exact tail_ok hp h₇

end VG.Proof.MlKem.RISCV64.KeyGen
