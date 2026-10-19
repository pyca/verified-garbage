module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrWin
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrWin
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# A candidate on x86-64: constant time of Miller–Rabin's exponentiation

Its loops over the words of `E` and their windows, with the invariants of
their correctness proofs (`WordInv`, `WinInv`) from the state `s₀` where
the exponentiation starts, whose header holds the public words (`EBase`);
then the three squarings after them.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of the exponentiation. -/
structure EPub where
  p : MrPub
  i : Nat
  u : Nat

/-- Where the exponentiation starts. -/
def EBase (q : EPub) (s₀ : State) : Prop :=
  KW q.p.B q.p.wr ∧ (∀ e ∈ q.p.vs q.i q.u, word s₀.mem q.p.B (8 * e.1) = e.2) ∧ s₀.wr = q.p.wr ∧
    MrDims q.p.B q.p.Z q.p.w

theorem mrS_exp (w : Nat) : ∀ j ∈ mrS, ∀ r ∈ expRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  have h : ∀ j ∈ mrS, 8 * j + 8 ≤ VG.Impl.Bignum.hdrBytes ∧ ∀ h ∈ ([(248, 8), (176, 8), (208, 8), (224, 8),
      (216, 8)] : List (Nat × Nat)), 8 * j + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * j := by
    decide
  exact fun j hj => VG.Proof.RsaKeyGen.hdr_of_shape (expRanges_shape w) (h j hj).1 (h j hj).2

theorem vs_exp' (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ [(8 * kFlag, 8)], 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 ∧ ∀ r ∈ [(8 * kFlag, 8)], 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
    decide
  exact h2 _ h1

theorem vs_exp (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ expRanges p.w, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 := by decide
  exact ⟨h2 _ h1, mrS_exp p.w _ h1⟩

/-- After `j` windows of word `k − 1`. -/
def WinL (a : EPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (W : BitVec 64) (s₀ : State), EBase a.1 s₀ ∧
    WinInv a.1.p.B a.1.p.Z a.1.p.w mi c bm b a.2 W s₀ j s ∧ c % 2 = 1 ∧ 1 < c ∧ 1 ≤ a.2 ∧
    a.2 ≤ a.1.p.w ∧ W.toNat = Proof.RsaKeyGen.mrE c / 2 ^ (64 * (a.2 - 1)) % 2 ^ 64

/-- The header in a word. -/
theorem winL_hp {a : EPub × Nat} {j : Nat} {s : State} (h : WinL a j s) :
    HP a.1.p.B a.1.p.wr (a.1.p.vs a.1.i a.1.u ++
      [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (16 - j))]) s := by
  obtain ⟨mi, c, bm, b, W, s₀, ⟨_, hh, hw, _⟩, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hI.words
    · exact hI.bits

theorem winL_winW {a : EPub × Nat} {j : Nat} {s : State} (h : WinL a j s) :
    WinW ⟨a.1.p, a.1.i, a.1.u, a.2, 16 - j⟩ s := by
  have hp := winL_hp h
  obtain ⟨mi, c, bm, b, W, s₀, ⟨hk, _, _, hd⟩, hI, hodd, hc1, -⟩ := h
  exact ⟨hk, hp, hd, mi, c, b, bm, hI.ctx, hI.tab, hodd, hc1, by rw [hI.y]; exact Nat.mod_lt _ (by omega)⟩

/-- The windows of a word leak the same in runs that agree on the public data. -/
theorem wins_ct (M : Mont) :
    RelCT isa (Two fun (a : EPub × Nat) s => 0 < 16 ∧ WinL a 0 s) (.loop (seqs (mrWin M.mm)) .ne)
      (Two fun a s => WinL a 16 s) := by
  refine two_loop (Φ := WinL) (fun _ => 16)
    (two_map (fun p => (⟨p.1.1.p, p.1.1.i, p.1.1.u, p.1.2, 16 - p.2⟩ : WPub)) (fun _ _ h => winL_winW h.2)
      (mrWin_ct M)) ?_
  rintro a j s hj ⟨mi, c, bm, b, W, s₀, hE, hI, hodd, hc1, hk, hkw, hWc⟩
  refine WP.mono (mrWinStep_ok M hE.2.2.2 hodd hc1 hk hkw hWc hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
  · simp only [eval, hz, Option.map_some, Option.some.injEq]
    by_cases h : j + 1 = 16 <;> simp [h]; omega
  · exact ⟨mi, c, bm, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩
  · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩

/-- After `j` of the `w` words. -/
def WordL (q : EPub) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (s₀ : State), EBase q s₀ ∧ ECtx s₀.mem q.p.B q.p.w c ∧
    WordInv q.p.B q.p.Z q.p.w mi c bm b s₀ j s ∧ c % 2 = 1 ∧ 1 < c

theorem wordL_hp {q : EPub} {j : Nat} {s : State} (h : WordL q j s) :
    HP q.p.B q.p.wr (q.p.vs q.i q.u ++ [(kWords, BitVec.ofNat 64 (q.p.w - j))]) s := by
  obtain ⟨mi, c, bm, b, s₀, ⟨_, hh, hw, _⟩, _, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact hI.words

theorem vs_fst1 (p : MrPub) (i u : Nat) (x : BitVec 64) : (p.vs i u ++ [(kWords, x)]).map (·.1) = mrS ++ [kWords] :=
  p.vs_fst i u _

theorem vs_fst2 (p : MrPub) (i u : Nat) (x y : BitVec 64) :
    (p.vs i u ++ [(kWords, x), (kBits, y)]).map (·.1) = mrS ++ [kWords, kBits] := p.vs_fst i u _

theorem vs_fst0 (p : MrPub) (i u : Nat) : (p.vs i u).map (·.1) = mrS := by
  simpa using p.vs_fst i u []

/-- The words of the exponentiation leak the same in runs that agree on the
public data. -/
theorem words_ct (M : Mont) :
    RelCT isa (Two fun (q : EPub) s => 0 < q.p.w ∧ WordL q 0 s)
      (.loop (seqs [
        .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
          extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
          .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
        .loop (seqs (mrWin M.mm)) .ne,
        .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne)
      (Two fun q s => WordL q q.p.w s) := by
  refine two_loop (Φ := WordL) (fun q => q.p.w) ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two fun (p : EPub × Nat) s => 0 < 16 ∧ WinL (p.1, p.1.p.w - p.2) 0 s)
      (kt_piece (fun p : EPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kWords])
        (fun p => p.1.p.vs p.1.i p.1.u ++ [(kWords, BitVec.ofNat 64 (p.1.p.w - p.2))]) [] (by decide)
        (fun p => vs_fst1 _ _ _ _)
        (fun _ _ h => ⟨let ⟨_, _, _, _, _, hE, _⟩ := h.2; hE.1, wordL_hp h.2⟩) (pins_nil _) (by taint_decide) ?_)
      (RelCT.seq ((wins_ct M).mono (fun _ _ h => two_bind (fun p _ _ h₁ h₂ => ⟨(p.1, p.1.p.w - p.2), h₁, h₂⟩) h)
        fun _ _ h => h) ?_)
    · rintro ⟨q, j⟩ s ⟨hj, mi, c, bm, b, s₀, hE, hx, hI, hodd, hc1⟩
      dsimp only at hj
      have hd := hE.2.2.2
      have hn := hI.ctx.good.scr.nowrap
      have hxs : ECtx s.mem q.p.B q.p.w c := hx.of_low hI.frm (expRanges_low _) (by
        have := aE_fits hd; have := hd.z; omega_arith)
      have hj' : j < q.p.w := hj
      refine WP.mono (wordStart_ok hd hj' hI) fun t hB => ⟨by decide, mi, c, bm, b, _, s₀, hE, hB, hodd, hc1,
        (show 1 ≤ q.p.w - j by omega), (show q.p.w - j ≤ q.p.w by omega), ?_⟩
      rw [← hxs.e]; exact word_of_wv s.mem q.p.B (slot q.p.w aE) q.p.w (show q.p.w - j - 1 < q.p.w by omega)
    · exact kt_ct (fun a : EPub × Nat => a.1.p.B) (fun a => a.1.p.wr) (mrS ++ [kWords, kBits])
        (fun a => a.1.p.vs a.1.i a.1.u ++
          [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (16 - 16))]) [] (by decide)
        (fun a => vs_fst2 _ _ _ _ _) (fun _ _ h => ⟨let ⟨_, _, _, _, _, _, hE, _⟩ := h; hE.1, winL_hp h⟩)
        (pins_nil _) (by taint_decide)
  · rintro q j s hj ⟨mi, c, bm, b, s₀, hE, hx, hI, hodd, hc1⟩
    have hd := hE.2.2.2
    have hn := hI.ctx.good.scr.nowrap
    refine WP.mono (mrWord_ok M hd (hx.of_low hI.frm (expRanges_low _) (by
      have := aE_fits hd; have := hd.z; omega_arith)) hodd hc1 hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases h : j + 1 = q.p.w <;> simp [h]; omega
    · exact ⟨mi, c, bm, b, s₀, hE, hx, hI', hodd, hc1⟩
    · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, s₀, hE, hx, hI', hodd, hc1⟩

/-- What the exponentiation needs. -/
def ExpPre (q : EPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ TabOK s.mem q.p.B q.p.w c b ∧
      ECtx s.mem q.p.B q.p.w c ∧ c % 2 = 1 ∧ 1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w = 2 ^ (64 * q.p.w) % c

/-- What each run keeps between the squarings after the windows. -/
def LastW (q : EPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧ ECtx s.mem q.p.B q.p.w c ∧
      c % 2 = 1 ∧ 1 < c ∧ wv s.mem q.p.B (slot q.p.w aY) q.p.w < c

theorem LastW.goodW {q : EPub} {s : State} (h : LastW q s) : GoodW ⟨q.p.B, q.p.Z, q.p.w⟩ s :=
  let ⟨_, _, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩

/-- `LastW` after `y := y²`. -/
theorem lastW_mm (M : Mont) {q : EPub} {s : State} (h : LastW q s) : WP isa (M.mm aY aY aY) s fun t => LastW q t := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hE, hodd, hc1, hy⟩ := h
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hc.good.scr.nowrap
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aY) (a := aY) (b := aY) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hc.n]; exact hy))
    fun t ⟨hg, hlt, _, ha', k⟩ => ?_
  have hf : Frm q.p.B [(slot q.p.w aAcc, 8 * (q.p.w + 2)), (slot q.p.w aTmp, 8 * (q.p.w + 2)),
      (slot q.p.w aY, 8 * (q.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  refine ⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) (q.p.vs_lt _ _ [] (by simp) |> fun h e he => h e (by simpa using he)) hg.rdi k.2.2,
    hd, mi, c, bm, hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl),
    hE.of_low hf ((VG.Proof.RsaKeyGen.mm_shape _ _).leD rfl rfl) (by have := aE_fits hd; have := hd.z; omega_arith), hodd, hc1, by rw [← hc.n]; exact hlt⟩

theorem mrLast_eq' (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : mrLast mul j = ([mul aY aY aY] : List (Prog isa)) ++ (eqMask aRm1 ++
    ([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
    .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
    .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))] : List (Prog isa))) := by
  simp only [mrLast, List.append_assoc]

/-- The comparison and the flag after a squaring keep `LastW`. -/
theorem lastW_tail {q : EPub} {s : State} (h : LastW q s) (j : Nat) :
    WP isa (seqs (eqMask aRm1 ++ ([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .movImm64 .rdx (sigK j),
      .alu .and .rdx (.mem (ix .rbx .r12)), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
      .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rbp (.reg .rdx), .mov .rax (.mem (hdr kFlag)),
      .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax] : List Instr))] : List (Prog isa)))) s fun t => LastW q t := by
  obtain ⟨hk, hp, hd, mi, c, bm, hc, hE, hodd, hc1, hy⟩ := h
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hEZ := aE_fits hd
  refine wp_seqs_append (by simp [eqMask]) (by simp) (WP.mono (eqMask_ok hg hd.z (by have := hd.w4; omega_arith) hw'
    (j := aRm1) (by decide) hd.x) fun s₁ ⟨_, hm₁, k₁⟩ => ?_)
  have hg₁ : Good s₁ q.p.B q.p.Z q.p.w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  simp only [seqs]
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg₁ hd.z hw' (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₂ ⟨hbx, hm₂, k₂⟩ => ?_
  have hs₂ := hg₁.scr.congr k₂.2.2
  have hdi₂ : s₂.gpr .rdi = q.p.B := (k₂.gpr (by decide)).trans hg₁.rdi
  have hl : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off q.p.B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot q.p.w 8 hi; have := hd.z; omega_arith)
  have hst : InRegions s₂.wr (off q.p.B (8 * kFlag)) 8 :=
    hs₂.st (by have := hdr_lt_slot q.p.w 8 (show kFlag < 32 by decide); have := hd.z; omega_arith)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r12] (Q := fun t => ∃ v : BitVec 64,
      t.mem = s₂.mem.writeW (off q.p.B (8 * kFlag)) v) (by
    xrun [State.ea, hdr, ix, hdi₂, hdrOff, hl kFlag (by decide), hl sW (by decide), hst, hm₂, hg₁.hdr.hw, hbx,
      addr0 rfl rfl, hs₂.ld (d := slot q.p.w aE + 8 * q.p.w) (by omega_arith)]
    exact ⟨_, rfl⟩) rfl) fun t ⟨⟨v, hm⟩, k⟩ => ?_
  have hf : Frm q.p.B [(8 * kFlag, 8)] s.mem t.mem := by
    rw [hm, hm₂, hm₁]; exact Frm.of_outside (writeW_outside _ _ _ (by unfold kFlag kPlen sFn; omega_arith)) (by simp)
  have hgt : Good t q.p.B q.p.Z q.p.w mi := ⟨hs₂.congr k.2.2, (k.gpr (by decide)).trans hdi₂,
    Hdr.of_frm hg.hdr hf ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl)⟩
  refine ⟨hk, ⟨hgt.rdi, (k.2.2.trans (k₂.2.2.trans k₁.2.2)).trans hp.wr,
    hdr_frm hf (vs_exp' _ _ _) hp.hdr⟩, hd, mi, c, bm,
    hc.of_frm hd hf hgt.scr hgt.rdi ((VG.Proof.RsaKeyGen.hdr_shape 0 _).geD rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl),
    hE.of_frm hf ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW1 rfl rfl) (by omega_arith), hodd, hc1, ?_⟩
  rw [hf.wv_eq (d := slot q.p.w aY) (k := q.p.w) ((VG.Proof.RsaKeyGen.hdr_shape _ _).apartW rfl rfl)
    (by have := slot_le (w := q.p.w) (show aY < 8 by decide); have := hd.z; omega_arith)]
  exact hy

/-- A squaring after the windows leaks the same in runs that agree on the
public data. -/
theorem mrLast_ct (M : Mont) {j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    RelCT isa (Two LastW) (seqs (mrLast M.mm j)) (Two LastW) := by
  rw [mrLast_eq']
  refine RelCT.seqs_app (by simp) (by simp [eqMask]) (RelCT.seq (R := Two LastW) ?_ ?_)
  · simp only [seqs]
    exact two_post (two_map (fun q : EPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws)) (fun _ _ h => h.goodW)
      (M.ct (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) fun q s h => lastW_mm M h
  · rcases hj with rfl | rfl | rfl
    all_goals
      exact kt_piece (fun q : EPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) fun _ _ h => lastW_tail h _

theorem wordL_lastW {q : EPub} {s : State} (h : WordL q q.p.w s) : LastW q s := by
  obtain ⟨mi, c, bm, b, s₀, ⟨hk, hh, hw, hd⟩, hx, hI, hodd, hc1⟩ := h
  have hn := hI.ctx.good.scr.nowrap
  exact ⟨hk, ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => hdr_frm hI.frm (vs_exp _ _ _) hh e he⟩, hd, mi, c,
    bm, hI.ctx, hx.of_low hI.frm (expRanges_low _) (by have := aE_fits hd; have := hd.z; omega_arith), hodd, hc1,
    by rw [hI.y]; exact Nat.mod_lt _ (by omega_arith)⟩

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem mrExpLoop_ct (M : Mont) : RelCT isa (Two ExpPre) (seqs (mrExpLoop M.mm)) fun _ _ => True := by
  rw [mrExpLoop_eq]
  refine RelCT.seqs_app (by simp) (by simp [mrLast]) (RelCT.seq (R := Two LastW) ?_ ?_)
  · simp only [seqs]
    refine RelCT.seq (kt_piece (fun q : EPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_)
      ((words_ct M).mono (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => wordL_lastW h) h)
    rintro q s ⟨hk, hp, hd, mi, c, bm, b, hc, hT, hE, hodd, hc1, hY⟩
    exact WP.mono (expStart_ok hd hc hT hY) fun t hI =>
      ⟨by have := hd.w4; omega, mi, c, bm, b, s, ⟨hk, hp.hdr, hp.wr, hd⟩, hE, hI, hodd, hc1⟩
  · refine RelCT.seqs_app (by simp [mrLast]) (by simp [mrLast]) (RelCT.seq (mrLast_ct M (Or.inl rfl)) ?_)
    refine RelCT.seqs_app (by simp [mrLast]) (by simp [mrLast]) (RelCT.seq (mrLast_ct M (Or.inr (Or.inl rfl))) ?_)
    exact (mrLast_ct M (Or.inr (Or.inr rfl))).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.RsaKeyGen.X86_64
