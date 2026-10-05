import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrBit

/-!
# A candidate on x86-64: constant time of Miller–Rabin's exponentiation

Its loops over the words of `c` and their bits, with the invariants of
their correctness proofs (`WordInv`, `BitInv`) from the state `s₀` where
the exponentiation starts, whose header holds the public words (`EBase`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
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
  simp only [mrS, expRanges, bitRanges, List.cons_append, List.nil_append]
  rng_disj

theorem vs_exp (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ expRanges p.w, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 := by decide
  exact ⟨h2 _ h1, mrS_exp p.w _ h1⟩

/-- The bits of a word. -/
abbrev nbOf (k : Nat) : Nat := if k = 1 then 63 else 64

/-- After `j` bits of word `k − 1`. -/
def BitL (a : EPub × Nat) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c b : Nat) (W : BitVec 64) (s₀ : State), EBase a.1 s₀ ∧
    BitInv a.1.p.B a.1.p.Z a.1.p.w mi c b a.2 (nbOf a.2) W s₀ j s ∧ c % 2 = 1 ∧ 1 < c ∧ 1 ≤ a.2 ∧
    a.2 ≤ a.1.p.w ∧ ∀ u < 64, W.toNat.testBit u = c.testBit (64 * (a.2 - 1) + u)

/-- The header in a word. -/
theorem bitL_hp {a : EPub × Nat} {j : Nat} {s : State} (h : BitL a j s) :
    HP a.1.p.B a.1.p.wr (a.1.p.vs a.1.i a.1.u ++
      [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (nbOf a.2 - j))]) s := by
  obtain ⟨mi, c, b, W, s₀, ⟨_, hh, hw, _⟩, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hI.words
    · exact hI.bits

theorem bitL_bitW {a : EPub × Nat} {j : Nat} {s : State} (h : BitL a j s) :
    BitW ⟨a.1.p, a.1.i, a.1.u, a.2, nbOf a.2 - j⟩ s := by
  have hp := bitL_hp h
  obtain ⟨mi, c, b, W, s₀, ⟨hk, _, _, hd⟩, hI, hodd, hc1, -⟩ := h
  exact ⟨hk, hp, hd, mi, c, b, hI.ctx, hodd, hc1, by rw [hI.y]; exact Nat.mod_lt _ (by omega)⟩

/-- The bits of a word leak the same in runs that agree on the public data. -/
theorem bits_ct (M : Mont) :
    RelCT isa (Two fun (a : EPub × Nat) s => 0 < nbOf a.2 ∧ BitL a 0 s) (.loop (seqs (mrExpBit M.mm)) .ne)
      (Two fun a s => BitL a (nbOf a.2) s) := by
  refine two_loop (Φ := BitL) (fun a => nbOf a.2)
    (two_map (fun p => (⟨p.1.1.p, p.1.1.i, p.1.1.u, p.1.2, nbOf p.1.2 - p.2⟩ : BPub)) (fun _ _ h => bitL_bitW h.2)
      (mrExpBit_ct M)) ?_
  rintro a j s hj ⟨mi, c, b, W, s₀, hE, hI, hodd, hc1, hk, hkw, hWc⟩
  refine WP.mono (mrBitStep_ok M hE.2.2.2 hodd hc1 hk hkw rfl hWc hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
  · simp only [eval, hz, Option.map_some, Option.some.injEq]
    by_cases h : j + 1 = nbOf a.2 <;> simp [h]; omega
  · exact ⟨mi, c, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩
  · rename_i e; rw [← e]; exact ⟨mi, c, b, W, s₀, hE, hI', hodd, hc1, hk, hkw, hWc⟩

/-- After `j` of the `w` words. -/
def WordL (q : EPub) (j : Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c b : Nat) (s₀ : State), EBase q s₀ ∧ WordInv q.p.B q.p.Z q.p.w mi c b s₀ j s ∧ c % 2 = 1 ∧
    1 < c

theorem wordL_hp {q : EPub} {j : Nat} {s : State} (h : WordL q j s) :
    HP q.p.B q.p.wr (q.p.vs q.i q.u ++ [(kWords, BitVec.ofNat 64 (q.p.w - j))]) s := by
  obtain ⟨mi, c, b, s₀, ⟨_, hh, hw, _⟩, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_exp _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; exact hI.words

theorem vs_fst1 (p : MrPub) (i u : Nat) (x : BitVec 64) : (p.vs i u ++ [(kWords, x)]).map (·.1) = mrS ++ [kWords] :=
  p.vs_fst i u _

theorem vs_fst2 (p : MrPub) (i u : Nat) (x y : BitVec 64) :
    (p.vs i u ++ [(kWords, x), (kBits, y)]).map (·.1) = mrS ++ [kWords, kBits] := p.vs_fst i u _

/-- The words of the exponentiation leak the same in runs that agree on the
public data. -/
theorem words_ct (M : Mont) :
    RelCT isa (Two fun (q : EPub) s => 0 < q.p.w ∧ WordL q 0 s)
      (.loop (seqs [
        .block [.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax,
          .mov .rdx (.mem (hdr (sArr aN))), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
          .mov32 .rcx (.imm 64), .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.imm 0), .store (hdr kBits) .rcx],
        .loop (seqs (mrExpBit M.mm)) .ne,
        .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne)
      (Two fun q s => WordL q q.p.w s) := by
  refine two_loop (Φ := WordL) (fun q => q.p.w) ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two fun (p : EPub × Nat) s => 0 < nbOf (p.1.p.w - p.2) ∧ BitL (p.1, p.1.p.w - p.2) 0 s)
      (kt_piece (fun p : EPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kWords])
        (fun p => p.1.p.vs p.1.i p.1.u ++ [(kWords, BitVec.ofNat 64 (p.1.p.w - p.2))]) [] (by decide)
        (fun p => vs_fst1 _ _ _ _)
        (fun _ _ h => ⟨let ⟨_, _, _, _, hE, _⟩ := h.2; hE.1, wordL_hp h.2⟩) (pins_nil _) (by taint_decide) ?_)
      (RelCT.seq ((bits_ct M).mono (fun _ _ h => two_bind (fun p _ _ h₁ h₂ => ⟨(p.1, p.1.p.w - p.2), h₁, h₂⟩) h)
        fun _ _ h => h) ?_)
    · rintro ⟨q, j⟩ s ⟨hj, mi, c, b, s₀, hE, hI, hodd, hc1⟩
      dsimp only at hj
      refine WP.mono (wordStart_ok hE.2.2.2 hj hI) fun t ⟨hB, hWc⟩ =>
        ⟨by simp only [nbOf]; split <;> omega, mi, c, b, _, s₀, hE, hB, hodd, hc1, by dsimp only; omega,
          by dsimp only; omega, hWc⟩
    · exact kt_ct (fun a : EPub × Nat => a.1.p.B) (fun a => a.1.p.wr) (mrS ++ [kWords, kBits])
        (fun a => a.1.p.vs a.1.i a.1.u ++
          [(kWords, BitVec.ofNat 64 (a.2 - 1)), (kBits, BitVec.ofNat 64 (nbOf a.2 - nbOf a.2))]) [] (by decide)
        (fun a => vs_fst2 _ _ _ _ _) (fun _ _ h => ⟨let ⟨_, _, _, _, _, hE, _⟩ := h; hE.1, bitL_hp h⟩)
        (pins_nil _) (by taint_decide)
  · rintro q j s hj ⟨mi, c, b, s₀, hE, hI, hodd, hc1⟩
    refine WP.mono (mrWord_ok M hE.2.2.2 hodd hc1 hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases h : j + 1 = q.p.w <;> simp [h]; omega
    · exact ⟨mi, c, b, s₀, hE, hI', hodd, hc1⟩
    · rename_i e; rw [← e]; exact ⟨mi, c, b, s₀, hE, hI', hodd, hc1⟩

/-- What the exponentiation needs. -/
def ExpPre (q : EPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c (b * 2 ^ (64 * q.p.w) % c) ∧ c % 2 = 1 ∧ 1 < c ∧
      wv s.mem q.p.B (slot q.p.w aY) q.p.w = 2 ^ (64 * q.p.w) % c

theorem vs_fst0 (p : MrPub) (i u : Nat) : (p.vs i u).map (·.1) = mrS := by
  simpa using p.vs_fst i u []

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem mrExpLoop_ct (M : Mont) :
    RelCT isa (Two ExpPre) (seqs (mrExpLoop M.mm)) (Two fun q s => WordL q q.p.w s) := by
  unfold mrExpLoop
  simp only [seqs]
  refine RelCT.seq (kt_piece (fun q : EPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
    (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_) (words_ct M)
  rintro q s ⟨hk, hp, hd, mi, c, b, hc, hodd, hc1, hY⟩
  exact WP.mono (expStart_ok hd hc hc1 hY) fun t hI =>
    ⟨by have := hd.w4; omega, mi, c, b, s, ⟨hk, hp.hdr, hp.wr, hd⟩, hI, hodd, hc1⟩

end VG.Proof.RsaKeyGen.X86_64
