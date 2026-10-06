import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrBit

/-!
# A candidate on AArch64: constant time of Miller–Rabin's exponentiation

`mrExpLoop`, for runs that agree on the working space (`mrExpLoop_ct`): its
loops run `w` words and 64 bits a word (63 of the last), counts that
correctness pins (`mrWord_ok`, `mrBitStep_ok`); the start of each word loads
`kWords` and `c`'s base, which are pinned before the word's load
(`wordHead_ct`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

theorem eval_cnt (r : Reg) {t : State} {j c : Nat} (hj : j < c) (h : (t.gpr r).toNat ≠ 0 ↔ j + 1 ≠ c) :
    isa.eval (.nonzero .x r) t = some (decide (j + 1 < c)) := by
  rw [eval_nonzero]
  congr 1
  by_cases hc : j + 1 < c
  · have hne : t.gpr r ≠ 0 := fun e => by
      rw [e] at h; exact absurd (h.mpr (by omega)) (by simp)
    rw [bne_iff_ne.mpr hne, decide_eq_true hc]
  · have he : t.gpr r = 0 := BitVec.eq_of_toNat_eq (by
      by_contra hne; exact (h.mp (by simpa using hne)) (by omega))
    rw [he, decide_eq_false hc]; rfl

/-- Before the exponentiation (`mrExpLoop_ok`'s hypotheses). -/
def E0 (L : WsP) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 64 ∧ ∃ c b, MrCtx s L.B L.Z L.w c (b * 2 ^ (64 * L.w) % c) ∧ c % 2 = 1 ∧ 1 < c ∧
    wv s.mem L.B (slot L.w aY) L.w = 2 ^ (64 * L.w) % c

/-- After `j` words. -/
def WI (L : WsP) (j : Nat) (s : State) : Prop :=
  4 ≤ L.w ∧ L.w ≤ 64 ∧ ∃ c b s₀, WordInv L.B L.Z L.w c b s₀ j s ∧ c % 2 = 1 ∧ 1 < c

/-- The bits of word `w − 1 − j`. -/
abbrev nbOf (w j : Nat) : Nat := if w - j = 1 then 63 else 64

/-- After `i` bits of word `w − 1 − j`. -/
def BI (p : WsP × Nat) (i : Nat) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 64 ∧ p.2 < p.1.w ∧ ∃ c b s₀ W,
    BitInv p.1.B p.1.Z p.1.w c b (p.1.w - p.2) (nbOf p.1.w p.2) W s₀ i s ∧
    (∀ u < 64, W.toNat.testBit u = c.testBit (64 * (p.1.w - p.2 - 1) + u)) ∧ c % 2 = 1 ∧ 1 < c

/-- The registers pinned before a word's load. -/
def whVal (p : WsP × Nat) : Reg → BitVec 64
  | .x0 => p.1.B
  | .x3 => BitVec.ofNat 64 (p.1.w - p.2 - 1)
  | _ => off p.1.B (slot p.1.w aN)

/-- The start of a word, up to `c`'s base. -/
theorem wordPre_ok {p : WsP × Nat} {s : State} (h : p.2 < p.1.w ∧ WI p.1 p.2 s) :
    WP isa (.block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN)]) s
      fun t => ∀ r ∈ [Reg.x0, .x3, .x4], t.gpr r = whVal p r := by
  obtain ⟨hj, h4, h64, c, b, s₀, hI, -⟩ := h
  have hw := hI.ctx.ws
  have hs := hw.scr
  have hn := hs.nowrap
  have h256 := hw.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.1.B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hst : ∀ i < 32, InRegions s.wr (off p.1.B (8 * i)) 8 := fun i hi => hs.st (by omega)
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (p.1.w - p.2 - 1) ∧
      t.gpr .x4 = off p.1.B (slot p.1.w aN)) (by
    brun [hw.x0, hdr_enc (show kWords < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
      hl kWords (by decide), hl (sArr aN) (by decide), hst kWords (by decide), hI.words,
      ofNat64_pred (show 1 ≤ p.1.w - p.2 by omega) (by omega),
      fun X => (hdrStore_hdr s.mem p.1.B X (show kWords < 32 by decide) (show sArr aN < 32 by decide)
        (by decide)).trans (hw.harr aN (by decide))]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h3, h4⟩, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr .x0 (by decide)).trans hw.x0
  · exact h3
  · exact h4

theorem wordHead_ct : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < p.1.w ∧ WI p.1 p.2 s)
    (.block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
      .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
      .csel .x .x6 .x6 .x7, sth .x6 kBits]) (Two fun p s => 0 < nbOf p.1.w p.2 ∧ BI p 0 s) :=
  blk_pin [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN)]
    [.lsl .x .x5 .x3 3, .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1,
      .subs .x .x8 .x3 .x4, .csel .x .x6 .x6 .x7, sth .x6 kBits] [.x0] [.x0, .x3, .x4] whVal
    (pins_ws' (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ ⟨_, _, _, _, _, _, hI, _⟩ => hI.ctx.ws) (by taint_decide) (fun _ _ h => wordPre_ok h)
    (by taint_decide) fun p s ⟨hj, h4, h64, c, b, s₀, hI, hodd, hc1⟩ =>
      WP.mono (wordStart_ok hj hI) fun t ⟨hB, hWc⟩ => ⟨by unfold nbOf; split <;> decide,
        h4, h64, hj, c, b, s₀, _, hB, hWc, hodd, hc1⟩

/-- The bits of a word. -/
theorem wordBits_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => 0 < nbOf p.1.w p.2 ∧ BI p 0 s)
    (.loop (seqs (mrExpBit M.mm)) (.nonzero .x .x3)) (Two fun p s => BI p (nbOf p.1.w p.2) s) := by
  refine two_loop (Φ := BI) (fun p => nbOf p.1.w p.2) (two_map (fun q : (WsP × Nat) × Nat => q.1.1)
    (fun _ _ ⟨_, h4, h64, _, c, b, s₀, W, hI, _, hodd, hc1⟩ => ⟨h4, h64, c, b, _, hI.ctx, hodd, hc1, hI.y⟩)
    (mrExpBit_ct M)) ?_
  rintro p i s hi ⟨h4, h64, hj, c, b, s₀, W, hI, hWc, hodd, hc1⟩
  exact WP.mono (mrBitStep_ok M h4 h64 hodd hc1 (by omega) (by omega) rfl hWc hi hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hi hz, fun _ => ⟨h4, h64, hj, c, b, s₀, W, hI', hWc, hodd, hc1⟩,
      fun e => e ▸ ⟨h4, h64, hj, c, b, s₀, W, hI', hWc, hodd, hc1⟩⟩

/-- One word. -/
theorem word_ct (M : Mont) : RelCT isa (Two fun (p : WsP × Nat) s => p.2 < p.1.w ∧ WI p.1 p.2 s)
    (seqs [
      .block [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, ldh .x4 (sArr aN), .lsl .x .x5 .x3 3,
        .add .x .x4 .x4 .x5, ld .x5 .x4, sth .x5 kV, movi .x6 64, movi .x7 63, movi .x4 1, .subs .x .x8 .x3 .x4,
        .csel .x .x6 .x6 .x7, sth .x6 kBits],
      .loop (seqs (mrExpBit M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) fun _ _ => True :=
  RelCT.seq wordHead_ct (RelCT.seq (wordBits_ct M) (two_taint [.x0]
    (pins_ws' (fun p : WsP × Nat => p.1.B) (fun p => p.1.Z) (fun p => p.1.w)
      fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => hI.ctx.ws) (by taint_decide)))

/-- The exponentiation leaks the same in runs that agree on the working space. -/
theorem mrExpLoop_ct (M : Mont) : RelCT isa (Two E0) (seqs (mrExpLoop M.mm)) fun _ _ => True := by
  unfold mrExpLoop
  refine RelCT.seq (two_piece (Ψ := fun L s => 0 < L.w ∧ WI L 0 s) [.x0]
    (pins_ws' (fun L : WsP => L.B) (fun L : WsP => L.Z) (fun L : WsP => L.w)
      fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.ws) (by taint_decide)
    fun L s ⟨h4, h64, c, b, hc, hodd, hc1, hY⟩ => WP.mono (expStart_ok hc hc1 hY) fun t hI =>
      ⟨by omega, h4, h64, c, b, s, hI, hodd, hc1⟩) ?_
  refine (two_loop (Φ := WI) (Ψ := fun _ _ => True) (fun L => L.w) (word_ct M) ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  rintro L j s hj ⟨h4, h64, c, b, s₀, hI, hodd, hc1⟩
  exact WP.mono (mrWord_ok M h4 h64 hodd hc1 hj hI) fun t ⟨hI', hz⟩ =>
    ⟨eval_cnt .x3 hj hz, fun _ => ⟨h4, h64, c, b, s₀, hI', hodd, hc1⟩, fun _ => trivial⟩

end VG.Proof.RsaKeyGen.AArch64
