import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTBase

/-!
# A candidate on AArch64: constant time of Miller–Rabin's loop

The loop over the witnesses, from what its correctness proof keeps
(`MrSt`), for runs that agree on the public data `q : FPub` and so on the
shape of the test's result `q.sch.mr`, which fixes how many iterations
remain from each offset (`itersOf`) and whether each witness passes
(`passS`): `millerRabin_ct`.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)
open VG.Proof.RsaKeyGen (shapeOf itersOf passS checksW)

/-- The working space of the public data. -/
abbrev FPub.L (q : FPub) : WsP := ⟨q.B, q.Z, q.w⟩

/-- The offset of iteration `j`'s witness. -/
abbrev uOf (q : FPub) (j : Nat) : Nat := 8 * q.w + 8 * q.w * j

/-- The iterations of the loop. -/
abbrev Nq (q : FPub) : Nat := itersOf (8 * q.w) q.rl q.sch.mr (8 * q.w)

/-- What the end needs of the state before Miller–Rabin. -/
def EndW (q : FPub) (s : State) : Prop :=
  word s.mem q.B (8 * kOut) = q.op ∧ word s.mem q.B (8 * kUsedP) = q.up ∧
    word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) ∧ OutUp s q.B q.Z q.op q.up (8 * q.w)

/-- At the head of iteration `j`. -/
def LoopI (q : FPub) (j : Nat) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 64 ∧ q.rl < 2 ^ 64 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte))
    (uni : Nat), MrSt q.B q.Z q.w c (checksW q.w) q.rP r s₀ res (j + 1) uni (uOf q j) s ∧ shapeOf res = q.sch.mr ∧
    r.length = q.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧ EndW q s₀ ∧
    itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = Nq q - j

/-- `MrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem MrSt.congr {B : Addr} {Z w c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : MrSt B Z w c ch rp r s₀ res i uni used s) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : MrSt B Z w c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨⟨bm, hc.of_frm (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k
    (fun h => by have := hrs _ h; simp [mmRegs] at this) (by simp) (by simp) (by simp) (by simp) (by simp)⟩,
    by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4, by rw [hm]; exact h5,
    h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

theorem loopI_ws {q : FPub} {j : Nat} {s : State} (h : LoopI q j s) : Ws s q.B q.Z q.w := by
  obtain ⟨-, -, -, c, r, s₀, res, uni, hI, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  exact hc.ws

/-- Before the branch on `rand`'s length. -/
def AvI (p : FPub × Nat) (s : State) : Prop :=
  LoopI p.1 p.2 s ∧ isa.eval (.zero .x .x5) s = some (decide (p.1.rl < uOf p.1 p.2 + 8 * p.1.w))

theorem checksW_lt (w : Nat) : checksW w < 2 ^ 62 := by
  unfold checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide

/-- What a round needs, at the head of an iteration with the witness's octets. -/
theorem avI_r0 {p : FPub × Nat} {s : State} (h : AvI p s) (hb : isa.eval (.zero .x .x5) s = some false) :
    R0 ⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ s := by
  obtain ⟨⟨h4, h64, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  rw [hcf] at hb
  simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega)
  have hun := hI.unii
  refine ⟨h4, h64, c, bm, r, p.2 + 1, uni, checksW p.1.w, hc, hI.r2, hc1, hsh, hI.rand, hI.kused, hI.len, hI.src,
    by rw [hrlen]; exact hb, hI.ki, hI.kuni, hI.chk, by omega, by omega, checksW_lt _, ?_⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def LoopEnd (q : FPub) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 64 ∧ ∃ (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
    MrEnd q.B q.Z q.w c r s₀ res s ∧ shapeOf res = q.sch.mr ∧ r.length = q.rl ∧ EndW q s₀

/-- The registers of the round's branch and of `kStat`'s test. -/
theorem kStat0_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [movi .x3 0, sth .x3 kStat]) s fun t => Ws t B Z w := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  exact h.congr' (Frm.of_outside (by rw [hm]; exact writeW_outside _ _ _ (by simp only [kStat, sFn]; omega))
    (List.mem_singleton_self (8 * kStat, 8))) (by msb_mut) k (by decide)

/-- An iteration of the loop. -/
theorem mrIterB_ct (M : Mont) : RelCT isa (Two fun (p : FPub × Nat) s => p.2 < Nq p.1 ∧ LoopI p.1 p.2 s)
    (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRound M.mm)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) fun _ _ => True := by
  have pw : ∀ {Φ : FPub × Nat → State → Prop}, (∀ p s, Φ p s → Ws s p.1.B p.1.Z p.1.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun p : FPub × Nat => p.1.B) (fun p : FPub × Nat => p.1.Z) (fun p : FPub × Nat => p.1.w) h
  refine RelCT.seq (two_piece (Ψ := AvI) [.x0] (pw fun _ _ h => loopI_ws h.2) (by taint_decide) ?_)
    (RelCT.seq (R := Two fun (p : FPub × Nat) t => Ws t p.1.B p.1.Z p.1.w)
      (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
        (two_piece [.x0] (pw fun _ _ h => loopI_ws h.1.1) (by taint_decide) fun _ _ h => kStat0_ok (loopI_ws h.1.1))
        (two_post (two_map (fun p : FPub × Nat =>
            (⟨p.1.L, p.1.rP, uOf p.1 p.2, passS (8 * p.1.w) p.1.rl p.1.sch.mr (uOf p.1 p.2)⟩ : RP))
          (fun _ _ h => avI_r0 h.1 h.2) (mrRound_ct M)) ?_))
      (two_taint [.x0] (pw fun _ _ h => h) (by taint_decide)))
  · rintro ⟨q, j⟩ s ⟨hj, h⟩
    have h' := h
    obtain ⟨h4, h64, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩ := h'
    obtain ⟨bm, hc⟩ := hI.ctx
    exact WP.mono (iterHead_ok (r := r) hc.ws h64 (by rw [hrlen]; exact hrl) hI.ul hI.len hI.rlen hI.kused)
      fun t ⟨hz, hm, k⟩ => ⟨⟨h4, h64, hrl, c, r, s₀, res, uni, hI.congr hm k (by decide), hS, hrlen, hc1,
        hsh, hE, hit⟩, by rw [hz, hrlen]⟩
  · intro p s h
    have hr := avI_r0 h.1 h.2
    obtain ⟨h4, h64, c, bm, r, i, uni, ch, hc, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, hi, huni, hch, -⟩ := hr
    exact WP.mono (mrRound_ok M h4 h64 hc hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC hi huni hch)
      fun t ⟨hc', _⟩ => hc'.ws

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data. -/
theorem mrLoop_ct (M : Mont) : RelCT isa (Two fun (q : FPub) s => 0 < Nq q ∧ LoopI q 0 s)
    (.loop (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRound M.mm)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) (.zero .x .x3)) (Two LoopEnd) := by
  refine two_loop (Φ := LoopI) Nq (mrIterB_ct M) ?_
  rintro q j s hj ⟨h4, h64, hrl, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, hE, hit⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  refine WP.mono (mrIter_ok M h4 h64 hc1 hsh (by omega) (checksW_lt _) s hI) fun t ht => ?_
  rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
  · have h1 : itersOf (8 * q.w) q.rl q.sch.mr (uOf q j) = 1 := by
      rcases hres : res with _ | ⟨b, rest⟩
      · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega) (by rw [← hrlen]; exact hnone hres)
      · rw [← hS, hres]
        exact VG.Proof.RsaKeyGen.iters_end_some (by omega) (by rw [← hrlen]; exact hsome b rest hres)
    refine ⟨by rw [he]; exact congrArg some (decide_eq_false (by omega)).symm, fun h => absurd h (by omega),
      fun _ => ⟨h4, h64, c, r, s₀, res, hend, hS, hrlen, hE⟩⟩
  · have hu' : uOf q (j + 1) = uOf q j + 8 * q.w := by simp only [uOf]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega) (by omega) hI'.ul
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (uOf q j + 8 * q.w) r) = res := hI'.rest
    rw [show uOf q j + 8 * q.w - 8 * q.w = uOf q j by omega, hr', hS, hrlen] at hc
    refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega)).symm, fun _ => ?_,
      fun h => absurd h (by omega)⟩
    rw [← hu'] at hI'
    exact ⟨h4, h64, hrl, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, hE, by rw [hu']; omega⟩

/-- What `millerRabin` needs (`millerRabin_ok`'s hypotheses), for the public
data. -/
def MrPre (q : FPub) (s : State) : Prop :=
  4 ≤ q.w ∧ q.w ≤ 64 ∧ q.rl < 2 ^ 64 ∧ ∃ (c bm : Nat) (r : List Byte), MrCtx s q.B q.Z q.w c bm ∧
    wv s.mem q.B (slot q.w aR2) q.w = 2 ^ (64 * q.w) * 2 ^ (64 * q.w) % c ∧ 1 < c ∧
    VG.Proof.RsaKeyGen.PrimeShape (64 * q.w) c ∧ word s.mem q.B (8 * kRand) = q.rP ∧
    word s.mem q.B (8 * kRandLen) = BitVec.ofNat 64 r.length ∧ r.length = q.rl ∧
    word s.mem q.B (8 * kChecks) = BitVec.ofNat 64 (checksW q.w) ∧ Src s q.B q.Z q.rP r ∧
    word s.mem q.B (8 * kUsed) = BitVec.ofNat 64 (8 * q.w) ∧ 8 * q.w ≤ r.length ∧
    shapeOf (mrRest c (checksW q.w) r 1 0 (8 * q.w)) = q.sch.mr ∧ EndW q s

/-- `millerRabin` leaks the same in runs that agree on the public data. -/
theorem millerRabin_ct (M : Mont) : RelCT isa (Two MrPre) (seqs (millerRabin M.mm)) (Two LoopEnd) := by
  unfold millerRabin
  refine RelCT.seq (two_piece [.x0] (pins_ws' (fun q : FPub => q.B) (fun q : FPub => q.Z) (fun q : FPub => q.w)
    fun _ _ ⟨_, _, _, _, _, _, hc, _⟩ => hc.ws) (by taint_decide) ?_) (mrLoop_ct M)
  rintro q s ⟨h4, h64, hrl, c, bm, r, hc, hr2, hc1, hsh, hR, hRL, hrlen, hC, hsrc, hU, hu1, hS, hE⟩
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hN : 1 ≤ Nq q := by
    have := (VG.Proof.RsaKeyGen.iters_cont (L := 8 * q.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
      (m := (Spec.Rsa.splitTwos (c - 1)).2) (ch := checksW q.w) (i := 1) (uni := 0) (Or.inl (by decide)) hwb
      (by omega) (Nat.le_refl _) hu1).2
    have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c (checksW q.w) (Spec.Rsa.splitTwos (c - 1)).1
        (Spec.Rsa.splitTwos (c - 1)).2) (1, 0) (List.drop (8 * q.w) r) = mrRest c (checksW q.w) r 1 0 (8 * q.w) :=
      rfl
    rwa [hr', hS, hrlen] at this
  have hK : word s.mem q.B (8 * kLen) = BitVec.ofNat 64 (8 * q.w) := hE.2.2.1
  exact WP.mono (mrInit_ok hc hr2 hR hK hRL hC hsrc hU (Nat.le_refl _) hu1) fun t hI =>
    ⟨hN, h4, h64, hrl, c, r, s, _, 0, by simpa [uOf] using hI, hS, hrlen, hc1, hsh, hE, by simp [uOf]⟩

end VG.Proof.RsaKeyGen.AArch64
