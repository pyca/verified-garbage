import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMrWit

/-!
# A candidate on AArch64: constant time of a round of Miller–Rabin

`mrRound`, from what `mrRound_ok` needs (`R0`), for runs that agree on the
working space, `rand`, the octets read and whether the witness passes
(`RP`): the witness (`mrWitness_ct`), its Montgomery form and `y := 1`, the
exponentiation (`mrExpLoop_ct`), whose preconditions come from
`roundPre_ok`, and the end, which branches on the flag `roundMid_ok` fixes.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY)

/-- The public data of a round: the working space, `rand`, the octets read
and whether the witness passes. -/
structure RP where
  L : WsP
  rP : Addr
  u : Nat
  pass : Bool

/-- What a round needs (`mrRound_ok`'s hypotheses). -/
def R0 (p : RP) (s : State) : Prop :=
  4 ≤ p.L.w ∧ p.L.w ≤ 64 ∧ ∃ (c bm : Nat) (r : List Byte) (i uni ch : Nat), MrCtx s p.L.B p.L.Z p.L.w c bm ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) * 2 ^ (64 * p.L.w) % c ∧ 1 < c ∧
    VG.Proof.RsaKeyGen.PrimeShape (64 * p.L.w) c ∧ word s.mem p.L.B (8 * kRand) = p.rP ∧
    word s.mem p.L.B (8 * kUsed) = BitVec.ofNat 64 p.u ∧ word s.mem p.L.B (8 * kLen) = BitVec.ofNat 64 (8 * p.L.w) ∧
    Src s p.L.B p.L.Z p.rP r ∧ p.u + 8 * p.L.w ≤ r.length ∧ word s.mem p.L.B (8 * kI) = BitVec.ofNat 64 i ∧
    word s.mem p.L.B (8 * kUni) = BitVec.ofNat 64 uni ∧ word s.mem p.L.B (8 * kChecks) = BitVec.ofNat 64 ch ∧
    i < 2 ^ 61 ∧ uni < 2 ^ 61 ∧ ch < 2 ^ 62 ∧ passOf c p.L.w p.u r = p.pass

theorem r0_wa {p : RP} {s : State} (h : R0 p s) : WA ⟨p.L, p.rP, p.u⟩ s := by
  obtain ⟨-, -, c, bm, r, i, uni, ch, hc, -, -, -, hR, hU, hK, hsrc, hlen, -⟩ := h
  exact ⟨hc.ws, hR, hU, hK, _, Src.seg hsrc hlen, by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega⟩

/-- After the witness: `c`, `-c⁻¹` and `R² mod c`. -/
def P1 (p : RP) (s : State) : Prop :=
  4 ≤ p.L.w ∧ p.L.w ≤ 64 ∧ ∃ c bm, MrCtx s p.L.B p.L.Z p.L.w c bm ∧ wv s.mem p.L.B (slot p.L.w aR2) p.L.w < c

theorem witP1_ct : RelCT isa (Two R0) (seqs mrWitness) (Two P1) := by
  refine two_post (two_map (fun p : RP => (⟨p.L, p.rP, p.u⟩ : WPub)) (fun _ _ h => r0_wa h) mrWitness_ct) ?_
  rintro p s ⟨h4, h64, c, bm, r, i, uni, ch, hc, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, -⟩
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sR2 : slot p.L.w aR2 + 8 * (p.L.w + 2) ≤ p.L.Z := by
    have := slot_lt (w := p.L.w) (show aR2 < 16 by decide); omega
  refine WP.mono (mrWitness_ok hc h4 h64 hsh.1 hb hR hU hK (Src.seg hsrc hlen) (by
      simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega))
    fun t ⟨hc', _, _, _, hf, _⟩ => ⟨h4, h64, c, bm, hc', ?_⟩
  rw [hf.wv_eq (d := slot p.L.w aR2) (k := p.L.w) (by rd_disj) (by omega), hR2]
  exact Nat.mod_lt _ (by omega)

theorem preMul_ct (M : Mont) : RelCT isa (Two P1) (M.mm aXm aX aR2) (Two fun (p : RP) t => Ws t p.L.B p.L.Z p.L.w) :=
  two_post (two_map (fun p : RP => p.L) (fun _ _ ⟨_, _, _, _, hc, _⟩ => ⟨_, hc.good⟩)
    (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) fun p s ⟨h4, h64, c, bm, hc, hlt⟩ => by
    have hg := hc.good
    exact WP.mono (M.mm_ok hg.1 hg.2 (by omega) (by omega) (o := aXm) (a := aX) (b := aR2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hc.n]; exact hlt))
      fun t ⟨_, _, _, ha, k⟩ => hc.ws.congrA ha k (by decide)

theorem copyA_wsct {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two fun (p : RP) t => Ws t p.L.B p.L.Z p.L.w) (copyA o a)
      (Two fun (p : RP) t => Ws t p.L.B p.L.Z p.L.w) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .x16 ++ base o .x17))) copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  refine ws_ct (fun p : RP => p.L.B) (fun p : RP => p.L.Z) (fun p : RP => p.L.w) (fun _ _ h => h) ht
    fun p s h => ?_
  rw [← e]
  have hn := h.scr.nowrap
  have so := h.sl ho
  exact WP.mono (copyA_ok h ho ha hoa) fun t ⟨_, o', _, _, k⟩ =>
    h.congr' (Frm.of_outside (o'.mono (o' := slot p.L.w o) (n' := 8 * (p.L.w + 2)) (Nat.le_refl _) (by omega))
      (List.mem_singleton_self (slot p.L.w o, 8 * (p.L.w + 2)))) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k (by decide)

/-- The round up to the exponentiation. -/
theorem roundPre_ct (M : Mont) : RelCT isa (Two R0) (seqs (mrWitness ++ [M.mm aXm aX aR2, copyA aB aXm,
    copyA aY aR1])) (Two fun (p : RP) t => E0 p.L t) := by
  refine two_post (ct_app' (by simp [mrWitness]) (by simp) witP1_ct (RelCT.seq (preMul_ct M)
    (RelCT.seq (copyA_wsct (by decide) (by decide) (by decide) (by taint_decide))
      ((copyA_wsct (by decide) (by decide) (by decide) (by taint_decide)).mono (fun _ _ h => h)
        fun _ _ _ => trivial)))) ?_
  rintro p s ⟨h4, h64, c, bm, r, i, uni, ch, hc, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, -⟩
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  exact WP.mono (roundPre_ok M h4 h64 hc hR2 hsh.1 hc1 hb hR hU hK hsrc hlen)
    fun t ⟨hc', hy, _⟩ => ⟨h4, h64, c, _, hc', hsh.1, hc1, hy⟩

/-- After the exponentiation: the flag, the witness passing or not. -/
def Rmid (p : RP) (s : State) : Prop := Ws s p.L.B p.L.Z p.L.w ∧ word s.mem p.L.B (8 * kFlag) = mask p.pass

theorem roundMid_ct (M : Mont) : RelCT isa (Two R0) (seqs ((mrWitness ++ [M.mm aXm aX aR2, copyA aB aXm,
    copyA aY aR1]) ++ mrExpLoop M.mm)) (Two Rmid) := by
  refine two_post (ct_app' (by simp [mrWitness]) (by simp [mrExpLoop]) (roundPre_ct M)
    (two_map (fun p : RP => p.L) (fun _ _ h => h) (mrExpLoop_ct M))) ?_
  rintro p s ⟨h4, h64, c, bm, r, i, uni, ch, hc, hR2, hc1, hsh, hR, hU, hK, hsrc, hlen, hI, hN, hC, -, -, -, hpass⟩
  exact WP.mono (roundMid_ok M h4 h64 hc hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun t ⟨hc', hfl, _⟩ => ⟨hc'.ws, by rw [hfl, hpass]⟩

theorem mask_beq (b : Bool) : (mask b == 0) = !b := by cases b <;> decide

/-- The end of a round. -/
theorem roundTail_ct : RelCT isa (Two Rmid) (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
        (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
          ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
          movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
          .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])]) fun _ _ => True := by
  have pw : ∀ {Φ : RP → State → Prop}, (∀ p s, Φ p s → Ws s p.L.B p.L.Z p.L.w) → Pins Φ [.x0] :=
    fun h => pins_ws' (fun p : RP => p.L.B) (fun p : RP => p.L.Z) (fun p : RP => p.L.w) h
  refine RelCT.seq (two_piece (Ψ := fun p t => Ws t p.L.B p.L.Z p.L.w ∧
      isa.eval (.zero .x .x3) t = some (!p.pass)) [.x0] (pw fun _ _ h => h.1) (by taint_decide)
    fun p s ⟨hw, hF⟩ => ?_) (two_ite (fun _ _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide))
      (two_taint [.x0] (pw fun _ _ h => h.1.1) (by taint_decide)))
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask p.pass ∧ t.mem = s.mem) (by
    brun [hw.x0, hdr_enc (show kFlag < 32 by decide), hw.scr.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
      hF]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · exact hw.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)
  · rw [eval_zero, h3, mask_beq]

/-- A round leaks the same in runs that agree on the public data, the
witness passing or not among them. -/
theorem mrRound_ct (M : Mont) : RelCT isa (Two R0) (seqs (mrRound M.mm)) fun _ _ => True := by
  rw [mrRound_eq, ← List.append_assoc]
  exact ct_app' (by simp [mrWitness]) (by simp) (roundMid_ct M) roundTail_ct

end VG.Proof.RsaKeyGen.AArch64
