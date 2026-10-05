import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrExp

/-!
# A candidate on x86-64: constant time of a round of Miller–Rabin

`mrRound`, from what `mrRound_ok` needs (`R0`), for runs that agree on the
public data, the witness passing or not among them (`RPub.pass`): its
witness, the witness in Montgomery form, the exponentiation, and the end,
which branches on the flag. Between the pieces, what each run keeps is
little (the header, `Good`); the facts that make the next pieces run come
from the correctness lemmas of whole stretches (`roundPre_ok`,
`roundMid_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- An entry of `MrPub.vs`. -/
macro "mem_vs" : tactic => `(tactic| first
  | (simp only [MrPub.vs, List.mem_cons, true_or]; done)
  | simp only [MrPub.vs, List.mem_cons, true_or, or_true])

/-- The header words of `MrH`, from `HP`. -/
theorem HP.mrh {p : MrPub} {i u : Nat} {ex : List (Nat × BitVec 64)} {s : State}
    (h : HP p.B p.wr (p.vs i u ++ ex) s) : MrH p i u s.mem :=
  ⟨h.hdr (kOut, p.op) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kLen, BitVec.ofNat 64 (8 * p.w)) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kUsedP, p.up) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kRand, p.rP) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kRandLen, BitVec.ofNat 64 p.rl) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kChecks, BitVec.ofNat 64 p.ch) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kI, BitVec.ofNat 64 i) (List.mem_append_left _ (by mem_vs)),
    h.hdr (kUsed, BitVec.ofNat 64 u) (List.mem_append_left _ (by mem_vs))⟩

theorem hp0 {p : MrPub} {i u : Nat} {s : State} (h : HP p.B p.wr (p.vs i u) s) :
    HP p.B p.wr (p.vs i u ++ []) s := by rw [List.append_nil]; exact h

/-- `HP` after changes to the arrays and the header words `ks` outside `MrH`,
and `kUsed` to `u'`. -/
theorem hp_used {p : MrPub} {i u u' : Nat} {s t : State} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (h : HP p.B p.wr (p.vs i u) s) (hg : Good t p.B p.Z p.w mi) (hw : t.wr = s.wr)
    (hf : Frm p.B rs s.mem t.mem)
    (hd : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k)
    (hu : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u') : HP p.B p.wr (p.vs i u') t := by
  have hm := (hp0 h).mrh
  have e : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], word t.mem p.B (8 * k) = word s.mem p.B (8 * k) :=
    fun k hk => hf.word_eq (hd k hk) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have := mr_hp (ex := []) hg (hw.trans h.wr) ⟨(e _ (by simp)).trans hm.out, (e _ (by simp)).trans hm.len,
    (e _ (by simp)).trans hm.usedP, (e _ (by simp)).trans hm.rand, (e _ (by simp)).trans hm.rlen,
    (e _ (by simp)).trans hm.chk, (e _ (by simp)).trans hm.ki, hu⟩ (by simp)
  rwa [List.append_nil] at this

/-- The public data of a round: the witnesses so far plus one, the octets
read, and whether the witness passes. -/
structure RPub where
  p : MrPub
  i : Nat
  u : Nat
  pass : Bool

/-- What a round needs (`mrRound_ok`'s hypotheses). -/
def R0 (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i q.u) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm : Nat) (r : List Byte) (uni : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
      wv s.mem q.p.B (slot q.p.w aR2) q.p.w = 2 ^ (64 * q.p.w) * 2 ^ (64 * q.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * q.p.w) c ∧ Src s q.p.B q.p.Z q.p.rP r ∧ r.length = q.p.rl ∧
      q.u + 8 * q.p.w ≤ r.length ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧ q.i < 2 ^ 61 ∧
      uni < 2 ^ 61 ∧ q.p.ch < 2 ^ 62 ∧ passOf c q.p.w q.u r = q.pass

/-- After the witness's octets. -/
def W1 (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s

theorem witRanges_mrh (w : Nat) :
    ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ witRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [witRanges]; rng_disj

/-- The witness leaks the same in runs that agree on the public data. -/
theorem mrWitness_ct : RelCT isa (Two R0) (seqs mrWitness) (Two fun q s => W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
      wv s.mem q.p.B (slot q.p.w aR2) q.p.w < wv s.mem q.p.B (slot q.p.w aN) q.p.w) := by
  rw [mrWitness_eq]
  refine two_post (RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two W1) ?_ ?_)) ?_
  · simp only [seqs]
    refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, -, -, -, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    refine WP.mono (witLoad_ok hc.good hd.z (by omega) (by have := hd.w64; omega) hm.rand hm.used hm.len
      (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega))
      fun t ⟨_, hu, hf, hg, k⟩ => ⟨hk, hp_used hp hg k.2.2 hf (by rng_disj) hu⟩
  · exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)
  · rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hR2, hc1, hsh, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
    refine WP.mono (mrWitness_ok hd hc hsh.1 hb hm.rand hm.used hm.len (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega))
      fun t ⟨hc', _, _, hu, hf, k⟩ => ⟨⟨hk, hp_used hp hc'.good k.2.2 hf (witRanges_mrh _) hu⟩, hd, mi, c, _, hc', ?_⟩
    rw [hc'.n, hf.wv_eq (d := slot q.p.w aR2) (k := q.p.w) (by simp only [witRanges]; rng_disj)
      (by have := hc.good.scr.nowrap; have := slot_le (w := q.p.w) (show aR2 < 8 by decide); have := hd.z; omega), hR2]
    exact Nat.mod_lt _ (by omega)

/-- Between the copies. -/
def W3 (q : RPub) (s : State) : Prop := W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧ ∃ mi, Good s q.p.B q.p.Z q.p.w mi

theorem preRanges_mrh (w : Nat) :
    ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ preRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [preRanges, witRanges, List.cons_append, List.nil_append]; rng_disj

/-- The round up to the exponentiation leaks the same in runs that agree on
the public data. -/
theorem roundPre_ct (M : Mont) : RelCT isa (Two R0) (seqs (mrWitness ++ [M.mm aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords]))
    (Two fun (q : RPub) s => ExpPre ⟨q.p, q.i, q.u + 8 * q.p.w⟩ s) := by
  refine two_post (RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq (mrWitness_ct) ?_)) ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two W3) (two_post (two_map (fun q : RPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws))
      (fun _ _ h => let ⟨_, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩)
      (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) ?_) (RelCT.assoc (RelCT.seq (R := Two W3) ?_ ?_))
    · rintro q s ⟨⟨hk, hp⟩, hd, mi, c, bm, hc, hlt⟩
      have hw' : q.p.w < 2 ^ 31 := by have := hd.w64; omega
      refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega) hw' (o := aXm) (a := aX) (b := aR2) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv hlt)
        fun t ⟨hg, _, _, ha, k⟩ => ⟨⟨hk, hp.frm (Frm.of_arrays ha (rs := [(slot q.p.w aAcc, 8 * (q.p.w + 2)),
          (slot q.p.w aTmp, 8 * (q.p.w + 2)), (slot q.p.w aXm, 8 * (q.p.w + 2))]) (by simp)) (by rng_le)
          (q.p.vs_lt _ _ [] (by simp) |> fun h e he => h e (by simpa using he)) hg.rdi k.2.2⟩, hd, mi, hg⟩
    · refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
        (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1) (pins_nil _) (by taint_decide) ?_
      rintro q s ⟨⟨hk, hp⟩, hd, mi, hg⟩
      have hw' : q.p.w < 2 ^ 31 := by have := hd.w64; omega
      have hn := hg.scr.nowrap
      refine WP.mono (copyToExt_ok hg hd.z (by have := hd.w4; omega) hw' (a := aXm) (d := aB) (by decide) (by decide)
        (by have := hd.x; unfold slot aB aRm1 at *; omega)) fun t ⟨_, ho, k⟩ => ?_
      have hf : Frm q.p.B [(slot q.p.w aB, 8 * (q.p.w + 2))] s.mem t.mem :=
        Frm.of_outside (ho.mono (o' := slot q.p.w aB) (n' := 8 * (q.p.w + 2)) (Nat.le_refl _) (by omega)) (by simp)
      exact ⟨⟨hk, hp.frm hf (by rng_le) (q.p.vs_lt _ _ [] (by simp) |> fun h e he => h e (by simpa using he))
        ((k.gpr (by decide)).trans hg.rdi) k.2.2⟩, hd, mi, hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
        Hdr.of_frm hg.hdr hf (by rng_le)⟩
    · exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
        (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1) (pins_nil _) (by taint_decide)
  · rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hR2, hc1, hsh, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
    refine WP.mono (roundPre_ok M hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen)
      fun t ⟨hc', hy, _, _, hu, hf, k⟩ => ⟨hk, hp_used hp hc'.good k.2.2 hf (preRanges_mrh _) hu, hd, mi, c, _, hc',
        hsh.1, hc1, hy⟩

/-- After the exponentiation: the flag, the witness passing or not. -/
def Rmid (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (uni : Nat) (u : Bool), Good s q.p.B q.p.Z q.p.w mi ∧
      word s.mem q.p.B (8 * kFlag) = mask q.pass ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word s.mem q.p.B (8 * kU) = mask u ∧ uni < 2 ^ 61

theorem midRanges_mrh (w : Nat) : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI],
    ∀ r ∈ preRanges w ++ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj

/-- The round up to its flag leaks the same in runs that agree on the public
data. -/
theorem roundMid_ct (M : Mont) : RelCT isa (Two R0) (seqs ((mrWitness ++ [M.mm aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords]) ++
      mrExpLoop M.mm)) (Two Rmid) := by
  refine two_post (RelCT.seqs_app (by simp [mrWitness]) (by simp [mrExpLoop]) (RelCT.seq (roundPre_ct M)
    ((mrExpLoop_ct M).mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ => ⟨⟨q.p, q.i, q.u + 8 * q.p.w⟩, h₁, h₂⟩) h)
      fun _ _ _ => trivial))) ?_
  rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hR2, hc1, hsh, hsrc, -, hlen, hun, -, huni, -, hpass⟩
  have hm := (hp0 hp).mrh
  refine WP.mono (roundMid_ok M hd hc hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen hm.ki hun hm.chk)
    fun t ⟨hc', hfl, _, hN, _, hU, hu, _, hf, k⟩ => ⟨hk, hp_used hp hc'.good k.2.2 hf (midRanges_mrh _) hu, hd, mi,
      uni, _, hc'.good, by rw [hfl, hpass], hN, hU, huni⟩

/-- The test of the flag. -/
theorem flagTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {f : Bool} (hF : word s.mem B (8 * kFlag) = mask f) :
    WP isa (.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!f) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kFlag)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega)
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.zf = some (!f) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hF, BitVec.and_self]
    cases f <;> decide) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- The end of the round leaks the same in runs that agree on the public
data, the witness passing or not among them. -/
theorem roundTail_ct : RelCT isa (Two Rmid) (seqs [
      .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two fun (q : RPub) s => (KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s) ∧
      s.zf = some (!q.pass))
    (kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_)
    (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
      (kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1.1) (pins_nil _) (by taint_decide))
      (kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
        (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1.1) (pins_nil _) (by taint_decide)))
  rintro q s ⟨hk, hp, hd, mi, uni, u, hg, hF, -⟩
  exact WP.mono (flagTest_ok hg hd.z hF) fun t ⟨hz, hm, k⟩ =>
    ⟨⟨hk, ⟨(k.gpr (by decide)).trans hp.rdi, k.2.2.trans hp.wr, fun e he => by rw [hm]; exact hp.hdr e he⟩⟩, hz⟩

/-- A round leaks the same in runs that agree on the public data, the
witness passing or not among them. -/
theorem mrRound_ct (M : Mont) : RelCT isa (Two R0) (seqs (mrRound M.mm)) fun _ _ => True := by
  rw [mrRound_eq, ← List.append_assoc]
  exact RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq (roundMid_ct M) roundTail_ct)

end VG.Proof.RsaKeyGen.X86_64
