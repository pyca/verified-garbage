module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrExp
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrExp
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.CrtExp
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- An entry of `MrPub.vs`. -/
tactic_template "mem_vs" : tactic => `(tactic| plain_simp_names first
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
      ECtx s.mem q.p.B q.p.w c ∧
      wv s.mem q.p.B (slot q.p.w aR2) q.p.w = 2 ^ (64 * q.p.w) * 2 ^ (64 * q.p.w) % c ∧ 1 < c ∧
      VG.Proof.RsaKeyGen.PrimeShape (64 * q.p.w) c ∧ Src s q.p.B q.p.Z q.p.rP r ∧ r.length = q.p.rl ∧
      q.u + 8 * q.p.w ≤ r.length ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧ q.i < 2 ^ 61 ∧
      uni < 2 ^ 61 ∧ q.p.ch < 2 ^ 62 ∧ passOf c q.p.w q.u r = q.pass

/-- After the witness's octets. -/
def W1 (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s

theorem midRanges_mrh (w : Nat) : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI],
    ∀ r ∈ preRanges w ++ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have h : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], 8 * k + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(200, 8), (240, 8), (208, 8), (224, 8)] ++ [(248, 8), (176, 8), (208, 8), (224, 8), (216, 8)] :
        List (Nat × Nat)), 8 * k + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * k := by
    decide
  exact fun k hk => VG.Proof.RsaKeyGen.hdr_of_shape
    (VG.Proof.RsaKeyGen.shape_append (preRanges_shape w) (expRanges_shape w)) (h k hk).1 (h k hk).2

theorem witRanges_mrh (w : Nat) :
    ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ witRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k :=
  fun k hk r hr => midRanges_mrh w k hk r
    (List.mem_append_left _ (by unfold preRanges; exact List.mem_append_left _ (List.mem_append_left _ hr)))

/-- After the witness: what its Montgomery form needs. -/
def W2 (q : RPub) (s : State) : Prop :=
  W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧ ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
    wv s.mem q.p.B (slot q.p.w aR2) q.p.w = 2 ^ (64 * q.p.w) * 2 ^ (64 * q.p.w) % c ∧ c % 2 = 1 ∧ 1 < c

/-- The witness leaks the same in runs that agree on the public data. -/
theorem mrWitness_ct : RelCT isa (Two R0) (seqs mrWitness) (Two W2) := by
  rw [mrWitness_eq]
  refine two_post (RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two W1) ?_ ?_)) ?_
  · simp only [seqs]
    refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i q.u) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, -, -, -, -, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    refine WP.mono (witLoad_ok hc.good hd.z (by omega_arith) (by have := hd.w128; omega_arith) hm.rand hm.used hm.len
      (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_arith))
      fun t ⟨_, hu, hf, hg, k⟩ => ⟨hk, hp_used hp hg k.2.2 hf (by rng_disj) hu⟩
  · exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) [] (by decide)
      (fun q => vs_fst0 _ _ _) (fun _ _ h => h) (pins_nil _) (by taint_decide)
  · rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, -, hR2, hc1, hsh, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
    refine WP.mono (mrWitness_ok hd hc hsh.1 hb hm.rand hm.used hm.len (VG.Proof.RsaKeyGen.X86_64.Src.seg hsrc hlen) (by
        simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_arith))
      fun t ⟨hc', _, _, hu, hf, k⟩ => ⟨⟨hk, hp_used hp hc'.good k.2.2 hf (witRanges_mrh _) hu⟩, hd, mi, c, _, hc', ?_,
        hsh.1, hc1⟩
    rw [hf.wv_eq (d := slot q.p.w aR2) (k := q.p.w) (by simp only [witRanges]; rng_disj)
      (by have := hc.good.scr.nowrap; have := slot_le (w := q.p.w) (show aR2 < 8 by decide); have := hd.z; omega_arith), hR2]

/-- After the witness's Montgomery form. -/
def W3 (q : RPub) (s : State) : Prop :=
  W1 q s ∧ MrDims q.p.B q.p.Z q.p.w ∧ ∃ (mi : BitVec 64) (c bm b : Nat), MrCtx s q.p.B q.p.Z q.p.w mi c bm ∧
    wv s.mem q.p.B (slot q.p.w aXm) q.p.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * q.p.w) % c ∧ c % 2 = 1 ∧ 1 < c

theorem preRanges_mrh (w : Nat) :
    ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ preRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k :=
  fun k hk r hr => midRanges_mrh w k hk r (List.mem_append_left _ hr)

/-- The table's public header words: the entry pointer and the count. -/
abbrev RPub.tvs (q : RPub) (j : Nat) : List (Nat × BitVec 64) :=
  q.p.vs q.i (q.u + 8 * q.p.w) ++ [(kV, off q.p.B (slot q.p.w (8 + (j + 2)))), (kBits, BitVec.ofNat 64 (14 - j))]

theorem RPub.tvs_fst (q : RPub) (j : Nat) : (q.tvs j).map (·.1) = mrS ++ [kV, kBits] := q.p.vs_fst _ _ _

/-- Within the table's loop: the header, and what a multiplication `y := y T_1`
needs. -/
def TLW (p : RPub × Nat) (s : State) : Prop :=
  KW p.1.p.B p.1.p.wr ∧ HP p.1.p.B p.1.p.wr (p.1.tvs p.2) s ∧ MrDims p.1.p.B p.1.p.Z p.1.p.w ∧ p.2 < 14 ∧
    ∃ (mi : BitVec 64) (c bm : Nat), MrCtx s p.1.p.B p.1.p.Z p.1.p.w mi c bm ∧
      wv s.mem p.1.p.B (slot p.1.p.w aXm) p.1.p.w < c

theorem tvs_lt (q : RPub) (j : Nat) : ∀ e ∈ q.tvs j, e.1 < 32 :=
  q.p.vs_lt _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; decide)

/-- `y := y T_1` keeps `TLW`. -/
theorem tlw_mm (M : Mont) {p : RPub × Nat} {s : State} (h : TLW p s) : WP isa (M.mm aY aY aXm) s (TLW p) := by
  obtain ⟨hk, hp, hd, hj, mi, c, bm, hc, hx⟩ := h
  have hw' : p.1.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
  refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aY) (a := aY) (b := aXm) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hc.n]; exact hx))
    fun t ⟨hg, _, _, ha', k⟩ => ?_
  have hf : Frm p.1.p.B [(slot p.1.p.w aAcc, 8 * (p.1.p.w + 2)), (slot p.1.p.w aTmp, 8 * (p.1.p.w + 2)),
      (slot p.1.p.w aY, 8 * (p.1.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
  refine ⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) (tvs_lt _ _) hg.rdi k.2.2, hd, hj, mi, c, bm,
    hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl), ?_⟩
  rw [hf.wv_eq (d := slot p.1.p.w aXm) (k := p.1.p.w) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl)
    (by have := hc.good.scr.nowrap; have := slot_le (w := p.1.p.w) (show aXm < 8 by decide); have := hd.z; omega_arith)]
  exact hx

/-- The copy of `y` into entry `j + 2`, at `kV`. -/
theorem tabCopy_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm j : Nat} (hd : MrDims B Z w)
    (hc : MrCtx s B Z w mi c bm) (hj : j < 14) (hV : word s.mem B (8 * kV) = off B (slot w (8 + (j + 2)))) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))],
      copyWords]) s fun t => MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aXm) w = wv s.mem B (slot w aXm) w ∧ Frm B [(slot w 8, tabBytes w)] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hn := hg.scr.nowrap
  have hZ := hd.z
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hE := ent_in_tab w (e := j + 2) (by omega)
  have hte := tab_end w
  have haE := aE_fits hd
  have hY8 := slot_le (w := w) (show aY < 8 by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aY) ∧ t.gpr .rbx = off B (slot w (8 + (j + 2))) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aY) (by decide), hl kV (by decide), hg.hdr.hw,
      hg.hdr.harr aY (by decide), hV]) rfl) fun s₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (copyB_ok (hg.scr.congr k₁.2.2) hsi hbx h12 (by have := hd.w4; omega) hw' (by omega)
    (by omega) (Or.inr (by omega))) fun t ⟨_, ho, k⟩ => ?_
  rw [hm₁] at ho
  have hf : Frm B [(slot w 8, tabBytes w)] s.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w 8) (n' := tabBytes w) hE.1 (by omega)) (by simp)
  have hdi : t.gpr .rdi = B := (k.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have h8 : 256 ≤ slot w 8 := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega
  have hgt : Good t B Z w mi := ⟨hg.scr.congr (k.2.2.trans k₁.2.2), hdi, Hdr.of_frm hg.hdr hf (by simp; omega)⟩
  have hN8 := slot_le (w := w) (show aN < 8 by decide)
  have hX8 := slot_le (w := w) (show aXm < 8 by decide)
  have hR1 := slot_mono w (show aE ≤ aR1 by decide)
  have hRm := slot_mono w (show aE ≤ aRm1 by decide)
  have h1s := slot_succ w aR1
  have h1m : slot w (aR1 + 1) = slot w aRm1 := rfl
  have hx' := hd.x
  have hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  have h10 : slot w 8 + 2 * (8 * (w + 2)) ≤ slot w (8 + (j + 2)) := by
    rw [show 8 + (j + 2) = 8 + (2 + j) by omega, slot_add_mul, Nat.add_mul]; omega
  have lo : ∀ {d : Nat}, d + 8 * w ≤ slot w 8 →
      ∀ r ∈ [(slot w 8, tabBytes w)], d + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd' r hr; simp only [List.mem_singleton] at hr; subst hr; exact Or.inl hd'
  have hi : ∀ {d : Nat}, slot w aE ≤ d → ∀ r ∈ [(slot w 8, tabBytes w)], d + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd' r hr; simp only [List.mem_singleton] at hr; subst hr; right; dsimp only; omega
  refine ⟨⟨hgt, ?_, ?_, ?_, ?_, ?_⟩, ?_, hf, (k₁.trans k).mono (by decide)⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by
      have := lo (d := slot w aN) (by omega) r hr; have := hd.w4; omega) (by omega)]
    exact hc.inv
  · rw [hf.wv_eq (lo (by omega)) (by omega)]; exact hc.n
  · rw [ho.wv (Or.inl (by omega)) (by omega)]; exact hc.b
  · rw [hf.wv_eq (hi hR1) (by omega)]; exact hc.r1
  · rw [hf.wv_eq (hi hRm) (by omega)]; exact hc.rm1
  · exact hf.wv_eq (lo (by omega)) (by omega)

/-- The copy of `y` into the entry keeps `TLW`. -/
theorem tlw_copy {p : RPub × Nat} {s : State} (h : TLW p s) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))],
      copyWords]) s (TLW p) := by
  obtain ⟨hk, hp, hd, hj, mi, c, bm, hc, hx⟩ := h
  have hmem : (kV, off p.1.p.B (slot p.1.p.w (8 + (p.2 + 2)))) ∈ p.1.tvs p.2 := by
    unfold RPub.tvs; exact List.mem_append_right _ List.mem_cons_self
  have hV := hp.hdr _ hmem
  dsimp only at hV
  have h8 := hdr_lt_slot p.1.p.w 8 (show 31 < 32 by decide)
  refine WP.mono (tabCopy_ok hd hc hj hV) fun t ⟨hct, hxt, hf, k⟩ => ⟨hk, hp.frm hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega) (tvs_lt _ _) hct.good.rdi k.2.2, hd, hj, mi, c,
    bm, hct, by rw [hxt]; exact hx⟩

/-- At iteration `j` of the table's loop, from `s₀` where it starts. -/
def TL (p : RPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (c bm b : Nat) (s₀ : State), KW p.1.p.B p.1.p.wr ∧
    (∀ e ∈ p.1.p.vs p.1.i (p.1.u + 8 * p.1.p.w), word s₀.mem p.1.p.B (8 * e.1) = e.2) ∧ s₀.wr = p.1.p.wr ∧
    MrDims p.1.p.B p.1.p.Z p.1.p.w ∧ TabI p.1.p.B p.1.p.Z p.1.p.w mi c bm b s₀ p.2 s ∧ c % 2 = 1 ∧ 1 < c

theorem mrS_tab (w : Nat) : ∀ j ∈ mrS, ∀ r ∈ tabRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  have h : ∀ j ∈ mrS, 8 * j + 8 ≤ VG.Impl.Bignum.hdrBytes ∧
      ∀ h ∈ ([(208, 8), (224, 8)] : List (Nat × Nat)), 8 * j + 8 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * j := by
    decide
  exact fun j hj => VG.Proof.RsaKeyGen.hdr_of_shape (tabRanges_shape w) (h j hj).1 (h j hj).2

theorem vs_tab (p : MrPub) (i u : Nat) :
    ∀ e ∈ p.vs i u, e.1 < 32 ∧ ∀ r ∈ tabRanges p.w, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1 := fun e he => by
  have h1 : e.1 ∈ mrS := by
    have := List.mem_map_of_mem (f := (·.1)) he
    rwa [show (p.vs i u).map (·.1) = mrS by simp only [MrPub.vs, mrS, List.map_cons, List.map_nil]] at this
  have h2 : ∀ j ∈ mrS, j < 32 := by decide
  exact ⟨h2 _ h1, mrS_tab p.w _ h1⟩

theorem tl_hp {p : RPub × Nat} {s : State} (h : TL p s) : HP p.1.p.B p.1.p.wr (p.1.tvs p.2) s := by
  obtain ⟨mi, c, bm, b, s₀, -, hh, hw, -, hI, -⟩ := h
  refine ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hdr_frm hI.frm (vs_tab _ _ _) hh e he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hI.v
    · exact hI.bits

theorem tl_hp0 {p : RPub × Nat} {s : State} (h : TL p s) :
    HP p.1.p.B p.1.p.wr (p.1.p.vs p.1.i (p.1.u + 8 * p.1.p.w)) s := by
  obtain ⟨mi, c, bm, b, s₀, -, hh, hw, -, hI, -⟩ := h
  exact ⟨hI.ctx.good.rdi, hI.keep.2.2.trans hw, fun e he => hdr_frm hI.frm (vs_tab _ _ _) hh e he⟩

theorem tl_tlw {p : RPub × Nat} {s : State} (h : TL p s) (hj : p.2 < 14) : TLW p s := by
  have hp := tl_hp h
  obtain ⟨mi, c, bm, b, s₀, hk, -, -, hd, hI, -, hc1⟩ := h
  exact ⟨hk, hp, hd, hj, mi, c, bm, hI.ctx, by rw [hI.xm]; exact Nat.mod_lt _ (by omega_arith)⟩

/-- The table's loop leaks the same in runs that agree on the public data. -/
theorem tabLoop_ct (M : Mont) :
    RelCT isa (Two fun (q : RPub) s => 0 < 14 ∧ TL (q, 0) s)
      (.loop (seqs [M.mm aY aY aXm,
        .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
        .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
          .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
          .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne)
      (Two fun q s => TL (q, 14) s) := by
  refine two_loop (Φ := fun q j s => TL (q, j) s) (fun _ => 14) ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two TLW) (two_post (two_map (fun p : RPub × Nat => (⟨p.1.p.B, p.1.p.Z, p.1.p.w⟩ : Ws))
      (fun _ _ h => let ⟨_, _, hd, _, mi, _, _, hc, _⟩ := tl_tlw h.2 h.1; ⟨mi, hc.good, hd.z⟩)
      (M.ct (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))) fun p s h => tlw_mm M (tl_tlw h.2 h.1)) ?_
    refine RelCT.assoc (RelCT.seq (R := Two TLW)
      (kt_piece (fun p : RPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kV, kBits]) (fun p => p.1.tvs p.2) []
        (by decide) (fun p => p.1.tvs_fst p.2) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)
        fun _ _ h => tlw_copy h)
      (kt_ct (fun p : RPub × Nat => p.1.p.B) (fun p => p.1.p.wr) (mrS ++ [kV, kBits]) (fun p => p.1.tvs p.2) []
        (by decide) (fun p => p.1.tvs_fst p.2) (fun _ _ h => ⟨h.1, h.2.1⟩) (pins_nil _) (by taint_decide)))
  · rintro q j s hj ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI, hodd, hc1⟩
    refine WP.mono (tabStep_ok M hd hodd hc1 hj hI) fun t ⟨hz, hI'⟩ => ⟨?_, fun _ => ?_, fun _ => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases h : j + 1 = 14 <;> simp [h]; omega
    · exact ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI', hodd, hc1⟩
    · rename_i e; rw [← e]; exact ⟨mi, c, bm, b, s₀, hk, hh, hw, hd, hI', hodd, hc1⟩

/-- The table leaks the same in runs that agree on the public data. -/
theorem tabBuild_ct (M : Mont) : RelCT isa (Two W3) (seqs (tabBuild M.mm)) fun _ _ => True := by
  rw [tabBuild_eq]
  refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (R := Two fun (q : RPub) s => 0 < 14 ∧ TL (q, 0) s) ?_ ?_)
  · simp only [seqs]
    refine kt_piece (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
      (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => h.1) (pins_nil _) (by taint_decide) ?_
    rintro q s ⟨⟨hk, hp⟩, hd, mi, c, bm, b, hc, hX, hodd, hc1⟩
    exact WP.mono (tabHead_ok hd hc hc1 hX) fun t ⟨hI, hf, k⟩ => ⟨by decide, mi, c, _, b, t, hk,
      fun e he => by rw [← hI.frm.word_eq (by have := vs_tab _ _ _ e he; exact this.2) (by
        have := (vs_tab _ _ _ e he).1; omega_arith)]; exact hdr_frm hf (vs_tab _ _ _) hp.hdr e he,
      (hI.keep.2.2.symm.trans (k.2.2.trans hp.wr)), hd, hI, hodd, hc1⟩
  · refine RelCT.seqs_app (by simp) (by simp) (RelCT.seq (tabLoop_ct M) ?_)
    exact kt_ct (fun q : RPub => q.p.B) (fun q => q.p.wr) mrS (fun q => q.p.vs q.i (q.u + 8 * q.p.w)) []
      (by decide) (fun q => vs_fst0 _ _ _) (fun _ _ h => ⟨let ⟨_, _, _, _, _, hk, _⟩ := h; hk, tl_hp0 h⟩)
      (pins_nil _) (by taint_decide)

/-- The round up to the exponentiation leaks the same in runs that agree on
the public data. -/
theorem roundPre_ct (M : Mont) : RelCT isa (Two R0) (seqs (mrWitness ++ [M.mm aXm aX aR2] ++ tabBuild M.mm))
    (Two fun (q : RPub) s => ExpPre ⟨q.p, q.i, q.u + 8 * q.p.w⟩ s) := by
  refine two_post ?_ ?_
  · rw [roundPre_eq]
    refine RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq mrWitness_ct ?_)
    refine RelCT.seqs_app (by simp) (by simp [tabBuild]) (RelCT.seq (R := Two W3) ?_ (tabBuild_ct M))
    simp only [seqs]
    refine two_post (two_map (fun q : RPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws))
      (fun _ _ h => let ⟨_, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩)
      (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))) ?_
    rintro q s ⟨⟨hk, hp⟩, hd, mi, c, bm, hc, hR2, hodd, hc1⟩
    have hw' : q.p.w < 2 ^ 31 := by have := hd.w128; omega_arith
    have hRc : Nat.Coprime (2 ^ (64 * q.p.w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
    have hc0 : 0 < c := by omega_arith
    refine WP.mono (M.mm_ok hc.good hd.z (by have := hd.w4; omega_arith) hw' (o := aXm) (a := aX) (b := aR2) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun t ⟨hg, hlt, hy, ha', k⟩ => ?_
    have hf : Frm q.p.B [(slot q.p.w aAcc, 8 * (q.p.w + 2)), (slot q.p.w aTmp, 8 * (q.p.w + 2)),
        (slot q.p.w aXm, 8 * (q.p.w + 2))] s.mem t.mem := Frm.of_arrays ha' (by simp)
    rw [hc.n] at hlt hy
    rw [hR2] at hy
    refine ⟨⟨hk, hp.frm hf ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) (q.p.vs_lt _ _ [] (by simp) |> fun h e he => h e (by simpa using he))
      hg.rdi k.2.2⟩, hd, mi, c, bm, wv s.mem q.p.B (slot q.p.w aX) q.p.w,
      hc.of_frm hd hf hg.scr hg.rdi ((VG.Proof.RsaKeyGen.mm_shape _ _).geD rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl) ((VG.Proof.RsaKeyGen.mm_shape _ _).apartW rfl rfl), ?_, hodd, hc1⟩
    rw [← Nat.mod_eq_of_lt hlt, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  · rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hE, hR2, hc1, hsh, hsrc, -, hlen, -⟩
    have hm := (hp0 hp).mrh
    have hw4 := hd.w4
    have hn := hc.good.scr.nowrap
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
    refine WP.mono (roundPre_ok M hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen)
      fun t ⟨hc', hT, hy, _, _, hu, hf, k⟩ => ⟨hk, hp_used hp hc'.good k.2.2 hf (preRanges_mrh _) hu, hd, mi, c, _, _,
        hc', hT, hE.of_frm hf (fun r hr => Or.inr (preRanges_lt _ r hr)) (by
          have := aE_fits hd; have := hd.z; omega_arith), hsh.1, hc1, hy⟩

/-- After the exponentiation: the flag, the witness passing or not. -/
def Rmid (q : RPub) (s : State) : Prop :=
  KW q.p.B q.p.wr ∧ HP q.p.B q.p.wr (q.p.vs q.i (q.u + 8 * q.p.w)) s ∧ MrDims q.p.B q.p.Z q.p.w ∧
    ∃ (mi : BitVec 64) (uni : Nat) (u : Bool), Good s q.p.B q.p.Z q.p.w mi ∧
      word s.mem q.p.B (8 * kFlag) = mask q.pass ∧ word s.mem q.p.B (8 * kUni) = BitVec.ofNat 64 uni ∧
      word s.mem q.p.B (8 * kU) = mask u ∧ uni < 2 ^ 61

/-- The round up to its flag leaks the same in runs that agree on the public
data. -/
theorem roundMid_ct (M : Mont) : RelCT isa (Two R0) (seqs ((mrWitness ++ [M.mm aXm aX aR2] ++ tabBuild M.mm) ++
      mrExpLoop M.mm)) (Two Rmid) := by
  refine two_post (RelCT.seqs_app (by simp [mrWitness]) (by simp [mrExpLoop]) (RelCT.seq (roundPre_ct M)
    ((mrExpLoop_ct M).mono (fun _ _ h => two_bind (fun q _ _ h₁ h₂ => ⟨⟨q.p, q.i, q.u + 8 * q.p.w⟩, h₁, h₂⟩) h)
      fun _ _ _ => trivial))) ?_
  rintro q s ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hE, hR2, hc1, hsh, hsrc, -, hlen, hun, -, huni, -, hpass⟩
  have hm := (hp0 hp).mrh
  refine WP.mono (roundMid_ok M hd hc hE hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen hm.ki hun hm.chk)
    fun t ⟨⟨_, hc'⟩, hfl, _, hN, _, hU, hu, _, hf, k⟩ => ⟨hk, hp_used hp hc'.good k.2.2 hf (midRanges_mrh _) hu, hd, mi,
      uni, _, hc'.good, by rw [hfl, hpass], hN, hU, huni⟩

/-- The test of the flag. -/
theorem flagTest_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {f : Bool} (hF : word s.mem B (8 * kFlag) = mask f) :
    WP isa (.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!f) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kFlag)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
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
