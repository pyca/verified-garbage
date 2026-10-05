import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak

/-!
# A candidate on x86-64: constant time of Miller–Rabin's loop

The loop over the witnesses, from what its correctness proof keeps
(`MrSt`), for runs that agree on the public data and on the shape of the
test's result (`shapeOf`: what became of the candidate, and how many octets
of `rand` were left). The shape fixes how many iterations remain from each
offset (`itersOf`), and whether each witness passes (`passS`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf itersOf passS)

/-- Whether `rand` has the next witness. -/
theorem availCmp_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {rl u : Nat} (hrl : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 rl)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hul : u ≤ rl) (hrl' : rl < 2 ^ 64) (hw : 8 * w < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
      .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)]) s fun t =>
      t.cf = some (decide (rl < u + 8 * w)) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hnw := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have e1 : BitVec.ofNat 64 rl - BitVec.ofNat 64 u = BitVec.ofNat 64 (rl - u) := ofNat_sub_ofNat' hul hrl'
  have e2 : rl - u < 2 ^ 64 := by omega
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.cf = some (decide (rl < u + 8 * w)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kUsed (by decide), hl kLen (by decide), hl kRandLen (by decide), hu, hK,
      hrl, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt hw]
    exact decide_eq_decide.mpr (by omega)) rfl) fun t ⟨⟨hc, hm⟩, k⟩ => ⟨hc, hm, k⟩

/-- `MrSt` survives changes to registers Montgomery multiplication may
change, and none to memory. -/
theorem MrSt.congr {B : Addr} {Z w : Nat} {mi : BitVec 64} {c ch : Nat} {rp : Addr} {r : List Byte} {s₀ : State}
    {res : Option (Bool × List Byte)} {i uni used : Nat} {s t : State} {rs : List Reg}
    (h : MrSt B Z w mi c ch rp r s₀ res i uni used s) (hd : MrDims B Z w) (hm : t.mem = s.mem) (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ∈ mmRegs) : MrSt B Z w mi c ch rp r s₀ res i uni used t := by
  obtain ⟨⟨bm, hc⟩, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨⟨bm, hc.of_frm hd (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (hc.good.scr.congr k.2.2)
    ((k.gpr (by intro h; have := hrs _ h; simp [mmRegs] at this)).trans hc.good.rdi) (by simp) (by simp) (by simp)
    (by simp) (by simp)⟩, by rw [hm]; exact h1, by rw [hm]; exact h2, by rw [hm]; exact h3, by rw [hm]; exact h4,
    by rw [hm]; exact h5, h6.congrK (by rw [hm]; exact InScr.refl _ _ _) k, by rw [hm]; exact h7, by rw [hm]; exact h8,
    by rw [hm]; exact h9, h10, h11, h12, h13, h14, by rw [hm]; exact h15, (h16.trans k).mono fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hr
  · exact hrs r hr

/-- The public data of Miller–Rabin's loop: the offset of the first witness
and the shape of the result. -/
structure LPub where
  p : MrPub
  u0 : Nat
  S : Option (Bool × Nat)

/-- The offset of iteration `j`'s witness. -/
abbrev LPub.u (a : LPub) (j : Nat) : Nat := a.u0 + 8 * a.p.w * j

/-- The iterations of the loop. -/
abbrev LPub.N (a : LPub) : Nat := itersOf (8 * a.p.w) a.p.rl a.S a.u0

/-- At the head of iteration `j`. -/
def LoopI (a : LPub) (j : Nat) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧ a.p.ch < 2 ^ 62 ∧ a.p.rl < 2 ^ 64 ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)) (uni : Nat),
      MrSt a.p.B a.p.Z a.p.w mi c a.p.ch a.p.rP r s₀ res (j + 1) uni (a.u j) s ∧ shapeOf res = a.S ∧
      r.length = a.p.rl ∧ 1 < c ∧ VG.Proof.RsaKeyGen.PrimeShape (64 * a.p.w) c ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧ s₀.wr = a.p.wr ∧
      itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = a.N - j

/-- The header at the head of an iteration. -/
theorem LoopI.hp {a : LPub} {j : Nat} {s : State} (h : LoopI a j s) :
    HP a.p.B a.p.wr (a.p.vs (j + 1) (a.u j)) s := by
  obtain ⟨-, hd, -, -, mi, c, r, s₀, res, uni, hI, -, hrl, -, -, hout, hup, hw, -⟩ := h
  obtain ⟨bm, hc⟩ := hI.ctx
  have hf := hI.frm
  have e : ∀ k, k = kOut ∨ k = kUsedP → word s.mem a.p.B (8 * k) = word s₀.mem a.p.B (8 * k) := fun k hk => by
    rcases hk with rfl | rfl
    · exact hf.word_eq (roundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (by decide)
    · exact hf.word_eq (roundRanges_hdr _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (by decide)
  have := mr_hp (ex := []) (i := j + 1) (u := a.u j) hc.good (hI.keep.2.2.trans hw)
    ⟨(e _ (Or.inl rfl)).trans hout, hI.len, (e _ (Or.inr rfl)).trans hup, hI.rand, by rw [hI.rlen, hrl], hI.chk,
      hI.ki, hI.kused⟩ (by simp)
  rwa [List.append_nil] at this

/-- Before the branch on `rand`'s length. -/
def AvI (p : LPub × Nat) (s : State) : Prop :=
  LoopI p.1 p.2 s ∧ s.cf = some (decide (p.1.p.rl < p.1.u p.2 + 8 * p.1.p.w))

/-- What a round needs, at the head of an iteration with the witness's octets. -/
theorem avI_r0 {p : LPub × Nat} {s : State} (h : AvI p s) (hb : isa.eval .b s = some false) :
    R0 ⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩ s := by
  have hp := h.1.hp
  obtain ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, -⟩, hcf⟩ := h
  simp only [eval, hcf, Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hb
  obtain ⟨bm, hc⟩ := hI.ctx
  have hw4 := hd.w4
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hiu := hI.iu
  have hul := hI.ul
  have hi : 32 * (p.2 + 1) ≤ 8 * p.1.p.w * (p.2 + 1) := Nat.mul_le_mul_right _ (by omega)
  have hj : p.2 + 1 < 2 ^ 59 := by omega
  have hun := hI.unii
  refine ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hI.r2, hc1, hsh, hI.src, hrlen, by rw [hrlen]; exact hb, hI.kuni,
    show p.2 + 1 < 2 ^ 61 by omega, by omega, hch, ?_⟩
  rw [← hS, ← hI.rest, ← hrlen]
  exact (VG.Proof.RsaKeyGen.mr_pass hI.go hwb (by omega) (by rw [hrlen]; exact hb)).symm

/-- Where the loop ends. -/
def LoopEnd (a : LPub) (s : State) : Prop :=
  KW a.p.B a.p.wr ∧ MrDims a.p.B a.p.Z a.p.w ∧
    ∃ (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State) (res : Option (Bool × List Byte)),
      MrEnd a.p.B a.p.Z a.p.w mi c r s₀ res s ∧ shapeOf res = a.S ∧ r.length = a.p.rl ∧
      word s₀.mem a.p.B (8 * kOut) = a.p.op ∧ word s₀.mem a.p.B (8 * kUsedP) = a.p.up ∧ s₀.wr = a.p.wr

theorem hp_nil {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {s : State} (h : HP B wr vs s) :
    HP B wr [] s := ⟨h.rdi, h.wr, fun _ he => absurd he (List.not_mem_nil)⟩

/-- Miller–Rabin's loop leaks the same in runs that agree on the public data
and on the shape of the result. -/
theorem mrLoop_ct (M : Mont) :
    RelCT isa (Two fun (a : LPub) s => 0 < a.N ∧ LoopI a 0 s)
      (.loop (seqs [
        .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
          .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
        .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRound M.mm)),
        .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) .e) (Two LoopEnd) := by
  refine two_loop (Φ := LoopI) LPub.N ?_ ?_
  · simp only [seqs]
    refine RelCT.seq (R := Two AvI) (kt_piece (fun p : LPub × Nat => p.1.p.B) (fun p => p.1.p.wr) mrS
      (fun p => p.1.p.vs (p.2 + 1) (p.1.u p.2)) [] (by decide) (fun p => vs_fst0 _ _ _)
      (fun _ _ h => ⟨h.2.1, h.2.hp⟩) (pins_nil _) (by taint_decide) ?_)
      (two_ite_seq (fun _ _ _ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)
    · rintro ⟨a, j⟩ s ⟨hj, h⟩
      have h' := h
      obtain ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hw, hit⟩ := h'
      obtain ⟨bm, hc⟩ := hI.ctx
      refine WP.mono (availCmp_ok hc.good hd.z (hI.rlen.trans (by rw [hrlen])) hI.kused hI.len (by rw [← hrlen]; exact hI.ul)
        hrl (by have := hd.w64; omega)) fun t ⟨hcf, hm, k⟩ =>
          ⟨⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI.congr hd hm k (by decide), hS, hrlen, hc1, hsh, ho, hu, hw,
            hit⟩, hcf⟩
    · exact kt_ct (fun p : LPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
        (fun _ => rfl) (fun _ _ h => ⟨h.1.1.1, hp_nil h.1.1.hp⟩) (pins_nil _) (by taint_decide)
    · refine RelCT.seq (R := Two fun (p : LPub × Nat) s => KW p.1.p.B p.1.p.wr ∧ HP p.1.p.B p.1.p.wr [] s)
        (two_post (two_map (fun p : LPub × Nat =>
          (⟨p.1.p, p.2 + 1, p.1.u p.2, passS (8 * p.1.p.w) p.1.p.rl p.1.S (p.1.u p.2)⟩ : RPub))
          (fun _ _ h => avI_r0 h.1 h.2) (mrRound_ct M)) ?_)
        (kt_ct (fun p : LPub × Nat => p.1.p.B) (fun p => p.1.p.wr) [] (fun _ => []) [] (by decide)
          (fun _ => rfl) (fun _ _ h => h) (pins_nil _) (by taint_decide))
      rintro p s ⟨h, hb⟩
      have hr := avI_r0 h hb
      obtain ⟨hk, hp, hd, mi, c, bm, r, uni, hc, hR2, hc1, hsh, hsrc, -, hlen, hun, hi, huni, hch, -⟩ := hr
      have hm := (hp0 hp).mrh
      exact WP.mono (mrRound_ok M hd hc hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen hm.ki hun hm.chk hi huni hch)
        fun t ⟨hc', _, _, _, _, _, k⟩ => ⟨hk, hc'.good.rdi, k.2.2.trans hp.wr, fun _ he => absurd he (List.not_mem_nil)⟩
  · rintro a j s hj ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni, hI, hS, hrlen, hc1, hsh, ho, hu, hw, hit⟩
    have hw4 := hd.w4
    obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
    refine WP.mono (mrIter_ok M hd hc1 hsh (by omega) hch s hI) fun t ht => ?_
    rcases ht with ⟨he, hend, hnone, hsome⟩ | ⟨he, uni', hI'⟩
    · have h1 : itersOf (8 * a.p.w) a.p.rl a.S (a.u j) = 1 := by
        rcases hres : res with _ | ⟨b, rest⟩
        · rw [← hS, hres]; exact VG.Proof.RsaKeyGen.iters_end_none (by omega) (by rw [← hrlen]; exact hnone hres)
        · rw [← hS, hres]
          exact VG.Proof.RsaKeyGen.iters_end_some (by omega) (by rw [← hrlen]; exact hsome b rest hres)
      refine ⟨by rw [he]; simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not, Nat.not_lt]; omega,
        fun h => absurd h (by omega), fun _ => ⟨hk, hd, mi, c, r, s₀, res, hend, hS, hrlen, ho, hu, hw⟩⟩
    · have hu' : a.u (j + 1) = a.u j + 8 * a.p.w := by simp only [LPub.u]; rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      have hc := VG.Proof.RsaKeyGen.iters_cont (L := 8 * a.p.w) (r := r) (a := (Spec.Rsa.splitTwos (c - 1)).1)
        (m := (Spec.Rsa.splitTwos (c - 1)).2) hI'.go hwb (by omega) (by omega) hI'.ul
      have hr' : Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c a.p.ch (Spec.Rsa.splitTwos (c - 1)).1
          (Spec.Rsa.splitTwos (c - 1)).2) (j + 1 + 1, uni') (List.drop (a.u j + 8 * a.p.w) r) = res := hI'.rest
      rw [show a.u j + 8 * a.p.w - 8 * a.p.w = a.u j by omega, hr', hS, hrlen] at hc
      refine ⟨by rw [he]; exact congrArg some (decide_eq_true (by omega)).symm, fun _ => ?_, fun h => absurd h (by omega)⟩
      rw [← hu'] at hI'
      exact ⟨hk, hd, hch, hrl, mi, c, r, s₀, res, uni', hI', hS, hrlen, hc1, hsh, ho, hu, hw, by rw [hu']; omega⟩

end VG.Proof.RsaKeyGen.X86_64
