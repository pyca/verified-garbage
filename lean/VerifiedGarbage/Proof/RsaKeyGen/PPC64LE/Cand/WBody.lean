module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WLoop
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Out
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the witnesses' loop, iteration by iteration

`mid_ok`: an iteration's draw, or `hStat := 0` when too few octets are left;
`body_ok`: the iteration and its test; `millerRabin_ok`: the loop
(`MrOut`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth geFlag hRand hRandLen hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS goS wit)

/-- The loop's invariant, `n + 1` iterations left. -/
def Inv (s : State) (B : Addr) (L w c ch : Nat) (r : Spec.RsaKeyGen.Rand) (n : Nat) (t : State) : Prop :=
  ∃ k, MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n ∧
    St s B L w c r k t

/-- Whether the loop goes on after the iteration that draws at offset
`8 w (k + 1)`, with `n + 1` iterations left: enough octets, the witness
passes, and more iterations are left. -/
def MC (c w : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) : Prop :=
  8 * w * (k + 1) + 8 * w ≤ r.length ∧ Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 (wit c (8 * w) r (8 * w * (k + 1))).1 = true ∧ 0 < n

/-- After an iteration from `k` witnesses passed, before its test. -/
def Mid (s : State) (B : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) (t : State) : Prop :=
  (MC c w r k n ∧ MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r (k + 1) (n - 1) ∧
      St s B L w c r (k + 1) t) ∨
    (¬ MC c w r k n ∧ ∃ v < 4, word t.mem B (8 * hStat) = BitVec.ofNat 64 v ∧ MrOut s B L w c rl r t)

theorem used_succ (w k : Nat) : 8 * w * (k + 1) + 8 * w = 8 * w * (k + 1 + 1) := by
  rw [Nat.mul_add (8 * w) (k + 1) 1, Nat.mul_one]

theorem tape_len {s : State} {B Ra : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) : r.length = rl := by
  rw [← P.tape]; simp [Spec.Rsa.bytesAt]

theorem drIn_of {s t : State} {B Ra : Addr} {L w c rl ch k : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hi : St s B L w c r k t) (hav : 8 * w * (k + 1) + 8 * w ≤ r.length) :
    DrIn t B Ra L w c (8 * w * (k + 1)) (mrS c (8 * w) r k).1 (mrS c (8 * w) r k).2 ch := by
  have e := hi.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  obtain ⟨_, hb1, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ w) P.shape
  have hrl := tape_len P
  have hrl' := P.hrl
  have hk1 : 32 * (k + 1) ≤ 8 * w * (k + 1) := Nat.mul_le_mul_right _ (by omega)
  have hsn := mrS_snd c (8 * w) r k
  have hwd : ∀ d, d < 31 → d ∉ lpWords → word t.mem B (8 * d) = word s.mem B (8 * d) := fun d h1 h2 =>
    hi.hdr _ (by omega) (fun j hj => by
      have : j ≠ d := fun e => h2 (e ▸ hj)
      simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hj; omega)
  exact ⟨hi.prep, P.h35, hb1, P.shape.2.2, (hwd hRand (by decide) (by decide)).trans P.rand, hi.used,
    (hwd hK (by decide) (by decide)).trans P.kk,
    fun i hi' => by rw [hi.rd, hi.wr]; exact P.rN _ (by omega),
    fun i hi' x hx hxe => P.rD ⟨B, 8 * L⟩ (by simp) _
      (Offset.contains_base Ra (d := 8 * w * (k + 1) + i) (by omega) (by omega))
      (by show Region.Contains _ (off Ra (8 * w * (k + 1) + i)) 1
          rw [hxe]; simp only [Region.Contains]; simp only [ofs] at hx; omega),
    by rw [hi.wr]; exact P.wr, by rw [hi.sp]; exact P.hsp, by rw [hi.sp]; exact P.hstk, hi.idx, hi.uni,
    (hwd hChecks (by decide) (by decide)).trans P.chk, by rw [mrS_fst]; omega, by omega, P.hch'⟩

/-- The witness drawn is the tape's. -/
theorem drX_eq {s t : State} {B Ra : Addr} {L w c rl ch k : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hi : St s B L w c r k t) (hav : 8 * w * (k + 1) + 8 * w ≤ r.length) :
    Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off Ra (8 * w * (k + 1)))
      (8 * w))) = wit c (8 * w) r (8 * w * (k + 1)) := by
  have hrl := tape_len P
  have hrl' := P.hrl
  unfold wit
  rw [← seg_eq t.mem Ra (n := rl) (by omega), bytes_keep hi.frame (by omega) P.rD, P.tape]

theorem mid_ok (R : RoundImpl) {s t : State} {B Ra : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r)
    (ha : MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n)
    (hi : St s B L w c r k t)
    (h5 : t.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - 8 * w * (k + 1) then 1 else 0)) :
    WP isa (.ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code)) t
      (Mid s B L w c rl ch r k n) := by
  have e := hi.prep.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  obtain ⟨_, hb1, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ w) P.shape
  have hL : 0 < 8 * w := by omega
  have hrl := tape_len P
  have hrl' := P.hrl
  have hu := ha.used
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) h5) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ 8 * w * (k + 1) + 8 * w ≤ r.length := by
      intro hc; simp only [decide_eq_true_eq] at hz; split at hz <;> first | exact absurd hz (by decide) | omega
    obtain ⟨_, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_short ha hwb hL hav
    refine WP.mono (WP.keep [.r3] (Q := fun t' => t'.mem = t.mem.writeW (off B (8 * hStat)) (BitVec.ofNat 64 0)) (by
      simp only [sth, hStat]; prun [e.h31, hs.st (d := 160) (n := 8) (by omega)]) (by decide)) fun t' ⟨tm, kt⟩ => ?_
    have st0 : word t'.mem B (8 * hStat) = BitVec.ofNat 64 0 := by rw [tm]; exact word_writeW_self _ _ _ _
    have wo := writeW_outside t.mem B (d := 8 * hStat) (BitVec.ofNat 64 0) (by simp only [hStat]; omega)
    refine .inr ⟨fun h => hav h.1, 0, by decide, st0, hi.toLKeep.write (d := hStat) (by simp [lpWords, hStat]) (by omega) kt tm
      (by decide), hi.prep.keep (e.keep kt (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_⟩
    · have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega
      have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega
      have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega
      have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega
      rw [tm]
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      all_goals exact wo.word (by simp only [hStat]; omega) (by omega)
    · rw [tm]
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        exact wo.val32 (by simp only [hStat]; rw [slot_lin]; omega) (by rw [slot_lin]; omega)
    · show match Spec.RsaKeyGen.primalityTest c (r.drop (8 * w)) with
        | none => word t'.mem B (8 * hStat) = BitVec.ofNat 64 0
        | some (b, rest) => word t'.mem B (8 * hStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
            word t'.mem B (8 * hUsed) = BitVec.ofNat 64 (rl - rest.length)
      rw [hpt]; exact st0
  · have hav : 8 * w * (k + 1) + 8 * w ≤ r.length := by
      simp only [decide_eq_false_iff_not] at hz
      split at hz <;> first | omega | exact absurd rfl hz
    refine WP.mono (draw_ok R (drIn_of P hi hav)) fun t₂ hd => ?_
    have hX := drX_eq P hi hav
    have hst := hd.stat
    have hid := hd.idx
    have hun := hd.uni
    rw [hX] at hst hid hun
    have K := hi.toLKeep.draw hd
    by_cases hp : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
        (wit c (8 * w) r (8 * w * (k + 1))).1 = true
    · have hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w * (k + 1))).1 = true := by rw [round_eq]; exact hp
      simp only [hr, ↓reduceIte] at hst hid
      rw [statOf_eq] at hst
      by_cases hg : goS ch (mrS c (8 * w) r (k + 1))
      · obtain ⟨hn, ha'⟩ := VG.Proof.RsaKeyGen.mrAt_next ha hwb hL hav hp hg
        have hg' : (mrS c (8 * w) r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨
            (mrS c (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w * (k + 1))).2 then 1 else 0) < ch := hg
        simp only [hg', ↓reduceIte] at hst
        refine .inl ⟨⟨hav, hp, hn⟩, ha', K, hd.prep, ?_, hid, hun, hst⟩
        rw [hd.used, used_succ]
      · obtain ⟨hn0, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_done ha hwb hL hav hp hg
        have hg' : ¬ ((mrS c (8 * w) r k).1 + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨
            (mrS c (8 * w) r k).2 + (if (wit c (8 * w) r (8 * w * (k + 1))).2 then 1 else 0) < ch) := hg
        simp only [hg', ↓reduceIte] at hst
        refine .inr ⟨fun h => by have := h.2.2; omega, 1, by decide, hst, K, hd.prep, ?_⟩
        rw [hpt]
        refine ⟨hst, ?_⟩
        rw [hd.used, List.length_drop]
        congr 1; omega
    · have hp' : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (wit c (8 * w) r (8 * w * (k + 1))).1 = false := by simpa using hp
      have hr : Proof.MillerRabin.Round.round c (wit c (8 * w) r (8 * w * (k + 1))).1 = false := by
        rw [round_eq]; exact hp'
      obtain ⟨_, hpt⟩ := VG.Proof.RsaKeyGen.mrAt_fail ha hwb hL hav hp'
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hst
      refine .inr ⟨fun h => hp h.2.1, 2, by decide, hst, K, hd.prep, ?_⟩
      rw [hpt]
      refine ⟨hst, ?_⟩
      rw [hd.used, List.length_drop]
      congr 1; omega

/-- The loop's test of octets left. -/
abbrev availB : List Instr := [ldh .r3 hRandLen, ldh .r4 hUsed, .sub .r3 .r3 .r4, ldh .r4 hK] ++ geFlag .r5 .r3 .r4

/-- The loop's draw, or its end for want of octets. -/
abbrev drawI (R : RoundImpl) : Prog isa := .ite (.zero .d .r5) (.block [.li .r3 0, sth .r3 hStat]) (draw R.name R.code)

/-- The loop's test of its status. -/
abbrev tailB : List Instr := [ldh .r3 hStat, .subi .r3 .r3 4]

/-- What the loop leaves for the result. -/
abbrev mrLoop (R : RoundImpl) : Prog isa :=
  .loop (.seq (.block availB) (.seq (drawI R) (.block tailB))) (.zero .d .r3)

theorem availS {s t : State} {B Ra : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r)
    (ha : MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r k n)
    (hi : St s B L w c r k t) :
    WP isa (.block availB) t fun t₁ => St s B L w c r k t₁ ∧
      t₁.gpr .r5 = BitVec.ofNat 64 (if 8 * w ≤ rl - 8 * w * (k + 1) then 1 else 0) := by
  have e := hi.prep.env
  have hZ := e.hZ
  have hw4 := e.hw
  have hw' := e.hw'
  rw [slot_lin] at hZ
  have hrl := tape_len P
  have hrl' := P.hrl
  have hu := ha.used
  have hwd : ∀ d, d < 31 → d ∉ lpWords → word t.mem B (8 * d) = word s.mem B (8 * d) := fun d h1 h2 =>
    hi.hdr _ (by omega) (fun j hj => by
      have : j ≠ d := fun e => h2 (e ▸ hj)
      simp only [lpWords, List.mem_cons, List.not_mem_nil, or_false] at hj; omega)
  exact WP.mono (avail_ok e.hs e.h31 (by omega) ((hwd hRandLen (by decide) (by decide)).trans P.rlen)
    hi.used ((hwd hK (by decide) (by decide)).trans P.kk) (by omega) (by omega) (by omega))
    fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ⟨hi.keep k₁ m₁, a5⟩

/-- After the loop's test. -/
def Tl (s : State) (B : Addr) (L w c rl ch : Nat) (r : Spec.RsaKeyGen.Rand) (k n : Nat) (t : State) : Prop :=
  (MC c w r k n ∧ isa.eval (.zero .d .r3) t = some true ∧
      MrAt c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (8 * w) r (k + 1) (n - 1) ∧
      St s B L w c r (k + 1) t) ∨
    (¬ MC c w r k n ∧ isa.eval (.zero .d .r3) t = some false ∧ MrOut s B L w c rl r t)

theorem tailS {s t : State} {B : Addr} {L w c rl ch k n : Nat} {r : Spec.RsaKeyGen.Rand}
    (hm : Mid s B L w c rl ch r k n t) : WP isa (.block tailB) t (Tl s B L w c rl ch r k n) := by
  rcases hm with ⟨hc, ha', hi'⟩ | ⟨hc, v, hv, hst, ho⟩
  · have e' := hi'.prep.env
    have hZ' := e'.hZ
    rw [slot_lin] at hZ'
    exact WP.mono (tail_ok e'.hs e'.h31 (by omega) hi'.stat (by decide)) fun t₃ ⟨⟨ev, m₃⟩, k₃⟩ =>
      .inl ⟨hc, ev, ha', hi'.keep k₃ m₃⟩
  · have e' := ho.prep.env
    have hZ' := e'.hZ
    rw [slot_lin] at hZ'
    exact WP.mono (tail_ok e'.hs e'.h31 (by omega) hst (by omega)) fun t₃ ⟨⟨ev, m₃⟩, k₃⟩ =>
      .inr ⟨hc, by rw [ev, decide_eq_false (by omega)], ho.keep k₃ m₃⟩

theorem loop_ok (R : RoundImpl) {s t : State} {B Ra : Addr} {L w c rl ch n : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hI : Inv s B L w c ch r n t) :
    WP isa (mrLoop R) t (MrOut s B L w c rl r) := by
  refine WP.loop (M := isa) (Q := MrOut s B L w c rl r) (Inv s B L w c ch r) ?_ n t hI
  intro n t hI
  obtain ⟨k, ha, hi⟩ := hI
  refine WP.seq (WP.mono (availS P ha hi) fun t₁ ⟨h₁, a5⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok R P ha h₁ a5) fun t₂ hm => ?_)
  refine WP.mono (tailS hm) fun t₃ ht => ?_
  rcases ht with ⟨hc, ev, ha', hi'⟩ | ⟨-, ev, ho⟩
  · exact .inr ⟨ev, n - 1, by have := hc.2.2; omega, k + 1, ha', hi'⟩
  · exact .inl ⟨ev, ho⟩

/-- The loop's counts set up. -/
abbrev mrInit : List Instr :=
  [.li .r3 1, sth .r3 hIdx, .li .r3 0, sth .r3 hUni, .li .r3 4, sth .r3 hStat]

theorem init_ok {s : State} {B : Addr} {L w c : Nat} {r : Spec.RsaKeyGen.Rand} (hp : Prep s B L w c)
    (hu0 : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w)) :
    WP isa (.block mrInit) s (St s B L w c r 0) := by
  have e := hp.env
  have hs := e.hs
  have hnw := hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  refine (WP.mono (WP.keep [.r3] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (8 * hIdx)) (BitVec.ofNat 64 1)).writeW (off B (8 * hUni)) (BitVec.ofNat 64 0)).writeW
        (off B (8 * hStat)) (BitVec.ofNat 64 4)) (by
    simp only [mrInit, sth, hIdx, hUni, hStat]
    prun [e.h31, hs.st (d := 176) (n := 8) (by omega), hs.st (d := 16) (n := 8) (by omega),
      hs.st (d := 160) (n := 8) (by omega)]) (by decide)) fun t₀ ⟨tm, k₀⟩ => ?_)
  have o : Outs B [(8 * hIdx, 8), (8 * hUni, 8), (8 * hStat, 8)] s.mem t₀.mem := by
    rw [tm]
    exact ((Outs.of_outside (writeW_outside _ B (d := 8 * hIdx) _ (by simp only [hIdx]; omega)) (by simp)).trans
      (Outs.of_outside (writeW_outside _ B (d := 8 * hUni) _ (by simp only [hUni]; omega)) (by simp))).trans
      (Outs.of_outside (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega)) (by simp))
  have ow : ∀ d, d + 8 ≤ 2 ^ 64 → (d + 8 ≤ 16 ∨ 24 ≤ d) → (d + 8 ≤ 160 ∨ 168 ≤ d) → (d + 8 ≤ 176 ∨ 184 ≤ d) →
      word t₀.mem B d = word s.mem B d := fun d h0 h1 h2 h3 =>
    o.word (fun x hx => by
      simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp only [] <;> omega) h0
  refine ⟨⟨fun d hd hk => ow d (by omega) (hk 2 (by decide)) (hk 20 (by decide)) (hk 22 (by decide)),
    Frame.mono (frame_of_outs o (Z := 8 * L) (fun x hx => by
      simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp only [] <;> omega)) (by simp),
    k₀.rd, k₀.wr, k₀.sp, fun x _ _ h2 => k₀.gpr x (not_mem_of_sub (by decide) h2)⟩,
    hp.keep (e.keep k₀ (by decide)) (fun d hd => ?_) (fun j hj => ?_), ?_, ?_, ?_, ?_⟩
  · have s0' : slot w 0 + 8 ≤ 8 * L := by rw [slot_lin]; omega
    have s27' : slot w 27 + 8 * w + 8 ≤ 8 * L := by rw [slot_lin]; omega
    have s0 : 256 ≤ slot w 0 := by rw [slot_lin]; omega
    have s27 : 256 ≤ slot w 27 := by rw [slot_lin]; omega
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
    all_goals exact ow _ (by omega) (by omega) (by omega) (by omega)
  · refine o.val32 (fun x hx => ?_) (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [slot_lin] <;> omega)
    simp only [hIdx, hUni, hStat, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega
  · rw [ow _ (by simp only [hUsed]; omega) (by simp only [hUsed]; omega) (by simp only [hUsed]; omega)
      (by simp only [hUsed]; omega), hu0, Nat.zero_add, Nat.mul_one]
  · rw [tm, (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega)).word
      (by simp only [hStat, hIdx]; omega) (by simp only [hIdx]; omega),
      (writeW_outside _ B (d := 8 * hUni) _ (by simp only [hUni]; omega)).word
      (by simp only [hUni, hIdx]; omega) (by simp only [hIdx]; omega), word_writeW_self]
    rfl
  · rw [tm, (writeW_outside _ B (d := 8 * hStat) _ (by simp only [hStat]; omega)).word
      (by simp only [hStat, hUni]; omega) (by simp only [hUni]; omega), word_writeW_self]
    rfl
  · rw [tm, word_writeW_self]


theorem millerRabin_ok (R : RoundImpl) {s : State} {B Ra : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand}
    (P : LIn s B Ra L w c rl ch r) (hp : Prep s B L w c)
    (hu0 : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (8 * w)) (h8 : 8 * w ≤ rl) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) s (MrOut s B L w c rl r) := by
  have hw4 := hp.env.hw
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ w) P.shape
  have hrl := tape_len P
  have hc := VG.Proof.RsaKeyGen.primalityTest_cand (by omega) P.shape (r.drop (8 * w))
  rw [← P.hch] at hc
  have h0 := VG.Proof.RsaKeyGen.mrAt_zero (ch := ch) hc hwb (by omega) (by omega)
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin
  exact WP.seq (WP.mono (init_ok hp hu0) fun t ht => loop_ok R P ⟨0, h0, ht⟩)

end VG.Proof.RsaKeyGen.PPC64LE.Cand
