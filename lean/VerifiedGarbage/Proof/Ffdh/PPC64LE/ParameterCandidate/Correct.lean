module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Result
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Main
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Entry`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the entry

`entryA_ok`: `scratch_len` from the stack, the save area's address in
`r11`, the link register saved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE.Search (rw_off rw_self)
open VG.Impl.MillerRabin.PPC64LE.Search (sth ldh hWsLen hUsed hRand hRandLen)

theorem entryA_ok {s : State} {B : Addr} {n : Nat} (h10 : s.gpr .r10 = B) (hn : stackArg s 0 = BitVec.ofNat 64 n)
    (hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (hn160 : 160 ≤ 8 * n)
    (hsv : InRegions s.wr (off B (8 * n - 160 + 144)) 8) :
    WP isa (.block [.addSp .r11 96, .load .d .r12 .r11 0, .lsl .r11 .r12 3, .add .r11 .r10 .r11,
      .subi .r11 .r11 saveBytes, .mflr .r0, .store .d .r0 .r11 144]) s fun t =>
      (t.gpr .r11 = off B (8 * n - 160) ∧ t.gpr .r12 = BitVec.ofNat 64 n ∧
        t.mem = s.mem.writeW (off B (8 * n - 160 + 144)) s.lr) ∧ Keep [.r0, .r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, stackArg, Nat.reduceMul, Nat.reduceAdd] at hargs hn
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  have e1 : B + BitVec.ofNat 64 (8 * n) - BitVec.ofNat 64 160 = off B (8 * n - 160) :=
    VG.Offset.add_ofNat_sub B hn160
  prun [ea, hargs, hn, h10, Pub.ofNat_shl3, saveBytes, e1, exec_mflr, off_add, hsv]

/-- The first `k` registers saved, from the state `s₀` after `entryA`. -/
structure SV (B : Addr) (n : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside B (8 * n - 160) 160 s₀.mem s.mem
  saved : ∀ i < k, word s.mem B (8 * n - 160 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i)
  lrW : word s.mem B (8 * n - 160 + 144) = word s₀.mem B (8 * n - 160 + 144)

theorem save_step {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) {k : Nat} (hk : k < 18) {s : State}
    (h : SV B n s₀ k s) : WP isa (.block [.store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k) .r11 (8 * k)]) s (SV B n s₀ (k + 1)) := by
  have hw : s.gpr .r11 = off B (8 * n - 160) := by rw [h.gpr, h11]
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.wr, hw, off_add]; exact hin k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega_using [hk]) hout,
    Option.some.injEq, exists_eq_left', hw, off_add]
  have hW := writeW_outside s.mem B (d := 8 * n - 160 + 8 * k) (s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved k)) (by omega_using [hn, hk])
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr, h.out.trans (hW.mono (by omega_using []) (by omega_using [hk])), fun i hi => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simp only [word, off]
      rw [rw_off _ _ _ (by omega_using [hi]) (by omega_using [hn, hk]) (by omega_arith)]
      exact h.saved i hi
    · simp only [word, off]; rw [rw_self, h.gpr]
  · simp only [word, off] at h ⊢
    rw [rw_off _ _ _ (by omega_using [hk]) (by omega_using [hn, hk]) (by omega_using [hn])]
    exact h.lrW

theorem map_flatMap {α β : Type} (g : α → β) (l : List α) : l.map g = l.flatMap fun i => [g i] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem saves_ok {B : Addr} {n : Nat} {s₀ : State} (h11 : s₀.gpr .r11 = off B (8 * n - 160))
    (hn160 : 160 ≤ 8 * n) (hn : 8 * n ≤ 2 ^ 64)
    (hin : ∀ i < 18, InRegions s₀.wr (off B (8 * n - 160 + 8 * i)) 8) :
    WP isa (.block ((List.range 18).map fun i => .store .d (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) .r11 (8 * i))) s₀ (SV B n s₀ 18) := by
  rw [map_flatMap]
  exact wp_range_flatMap (M := isa) (SV B n s₀) (fun k s hk h => save_step h11 hn160 hn hin hk h) 18
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), rfl⟩

/-- The header's stores. -/
def hdrW (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) : Mem :=
  ((((((((m.writeW (B + BitVec.ofNat 64 0) r12).writeW (B + BitVec.ofNat 64 16) r3).writeW
    (B + BitVec.ofNat 64 24) r4).writeW (B + BitVec.ofNat 64 152) r4).writeW (B + BitVec.ofNat 64 32) r5).writeW
    (B + BitVec.ofNat 64 40) r6).writeW (B + BitVec.ofNat 64 128) r7).writeW (B + BitVec.ofNat 64 136) r8).writeW
    (B + BitVec.ofNat 64 144) r9

theorem header_ok {s : State} {B : Addr} (h10 : s.gpr .r10 = B)
    (hst : ∀ d, d + 8 ≤ 256 → InRegions s.wr (B + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.addi .r31 .r10 0, sth .r12 hWsLen, sth .r3 hOut, sth .r4 hLen, sth .r4 hUsed, sth .r5 hUsedP,
      sth .r6 hBits, .lsr .w .r7 .r7 0, sth .r7 hGen, sth .r8 hRand, sth .r9 hRandLen]) s fun t =>
      (t.gpr .r31 = B ∧ t.gpr .r7 = ((s.gpr .r7).setWidth 32).setWidth 64 ∧
        t.mem = hdrW s.mem B (s.gpr .r12) (s.gpr .r3) (s.gpr .r4) (s.gpr .r5) (s.gpr .r6)
          (((s.gpr .r7).setWidth 32).setWidth 64) (s.gpr .r8) (s.gpr .r9)) ∧ Keep [.r7, .r31] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [sth, hWsLen, hOut, hLen, hUsed, hUsedP, hBits, hGen, hRand,
    hRandLen]
  prun [h10, hst 0 (by decide), hst 16 (by decide), hst 24 (by decide), hst 152 (by decide),
    hst 32 (by decide), hst 40 (by decide), hst 128 (by decide), hst 136 (by decide), hst 144 (by decide),
    BitVec.ushiftRight_zero]
  exact ⟨BitVec.add_zero B, rfl⟩

theorem hdrW_words (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) :
    let h := hdrW m B r12 r3 r4 r5 r6 r7 r8 r9
    word h B 0 = r12 ∧ word h B 16 = r3 ∧ word h B 24 = r4 ∧ word h B 152 = r4 ∧ word h B 32 = r5 ∧
      word h B 40 = r6 ∧ word h B 128 = r7 ∧ word h B 136 = r8 ∧ word h B 144 = r9 := by
  simp (disch := decide) only [hdrW, word, off, rw_off, rw_self, and_self]

theorem hdrW_frm (m : Mem) (B : Addr) (r12 r3 r4 r5 r6 r7 r8 r9 : BitVec 64) :
    Frm B [(0, 256)] m (hdrW m B r12 r3 r4 r5 r6 r7 r8 r9) := by
  unfold hdrW
  iterate 9 (refine VG.Proof.MillerRabin.PPC64LE.Search.frm_writeW ?_ _ ⟨(0, 256), List.mem_singleton_self _, by decide, by decide⟩ (by decide))
  exact Frm.refl _ _ _

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Front`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.ParameterCandidate.ZeroOut`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: `out` zeroed

`zeroOut_ok`: `out`'s `k` bytes := 0, nothing else in memory changed.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

theorem zeroOut_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h31 : s.gpr .r31 = B)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63) (hZ : 32 ≤ Z) :
    WP isa zeroOut s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ Keep [.r0, .r4, .r5] s t := by
  have hno := ho.nowrap
  unfold zeroOut
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r0, .r4, .r5] (Q := fun s₂ => s₂.gpr .r4 = O ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧
    s₂.gpr .r0 = BitVec.ofNat 64 0 ∧ s₂.mem = s.mem)
    (by simp only [Impl.MillerRabin.PPC64LE.Search.ldh, hOut, hLen]
        prun [h31, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith)])
    (by decide)) fun s₂ ⟨⟨b4, b5, b0, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r4 = off O j ∧ t.gpr .r0 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ Keep [.r0, .r4, .r5] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r4 0, .addi .r4 .r4 1] ++
      ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t0, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4]; simp [off], b0, by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  obtain hst : WP isa (.block [.stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .r4 (off O (j + 1))).write .r5 (t.gpr .r5 - BitVec.ofNat 64 1) := by
    prun [t4, t0, exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (ho.congr tk.wr).st (d := j) (n := 1) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  obtain hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega_arith)
  refine ⟨⟨by gsimp, by gsimp; exact t0, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact tk.trans' (((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: the front

`front_ok`: the entry and `out` zeroed give `St` for the arguments
(`ppOf`), with `used` at `out_len`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

/-- The candidate's arguments, on entry. -/
def ppOf (s : State) : PP where
  B := s.gpr .r10
  n := (stackArg s 0).toNat
  op := s.gpr .r3
  up := s.gpr .r5
  bits := (s.gpr .r6).toNat
  g := ((s.gpr .r7).setWidth 32).toNat
  rp := s.gpr .r8
  r := pcRand s
  sp := s.sp
  sv i := if i < 18 then s.gpr (Impl.Ffdh.PPC64LE.ParameterCandidate.saved i) else s.lr
  toc := s.gpr .r2

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem zext_eq (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Memory kept outside a region. -/
theorem out_word {O B : Addr} {L Z : Nat} {m m' : Mem} (hd : (⟨O, L⟩ : Region).Disjoint ⟨B, Z⟩)
    (hm : Outside O 0 L m m') (hnw : B.toNat + Z ≤ 2 ^ 64) {d : Nat} (hdz : d + 8 ≤ Z) :
    m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := by
  refine Mem.readW_congr fun i hi => hm _ (Or.inr ?_)
  by_contra hc
  exact hd (B + BitVec.ofNat 64 d + BitVec.ofNat 64 i) (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)
    (by simp only [Region.Contains]; rw [VG.Offset.add_add, Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

theorem saved_notin : ∀ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i ∉ ([.r0, .r11, .r12] : List Reg) := by
  decide

theorem front_ok (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t =>
      St (ppOf s) t ∧ word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧ t.lr = s.lr ∧
        Frame [⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] s.mem t.mem ∧
        t.rd = s.rd := by
  obtain ⟨hsp, hspT, hrd, hwr, dOU, dOR, dOS, dOA, dUR, dUS, dUA, dRS, dSA, qO, qU, qR, qS, qA, nwO, nwU, nwR,
    nwS, hb1, hb2, hL, hg, hsw, -⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsw
  obtain hn : stackArg s 0 = BitVec.ofNat 64 (stackArg s 0).toNat := (ofNat_toNat _).symm
  obtain h8n : 160 ≤ 8 * (stackArg s 0).toNat := by omega_arith
  obtain hscr : Scr s (s.gpr .r10) (8 * (stackArg s 0).toNat) :=
    Scr.of_mem (by rw [hwr, Nat.mul_comm]; simp) (by omega_arith)
  obtain hargs : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 8⟩, by rw [hrd]; simp, by simp [Region.Contains]⟩
  refine WP.seq ?_
  simp only [entry]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (entryA_ok rfl hn hargs h8n (hscr.st (by omega_arith))) fun tA ⟨⟨a11, a12, am⟩, ka⟩ => ?_
  refine WP.mono (saves_ok (s₀ := tA) a11 h8n (by omega_arith) fun i hi => by
    rw [ka.wr]; exact hscr.st (by omega_arith)) fun tS hS => ?_
  obtain hS10 : tS.gpr .r10 = s.gpr .r10 := by rw [hS.gpr, ka.gpr _ (by decide)]
  refine WP.mono (header_ok (s := tS) hS10 fun d hd => by
    rw [hS.wr, ka.wr]; exact hscr.st (d := d) (by omega_arith)) fun t₁ ⟨⟨c31, c7, cm⟩, kc⟩ => ?_
  obtain gS : ∀ r, r ∉ ([.r0, .r11, .r12] : List Reg) → tS.gpr r = s.gpr r := fun r hr => by
    rw [hS.gpr]; exact ka.gpr r hr
  obtain hS12 : tS.gpr .r12 = BitVec.ofNat 64 (stackArg s 0).toNat := by rw [hS.gpr]; exact a12
  obtain ⟨w0, w16, w24, w152, w32, w40, w128, w136, w144⟩ := hdrW_words tS.mem (s.gpr .r10) (tS.gpr .r12)
    (tS.gpr .r3) (tS.gpr .r4) (tS.gpr .r5) (tS.gpr .r6) (((tS.gpr .r7).setWidth 32).setWidth 64) (tS.gpr .r8)
    (tS.gpr .r9)
  rw [← cm] at w0 w16 w24 w152 w32 w40 w128 w136 w144
  obtain hwr₁ : t₁.wr = s.wr := by rw [kc.wr, hS.wr, ka.wr]
  obtain hscr₁ : Scr t₁ (s.gpr .r10) (8 * (stackArg s 0).toNat) := hscr.congr hwr₁
  obtain hout₁ : Scr t₁ (s.gpr .r3) (s.gpr .r4).toNat := (Scr.of_mem (by rw [hwr]; simp) nwO).congr hwr₁
  refine WP.mono (zeroOut_ok (s := t₁) hscr₁ hout₁ c31 (by rw [gS _ (by decide)] at w16; exact w16)
    (by rw [gS _ (by decide), ← ofNat_toNat (s.gpr .r4)] at w24; exact w24) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨⟨zb, zo⟩, kz⟩ => ?_
  have hnw := hscr.nowrap
  obtain dOS' : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dOS
  obtain wsW : ∀ d, d + 8 ≤ 8 * (stackArg s 0).toNat →
      t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 = t₁.mem.readW (s.gpr .r10 + BitVec.ofNat 64 d) 64 :=
    fun d hd => out_word dOS' zo hnw hd
  -- The memory, changed only in the working space and `out`.
  obtain fr : Frame [⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] s.mem t.mem := by
    obtain ws_of : ∀ x, (∀ r ∈ ([⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩, ⟨s.gpr .r3, (s.gpr .r4).toNat⟩] : List Region),
        ¬ r.Contains x 1) → 8 * (stackArg s 0).toNat ≤ ofs (s.gpr .r10) x ∧ (s.gpr .r4).toNat ≤ ofs (s.gpr .r3) x :=
      fun x hx => by
        obtain h1 := hx _ (List.mem_cons_self ..)
        obtain h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        simp only [Region.Contains, ofs] at h1 h2 ⊢; omega_arith
    intro x hx
    obtain ⟨hx1, hx2⟩ := ws_of x hx
    rw [zo x (Or.inr (by omega_arith)), cm, hdrW_frm _ _ _ _ _ _ _ _ _ _ x (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith)), hS.out x (Or.inr (by omega_arith)), am]
    exact writeW_outside s.mem (s.gpr .r10) (d := 8 * (stackArg s 0).toNat - 160 + 144) s.lr (by omega_arith) x
      (Or.inr (by omega_arith))
  obtain hlen : (pcRand s).length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  obtain kall : ∀ r, r ∉ ([.r0, .r4, .r5, .r7, .r11, .r12, .r31] : List Reg) → t.gpr r = s.gpr r := fun r hr => by
    rw [kz.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp)),
      kc.gpr r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> simp)),
      gS r (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp))]
  obtain hd : ∀ {d}, d + 8 ≤ 256 → word t.mem (s.gpr .r10) d = word t₁.mem (s.gpr .r10) d := fun hd' =>
    wsW _ (by omega_arith)
  obtain sav : ∀ i < 19, word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - saveBytes + 8 * i) = (ppOf s).sv i := by
    intro i hi
    simp only [saveBytes]
    rw [show word t.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) =
        word t₁.mem (s.gpr .r10) (8 * (stackArg s 0).toNat - 160 + 8 * i) from wsW _ (by omega_arith), cm,
      (hdrW_frm _ _ _ _ _ _ _ _ _ _).word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by omega_arith))
        (by omega_arith)]
    by_cases h18 : i < 18
    · rw [hS.saved i h18, ka.gpr _ (saved_notin i h18)]; simp [ppOf, h18]
    · obtain rfl : i = 18 := by omega_arith
      rw [hS.lrW]; simp only [word, off] at am ⊢
      rw [am, show 8 * (stackArg s 0).toNat - 160 + 8 * 18 = 8 * (stackArg s 0).toNat - 160 + 144 by omega_arith,
        VG.Proof.MillerRabin.PPC64LE.Search.rw_self]
      simp [ppOf]
  obtain dRS' : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dRS
  obtain dUS' : (⟨s.gpr .r5, 8⟩ : Region).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩ := by
    rw [Nat.mul_comm]; exact dUS
  obtain hwrt : t.wr = s.wr := by rw [kz.wr, hwr₁]
  refine ⟨⟨hscr₁.congr kz.wr, (kz.gpr .r31 (by decide)).trans c31,
    ⟨(hd (d := 0) (by decide)).trans (w0.trans hS12),
     (hd (d := 16) (by decide)).trans (w16.trans (gS .r3 (by decide))),
     (hd (d := 24) (by decide)).trans (w24.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
     (hd (d := 32) (by decide)).trans (w32.trans (gS .r5 (by decide))),
     (hd (d := 40) (by decide)).trans (w40.trans ((gS .r6 (by decide)).trans (ofNat_toNat _).symm)),
     (hd (d := 128) (by decide)).trans (w128.trans (by rw [gS .r7 (by decide), zext_eq]; rfl)),
     (hd (d := 136) (by decide)).trans (w136.trans (gS .r8 (by decide))),
     (hd (d := 144) (by decide)).trans (w144.trans ((gS .r9 (by decide)).trans (by
       rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen, ofNat_toNat])))⟩,
    ⟨fun i hi => ?_, fun i hi x hx he => ?_, ?_, ?_, ?_, fun x hx => ?_, ?_, fun x hx => ?_, by show (below s.sp 176).Disjoint ⟨s.gpr .r8, (pcRand s).length⟩; rw [hlen]; exact qR,
      by show (below s.sp 176).Disjoint ⟨s.gpr .r3, (ppOf s).L⟩; rw [← hLe]; exact qO, qU, by
      show (⟨s.gpr .r3, (ppOf s).L⟩ : Region).Disjoint _; rw [← hLe]; exact dOU⟩,
    ⟨hb1, hb2, hg, by simp only [ppOf, PP.L] at hLe ⊢; omega_arith, by simp only [ppOf]; omega_arith,
      by show (pcRand s).length < 2 ^ 64; rw [hlen]; exact (s.gpr .r9).isLt⟩,
    by rw [hwrt, hwr]; simp [ppOf, PP.Z, Nat.mul_comm], by rw [kz.sp, kc.sp, hS.sp, ka.sp]; rfl, hsp,
    by show (below s.sp 176).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩; rw [Nat.mul_comm]; exact qS,
    sav, kall .r2 (by decide)⟩,
    (hd (d := 152) (by decide)).trans (w152.trans ((gS .r4 (by decide)).trans (by rw [← hLe, ofNat_toNat]))),
    by rw [kz.lr, kc.lr, hS.lr, ka.lr], fr, by rw [kz.rd, kc.rd, hS.rd, ka.rd]⟩
  · rw [kz.rd, kc.rd, hS.rd, ka.rd, hrd]
    rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    exact ⟨⟨s.gpr .r8, (s.gpr .r9).toNat⟩, by simp, VG.Proof.Bignum.contains_byte _ hi (by omega_arith)⟩
  · rw [show (ppOf s).r.length = (s.gpr .r9).toNat from hlen] at hi
    subst he
    exact dRS' _ (VG.Proof.Bignum.contains_byte _ hi (by omega_arith)) (VG.Proof.Bignum.contains_scr hx)
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r8) (pcRand s).length = pcRand s
    rw [hlen]
    refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .r9).isLt fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRS'
    · exact dOR.symm
  · show Spec.Rsa.bytesAt t.mem (s.gpr .r3) (ppOf s).L = List.replicate (ppOf s).L 0
    rw [← hLe]; exact Pub.zero_bytes zb
  · show Scr t (s.gpr .r3) (ppOf s).L
    rw [← hLe]; exact hout₁.congr kz.wr
  · have hx' : ofs (s.gpr .r3) x < (s.gpr .r4).toNat := by rw [hLe]; exact hx
    exact VG.Proof.Bignum.out_scr dOS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)
  · exact (Scr.of_mem (by rw [hwr]; simp) nwU).congr hwrt
  · have hx' : ofs (s.gpr .r5) x < 8 := hx
    exact VG.Proof.Bignum.out_scr dUS' (by simp only [Region.Contains]; simp only [ofs] at hx'; omega_arith)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Exit`, which only this module used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the exit

`exit_ok`: the link register and the nonvolatile registers back from the
save area, memory unchanged.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh hWsLen)

theorem exitA_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block [ldh .r11 hWsLen, .lsl .r11 .r11 3, .add .r11 .r31 .r11, .subi .r11 .r11 saveBytes,
      .load .d .r0 .r11 144, .mtlr .r0]) t fun u =>
      u.gpr .r11 = off p.B (8 * p.n - 160) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧
        u.sp = t.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r11 → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  obtain h8n : 160 ≤ 8 * p.n := by omega_arith
  obtain e1 : p.B + BitVec.ofNat 64 (8 * p.n) - BitVec.ofNat 64 160 = off p.B (8 * p.n - 160) :=
    VG.Offset.add_ofNat_sub p.B h8n
  obtain l0 : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 0) 8 := h.scr.ld (d := 0) (by omega_arith)
  obtain l144 : InRegions (t.rd ++ t.wr) (off p.B (8 * p.n - 160 + 144)) 8 := h.scr.ld (by omega_arith)
  have w0 : t.mem.readW (p.B + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 p.n := h.len
  obtain w144 : t.mem.readW (off p.B (8 * p.n - 160 + 144)) 64 = p.sv 18 := h.save 18 (by decide)
  simp only [ldh, hWsLen, saveBytes]
  prun [exec_mtlr, h.r31, l0, w0, Pub.ofNat_shl3, e1, l144, w144]
  intro r h0 h11
  simp only [h0, h11, ↓reduceIte]

local notation "sv" => Impl.Ffdh.PPC64LE.ParameterCandidate.saved

theorem sv_inj : ∀ i < 18, ∀ j < 18, sv i = sv j → i = j := by decide

theorem sv_ne11 : ∀ i < 18, sv i ≠ .r11 := by decide

/-- The first `k` registers restored to `v`, from the state `sB`. -/
structure XI (sB : State) (S : Addr) (v : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  r11 : s.gpr .r11 = S
  restored : ∀ i < k, s.gpr (sv i) = v i
  others : ∀ r, (∀ i < 18, r ≠ sv i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off S (8 * i)) 8)
    (hv : ∀ i < 18, sB.mem.readW (off S (8 * i)) 64 = v i)
    {k : Nat} (hk : k < 18) {s : State} (h : XI sB S v k s) :
    WP isa (.block [.load .d (sv k) .r11 (8 * k)]) s (XI sB S v (k + 1)) := by
  obtain hin' : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.rd, h.wr, h.r11]; exact hin k hk
  obtain hv' : s.mem.readW (S + BitVec.ofNat 64 (8 * k)) 64 = v k := by rw [h.mem]; exact hv k hk
  obtain hn11 := sv_ne11 k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r11 ≠ .r0 by decide) (show 8 * k < 2 ^ 15 ∧ (8 * k) % 4 = 0 by omega_arith) hin',
    Option.some.injEq, exists_eq_left', h.r11, hv']
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn11)]; exact h.r11
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : sv i ≠ sv k := fun e => absurd (sv_inj i (by omega_arith) k hk e) (by omega_arith)
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr k hk)]
    exact h.others r hr

/-- The exit: the registers and the link register back from the save area. -/
theorem exit_ok {p : PP} {t : State} (h : ESt p t) :
    WP isa (.block exit) t fun u =>
      (∀ i < 18, u.gpr (sv i) = p.sv i) ∧ u.lr = p.sv 18 ∧ u.mem = t.mem ∧ u.sp = t.sp ∧
        ∀ r, r ≠ .r0 → r ≠ .r11 → (∀ i < 18, r ≠ sv i) → u.gpr r = t.gpr r := by
  have hdn := h.dims.n
  have hb := h.dims.b1
  have hn' := h.dims.n'
  have hZe : p.Z = 8 * p.n := rfl
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  unfold exit
  rw [map_flatMap, WP.block_append_iff]
  refine WP.mono (exitA_ok h) fun sB ⟨b11, blr, bm, brd, bwr, bsp, bo⟩ => ?_
  obtain hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off (off p.B (8 * p.n - 160)) (8 * i)) 8 := fun i hi => by
    rw [brd, bwr, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.scr.ld (by omega_arith)
  obtain hv : ∀ i < 18, sB.mem.readW (off (off p.B (8 * p.n - 160)) (8 * i)) 64 = p.sv i := fun i hi => by
    rw [bm, show off (off p.B (8 * p.n - 160)) (8 * i) = off p.B (8 * p.n - 160 + 8 * i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact h.save i (by omega_arith)
  refine WP.mono (wp_range_flatMap (M := isa) (XI sB (off p.B (8 * p.n - 160)) p.sv)
    (fun k s hk hs => restore_step sB hin hv hk hs) 18 (Nat.le_refl _) sB
    ⟨b11, fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩) fun u hu => ?_
  exact ⟨hu.restored, by rw [hu.lr, blr], by rw [hu.mem, bm], by rw [hu.sp, bsp],
    fun r h0 h11 hs => by rw [hu.others r hs, bo r h0 h11]⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on PPC64LE: correctness

`code_correct`: `code` meets `pcContract`'s postcondition and keeps what the
calling convention preserves, for any implementation of the round.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
theorem sieved_short {bits g : Nat} {r : List Byte} (h : r.length < (bits + 7) / 8) :
    Spec.Ffdh.sievedParameterCandidate bits g r = none := by
  have : (r.take ((bits + 7) / 8)).length ≠ (bits + 7) / 8 := by rw [List.length_take]; omega_using [h]
  simp only [Spec.Ffdh.sievedParameterCandidate, Spec.RsaKeyGen.draw, this, ↓reduceIte, bind, Option.bind]

/-- The tape's length and `out_len`. -/
theorem lenLoad_ok {p : PP} {t : State} (h : St p t) :
    WP isa (.block [ldh .r3 hRandLen, ldh .r4 hLen]) t fun u => (u.gpr .r3 = BitVec.ofNat 64 p.r.length ∧
      u.gpr .r4 = BitVec.ofNat 64 p.L ∧ u.mem = t.mem) ∧ Keep [.r3, .r4] t u := by
  refine WP.keep [.r3, .r4] ?_ (by decide)
  simp only [ldh, hRandLen, hLen]
  prun [h.r31, h.ld (d := 144) (by decide), h.ld (d := 24) (by decide), h.args.rlen', h.args.len']

/-- The length check's flag. -/
theorem lenChk_ok {p : PP} {t : State} (h : St p t) (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4)) t fun v =>
      isa.eval (.zero .d .r5) v = some (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) ∧ St p v ∧
        word v.mem p.B 152 = BitVec.ofNat 64 p.L ∧ v.mem = t.mem ∧ v.rd = t.rd := by
  have hrl := h.dims.rl
  have hb2 := h.dims.b2
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (lenLoad_ok h) fun u ⟨⟨a3, a4, am⟩, ka⟩ => ?_
  refine WP.mono (geFlag_ok a3 a4 hrl (by omega_using [hb2, hLe])) fun v ⟨⟨a5, vm⟩, kv⟩ => ?_
  obtain hm : v.mem = t.mem := vm.trans am
  exact ⟨eval_zero_ofNat v .r5 (by split <;> decide) a5, h.step (by rw [hm]; exact Frm.refl _ _ _) (ka.trans kv),
    by rw [hm]; exact hU, hm, (ka.trans kv).rd⟩

/-- The length check, then `main` or the status 0. -/
theorem body_ok (R : RoundImpl) {p : PP} {T : Addr} {t : State} (h : St p t) (ht : TabIn p.B p.Z T t)
    (hU : word t.mem p.B 152 = BitVec.ofNat 64 p.L) :
    WP isa (.seq (.block (([ldh .r3 hRandLen, ldh .r4 hLen] : List Instr) ++ geFlag .r5 .r3 .r4))
      (.ite (.zero .d .r5) (.block (finish 0)) (main R.name R.code))) t
      (CEnd p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r)) := by
  refine WP.seq (WP.mono_syms (lenChk_ok h hU) fun v ⟨he, st, hUv, vm, vrd⟩ sy => ?_)
  refine WP.ite (decide ((if p.L ≤ p.r.length then 1 else 0) = 0)) he (fun hb => ?_) (fun hb => ?_)
  · have hs : p.r.length < p.L := by
      by_contra hc; simp only [decide_eq_true_eq] at hb; rw [ite_eq_left (by omega_using [hc])] at hb; exact absurd hb (by decide)
    rw [sieved_short (by omega)]
    exact finEnd st (r := 0) (Or.inl rfl) rfl rfl rfl hUv
  · have hl : p.L ≤ p.r.length := by
      by_contra hc; simp only [decide_eq_false_iff_not] at hb; exact hb (by rw [ite_eq_right (by omega_using [hc])])
    exact main_ok R st (ht.step sy (rs := []) (by rw [vm]; exact Frm.refl _ _ _) (by simp) vrd) hUv hl

theorem preserved_cases : ∀ r ∈ preserved,
    r = .r2 ∨ ∃ i < 18, Impl.Ffdh.PPC64LE.ParameterCandidate.saved i = r := by decide

theorem r2_cases : ∀ i < 18, Reg.r2 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem r3_cases : ∀ i < 18, Reg.r3 ≠ Impl.Ffdh.PPC64LE.ParameterCandidate.saved i := by decide

theorem small_setWidth {k : Nat} (hk : k < 2 ^ 32) : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hk]

theorem status_le (res : Option (Option Nat × Spec.RsaKeyGen.Rand)) : Proof.Ffdh.candidateStatus res ≤ 2 := by
  rcases res with _ | ⟨_ | _, _⟩ <;> simp [Proof.Ffdh.candidateStatus]

/-- The front, and the table where the state names it. -/
theorem front_tab (s : State) (h : pcPre s) :
    WP isa (.seq (.block entry) zeroOut) s fun t => St (ppOf s) t ∧
      word t.mem (ppOf s).B 152 = BitVec.ofNat 64 (ppOf s).L ∧
      TabIn (ppOf s).B (ppOf s).Z (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) t := by
  have hpre := h
  obtain ⟨-, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htab⟩ := h
  refine WP.mono_syms (front_ok s hpre) fun t ⟨st, hU, _, fr, trd⟩ sy => ⟨st, hU, ?_⟩
  obtain ⟨tfit, tat, tdO, tdS⟩ := htab
  refine ⟨by rw [sy], fun i hi => ?_, by rw [trd, hrd]; simp, tfit, ?_⟩
  · rw [fr.readW (r := tabR s) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [Nat.mul_comm]; exact tdS
      · exact tdO) (by decide)]
    exact tat i hi
  · show (tabR s).Disjoint ⟨s.gpr .r10, 8 * (stackArg s 0).toNat⟩
    rw [Nat.mul_comm]; exact tdS

/-- `vg_ffdh_parameter_candidate_sieved`, for any implementation of the round. -/
theorem code_correct (R : RoundImpl) (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (code R.name R.code) s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa (code R.name R.code) s fun t => abiPreserved s t ∧ pcPost s t
  have hpre := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, -⟩ := h
  have hLe : (s.gpr .r4).toNat = (ppOf s).L := hL
  obtain hlen : (ppOf s).r.length = (s.gpr .r9).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  unfold code
  refine wp_then (front_tab s hpre) fun t ⟨st, hU, ht⟩ => ?_
  refine wp_then (body_ok R st ht hU) fun u hu => ?_
  obtain ⟨E, u3, uo, uu⟩ := hu
  refine WP.mono (exit_ok E) fun w ⟨wr, wlr, wm, wsp, wo⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rcases preserved_cases r hr with rfl | ⟨i, hi, rfl⟩
    · rw [wo .r2 (by decide) (by decide) r2_cases, E.r2]; rfl
    · rw [wr i hi]; simp [ppOf, hi]
  · rw [wsp, E.sp]; rfl
  · rw [wlr]; simp [ppOf]
  · have hres : pcResult s = Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r := rfl
    simp only [pcPost]
    rw [hres, wm, wo .r3 (by decide) (by decide) r3_cases, u3, hLe]
    refine ⟨small_setWidth (by have := status_le (Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r); omega_using [this]),
      ?_, ?_⟩
    · refine uo.trans ?_
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      refine congrArg (· :: []) (uu.trans ?_)
      rw [← hlen]
      generalize Spec.Ffdh.sievedParameterCandidate (ppOf s).bits (ppOf s).g (ppOf s).r = res
      rcases res with _ | ⟨_ | _, _⟩ <;> rfl

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
