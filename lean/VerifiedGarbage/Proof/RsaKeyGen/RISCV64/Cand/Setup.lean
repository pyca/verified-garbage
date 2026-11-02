module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Fin
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Prep
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.RsaKeyGen.Bits

/-!
# A candidate on RISC-V: the working space's set-up

`setup_ok`: `setup` puts `w = out_len / 8` in `t0`, the arrays' size in
`s5` and array 0's address in `a7` (the round's context, `Env`), writes the
header's `scratch_len`, `w`, stride and the arrays' addresses (`Lay`), and
zeroes the first `nArr` arrays; it writes nothing else (`setupRanges`), and
keeps the body's state (`Ctx`).

`loadC_ok`: the first `8 w` octets of `rand` into array 0, most significant
first, its low bit and its two top bits set: array 0 holds
`RsaKeyGen.candidate (64 w) x`, and the octets read are `8 w`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Mont (off ofs word Outside Outs writeW_outside word_writeW_self)
open VG.Proof.MillerRabin.RISCV64 (Env)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (setup nArr ldf oWsLen oOutLen)
open VG.Proof.Mont (wordsVal)
open VG.Impl.MillerRabin.RISCV64.Search (sth hWsLen hW hStride)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The header the candidate's set-up writes: `scratch_len`, `w`, the
stride, and the addresses of arrays 0–7. -/
structure Lay (m : Mem) (B : Addr) (SL w : Nat) : Prop where
  len : word m B 0 = BitVec.ofNat 64 SL
  wW : word m B 48 = BitVec.ofNat 64 w
  strideW : word m B 224 = BitVec.ofNat 64 (8 * (w + 2))
  arrW : ∀ j < 8, word m B (8 * (8 + j)) = off B (slot w j)

/-- What changes through `setup`: the header's first 29 words and the arrays. -/
def setupRanges (w : Nat) : List (Nat × Nat) := [(0, 232), (256, nArr * (8 * (w + 2)))]

/-- `scratch_len`. -/
abbrev sL (s0 : State) : Nat := (stackArg s0 2).toNat

/-- The arrays' addresses into header words 8 to `8 + k`. -/
theorem hdrs_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h6 : s.gpr .s6 = B)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (hZ : 128 ≤ Z) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap (fun j => base .t2 j ++ [sth .t2 (8 + j)]))) s fun t =>
      ((∀ j < k, word t.mem B (8 * (8 + j)) = off B (slot w j)) ∧ Outside B 64 (8 * k) s.mem t.mem) ∧
        Keep [.t2] s t
  | 0, _ => WP.block_nil ⟨⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (hdrs_ok hs h6 h7 h5 hZ k (by omega_arith)) fun t ⟨⟨tw, tout⟩, tk⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (Pub.base_ok (rd := .t2) (by decide) ((tk.gpr (by decide)).trans h7)
      ((tk.gpr (by decide)).trans h5) k) fun u ⟨⟨u2, um⟩, uk⟩ => ?_
    have hs' := hs.congr (uk.2.2.trans tk.2.2)
    have h6' : u.gpr .s6 = B := (uk.gpr (by decide)).trans ((tk.gpr (by decide)).trans h6)
    refine WP.mono (WP.keep [] (Q := fun v => v.mem = u.mem.writeW (off B (8 * (8 + k))) (off B (slot w k)))
      (by brun [sth, h6', u2, (show 8 * (8 + k) < 2048 by omega_arith),
        hs'.st (d := 8 * (8 + k)) (n := 8) (by omega_arith), hs'.al8 (d := 8 * (8 + k)) (by omega_arith) (by omega_arith)])
      rfl rfl)
      fun v ⟨vm, vk⟩ => ⟨⟨fun j hj => ?_, ?_⟩, Keep.trans' (Keep.trans' tk uk) (vk.mono (by decide))⟩
    · rw [vm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [(writeW_outside u.mem B (d := 8 * (8 + k)) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
          um]
        exact tw j hj
      · exact word_writeW_self _ _ _ _
    · rw [vm, um]
      exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside t.mem B (d := 8 * (8 + k)) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The working space, from the contract. -/
theorem scr_of {s0 s : State} (h : Fr s0 s) : Scr s (stackArg s0 1) (8 * sL s0) := by
  have hp := h.pre
  have e : (⟨stackArg s0 1, 8 * sL s0⟩ : Region) = cS s0 := by simp only [cS, sL, Nat.mul_comm]
  exact Scr.of_mem (by rw [e, h.wr, hp.wr]; simp) (by have := hp.fS; simp only [sL]; omega_arith) hp.alS

theorem setup_ok' {s0 s : State} {w : Nat} (hc : Ctx s0 s) (h6 : s.gpr .s6 = stackArg s0 1)
    (hw : oL s0 = 8 * w) :
    WP isa setup s fun t =>
      (Env t (stackArg s0 1) (8 * sL s0) w ∧ Lay t.mem (stackArg s0 1) (sL s0) w ∧
        (∀ i < nArr * (w + 2), word t.mem (stackArg s0 1) (256 + 8 * i) = 0) ∧
        Outs (stackArg s0 1) (setupRanges w) s.mem t.mem) ∧
        Keep [.t0, .t2, .t3, .t5, .s5, .a7] s t := by
  have hp := hc.fr.pre
  have h := hc.fr
  generalize hB : stackArg s0 1 = B at h6
  generalize hSL : sL s0 = SL
  have hs : Scr s B (8 * SL) := hB ▸ hSL ▸ scr_of h
  have hnw := hs.nowrap
  have hw' : (s0.gpr .a1).toNat = 8 * w := hw
  have hSL' : (stackArg s0 2).toNat = SL := hSL
  have hw4 : 4 ≤ w := by have := hp.valid.1; omega_arith
  have hw64 : w ≤ 64 := by have := oL_le hp; simp only [oL] at this; omega_arith
  have hsc : 16 * (8 * w) + 32 ≤ SL := by
    have := hp.scr; simp only [Spec.Rsa.scratchWords] at this; omega_arith
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 35 * (8 * (w + 2)) ≤ 8 * SL := by omega_arith
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r184 : s.mem.readW (fb s0 + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 SL := by
    rw [show fb s0 + BitVec.ofNat 64 184 = fw s0 oWsLen from rfl, h.wl, ← hSL, sL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (8 * w) := by
    rw [show fb s0 + BitVec.ofNat 64 112 = fw s0 oOutLen from rfl, h.wOutLen, ← hw, oL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  unfold setup
  rw [WP.seq_iff, WP.block_append_iff, WP.block_append_iff]
  -- the header's lengths and stride
  have hA : WP isa (.block [ldf .t2 oWsLen, sth .t2 hWsLen, ldf .t2 oOutLen, .shift .srl .d .t0 .t2 3, sth .t0 hW,
      .addi .s5 .t0 2, .shift .sll .d .s5 .s5 3, sth .s5 hStride, .addi .a7 .s6 VG.Impl.Bignum.hdrBytes]) s fun t =>
      (t.mem = ((s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).writeW (off B 48) (BitVec.ofNat 64 w)).writeW
          (off B 224) (BitVec.ofNat 64 (8 * (w + 2))) ∧ t.gpr .a7 = off B (slot w 0) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .t0 = BitVec.ofNat 64 w ∧ t.gpr .s6 = B) ∧
        Keep [.t0, .t2, .s5, .a7] s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have e3 : BitVec.ofNat 64 (8 * w) >>> 3 = BitVec.ofNat 64 w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith
    have e5 : (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 3 = BitVec.ofNat 64 (8 * (w + 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      omega_arith
    have r112' : (s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).readW (fb s0 + 112#64) 64 =
        BitVec.ofNat 64 (8 * w) := by
      rw [← r112]
      refine ((Frame.refl [cS s0] s.mem).writeW (r := cS s0) List.mem_cons_self _ ?_).readW (r := ⟨fw s0 112, 8⟩)
        (Region.contains_self _ _) (fun ρ hρ => ?_) (by decide)
      · have hc0 := Offset.contains_base (stackArg s0 1) (d := 0) (n := 8) (k := (stackArg s0 2).toNat * 8)
          (by omega_arith) (by decide)
        rw [← hB]; exact hc0
      · simp only [List.mem_singleton] at hρ; subst hρ; exact hp.FS.sub_left (fw_sub s0 (by decide))
    brun [ldf, sth, oWsLen, oOutLen, hWsLen, hW, hStride, h.s11, r112', al 184 (by decide), al 112 (by decide),
      inr 184 (by decide), inr 112 (by decide), r184, r112, h6, e3, e5, hs.st (d := 0) (n := 8) (by omega_arith),
      hs.st (d := 48) (n := 8) (by omega_arith), hs.st (d := 224) (n := 8) (by omega_arith),
      hs.al8 (d := 0) (by omega_arith) (by decide), hs.al8 (d := 48) (by omega_arith) (by decide),
      hs.al8 (d := 224) (by omega_arith) (by decide), (show VG.Impl.Bignum.hdrBytes < 2048 by decide)]
    simp [slot, VG.Impl.Bignum.hdrBytes]
  refine WP.mono hA fun t₁ ⟨⟨m₁, a7, a5, a0, a6⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (hdrs_ok hs₁ a6 a7 a5 (by omega_arith) 8 (Nat.le_refl _)) fun t₂ ⟨⟨hw₂, out₂⟩, k₂⟩ => ?_
  have k12 := Keep.trans' k₁ (k₂.mono (by decide))
  have hs₂ := hs.congr k12.2.2
  have b7 : t₂.gpr .a7 = off B (slot w 0) := (k₂.gpr (by decide)).trans a7
  have b5 : t₂.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k₂.gpr (by decide)).trans a5
  have hC : WP isa (.block [.addi .t3 .a7 0, .li .t5 nArr, .mul .t5 .t5 .s5, .shift .srl .d .t5 .t5 3, .li .t2 0])
      t₂ fun t =>
      (t.mem = t₂.mem ∧ t.gpr .t3 = off B 256 ∧ t.gpr .t5 = BitVec.ofNat 64 (35 * (w + 2)) ∧ t.gpr .t2 = 0) ∧
        Keep [.t2, .t3, .t5] t₂ t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have e17 : (BitVec.ofNat 64 35 * BitVec.ofNat 64 (8 * (w + 2))) >>> 3 = BitVec.ofNat 64 (35 * (w + 2)) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : 8 * (w + 2) < 2 ^ 64 := by omega_arith
      have h2 : 35 * (8 * (w + 2)) < 2 ^ 64 := by omega_arith
      have h3 : 35 * (w + 2) < 2 ^ 64 := by omega_arith
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show 35 < 2 ^ 64 by decide), Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
      omega_arith
    brun [b7, b5, e17, nArr, fin64_exec_li_zero, add_ofNat_zero]
    simp [slot, VG.Impl.Bignum.hdrBytes]
  refine WP.mono hC fun t₃ ⟨⟨m₃, c3, c5, c2⟩, k₃⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (256 + 8 * i) ∧ t.gpr .t2 = 0 ∧ Outside B 256 (8 * i) t₃.mem t.mem ∧
      (∀ k < i, word t.mem B (256 + 8 * k) = 0) ∧ Keep [.t2, .t3, .t5] t₃ t
  refine WP.mono (wp_countdown (body := .block ([.store .d .t2 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := 35 * (w + 2)) (by omega_arith)
      (by omega_arith) Inv (fun i hi t ⟨j3, j2, jout, jz, jk⟩ _ => ?_)
      ⟨by rw [c3], c2, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), Keep.refl _ _⟩ c5)
    fun t ⟨_, _, tout, tz, tk⟩ => ?_
  · have hst : WP isa (.block [.store .d .t2 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t fun t' =>
        (t'.gpr .t3 = off B (256 + 8 * (i + 1)) ∧ t'.gpr .t2 = 0 ∧
          t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.writeW (off B (256 + 8 * i)) (0 : BitVec 64)) ∧ Keep [.t3, .t5] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      have hs₃ := (hs₂.congr k₃.2.2).congr jk.2.2
      brun [j3, j2, hs₃.st (d := 256 + 8 * i) (n := 8) (by omega_arith),
        hs₃.al8 (d := 256 + 8 * i) (by omega_arith) (by omega_arith), add_ofNat_zero]
      rw [show 256 + 8 * (i + 1) = 256 + 8 * i + 8 by omega_arith]
    refine WP.mono hst fun t' ⟨⟨l3, l2, l5, lm⟩, lk⟩ => ⟨⟨l3, l2, ?_, ?_, Keep.trans' jk (lk.mono (by decide))⟩, l5⟩
    · have hw := writeW_outside t.mem B (d := 256 + 8 * i) 0 (by omega_arith)
      rw [lm]
      exact (jout.mono (o' := 256) (n' := 8 * (i + 1)) (Nat.le_refl _) (by omega_arith)).trans
        (hw.mono (o' := 256) (n' := 8 * (i + 1)) (by omega_arith) (by omega_arith))
    · have hw := writeW_outside t.mem B (d := 256 + 8 * i) 0 (by omega_arith)
      intro k hk
      rw [lm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [hw.word (by omega_arith) (by omega_arith)]; exact jz k hk
      · exact word_writeW_self _ _ _ _
  · have K : Keep [.t0, .t2, .t3, .t5, .s5, .a7] s t :=
      Keep.trans' (Keep.trans' (k12.mono (by decide)) (k₃.mono (by decide))) (tk.mono (by decide))
    have e7 : t.gpr .a7 = off B (slot w 0) := (tk.gpr (by decide)).trans ((k₃.gpr (by decide)).trans b7)
    have e5 : t.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) :=
      (tk.gpr (by decide)).trans ((k₃.gpr (by decide)).trans b5)
    have e0 : t.gpr .t0 = BitVec.ofNat 64 w :=
      (tk.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans a0))
    have e6 : t.gpr .s6 = B :=
      (tk.gpr (by decide)).trans ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans a6))
    -- Memory below the arrays is as after the header.
    have lo : ∀ d, d + 8 ≤ 256 → word t.mem B d = word t₂.mem B d := fun d hd => by
      rw [tout.word (by omega_arith) (by omega_arith), m₃]
    have lo1 : ∀ d, d + 8 ≤ 64 ∨ 128 ≤ d → d + 8 ≤ 256 → word t.mem B d = word t₁.mem B d := fun d hd hd' => by
      rw [lo d hd', out₂.word (by omega_arith) (by omega_arith)]
    have hO : Outs B (setupRanges w) s.mem t.mem := by
      intro x hx
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      rw [tout x (by simp only [nArr] at hx; omega_arith), m₃, out₂ x (by omega_arith), m₁]
      have w1 := writeW_outside s.mem B (d := 0) (BitVec.ofNat 64 SL) (by omega_arith)
      have w2 := writeW_outside (s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)) B (d := 48) (BitVec.ofNat 64 w)
        (by omega_arith)
      have w3 := writeW_outside ((s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).writeW (off B 48)
        (BitVec.ofNat 64 w)) B (d := 224) (BitVec.ofNat 64 (8 * (w + 2))) (by omega_arith)
      rw [w3 x (by omega_arith), w2 x (by omega_arith), w1 x (by omega_arith)]
    refine ⟨⟨⟨hs.congr K.2.2,
      e7, e5, e0, e6, hw4, by omega_arith, by rw [es]; omega_arith⟩, ⟨?_, ?_, ?_, fun j hj => ?_⟩, tz, hO⟩, K⟩
    · rw [lo1 0 (by omega_arith) (by omega_arith), m₁]
      rw [(writeW_outside _ B (d := 224) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        (writeW_outside _ B (d := 48) _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
      exact word_writeW_self _ _ _ _
    · rw [lo1 48 (by omega_arith) (by omega_arith), m₁]
      rw [(writeW_outside _ B (d := 224) _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
      exact word_writeW_self _ _ _ _
    · rw [lo1 224 (by omega_arith) (by omega_arith), m₁]
      exact word_writeW_self _ _ _ _
    · rw [lo _ (by omega_arith)]; exact hw₂ j hj

/-- `setup`, keeping the body's state. -/
theorem setup_ok {s0 s : State} {w : Nat} (hc : Ctx s0 s) (h6 : s.gpr .s6 = stackArg s0 1) (hw : oL s0 = 8 * w) :
    WP isa setup s fun t =>
      (Ctx s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) w ∧ Lay t.mem (stackArg s0 1) (sL s0) w ∧
        (∀ i < nArr * (w + 2), word t.mem (stackArg s0 1) (256 + 8 * i) = 0) ∧
        Outs (stackArg s0 1) (setupRanges w) s.mem t.mem) ∧
        Keep [.t0, .t2, .t3, .t5, .s5, .a7] s t := by
  have hp := hc.fr.pre
  refine WP.mono (WP.rdwr (setup_ok' hc h6 hw)) fun t ⟨⟨⟨he, hl, hz, hO⟩, K⟩, _, _, tsp⟩ => ?_
  have hsc : 16 * oL s0 + 32 ≤ sL s0 := by have := hp.scr; simp only [Spec.Rsa.scratchWords] at this; exact this
  have hw' : (s0.gpr .a1).toNat = 8 * w := hw
  have hw4 : 32 ≤ (s0.gpr .a1).toNat := hp.valid.1
  have fS : Frame [cS s0] s.mem t.mem := fun x hx => hO x fun r hr => .inr (by
    have := hx _ List.mem_cons_self
    simp only [Region.Contains] at this
    simp only [setupRanges, nArr, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [ofs, sL] at this hsc ⊢
    rcases hr with rfl | rfl <;> dsimp only <;> omega_arith)
  exact ⟨⟨hc.step tsp K.2.1 K.2.2 (K.gpr (by decide)) (fS.mono (by simp)), he, hl, hz, hO⟩, K⟩


/-! ## Drawing the candidate -/

open VG.Proof.MillerRabin.RISCV64 (A)
open VG.Impl.RsaKeyGen.RISCV64.Candidate (loadC stf oRand oRead)

/-- What changes within `scratch` changes nothing outside it. -/
theorem out_frame {s0 : State} {m m' : Mem} {d n : Nat} (hdn : d + n ≤ 8 * sL s0)
    (o : Outside (stackArg s0 1) d n m m') : Frame [cS s0] m m' := fun x hx => o x (.inr (by
  have := hx _ List.mem_cons_self
  simp only [Region.Contains, sL, ofs] at this hdn ⊢
  omega_arith))

/-- A number of words of `scratch` survives what changes only regions apart
from it. -/
theorem wordsVal_frame {rs : List Region} {m m' : Mem} (f : Frame rs m m') {B : Addr} {Z : Nat}
    (hn : B.toNat + Z ≤ 2 ^ 64) (hd : ∀ ρ ∈ rs, (⟨B, Z⟩ : Region).Disjoint ρ) :
    ∀ k d, d + 8 * k ≤ Z → wordsVal m' B d k = wordsVal m B d k
  | 0, _, _ => rfl
  | k + 1, d, hk => by
    rw [wordsVal, wordsVal, wordsVal_frame f hn hd k (d + 8) (by omega_arith)]
    congr 2
    exact f.readW (r := ⟨B, Z⟩) (Offset.contains_base B (by omega_arith) (by omega_arith)) hd (by decide)

/-- The registers `loadC` writes. -/
def lcRegs : List Reg := [.s7, .s8, .a0, .s0, .t2, .t3, .t4, .t5]

theorem top2_eq : (BitVec.ofNat 64 3 <<< 62 : BitVec 64) = BitVec.ofNat 64 (3 * 2 ^ 62) := by decide

/-- `loadC`: the candidate from `rand`'s first `8 w` octets into array 0. -/
theorem loadC_ok {s0 s : State} {w : Nat} (hc : Ctx s0 s) (h : Env s (stackArg s0 1) (8 * sL s0) w)
    (hw : oL s0 = 8 * w) (hrl : oL s0 ≤ rL s0) :
    WP isa loadC s fun t =>
      (Ctx s0 t ∧ Env t (stackArg s0 1) (8 * sL s0) w ∧
        A t.mem (stackArg s0 1) w 0 = Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (8 * w))) ∧
        t.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (8 * w) ∧
        ∀ d, d + 8 ≤ 8 * sL s0 → (d + 8 ≤ slot w 0 ∨ slot w 0 + 8 * w ≤ d) →
          word t.mem (stackArg s0 1) d = word s.mem (stackArg s0 1) d) ∧ Keep lcRegs s t := by
  have hp := hc.fr.pre
  have hf := hc.fr
  generalize hB : stackArg s0 1 = B at h ⊢
  generalize hZ : 8 * sL s0 = Z at h ⊢
  generalize hR : s0.gpr .a7 = R
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have h0 : slot w 0 = 256 := by rw [es, Nat.zero_mul, Nat.add_zero]
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ Z := by rw [← es]; exact h.hZ
  have hw' : (s0.gpr .a1) = BitVec.ofNat 64 (8 * w) := by
    rw [← hw, oL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r160 : s.mem.readW (fb s0 + BitVec.ofNat 64 160) 64 = R := hR ▸ hf.wRand
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (8 * w) := hw' ▸ hf.wOutLen
  -- `rand`'s octets are readable, and apart from `scratch`.
  have hfr : R.toNat + rL s0 ≤ 2 ^ 64 := by rw [← hR]; exact hp.fr
  have cRc : ∀ i < 8 * w, (cR s0).Contains (off R i) 1 := fun i hi => by
    show (⟨s0.gpr .a7, (stackArg s0 0).toNat⟩ : Region).Contains _ _
    rw [hR]; exact Offset.contains_base _ (by simp only [rL] at hrl; omega_arith) (by omega_arith)
  have hN : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off R i) 1 := fun i hi =>
    ⟨cR s0, List.mem_append_left _ (by rw [hf.rd]; exact hp.rR), cRc i hi⟩
  have hsep : ∀ i < 8 * w, ∀ x, ofs B x < Z → off R i ≠ x := fun i hi x hx he => by
    refine hp.rS _ (cRc i hi) ?_
    rw [he]
    simp only [Region.Contains, ← hB, ofs] at hx ⊢
    rw [← hZ] at hx; simp only [sL] at hx; omega_arith
  have hbytes : Spec.Rsa.bytesAt s.mem R (8 * w) = Spec.Rsa.bytesAt s0.mem R (8 * w) := by
    refine bytes_keep hf.out (by omega_arith) fun ρ hρ => ?_
    have hsub : Region.Sub ⟨R, 8 * w⟩ (cR s0) := by
      show Region.Sub _ ⟨s0.gpr .a7, _⟩
      rw [hR]; intro x hx; simp only [Region.Contains, rL] at hx hrl ⊢; omega_arith
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact (hp.oR.symm).sub_left hsub
    · exact (hp.uR.symm).sub_left hsub
    · exact hp.rS.sub_left hsub
    · exact (hp.Fr.symm).sub_left hsub
  unfold loadC
  refine WP.seq ?_
  have hpre : WP isa (.block [ldf .s7 oRand, ldf .s8 oOutLen]) s fun u =>
      (u.gpr .s7 = off R 0 ∧ u.gpr .s8 = BitVec.ofNat 64 (8 * w) ∧ u.mem = s.mem) ∧ Keep [.s7, .s8] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ldf, oRand, oOutLen, hf.s11, al 160 (by decide), al 112 (by decide), inr 160 (by decide),
      inr 112 (by decide), r160, r112]
    exact (BitVec.add_zero _).symm
  refine WP.mono (WP.rdwr hpre) fun u ⟨⟨⟨u7, u8, um⟩, ku⟩, urd, uwr, usp⟩ => ?_
  have eu := h.keep ku (by decide)
  refine WP.seq (WP.mono (WP.rdwr (loadN_ok (dA := slot w 0) eu.hs eu.a7 u7 u8 eu.t0 (by omega_arith)
    (Nat.le_refl _) (by omega_arith) (by rw [h0]; decide) (by rw [h0]) (by rw [h0]; omega_arith)
    (fun i hi => by rw [ku.2.1, ku.2.2]; exact hN i hi) hsep))
    fun v ⟨⟨vv, vout, kv⟩, vrd, vwr, vsp⟩ => ?_)
  rw [um] at vv vout
  have ev := eu.keep kv (by decide)
  have hsv := ev.hs
  -- The candidate's bits.
  have e5 : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_arith
  have e6 : BitVec.ofNat 64 (8 * w) + off B (slot w 0) - BitVec.ofNat 64 8 = off B (slot w 0 + 8 * (w - 1)) := by
    rw [BitVec.add_comm, off_add, off_sub _ (show 8 ≤ slot w 0 + 8 * w by omega_arith),
      show slot w 0 + 8 * w - 8 = slot w 0 + 8 * (w - 1) by omega_arith]
  have sepW : ∀ (m : Mem) (x : BitVec 64), (m.writeW (off B (slot w 0)) x).readW
      (off B (slot w 0 + 8 * (w - 1))) 64 = m.readW (off B (slot w 0 + 8 * (w - 1))) 64 := fun m x =>
    Mem.readW_writeW_sep (Offset.sep B (d := slot w 0 + 8 * (w - 1)) (n := 8) (e := slot w 0) (k := 8)
      (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
  have a0 := ev.al 0 0
  have at' := ev.al 0 (w - 1)
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  generalize hX0 : word v.mem B (slot w 0) ||| BitVec.ofNat 64 1 = X0
  generalize hXt : word v.mem B (slot w 0 + 8 * (w - 1)) ||| BitVec.ofNat 64 (3 * 2 ^ 62) = Xt
  have hA : WP isa (.block [.load .d .t2 .a7 0, .logicImm .or .t2 .t2 1, .store .d .t2 .a7 0,
      .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t2 .t3 0, .li .t4 3,
      .shift .sll .d .t4 .t4 62, .logic .or .t2 .t2 .t4, .store .d .t2 .t3 0]) v fun t =>
      t.mem = (v.mem.writeW (off B (slot w 0)) X0).writeW (off B (slot w 0 + 8 * (w - 1))) Xt ∧
        Keep [.t2, .t3, .t4] v t := by
    refine WP.keep [.t2, .t3, .t4] (Q := fun t => t.mem = (v.mem.writeW (off B (slot w 0)) X0).writeW
      (off B (slot w 0 + 8 * (w - 1))) Xt) ?_ (by rfl) (by rfl)
    brun [ev.a7, ev.t0, e5, e6, sepW, top2_eq, hsv.ld (show slot w 0 + 8 ≤ Z by omega_arith),
      hsv.st (d := slot w 0) (n := 8) (by omega_arith), hsv.al8 (show slot w 0 + 8 ≤ Z by omega_arith) a0,
      hsv.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith),
      hsv.st (d := slot w 0 + 8 * (w - 1)) (n := 8) (by omega_arith),
      hsv.al8 (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega_arith) at', BitVec.add_zero, exec_li, ← hX0, ← hXt]
  show WP isa (.block (([.load .d .t2 .a7 0, .logicImm .or .t2 .t2 1, .store .d .t2 .a7 0,
      .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t2 .t3 0, .li .t4 3,
      .shift .sll .d .t4 .t4 62, .logic .or .t2 .t2 .t4, .store .d .t2 .t3 0] : List Instr) ++
      ([ldf .t2 oOutLen, stf .t2 oRead] : List Instr))) v _
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr hA) fun t₁ ⟨⟨m₁, k₁⟩, rd₁, wr₁, sp₁⟩ => ?_
  -- What changed is in `scratch`.
  have o1 := writeW_outside v.mem B (d := slot w 0) X0 (by omega_arith)
  have o2 := writeW_outside (v.mem.writeW (off B (slot w 0)) X0) B (d := slot w 0 + 8 * (w - 1)) Xt
    (by omega_arith)
  have hout₁ : Outside B (slot w 0) (8 * w) s.mem t₁.mem := by
    rw [m₁]; exact (vout.trans (o1.mono (by omega_arith) (by omega_arith))).trans (o2.mono (by omega_arith)
      (by omega_arith))
  have fS : Frame [cS s0] s.mem t₁.mem := out_frame (d := slot w 0) (n := 8 * w)
    (by rw [hZ]; omega_arith) (hB ▸ hout₁)
  have K₁ : Keep lcRegs s t₁ := Keep.trans' (Keep.trans' (ku.mono (by decide)) (kv.mono (by decide)))
    (k₁.mono (by decide))
  have hc₁ : Ctx s0 t₁ := hc.step (sp₁.trans (vsp.trans usp)) (rd₁.trans (vrd.trans urd))
    (wr₁.trans (vwr.trans uwr)) (K₁.gpr (by decide)) (fS.mono (by simp))
  have hf₁ := hc₁.fr
  have r112' : t₁.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (8 * w) := hw' ▸ hf₁.wOutLen
  have inr₁ : ∀ o, o + 8 ≤ 192 → InRegions (t₁.rd ++ t₁.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [hf₁.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have inw₁ : InRegions t₁.wr (fb s0 + BitVec.ofNat 64 176) 8 :=
    ⟨kF s0, by rw [hf₁.wr]; exact List.mem_cons_self, kF_contains (by decide)⟩
  have hB2 : WP isa (.block [ldf .t2 oOutLen, stf .t2 oRead]) t₁ fun t =>
      t.mem = t₁.mem.writeW (fw s0 oRead) (BitVec.ofNat 64 (8 * w)) ∧ Keep [.t2] t₁ t := by
    refine WP.keep [.t2] (Q := fun t => t.mem = t₁.mem.writeW (fw s0 oRead) (BitVec.ofNat 64 (8 * w))) ?_
      (by rfl) (by rfl)
    brun [ldf, stf, oOutLen, oRead, hf₁.s11, al 112 (by decide), al 176 (by decide), inr₁ 112 (by decide),
      inw₁, r112']
  refine WP.mono (WP.rdwr hB2) fun t ⟨⟨tm, kt⟩, rdt, wrt, spt⟩ => ?_
  have fR : Frame [rdW s0] t₁.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (r := rdW s0) (w := 64) (by simp) _ (Region.contains_self _ _)
  have hct : Ctx s0 t := hc₁.step spt rdt wrt (kt.gpr (by decide)) (fR.mono (by simp))
  have dS : ∀ ρ ∈ [rdW s0], (⟨B, Z⟩ : Region).Disjoint ρ := fun ρ hρ => by
    simp only [List.mem_singleton] at hρ; subst hρ
    have e : (⟨B, Z⟩ : Region) = cS s0 := by rw [← hB, ← hZ]; simp only [cS, sL, Nat.mul_comm]
    rw [e]; exact (hp.FS.symm).sub_right (fw_sub s0 (by decide))
  have hword : ∀ d, d + 8 ≤ Z → word t.mem B d = word t₁.mem B d := fun d hd =>
    fR.readW (r := ⟨B, Z⟩) (Offset.contains_base B (by omega_arith) (by omega_arith)) dS (by decide)
  have kvt : Keep [.t2, .t3, .t4] v t := Keep.trans' k₁ (kt.mono (by decide))
  refine ⟨⟨hct, ev.keep kvt (by decide), ?_, ?_, fun d hd hd' => ?_⟩, Keep.trans' K₁ (kt.mono (by decide))⟩
  · -- The candidate.
    have hA1 : A t.mem B w 0 = A t₁.mem B w 0 :=
      wordsVal_frame fR hnw dS w (slot w 0) (by omega_arith)
    have sep : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ Z → e + 8 ≤ Z → ∀ (m : Mem) (x : BitVec 64),
        (m.writeW (off B e) x).readW (off B d) 64 = m.readW (off B d) 64 := fun d e h1 h2 h3 m x =>
      Mem.readW_writeW_sep (Offset.sep B h1 (by omega_arith) (by omega_arith)) (by decide)
    rw [hA1, A, Pre.wordsVal_eq_wv, VG.Proof.RsaKeyGen.wv_candidate (m := v.mem) (by omega_arith) ?_ ?_ ?_,
      ← Pre.wordsVal_eq_wv, vv, hbytes]
    · show t₁.mem.readW _ 64 = _
      rw [m₁, sep _ _ (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self64, ← hX0]; rfl
    · show t₁.mem.readW _ 64 = _
      rw [m₁, Mem.readW_writeW_self64, ← hXt]
    · intro j hj0 hj
      show t₁.mem.readW _ 64 = v.mem.readW _ 64
      rw [m₁, sep _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [tm]; exact Mem.readW_writeW_self64 _ _ _
  · rw [hword d hd, hout₁.word (by omega_arith) (by omega_arith)]

end VG.Proof.RsaKeyGen.RISCV64.Cand
