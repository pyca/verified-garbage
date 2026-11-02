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

/-!
# A candidate on RISC-V: the working space's set-up

`setup_ok`: `setup` puts `w = out_len / 8` in `t0`, the arrays' size in
`s5` and array 0's address in `a7` (the round's context, `Env`), writes the
header's `scratch_len`, `w`, stride and the arrays' addresses (`Lay`), and
zeroes the first `nArr` arrays; it writes nothing else (`setupRanges`), and
keeps the body's state (`Ctx`).
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

end VG.Proof.RsaKeyGen.RISCV64.Cand
