module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Frame
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyBytes
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyLayout
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on RISC-V: `out` zeroed, and the ends

`zeroOut_ok`: `out`'s octets zeroed at the start, which gives the body's
state `Ctx` (`Fr`, and `out` still zero). The contract's results (`CQ`) at
each end: `fin_ok` through `finish k`, with `used` the octets read;
`finNone_post` through `finNone`, when `rand` is too short; `finPrime_post`
through `finPrime`, the probable prime `c` from array 0 of the working space
to `out`, most significant octet first.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Candidate (zeroOut finish finNone finPrime ldf stf oOut oOutLen oUsed oRead)

/-- `out_len`. -/
abbrev oL (s0 : State) : Nat := (s0.gpr .a1).toNat

/-- `rand_len`. -/
abbrev rL (s0 : State) : Nat := (stackArg s0 0).toNat

/-- What the call computes. -/
def cOp (s0 : State) : Option (Spec.RsaKeyGen.Candidate × Spec.RsaKeyGen.Rand) :=
  Spec.RsaKeyGen.candidateOp (oL s0) (Spec.Rsa.bytesAt s0.mem (s0.gpr .a3) (s0.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s0.mem (s0.gpr .a5) (s0.gpr .a6).toNat) (Spec.Rsa.bytesAt s0.mem (s0.gpr .a7) (rL s0))

/-- What `out` holds at the end. -/
def outOf (s0 : State) : List Byte :=
  match cOp s0 with
  | some (.prime c, _) => Spec.Rsa.i2osp c (oL s0)
  | _ => List.replicate (oL s0) 0

/-- What `used` holds at the end. -/
def usedOf (s0 : State) : Nat :=
  match cOp s0 with
  | some (_, rest) => rL s0 - rest.length
  | none => 0

/-- The contract's results. -/
def CQ (s0 : State) (r : BitVec 64) (m : Mem) : Prop :=
  r.toNat = Spec.RsaKeyGen.candidateStatus (cOp s0) ∧ Spec.Rsa.bytesAt m (s0.gpr .a0) (oL s0) = outOf s0 ∧
    Spec.Rsa.wordsAt m (s0.gpr .a2) 1 = [BitVec.ofNat 64 (usedOf s0)]

/-- The body's state, `out` still zero. -/
structure Ctx (s0 s : State) : Prop where
  fr : Fr s0 s
  zero : Spec.Rsa.bytesAt s.mem (s0.gpr .a0) (oL s0) = List.replicate (oL s0) 0

section
variable {s0 : State}

theorem oL_le (hp : CIn s0) : oL s0 ≤ 512 := hp.valid.2.1

/-- Octets survive what keeps their bytes. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {Ra : Addr} {rl : Nat} (hrl : rl < 2 ^ 64)
    (hd : ∀ ρ ∈ rs, (⟨Ra, rl⟩ : Region).Disjoint ρ) : Spec.Rsa.bytesAt m' Ra rl = Spec.Rsa.bytesAt m Ra rl := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact f _ fun ρ hρ => hd ρ hρ _ (Offset.contains_base Ra (by omega_arith) (by omega_arith))

/-- `Ctx` through code that keeps `Fr`'s registers and writes only `used`,
`scratch`, the round's frame and the octets read. -/
theorem Ctx.step {s t : State} (h : Ctx s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (s11 : t.gpr .s11 = s.gpr .s11) (f : Frame [cU s0, cS s0, rF s0, rdW s0] s.mem t.mem) : Ctx s0 t := by
  have hp := h.fr.pre
  refine ⟨h.fr.step sp rd wr s11 (f.mono (by simp)), ?_⟩
  rw [bytes_keep f (by have := oL_le hp; omega_arith) (fun ρ hρ => ?_), h.zero]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact hp.oU
  · exact hp.oS
  · exact (hp.Fo.sub_left (rF_sub s0)).symm
  · exact (hp.Fo.sub_left (fw_sub s0 (by decide))).symm

/-- `L` zero bytes from the frame's `oOut`, `L` its `oOutLen`. -/
theorem zeroOut_ok {s : State} (h : Fr s0 s) :
    WP isa zeroOut s fun t => Ctx s0 t ∧ Frame [cO s0] s.mem t.mem ∧ Keep [.t2, .t3, .t5] s t := by
  have hp := h.pre
  generalize hO : s0.gpr .a0 = O
  generalize hL : oL s0 = L
  have hL1 : 32 ≤ L := hL ▸ hp.valid.1
  have hL2 : L ≤ 512 := hL ▸ oL_le hp
  have hfo : O.toNat + L ≤ 2 ^ 64 := by rw [← hO, ← hL]; exact hp.fo
  have hOin : ∀ i < L, InRegions s.wr (off O i) 1 := fun i hi =>
    ⟨cO s0, by rw [h.wr, hp.wr]; simp, by
      show (⟨s0.gpr .a0, oL s0⟩ : Region).Contains _ _
      rw [hO, hL]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have eL : s0.gpr .a1 = BitVec.ofNat 64 L := by rw [← hL, oL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r104 : s.mem.readW (fb s0 + BitVec.ofNat 64 104) 64 = O := hO ▸ h.wOut
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 L := eL ▸ h.wOutLen
  suffices hz : WP isa zeroOut s fun t => Frame [cO s0] s.mem t.mem ∧ (∀ c < L, t.mem (off O c) = 0) ∧
      Keep [.t2, .t3, .t5] s t by
    refine WP.mono (WP.rdwr hz) fun t ⟨⟨fo, tz, tk⟩, _, _, tsp⟩ => ?_
    refine ⟨⟨h.step tsp tk.2.1 tk.2.2 (tk.1 _ (by decide)) (fo.mono (by simp)), ?_⟩, fo, tk⟩
    rw [hO, hL]
    unfold Spec.Rsa.bytesAt
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact tz i (List.mem_range.mp hi)
  rw [zeroOut, WP.seq_iff]
  have hb : WP isa (.block [ldf .t3 oOut, ldf .t5 oOutLen, .li .t2 0]) s fun u =>
      (u.gpr .t2 = 0 ∧ u.gpr .t3 = off O 0 ∧ u.gpr .t5 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
        Keep [.t2, .t3, .t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ldf, oOut, oOutLen, h.s11, al 104 (by decide), al 112 (by decide), inr 104 (by decide),
      inr 112 (by decide), r104, r112, fin64_exec_li_zero, add_ofNat_zero]
  refine WP.mono hb fun u ⟨⟨u2, u3, u5, um⟩, ku⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off O i ∧ t.gpr .t2 = 0 ∧ Outside O 0 i s.mem t.mem ∧ (∀ c < i, t.mem (off O c) = 0) ∧
      Keep [.t2, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .t2 .t3 0, .addi .t3 .t3 1] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t3, t2, tout, tz, tk⟩ _ => ?_)
    ⟨u3, u2, by rw [um]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), ku⟩ u5)
    fun t ⟨_, _, tout, tz, tk⟩ => ?_
  · have hst : WP isa (.block [.store .b .t2 .t3 0, .addi .t3 .t3 1, .addi .t5 .t5 (-1)]) t fun t' =>
        (t'.gpr .t3 = off O (i + 1) ∧ t'.gpr .t2 = 0 ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off O i) 1 0) ∧ Keep [.t3, .t5] t t' := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [t3, t2, (by rw [tk.2.2]; exact hOin i hi : InRegions t.wr (off O i) 1)]
      rfl
    refine WP.mono hst fun t' ⟨⟨l3, l2, l5, lm⟩, lk⟩ =>
      ⟨⟨l3, l2, ?_, ?_, Keep.trans' tk (lk.mono (by decide))⟩, l5⟩
    · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
      rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
        (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
    · have hw1 := write1_outside t.mem O (d := i) 0 (by omega_arith)
      intro c hc
      rw [lm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
      · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tz c hc
      · rw [write1_self]
  · refine ⟨fun x hx => tout x (Or.inr (by
      have := hx _ List.mem_cons_self
      simp only [Region.Contains, ofs, ← hO, ← hL, oL] at this ⊢
      omega_arith)), tz, tk⟩

/-! ## The ends -/

theorem wordsAt_one (m : Mem) (U : Addr) (v : BitVec 64) : Spec.Rsa.wordsAt (m.writeW U v) U 1 = [v] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    Mem.readW_writeW_self64]

/-- `finish r`: `used :=` the octets read, and the result `r`. -/
theorem finish_ok (r : Nat) {s : State} (h : Fr s0 s) (hr : r < 2048) :
    WP isa (finish r) s fun t =>
      (t.mem = s.mem.writeW (s0.gpr .a2) (s.mem.readW (fw s0 oRead) 64) ∧ t.gpr .a0 = BitVec.ofNat 64 r) ∧
        Keep [.t2, .t3, .a0] s t := by
  have hp := h.pre
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r120 : s.mem.readW (fb s0 + BitVec.ofNat 64 120) 64 = s0.gpr .a2 := h.wUsed
  have hU : InRegions s.wr (s0.gpr .a2) 8 := ⟨cU s0, by rw [h.wr, hp.wr]; simp, Region.contains_self _ _⟩
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [finish, ldf, oRead, oUsed, h.s11, al 176 (by decide), al 120 (by decide), inr 176 (by decide),
    inr 120 (by decide), r120, hp.alU, hU, add_ofNat_zero, hr]

theorem fin_ok (k : Nat) (hk : k < 2048) {u : State} (hc : Ctx s0 u)
    (hst : Spec.RsaKeyGen.candidateStatus (cOp s0) = k) (hout : outOf s0 = List.replicate (oL s0) 0)
    (hus : u.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (usedOf s0)) :
    WP isa (finish k) u fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hp := hc.fr.pre
  refine WP.mono (WP.rdwr (finish_ok k hc.fr hk)) fun t ⟨⟨⟨tm, t0⟩, kt⟩, _, _, tsp⟩ => ?_
  have fu : Frame [cU s0] u.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.fr.step tsp kt.2.1 kt.2.2 (kt.1 _ (by decide)) (fu.mono (by simp)), ?_, ?_, ?_⟩
  · rw [t0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), hst]
  · rw [bytes_keep fu (by have := oL_le hp; omega_arith) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU), hc.zero, hout]
  · rw [tm, hus]; exact wordsAt_one _ _ _

/-- The end through `finNone`, when `rand` is too short. -/
theorem finNone_post {u : State} (hc : Ctx s0 u) (hres : cOp s0 = none) :
    WP isa finNone u fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hp := hc.fr.pre
  rw [finNone, WP.seq_iff]
  refine WP.block_cons_iff.mpr ⟨_, fin64_exec_li_zero, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, Fr.store (s := u.write .t2 0) ⟨hp, hc.fr.sp, hc.fr.rd, hc.fr.wr,
    by rw [gpr_write_of_ne _ _ (by decide)]; exact hc.fr.s11, hc.fr.sv, hc.fr.args, hc.fr.rl, hc.fr.wl, hc.fr.out⟩
    (r := .t2) (o := oRead) (by decide) (by decide), WP.block_nil ?_⟩
  simp only [gpr_write_self, mem_write]
  have hc' : Ctx s0 { u.write .t2 0 with mem := u.mem.writeW (fw s0 oRead) 0 } :=
    hc.step rfl rfl rfl (by rw [gpr_write_of_ne _ _ (by decide)])
      ((Frame.refl _ _).writeW (r := rdW s0) (w := 64) (by simp) (0 : BitVec 64) (Region.contains_self _ _))
  refine fin_ok 0 (by decide) hc' (by rw [hres]; rfl) (by simp only [outOf, hres])
    (by show (u.mem.writeW _ _).readW _ 64 = _; rw [Mem.readW_writeW_self64, usedOf, hres]; rfl)

theorem byte_rt (x : BitVec (8 * 1)) : (x.setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega_arith

/-- `finPrime`'s copy: `out` the `L` bytes from `off B 256` reversed. -/
theorem copyOut_ok {s : State} {B O : Addr} {Z L : Nat} (h : Fr s0 s) (hs : Scr s B Z) (h7 : s.gpr .a7 = off B 256)
    (hO : s0.gpr .a0 = O) (hL : oL s0 = L) (hZ : 256 + L ≤ Z) (hd : (cO s0).Disjoint ⟨B, Z⟩) :
    WP isa (.seq (.block [ldf .t5 oOutLen, .add .t3 .a7 .t5, .addi .t3 .t3 (-1), ldf .t4 oOut])
      (VG.Impl.Bignum.RISCV64.countLoop .t5 [.load .b .t2 .t3 0, .store .b .t2 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1)])) s
      fun t => (∀ c < L, t.mem (off O c) = s.mem (off B (256 + (L - 1 - c)))) ∧ Outside O 0 L s.mem t.mem ∧
        Keep [.t2, .t3, .t4, .t5] s t := by
  have hp := h.pre
  have hL1 : 32 ≤ L := hL ▸ hp.valid.1
  have hL2 : L ≤ 512 := hL ▸ oL_le hp
  have hfo : O.toNat + L ≤ 2 ^ 64 := by rw [← hO, ← hL]; exact hp.fo
  have hnw := hs.nowrap
  have hOin : ∀ i < L, InRegions s.wr (off O i) 1 := fun i hi =>
    ⟨cO s0, by rw [h.wr, hp.wr]; simp, by
      show (⟨s0.gpr .a0, oL s0⟩ : Region).Contains _ _
      rw [hO, hL]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsep : ∀ i < L, ∀ x, ofs B x < Z → off O i ≠ x := fun i hi x hx e => by
    refine hd _ (by
      show (⟨s0.gpr .a0, oL s0⟩ : Region).Contains _ _
      rw [hO, hL]; exact Offset.contains_base _ (d := i) (by omega_arith) (by omega_arith)) ?_
    show Region.Contains _ (off O i) 1
    rw [e]; simp only [Region.Contains]; simp only [ofs] at hx; omega_arith
  have eL : s0.gpr .a1 = BitVec.ofNat 64 L := by rw [← hL, oL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have al : ∀ o, o % 8 = 0 → (fb s0 + BitVec.ofNat 64 o).toNat % 8 = 0 := fun o h8 => fw_al hp h8
  have inr : ∀ o, o + 8 ≤ 192 → InRegions (s.rd ++ s.wr) (fb s0 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨kF s0, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), kF_contains ho⟩
  have r104 : s.mem.readW (fb s0 + BitVec.ofNat 64 104) 64 = O := hO ▸ h.wOut
  have r112 : s.mem.readW (fb s0 + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 L := eL ▸ h.wOutLen
  rw [WP.seq_iff]
  have hb : WP isa (.block [ldf .t5 oOutLen, .add .t3 .a7 .t5, .addi .t3 .t3 (-1), ldf .t4 oOut]) s fun u =>
      (u.gpr .t3 = off B (256 + L - 1) ∧ u.gpr .t4 = off O 0 ∧ u.gpr .t5 = BitVec.ofNat 64 L ∧ u.mem = s.mem) ∧
        Keep [.t3, .t4, .t5] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [ldf, oOut, oOutLen, h.s11, al 104 (by decide), al 112 (by decide), inr 104 (by decide),
      inr 112 (by decide), r104, r112, h7, add_ofNat_zero]
    exact VG.Proof.Rsa.RISCV64.Keys.keys_sub1 _ (by omega_arith)
  refine WP.mono hb fun s₃ ⟨⟨j3, j4, j5, jm⟩, k₃⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (256 + L - 1 - i) ∧ t.gpr .t4 = off O i ∧ Outside O 0 i s.mem t.mem ∧
      (∀ c < i, t.mem (off O c) = s.mem (off B (256 + (L - 1 - c)))) ∧ Keep [.t2, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .t2 .t3 0, .store .b .t2 .t4 0, .addi .t4 .t4 1,
      .addi .t3 .t3 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := L)
    (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨t3, t4, tout, tb, tk⟩ _ => ?_)
    ⟨by rw [j3]; rfl, j4, by rw [jm]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k₃.mono (by decide)⟩ j5)
    fun t ⟨_, _, tout, tb, tk⟩ => ⟨tb, tout, tk⟩
  have hst : WP isa (.block [.load .b .t2 .t3 0, .store .b .t2 .t4 0, .addi .t4 .t4 1, .addi .t3 .t3 (-1),
      .addi .t5 .t5 (-1)]) t fun t' =>
        (t'.gpr .t3 = off B (256 + L - 1 - i) - BitVec.ofNat 64 1 ∧ t'.gpr .t4 = off O (i + 1) ∧
          t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem.write (off O i) 1 (t.mem.read (off B (256 + L - 1 - i)) 1)) ∧
        Keep [.t2, .t3, .t4, .t5] t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [t3, t4, (hs.congr tk.2.2).ld (d := 256 + L - 1 - i) (n := 1) (by omega_arith),
      (by rw [tk.2.2]; exact hOin i hi : InRegions t.wr (off O i) 1), byte_rt]
  refine WP.mono hst fun t' ⟨⟨l3, l4, l5, lm⟩, lk⟩ => ⟨⟨?_, l4, ?_, ?_, Keep.trans' tk lk⟩, l5⟩
  · rw [l3, VG.Proof.Rsa.RISCV64.Keys.keys_sub1 _ (by omega_arith), show 256 + L - 1 - i - 1 = 256 + L - 1 - (i + 1) by omega_arith]
  · have hw1 := write1_outside t.mem O (d := i) (t.mem.read (off B (256 + L - 1 - i)) 1) (by omega_arith)
    rw [lm]; exact (tout.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith)).trans
      (hw1.mono (o' := 0) (n' := i + 1) (by omega_arith) (by omega_arith))
  · have hw1 := write1_outside t.mem O (d := i) (t.mem.read (off B (256 + L - 1 - i)) 1) (by omega_arith)
    intro c hc
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb c hc
    · rw [write1_self]
      have ha : t.mem (off B (256 + L - 1 - c)) = s.mem (off B (256 + L - 1 - c)) := by
        refine tout _ (Or.inr ?_)
        by_contra hlt
        have hx : off O (ofs O (off B (256 + L - 1 - c))) = off B (256 + L - 1 - c) := by
          simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
        exact hsep _ (by omega_arith) _ (by rw [ofs_off0 B (by omega_arith)]; omega_arith) hx
      have r1 : ∀ (m : Mem) (a : Addr), m.read a 1 = m a := fun m a =>
        BitVec.eq_of_toNat_eq (by rw [read_toNat_succ]; simp [Mem.read])
      rw [r1, ha, show 256 + (L - 1 - c) = 256 + L - 1 - c by omega_arith]

/-- The end through `finPrime`: the probable prime `c`, of `w` words, from
array 0 to `out`. -/
theorem finPrime_post {u : State} {B : Addr} {Z w c : Nat} {rest : Spec.RsaKeyGen.Rand} (hc : Ctx s0 u)
    (hs : Scr u B Z) (h7 : u.gpr .a7 = off B 256) (hZ : 256 + oL s0 ≤ Z) (hw : oL s0 = 8 * w)
    (hd : (cO s0).Disjoint ⟨B, Z⟩) (hval : wordsVal u.mem B 256 w = c)
    (hres : cOp s0 = some (.prime c, rest)) (hus : u.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (rL s0 - rest.length)) :
    WP isa finPrime u fun t => Fr s0 t ∧ CQ s0 (t.gpr .a0) t.mem := by
  have hp := hc.fr.pre
  unfold finPrime
  have cp := copyOut_ok hc.fr hs h7 rfl rfl hZ hd
  rw [WP.seq_iff] at cp ⊢
  refine WP.mono (WP.rdwr cp) fun t₁ ⟨h₁, _, _, sp₁⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (WP.rdwr h₁) fun t₂ ⟨⟨hb, ho, k₂⟩, _, _, sp₂⟩ => ?_
  have fo : Frame [cO s0] u.mem t₂.mem := fun x hx => ho x (Or.inr (by
    have := hx _ List.mem_cons_self
    simp only [Region.Contains, ofs, oL] at this ⊢
    omega_arith))
  have f₂ : Fr s0 t₂ := hc.fr.step (sp₂.trans sp₁) k₂.2.1 k₂.2.2 (k₂.1 _ (by decide)) (fo.mono (by simp))
  have hus₂ : t₂.mem.readW (fw s0 oRead) 64 = BitVec.ofNat 64 (rL s0 - rest.length) := by
    rw [fo.readW (r := rdW s0) (Region.contains_self _ _) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ
      exact (hp.Fo.sub_left (fw_sub s0 (by decide)))) (by decide)]
    exact hus
  refine WP.mono (WP.rdwr (finish_ok 1 f₂ (by decide))) fun t ⟨⟨⟨tm, t0⟩, kt⟩, _, _, tsp⟩ => ?_
  have fu : Frame [cU s0] t₂.mem t.mem := by
    rw [tm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcw : c < 256 ^ oL s0 := by
    rw [← hval, hw, show (256 : Nat) ^ (8 * w) = 2 ^ (64 * w) by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega_arith]
    exact wordsVal_lt _ _ _ _
  have e0 : VG.Proof.Rsa.RISCV64.Keys.arr w 0 = 256 := by simp [VG.Proof.Rsa.RISCV64.Keys.arr, VG.Proof.Rsa.RISCV64.Keys.hdr, VG.Impl.Rsa.RISCV64.Keys.hdr]
  refine ⟨f₂.step tsp kt.2.1 kt.2.2 (kt.1 _ (by decide)) (fu.mono (by simp)), ?_, ?_, ?_⟩
  · rw [t0, hres]; rfl
  · rw [bytes_keep fu (by have := oL_le hp; omega_arith) (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ; exact hp.oU)]
    rw [VG.Proof.Rsa.RISCV64.Keys.bytes_of_store (w := w) (j := 0) (by omega_arith) (fun c' hc' => by rw [e0]; exact hb c' hc')]
    rw [outOf, hres]
    simp only [VG.Proof.Rsa.RISCV64.Keys.num, e0, hval, Nat.mod_eq_of_lt hcw]
  · rw [tm, hus₂, usedOf, hres]; exact wordsAt_one _ _ _

end

end VG.Proof.RsaKeyGen.RISCV64.Cand
