module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Base
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env3
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvMid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Env2

/-!
# `vg_rsa_keygen_key` on PPC64LE: the working space, the inputs and the constants

`setup_ok`: `w = p_len / 2` and the stride, and every array zeroed.
`loads_ok`: `p`, `q` and `e` read. `consts_ok`: 1, 2, 3, `2^(32 w - 1)`,
`2^(8 p_len) + 1` and `2^33`. `init_ok`: the three, in the environment the
body's phases work in (`KS`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs half aZero)
open VG.Impl.RsaKeyGen.PPC64LE.Key (setup loads consts nArr aOne aTwo aThree aTop aC aC33 aE aP0 aQ0 aDv)
open VG.Impl.RsaKeyGen.PPC64LE.Key (setDigit)
open VG.Impl.Rsa.PPC64LE.CrtValues (load)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot ranges)
open VG.Proof.Rsa.PPC64LE.CrtValues (past_of_disjoint mv2_ok val32_of_zero ofNat_toNat64 ofNat_stride)

/-- The inputs, from the caller's memory. -/
abbrev pIn (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kL s0))
abbrev qIn (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r9) (kL s0))
abbrev eIn (s0 : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (PPC64LE.stackArg s0 6) (PPC64LE.stackArg s0 7).toNat)

theorem pre_ws {s0 : State} (h : keyP.pre s0) :
    arr (kW s0) nArr ≤ kZ s0 ∧ 16 ≤ kW s0 ∧ kW s0 ≤ 256 ∧ kL s0 = 2 * kW s0 ∧ kL s0 % 4 = 0 := by
  have p := kpre h
  have := p.sl; have := p.l1; have := p.l2; have := p.l8
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr, kW] at *
  omega

/-- A step that writes only the arrays and the slots keeps `Base`. -/
theorem Base.of_kk {s0 s t : State} (h : Base s0 s) (k : KK (kB s0) (kW s0) s.mem t.mem) (sp : t.sp = s.sp)
    (lr : t.lr = s.lr) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  have p := kpre h.pre
  have nw := p.wS
  obtain ⟨fits, -, -, -⟩ := pre_ws h.pre
  have hjs : ∀ j ∈ allArrs, j < nArr := fun j hj => List.mem_range.mp hj
  have hds : ∀ d ∈ allSlots, 112 ≤ d ∧ d + 4 ≤ 160 := by decide
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]
    exact k.out (Z := kZ s0) (fun j hj => Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (hjs j hj)) fits)
      (fun d hd => by have := hds d hd; have : 160 ≤ kZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits; omega) hx
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine k _ fun r hr => ?_
    have h160 : 160 ≤ kZ s0 := Nat.le_trans (Nat.le_add_right _ _) fits
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega)]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, -, rfl⟩ | ⟨d, hd, rfl⟩
    · left; simp only [arr, VG.Proof.Rsa.KeyWorkspace.hdr]; omega
    · left; have := hds d hd; dsimp only; omega

/-- `Base` through a phase of the body. -/
theorem Base.of_phase {s0 s t : State} (h : Base s0 s) (k : KK (kB s0) (kW s0) s.mem t.mem) {rs : List Reg}
    (kr : Keep rs s t) (hr : .r31 ∉ rs := by decide) : Base s0 t :=
  h.of_kk k kr.sp kr.lr kr.rd kr.wr (kr.gpr _ hr)

/-- A step that writes only bytes from 160 on, within the working space, keeps `Base`. -/
theorem Base.of_outside {s0 s t : State} (h : Base s0 s) {n : Nat}
    (o : Outside (kB s0) 160 n s.mem t.mem) (hn : 160 + n ≤ kZ s0) (sp : t.sp = s.sp) (lr : t.lr = s.lr)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (r31 : t.gpr .r31 = s.gpr .r31) : Base s0 t := by
  have nw := (kpre h.pre).wS
  refine ⟨h.pre, sp.trans h.sp, lr.trans h.lr, rd.trans h.rd, wr.trans h.wr, fun x hx => ?_,
    fun i hi => ?_, r31.trans h.r31⟩
  · rw [← h.frame x hx]; exact o x (Or.inr (by omega))
  · rw [← h.hdr i hi]
    refine Mem.readW_congr fun b hb => ?_
    rw [off, Offset.add_add]
    refine o _ (Or.inl ?_)
    rw [ofs, Mem.sub_ofNat_toNat _ (by omega)]
    omega

theorem ofNat_shr1 (x : BitVec 64) : x >>> 1 = BitVec.ofNat 64 (x.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem ofNat_digits60 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 60 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (60 * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S]
  rw [Nat.mod_eq_of_lt (show 60 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 60 * (w + 2) < 2 ^ 64 by omega)]
  omega

theorem zero_bounds {w Z : Nat} (f : arr w nArr ≤ Z) (hw : w ≤ 256) :
    160 + 4 * (nArr * (w + 2)) ≤ Z ∧ 1 ≤ nArr * (w + 2) ∧ nArr * (w + 2) < 2 ^ 32 := by
  simp only [arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr] at f ⊢
  omega

/-- `setup`: `w` and the stride, and every array 0: the environment of zeros. -/
theorem setup_ok {s0 s : State} (h : Base s0 s) (h22 : s.gpr .r22 = s0.gpr .r8) :
    WP isa setup s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      KS t.mem (kB s0) (kW s0) (fun _ => 0) (fun d => slot t.mem (kB s0) d) ∧
      Keep (.r29 :: .r30 :: opRegs) s t := by
  have p := kpre h.pre
  have nw := p.wS
  have hm : (⟨kB s0, kZ s0⟩ : Region) ∈ s.wr := by rw [h.wr, p.wr]; simp
  obtain ⟨fits, hw16, hw, hlw, -⟩ := pre_ws h.pre
  have hs : Scr s (kB s0) (kZ s0) := Scr.of_mem hm nw
  rw [setup, WP.seq_iff]
  have hb : WP isa (.block ([.lsr .d .r29 .r22 1] ++ VG.Impl.Rsa.PPC64LE.Keys.stride ++
      [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2])) s fun u =>
        (u.gpr .r29 = BitVec.ofNat 64 (kW s0) ∧ u.gpr .r30 = BitVec.ofNat 64 (S (kW s0)) ∧
          u.gpr .r8 = BitVec.ofNat 64 (nArr * (kW s0 + 2)) ∧ u.mem = s.mem) ∧ Keep [.r8, .r29, .r30] s u := by
    refine WP.keep _ ?_ (by decide)
    prun [VG.Impl.Rsa.PPC64LE.Keys.stride, h22, ofNat_shr1, ofNat_stride, ofNat_digits60 _ hw, nArr]
  refine WP.mono hb fun u ⟨⟨u29, u30, u8, um⟩, ku⟩ => ?_
  have hu : Ws u (kB s0) (kZ s0) (kW s0) nArr :=
    ⟨hs.congr ku.wr, fits, by omega, Nat.le_trans hw (by decide), u29, u30, (ku.gpr _ (by decide)).trans h.r31⟩
  obtain ⟨hn, hn1, hn2⟩ := zero_bounds fits hw
  refine WP.mono (zeroArrays_ok hu u8 hn1 hn2 hn)
    fun t ⟨ht, z, out, kt⟩ => ⟨?_, ht, ?_, (ku.trans kt).mono⟩
  · have kk := ku.trans kt
    exact Base.of_outside h (by rw [← um]; exact out) hn kk.sp kk.lr kk.rd kk.wr (kk.gpr _ (by decide))
  · have zz : ∀ j < nArr, ∀ i < kW s0 + 2, w32 t.mem (kB s0) (arr (kW s0) j + 4 * i) = 0 := by
      intro j hj i hi
      have hb : j * (kW s0 + 2) + i < nArr * (kW s0 + 2) := by
        have := Nat.mul_le_mul_right (kW s0 + 2) (show j + 1 ≤ nArr by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      have := z (j * (kW s0 + 2) + i) hb
      rw [show 160 + 4 * (j * (kW s0 + 2) + i) = arr (kW s0) j + 4 * i by
        simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
      exact this
    exact ⟨fun j hj => val32_of_zero fun i hi => zz j hj i (by omega), fun _ _ => rfl,
      zz aDv (by decide) _ (by omega)⟩

/-- The bytes of a region apart from the working space are the caller's. -/
theorem Base.bytes {s0 s : State} (h : Base s0 s) {P : Addr} {L : Nat} (hd : (⟨P, L⟩ : Region).Disjoint (rS s0))
    (hw : P.toNat + L ≤ 2 ^ 64) : Spec.Rsa.bytesAt s.mem P L = Spec.Rsa.bytesAt s0.mem P L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.frame _ (past_of_disjoint hd ?_)
  have hi' := List.mem_range.mp hi
  exact Offset.contains_base _ (by omega) (by omega)

/-- `load j` from a region apart from the working space. -/
theorem ldE {s0 s : State} (h : Base s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr) {V F : Nat → Nat}
    (ks : KS s.mem (kB s0) (kW s0) V F) {j : Nat} (hj : j < nArr := by decide) (hjdv : j ≠ aDv := by decide)
    {P : Addr} {L : Nat} (h6 : s.gpr .r6 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hLw : L ≤ 4 * kW s0) (hm : (⟨P, L⟩ : Region) ∈ s0.rd ++ s0.wr) (hd : (⟨P, L⟩ : Region).Disjoint (rS s0))
    (hPw : P.toNat + L ≤ 2 ^ 64) (hz : V j = 0) :
    WP isa (load j) s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      KS t.mem (kB s0) (kW s0) (upd V j (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L))) F ∧ Keep opsRegs s t := by
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (loadE hw ks hj hjdv h6 h8 hL hLw
    (fun i hi => ⟨_, by rw [h.rd, h.wr]; exact hm, hc i hi⟩)
    (fun i hi x hx e => by have := past_of_disjoint hd (hc i hi); rw [e] at this; omega) hz)
    fun t ⟨ht, kt, kk, kr⟩ => ⟨h.of_phase kk kr, ht, ?_, kr⟩
  rw [h.bytes hd hPw] at kt
  exact kt

theorem loads_eq : loads = seqs [.block [.addi .r6 .r16 0, .addi .r8 .r22 0], load aP0,
    .block [.addi .r6 .r17 0, .addi .r8 .r22 0], load aQ0, .block [.addi .r6 .r21 0, .addi .r8 .r23 0],
    load aE] := rfl

/-- `loads`: `p`, `q` and `e` into their arrays. -/
theorem loads_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {V F : Nat → Nat} (ks : KS s.mem (kB s0) (kW s0) V F) (z1 : V aP0 = 0) (z2 : V aQ0 = 0) (z3 : V aE = 0) :
    WP isa loads s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      (∃ V', KS t.mem (kB s0) (kW s0) V' F ∧ (∀ j, j ≠ aP0 → j ≠ aQ0 → j ≠ aE → V' j = V j) ∧
        V' aP0 = pIn s0 ∧ V' aQ0 = qIn s0 ∧ V' aE = eIn s0) ∧ Keep opsRegs s t := by
  have p := kpre h.pre
  obtain ⟨-, hw16, -, hlw, -⟩ := pre_ws h.pre
  have l1 := p.l1
  have el1 := p.el1
  have el8 := p.el8
  have wq := p.wQ
  rw [p.ql] at wq
  rw [loads_eq, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := s) (d₁ := .r6) (d₂ := .r8) (a := .r16) (b := .r22) (by decide) (by decide)
    (by decide) (by decide)) fun u0 ⟨⟨a6, a8, am⟩, ak⟩ => ?_
  rw [ha.r16] at a6
  rw [ha.r22] at a8
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldE (h.of_regs ak am) (hw.of_keep ak) (am ▸ ks) (j := aP0) (h6 := a6)
    (h8 := by rw [a8]; exact ofNat_toNat64 _) (L := kL s0) (hL := by omega) (hLw := by omega)
    (hm := by rw [p.rd, p.wr]; simp) (hd := p.pS) (hPw := p.wP) (hz := z1)) fun t1 ⟨b1, w1, k1, r1⟩ => ?_
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t1) (d₁ := .r6) (d₂ := .r8) (a := .r17) (b := .r22) (by decide) (by decide)
    (by decide) (by decide)) fun u2 ⟨⟨c6, c8, m2⟩, k2⟩ => ?_
  have a1 := ha.of_keep (ak.trans r1)
  rw [a1.r17] at c6
  rw [a1.r22] at c8
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldE (b1.of_regs k2 m2) (w1.of_keep k2) (m2 ▸ k1) (j := aQ0) (h6 := c6)
    (h8 := by rw [c8]; exact ofNat_toNat64 _) (L := kL s0) (hL := by omega) (hLw := by omega)
    (hm := by rw [p.rd, p.wr, ← p.ql]; simp) (hd := by rw [← p.ql]; exact p.qS) (hPw := by rw [← p.ql]; exact p.wQ)
    (hz := by rw [o1 _ (by decide), z2])) fun t3 ⟨b3, w3, k3, r3⟩ => ?_
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (mv2_ok (s := t3) (d₁ := .r6) (d₂ := .r8) (a := .r21) (b := .r23) (by decide) (by decide)
    (by decide) (by decide)) fun u4 ⟨⟨c6', c8', m4⟩, k4⟩ => ?_
  have a3 := a1.of_keep (k2.trans r3)
  rw [a3.r21] at c6'
  rw [a3.r23] at c8'
  rw [show seqs [load aE] = load aE from rfl]
  refine WP.mono (ldE (b3.of_regs k4 m4) (w3.of_keep k4) (m4 ▸ k3) (j := aE) (h6 := c6')
    (h8 := by rw [c8']; exact ofNat_toNat64 _) (hL := el1) (hLw := by omega)
    (hm := by rw [p.rd, p.wr]; simp) (hd := p.eS) (hPw := p.wE)
    (hz := by rw [o3 _ (by decide), o1 _ (by decide), z3])) fun t ⟨b5, w5, k5, r5⟩ => ?_
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  refine ⟨b5, w5, ⟨V5, k5, fun j a b c => by rw [o5 j c, o3 j b, o1 j a], by rw [o5 _ (by decide),
    o3 _ (by decide), e1], by rw [o5 _ (by decide), e3], e5⟩,
    (((((ak.trans r1).trans k2).trans r3).trans k4).trans r5).mono⟩

/-- One instruction that writes a register. -/
theorem reg_step {u : State} {i : Instr} {r : Reg} {v : BitVec 64} (he : exec i u = some (u.write r v))
    {rest : List Instr} {Q : State → Prop} (k : WP isa (.block rest) (u.write r v) Q) :
    WP isa (.block (i :: rest)) u Q := by
  rw [show i :: rest = [i] ++ rest from rfl, WP.block_append_iff]
  exact WP.of_runBlock ⟨u.write r v, by simp only [runBlock_cons, runStep_some, he, runBlock_nil], k⟩

theorem consts_eq : seqs consts = .seq (.block (.li .r6 0 :: (setDigit aOne 1 ++ (setDigit aTwo 2 ++
    (setDigit aThree 3 ++ (setDigit aC 1 ++ (.addi .r6 .r22 0 :: (setDigit aC 1 ++ (.li .r6 4 ::
      (setDigit aC33 2 ++ ([.li .r9 1] : List Instr))))))))))) (half aTop) := rfl

/-- The six constants, into zero arrays. -/
theorem consts_ok {s0 s : State} (h : Base s0 s) (ha : Args s0 s) (hw : Ws s (kB s0) (kZ s0) (kW s0) nArr)
    {V F : Nat → Nat} (ks : KS s.mem (kB s0) (kW s0) V F) (z1 : V aOne = 0) (z2 : V aTwo = 0)
    (z3 : V aThree = 0) (z4 : V aC = 0) (z5 : V aC33 = 0) (z6 : V aTop = 0) :
    WP isa (seqs consts) s fun t => Base s0 t ∧ Ws t (kB s0) (kZ s0) (kW s0) nArr ∧
      (∃ V', KS t.mem (kB s0) (kW s0) V' F ∧
        (∀ j, j ≠ aOne → j ≠ aTwo → j ≠ aThree → j ≠ aC → j ≠ aC33 → j ≠ aTop → V' j = V j) ∧
        V' aOne = 1 ∧ V' aTwo = 2 ∧ V' aThree = 3 ∧ V' aC = 2 ^ (8 * kL s0) + 1 ∧ V' aC33 = 2 ^ 33 ∧
        V' aTop = 2 ^ (32 * kW s0 - 1)) ∧ Keep opsRegs s t := by
  obtain ⟨-, hw16, -, hlw, h4⟩ := pre_ws h.pre
  have p := kpre h.pre
  have l1 := p.l1
  rw [consts_eq, WP.seq_iff]
  refine reg_step (exec_li (show 0 < 2 ^ 15 by decide)) ?_
  have g0 : Keep [.r6] s (s.write .r6 (BitVec.ofNat 64 0)) := Keep.write _ _ _
  have w0 := hw.of_keep g0
  have q6 : (s.write .r6 (BitVec.ofNat 64 0)).gpr .r6 = BitVec.ofNat 64 (4 * 0) := by
    simp [State.write]
  refine setDigitE w0 ks (j := aOne) (x := 1) (k := 0) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [z1]; decide)
    (kk := fun t1 h1 k1 f1 r1 => ?_)
  obtain ⟨V1, k1, e1, o1⟩ := k1.vx
  have q6 : t1.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r1.gpr _ (by decide)]; exact q6
  refine setDigitE h1 k1 (j := aTwo) (x := 2) (k := 0) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [o1 _ (by decide), z2]; decide) (kk := fun t2 h2 k2 f2 r2 => ?_)
  obtain ⟨V2, k2, e2, o2⟩ := k2.vx
  have q6 : t2.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r2.gpr _ (by decide)]; exact q6
  refine setDigitE h2 k2 (j := aThree) (x := 3) (k := 0) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [o2 _ (by decide), o1 _ (by decide), z3]; decide) (kk := fun t3 h3 k3 f3 r3 => ?_)
  obtain ⟨V3, k3, e3, o3⟩ := k3.vx
  have q6 : t3.gpr .r6 = BitVec.ofNat 64 (4 * 0) := by rw [r3.gpr _ (by decide)]; exact q6
  refine setDigitE h3 k3 (j := aC) (x := 1) (k := 0) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z4]; decide) (kk := fun t4 h4' k4 f4 r4 => ?_)
  obtain ⟨V4, k4, e4, o4⟩ := k4.vx
  have a4 := ha.of_keep ((((g0.trans r1).trans r2).trans r3).trans r4)
  refine reg_step (exec_addi (show Reg.r22 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)) ?_
  have g5 : Keep [.r6] t4 (t4.write .r6 (t4.gpr .r22 + BitVec.ofNat 64 0)) := Keep.write _ _ _
  have q6 : (t4.write .r6 (t4.gpr .r22 + BitVec.ofNat 64 0)).gpr .r6 = BitVec.ofNat 64 (4 * (kL s0 / 4)) := by
    simp only [State.write, ↓reduceIte, BitVec.add_zero, a4.r22]
    rw [show 4 * (kL s0 / 4) = kL s0 by omega]; exact ofNat_toNat64 _
  have v4 : V4 aC = 1 := by rw [e4, o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z4]
  have hlt : (1 : Nat) < 2 ^ (32 * (kL s0 / 4)) := Nat.one_lt_two_pow (by omega)
  refine setDigitE (h4'.of_keep g5) k4 (j := aC) (x := 1) (k := kL s0 / 4) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [v4]; exact hlt) (kk := fun t5 h5 k5 f5 r5 => ?_)
  obtain ⟨V5, k5, e5, o5⟩ := k5.vx
  refine reg_step (exec_li (show 4 < 2 ^ 15 by decide)) ?_
  have g6 : Keep [.r6] t5 (t5.write .r6 (BitVec.ofNat 64 4)) := Keep.write _ _ _
  have q6 : (t5.write .r6 (BitVec.ofNat 64 4)).gpr .r6 = BitVec.ofNat 64 (4 * 1) := by simp [State.write]
  refine setDigitE (h5.of_keep g6) k5 (j := aC33) (x := 2) (k := 1) (hx := by decide) (hk := by omega) (h6 := q6)
    (hv := by rw [o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), z5]; decide)
    (kk := fun t6 h6 k6 f6 r6 => ?_)
  obtain ⟨V6, k6, e6, o6⟩ := k6.vx
  refine reg_step (exec_li (show 1 < 2 ^ 15 by decide)) (WP.block_nil ?_)
  have g7 : Keep [.r9] t6 (t6.write .r9 (BitVec.ofNat 64 1)) := Keep.write _ _ _
  have K7 := (((((((((g0.trans r1).trans r2).trans r3).trans r4).trans g5).trans r5).trans g6).trans
    r6).trans g7)
  have f7 : KK (kB s0) (kW s0) s.mem (t6.write .r9 (BitVec.ofNat 64 1)).mem :=
    ((((f1.trans f2).trans f3).trans f4).trans f5).trans f6
  have b7 : Base s0 (t6.write .r9 (BitVec.ofNat 64 1)) := h.of_phase f7 K7
  refine WP.mono (halfE (h6.of_keep g7) k6 (j := aTop) (c := 1) (h9 := by simp [State.write]) (hc := by decide))
    fun t ⟨ht, kt, ft, rt⟩ => ⟨b7.of_phase ft rt, ht, ?_, (K7.trans rt).mono⟩
  obtain ⟨V7, kt, e7, o7⟩ := kt.vx
  have c : ∀ j, j ≠ aOne → j ≠ aTwo → j ≠ aThree → j ≠ aC → j ≠ aC33 → V6 j = V j := fun j a b c d e => by
    rw [o6 j e, o5 j d, o4 j d, o3 j c, o2 j b, o1 j a]
  refine ⟨V7, kt, fun j a b c' d e f => by rw [o7 j f, c j a b c' d e], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide),
      o2 _ (by decide), e1, z1]
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), e2, o1 _ (by decide), z2]
  · rw [o7 _ (by decide), o6 _ (by decide), o5 _ (by decide), o4 _ (by decide), e3, o2 _ (by decide), o1 _ (by decide), z3]
  · rw [o7 _ (by decide), o6 _ (by decide), e5, v4, Nat.mul_one,
      show 32 * (kL s0 / 4) = 8 * kL s0 by omega, Nat.add_comm]
  · rw [o7 _ (by decide), e6, o5 _ (by decide), o4 _ (by decide), o3 _ (by decide), o2 _ (by decide),
      o1 _ (by decide), z5]
  · rw [e7, c _ (by decide) (by decide) (by decide) (by decide) (by decide), z6, Nat.zero_add, Nat.mul_one]
    have : 32 * kW s0 = (32 * kW s0 - 1) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel]

end VG.Proof.RsaKeyGen.PPC64LE.Key
