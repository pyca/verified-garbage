module

-- separate module: built alongside CT

public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Body
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_check_private` on RISC-V: correctness

`checkPrivate` runs the front (`cpFront_ok`), loads and checks p
(`loadP_X`), and for a valid p checks x's range (`xRange_ok`): out of range
the status is 2, otherwise `g^x mod p` is computed as the exchange computes
its shared value and compared (`good_ok`); then it restores the callee-saved
registers (`kp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.CheckPrivate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd xRange_ok off_off)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- `g^x mod p`, from the bytes of g and x in `m`. -/
abbrev gx (x : XD) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.Y x.k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.X x.xl) % x.p

/-- What the branches leave, from `s` after p's check. -/
def KPost (x : XD) (Yc : Addr) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    t.gpr .a0 = BitVec.ofNat 64 (if ¬ (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p) then 2 else
      if (1 < gx x s.mem ∧ gx x s.mem < x.p - 1) ∧ gx x s.mem = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k)
      then 1 else 0)) ∧
  t.gpr .s6 = x.S ∧ Arr x s.mem t.mem

/-- x in range: `g^x mod p`, compared. -/
theorem good_ok {x : XD} {Yc : Addr} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) (hy : YE x Yc s) :
    WP isa cpGood s fun t =>
      t.gpr .a0 = BitVec.ofNat 64 (if (1 < gx x s.mem ∧ gx x s.mem < x.p - 1) ∧
        gx x s.mem = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Yc x.k) then 1 else 0) ∧
      t.gpr .s6 = x.S ∧ Arr x s.mem t.mem := by
  have hv := h.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h.1.ctx.k64
  have hc := h.1.ctx
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  unfold cpGood exPre cpCmp
  refine WP.seq (WP.seq (WP.mono (WP.rdwr (exPre_split h hz)) fun s₁ ⟨⟨_, h1⟩, r1, w1, _⟩ =>
    WP.mono (WP.rdwr h1) fun s₅ ⟨⟨_, h5⟩, r5, w5, _⟩ =>
      WP.seq (WP.mono (WP.rdwr h5) fun s₆ ⟨pp, r6, w6, _⟩ => ?_)))
  have hy6 : YE x Yc s₆ := hy.keep hc (by rw [r6, r5, r1]) (by rw [w6, w5, w1]) pp.arr
  refine WP.seq (WP.mono (cmp_split pp.ctx pp.regs hy6 pp.p hf.1
    (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith))) fun s₇ ⟨_, h7⟩ =>
      WP.seq (WP.mono h7 fun s₈ ⟨_, h8⟩ => WP.mono h8 fun t op => ?_))
  obtain ⟨ta, t6, at'⟩ := op
  refine ⟨?_, t6, pp.arr.trans at'⟩
  rw [ta, pp.z, Pub.bytes_apart (Z := x.Z) pp.arr (by omega_arith) hy.sep]

/-- After p's check: the body for a valid p, else the status 0. -/
theorem branch_ok {x : XD} {Yc : Addr} {s : State} (h : X4 x s) (ha : AR x s) (hy : YE x Yc s) :
    WP isa (.ite (.zero .s0) cpBody (.block [.li .a0 0])) s (KPost x Yc s) := by
  have hZ := h.1.ctx.hZ
  unfold slot hdrBytes at hZ
  refine WP.ite (s.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hz : s.gpr .s0 = 0 := by simpa using hb
    have hv := h.2.2.mp hz
    unfold cpBody
    refine WP.seq (WP.mono (WP.rdwr (xRange_ok h hv ha)) fun s₁ ⟨⟨h1, z1, m1, a1⟩, r1, w1, _⟩ => ?_)
    have hY : ∀ n (Q : Addr), (∀ i < n, ∀ y, ofs x.S y < x.Z → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₁.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun n Q hq =>
      Pub.bytes_apart (Z := x.Z) a1 (by omega_arith) hq
    refine WP.ite (s₁.gpr .s9 == 0) (Steps.eval_zero _ _) (fun h9 => ?_) (fun h9 => ?_)
    · have h9' : s₁.gpr .s9 = 0 := by simpa using h9
      rw [m1] at h9'
      have hr : ¬ (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p) := fun hr => by
        rw [decide_eq_true hr] at h9'; exact absurd h9' (by decide)
      refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 2 ∧ t.mem = s₁.mem)
        (by brun [fin64_exec_li_lit (show 2 < 2048 by decide)]) (by rfl) (by rfl))
        fun t ⟨⟨ta, tm⟩, kt⟩ => ⟨fun _ => ?_, (kt.gpr (by decide)).trans h1.1.s6, by rw [tm]; exact a1⟩
      simp only [ta, hr, not_false_eq_true, ↓reduceIte]
    · have h9' : s₁.gpr .s9 ≠ 0 := by simpa using h9
      rw [m1] at h9'
      have hr : 0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p := by
        by_contra hr; rw [decide_eq_false hr] at h9'; exact h9' rfl
      refine WP.mono (good_ok h1 z1 (hy.keep h.1.ctx r1 w1 a1)) fun t ⟨ta, t6, at'⟩ =>
        ⟨fun _ => ?_, t6, a1.trans at'⟩
      have e : gx x s₁.mem = gx x s.mem := by simp only [gx]; rw [hY _ _ h1.1.ctx.sepY, hY _ _ h1.1.ctx.sepX]
      rw [ta, e, hY _ _ hy.sep]
      simp only [hr, and_self, not_true_eq_false, ↓reduceIte]
  · have hz : s.gpr .s0 ≠ 0 := by simpa using hb
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem) (by brun [exec_li]) (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨fun hv => absurd (h.2.2.mpr hv) hz, (kt.gpr (by decide)).trans h.1.s6,
        by rw [tm]; exact Outside.refl _ _ _ _⟩

theorem ret_status (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- Every register but `ra`. -/
def kpNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem kp_correct (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa checkPrivate s tr t ∧ abiPreserved s t ∧ kpContract.post s t := by
  show WP isa checkPrivate s fun t => abiPreserved s t ∧ kpContract.post s t
  suffices main : WP isa checkPrivate s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ kpContract.post s t from
    WP.mono (WP.rdwr (WP.keep kpNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL,
    hyl, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a2).toNat ≤ (s.gpr .a1).toNat ∧ (s.gpr .a1).toNat ≤ 3 * (s.gpr .a2).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have hwd : ((s.gpr .a2).toNat + 7) / 8 * 8 ≤ (s.gpr .a2).toNat + 7 := Nat.div_mul_le_self _ _
  have hcz : cpZ (s.gpr .a2).toNat ≤ (stackArg s 0).toNat * 8 := by unfold cpZ slot hdrBytes; omega_arith
  unfold checkPrivate
  refine WP.seq (WP.mono (WP.rdwr (cpFront_ok hpre)) fun s₃ ⟨⟨hb3, ha3, hw32, hsv, k3, o3⟩, r3, w3, _⟩ => ?_)
  have e24 : cpZ (s.gpr .a2).toNat = 256 + 24 * (8 * (((s.gpr .a2).toNat + 7) / 8 + 2)) := rfl
  have hy3 : YE (cxOf s) (s.gpr .a3) s₃ := ⟨hw32, fun i hi => by
      change i < (s.gpr .a2).toNat at hi
      rw [r3, w3]
      exact rd_of_mem (L := (s.gpr .a4).toNat) (by rw [hrd]; simp) (by change _ ≤ _; omega_arith) (BitVec.isLt _) i hi,
    fun i hi y hy => Pub.ne_of_disjoint dYS (Nat.le_of_lt (s.gpr .a4).isLt) i
      (by change i < (s.gpr .a2).toNat at hi; omega_arith) y (Nat.lt_of_lt_of_le hy hcz)⟩
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X hb3) (by rfl)))
    fun s₄ ⟨⟨⟨h4, a4⟩, k4⟩, r4, w4, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (branch_ok h4 (ha3.keep k4) (hy3.keep hb3.ctx r4 w4 a4)))
    fun t₅ ⟨⟨tpost, t6, am⟩, r5, w5, _⟩ => ?_)
  have hc := hb3.ctx
  have hnS := nwS
  change Outside (s.gpr .a7) 256 (cpZ (s.gpr .a2).toNat - 256) s₃.mem s₄.mem at a4
  change Outside (s.gpr .a7) 256 (cpZ (s.gpr .a2).toNat - 256) s₄.mem t₅.mem at am
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (s.gpr .a7)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hwr]
    show InRegions _ (s.gpr .a7 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (s.gpr .a7)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (s.gpr .a7)) (8 * i) = off (s.gpr .a7) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (s.gpr .a7) (128 + 8 * i) = word s₃.mem (s.gpr .a7) (128 + 8 * i)
    rw [Outside.word am (Or.inl (by omega_arith)) (by omega_arith), Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith)]
  refine WP.mono (Pub.restore_ok t₅ (S := s.gpr .a7) (v := fun i => s.gpr (PublicChecked.saved i)) t6 hin
    (fun i hi => Pub.sav_al alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, _, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  · intro hdv
    -- The memory apart from the working space, before the branch.
    have hOZ : Outside (s.gpr .a7) 0 (cpZ (s.gpr .a2).toNat) s.mem s₄.mem :=
      (o3.mono (Nat.le_refl _) (by omega_arith)).trans (a4.mono (by omega_arith) (by omega_arith))
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .a7) y < cpZ (s.gpr .a2).toNat → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₄.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
      Pub.bytes_apart (o := 0) hOZ (by omega_arith) hq
    have bG : Spec.Rsa.bytesAt s₄.mem (cxOf s).Y (cxOf s).k =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .a0) (s.gpr .a2).toNat) (s.gpr .a2).toNat := hsep _ _ hc.sepY
    have bX : Spec.Rsa.bytesAt s₄.mem (cxOf s).X (cxOf s).xl =
        Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat := hsep _ _ hc.sepX
    have bY : Spec.Rsa.bytesAt s₄.mem (s.gpr .a3) (cxOf s).k =
        Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat := by
      rw [hyl]; exact hsep _ _ hy3.sep
    have bB : bnd s₄.mem (cxOf s).D (cxOf s).k (cxOf s).L (cxOf s).p =
        bnd s.mem (s.gpr .a0) (s.gpr .a2).toNat (s.gpr .a1).toNat (cxOf s).p := by
      unfold bnd
      by_cases hq : (cxOf s).L = 3 * (cxOf s).k
      · have hq' : (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hq
        rw [ite_eq_left hq, ite_eq_left hq', hsep _ _ fun i hi => by
          change i < (s.gpr .a2).toNat at hi
          have h' := hc.sepD (2 * (s.gpr .a2).toNat + i) (by change _ < (s.gpr .a1).toNat; omega_arith)
          rw [← off_off] at h'; exact h']
        rfl
      · rw [ite_eq_right hq, ite_eq_right (show ¬ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat from hq)]
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hpe : (Spec.Ffdh.domainOf (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)).p =
        (cxOf s).p := by
      rw [Proof.Ffdh.domainOf_p _ _ hLk.1]
      show _ = Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat)
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega_arith)]
    have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a2).toNat) = (cxOf s).p := by
      rw [← hpe, Proof.Ffdh.domainOf_p _ _ hLk.1]
    rw [hpe] at hmod
    have ta := tpost hmod
    simp only [gx] at ta
    simp only [bG, bX, bB, bY] at ta
    have hL' : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
    show _ = Spec.Ffdh.privateStatus _ _ _
    rw [privateStatus_dom (by omega_arith) hL' hdv, uot .a0 (by decide), ta]
    simp only [hpD]
    rw [ret_status _ (by split <;> [decide; split <;> decide])]

end VG.Proof.Ffdh.RISCV64.CheckPrivate
