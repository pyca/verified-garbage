module

-- separate module: built alongside CT

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Out
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_derive_public` on RISC-V: correctness

`derivePublic` runs the front (`dpFront_ok`), loads and checks p (`loadP_X`),
and for a valid p checks x's range (`xRange_ok`): out of range it writes
zeros with the status 2 (`bad_ok`), otherwise `g^x mod p` or zeros with the
status 1 or 3 (`good_ok`), as the exchange computes its shared value; then it
restores the callee-saved registers (`dp_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Derive

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- What the branches leave, from `s` after p's check. -/
def DPost (x : XD) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    let g := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k)
    let xv := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl)
    let r := 0 < xv ∧ xv < bnd s.mem x.D x.k x.L x.p
    Spec.Rsa.bytesAt t.mem x.O x.k = (if r ∧ 1 < g ^ xv % x.p ∧ g ^ xv % x.p < x.p - 1 then
        Spec.Rsa.i2osp (g ^ xv % x.p) x.k else List.replicate x.k 0) ∧
      t.gpr .a0 = BitVec.ofNat 64 (if ¬ r then 2 else if 1 < g ^ xv % x.p ∧ g ^ xv % x.p < x.p - 1 then 1 else 3)) ∧
  t.gpr .s6 = x.S ∧ ∃ m, Arr x s.mem m ∧ Outside x.O 0 x.k m t.mem

/-- `g^x mod p`, from the bytes of g and x in `m`. -/
abbrev gx (x : XD) (m : Mem) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.Y x.k) ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.X x.xl) % x.p

theorem status_bv (c : Prop) [Decidable c] :
    BitVec.ofNat 64 3 - (BitVec.ofNat 64 (if c then 1 else 0) <<< 1) = BitVec.ofNat 64 (if c then 1 else 3) := by
  split <;> decide

/-- x in range: `g^x mod p` to `y` or zeros, the status 1 or 3. -/
theorem good_ok {x : XD} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) :
    WP isa dpGood s fun t =>
      (Spec.Rsa.bytesAt t.mem x.O x.k = (if 1 < gx x s.mem ∧ gx x s.mem < x.p - 1 then
          Spec.Rsa.i2osp (gx x s.mem) x.k else List.replicate x.k 0) ∧
        t.gpr .a0 = BitVec.ofNat 64 (if 1 < gx x s.mem ∧ gx x s.mem < x.p - 1 then 1 else 3)) ∧
      t.gpr .s6 = x.S ∧ ∃ m, Arr x s.mem m ∧ Outside x.O 0 x.k m t.mem := by
  have hv := h.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h.1.ctx.k64
  have hpk : x.p < 256 ^ x.k := by
    have := VG.Proof.Bignum.os2ip_lt (x.db.take x.k)
    rwa [take_len h.1.ctx.hL.1 h.1.ctx] at this
  unfold dpGood exPre exOut
  refine WP.seq (WP.seq (WP.mono (exPre_split h hz) fun s₁ ⟨_, h1⟩ => WP.mono h1 fun s₅ ⟨_, h5⟩ =>
    WP.seq (WP.mono h5 fun s₆ pp => ?_)))
  refine WP.seq (WP.seq (WP.mono (exOut_split pp.ctx pp.regs pp.p hf.1
    (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith)) hpk) fun s₇ ⟨_, h7⟩ =>
      WP.seq (WP.mono h7 fun s₈ ⟨_, h8⟩ => WP.mono h8 fun t op => ?_)))
  obtain ⟨m, am, om⟩ := op.mem
  refine WP.mono (WP.keep [.a0, .t2] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 3 - (t.gpr .a0 <<< 1) ∧
    u.mem = t.mem) (by unfold status; brun [fin64_exec_li_lit (show 3 < 2048 by decide)]) (by rfl) (by rfl))
    fun u ⟨⟨ua, um⟩, ku⟩ => ⟨?_, (ku.gpr (by decide)).trans op.s6, m, pp.arr.trans am, by rw [um]; exact om⟩
  rw [um, ua, op.out, op.a0, pp.z, status_bv]
  exact ⟨rfl, rfl⟩

/-- For a valid p: x's range, then zeros and the status 2, or `g^x mod p` or zeros and the status 1
or 3. -/
theorem body_ok {x : XD} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) (ha : AR x s) :
    WP isa dpBody s (DPost x s) := by
  have hv := h.2.2.mp hz
  unfold dpBody
  refine WP.seq (WP.mono (xRange_ok h hv ha) fun s₁ ⟨h1, z1, m1, a1⟩ => ?_)
  have hY : ∀ n (Q : Addr), (∀ i < n, ∀ y, ofs x.S y < x.Z → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₁.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun n Q hq =>
    Pub.bytes_apart (Z := x.Z) a1 (by have := h.1.ctx.hZ; unfold slot hdrBytes at this; omega_arith) hq
  refine WP.ite (s₁.gpr .s9 == 0) (Steps.eval_zero _ _) (fun h9 => ?_) (fun h9 => ?_)
  · have h9' : s₁.gpr .s9 = 0 := by simpa using h9
    rw [m1] at h9'
    have hr : ¬ (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p) := fun hr => by
      rw [decide_eq_true hr] at h9'; exact absurd h9' (by decide)
    refine WP.mono (bad_ok h1.1 (by rw [m1, decide_eq_false hr]; rfl)) fun t ⟨⟨tb, ta⟩, t6, ot⟩ =>
      ⟨fun _ => ?_, t6, s₁.mem, a1, ot⟩
    dsimp only
    simp only [hr, false_and, ↓reduceIte, not_false_eq_true]
    exact ⟨tb, ta⟩
  · have h9' : s₁.gpr .s9 ≠ 0 := by simpa using h9
    rw [m1] at h9'
    have hr : 0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.X x.xl) < bnd s.mem x.D x.k x.L x.p := by
      by_contra hr; rw [decide_eq_false hr] at h9'; exact h9' rfl
    refine WP.mono (good_ok h1 z1) fun t ⟨tp, t6, m, am, om⟩ => ⟨fun _ => ?_, t6, m, a1.trans am, om⟩
    have e : gx x s₁.mem = gx x s.mem := by simp only [gx]; rw [hY _ _ h1.1.ctx.sepY, hY _ _ h1.1.ctx.sepX]
    rw [e] at tp
    dsimp only
    simp only [hr, true_and, not_true_eq_false, ↓reduceIte]
    exact tp

/-- After p's check: the body for a valid p, else the status 0. -/
theorem branch_ok {x : XD} {s : State} (h : X4 x s) (ha : AR x s) :
    WP isa (.ite (.zero .s0) dpBody (.block [.li .a0 0])) s (DPost x s) := by
  refine WP.ite (s.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · exact body_ok h (by simpa using hb) ha
  · have hz : s.gpr .s0 ≠ 0 := by simpa using hb
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem) (by brun [exec_li]) (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨fun hv => absurd (h.2.2.mpr hv) hz, (kt.gpr (by decide)).trans h.1.s6, t.mem,
        by rw [tm]; exact Outside.refl _ _ _ _, Outside.refl _ _ _ _⟩

theorem ret_status (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- Every register but `ra`. -/
def dpNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem dp_correct (s : State) (h : dpContract.pre s) :
    ∃ tr t, Exec isa derivePublic s tr t ∧ abiPreserved s t ∧ dpContract.post s t := by
  show WP isa derivePublic s fun t => abiPreserved s t ∧ dpContract.post s t
  suffices main : WP isa derivePublic s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ dpContract.post s t from
    WP.mono (WP.rdwr (WP.keep dpNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dOD, dOX, dOS, dOA, dDS, dXS, dSA, nwO, nwD, nwX, nwS, ⟨hk, hk'⟩, hL,
    hol, hx1, hxk, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a4).toNat ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 3 * (s.gpr .a4).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have sepSO : ∀ y, ofs (s.gpr .a7) y < (stackArg s 0).toNat * 8 → (s.gpr .a1).toNat ≤ ofs (s.gpr .a0) y :=
    Pub.sep_of_disjoint dOS.symm
  rw [hol] at sepSO
  unfold derivePublic
  refine WP.seq (WP.mono (WP.rdwr (dpFront_ok hpre)) fun s₃ ⟨⟨hb3, hsv, k3, o3⟩, r3, w3, _⟩ => ?_)
  have ha3 : AR (dxOf s) s₃ := ⟨(k3.gpr (by decide)), by rw [k3.gpr (by decide)]; simp [dxOf],
    by rw [k3.gpr (by decide)]; simp [dxOf], (k3.gpr (by decide)), by rw [k3.gpr (by decide)]; simp [dxOf]⟩
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X hb3) (by rfl)))
    fun s₄ ⟨⟨⟨h4, a4⟩, k4⟩, r4, w4, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (branch_ok h4 (ha3.keep k4))) fun t₅ ⟨⟨tpost, t6, m, am, om⟩, r5, w5, _⟩ => ?_)
  have hc := hb3.ctx
  have hnS := hc.scr.nowrap
  change Outside (s.gpr .a7) 256 ((stackArg s 0).toNat * 8 - 256) s₃.mem s₄.mem at a4
  change Outside (s.gpr .a7) 256 ((stackArg s 0).toNat * 8 - 256) s₄.mem m at am
  change Outside (s.gpr .a0) 0 (s.gpr .a4).toNat m t₅.mem at om
  change (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 at hnS
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (s.gpr .a7)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hwr]
    show InRegions _ (s.gpr .a7 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (s.gpr .a7)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (s.gpr .a7)) (8 * i) = off (s.gpr .a7) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (s.gpr .a7) (128 + 8 * i) = word s₃.mem (s.gpr .a7) (128 + 8 * i)
    refine (Pub.Outside.word_apart om sepSO (by omega_arith) (by omega_arith) hnS).trans ?_
    show Mont.word m _ _ = Mont.word s₃.mem _ _
    rw [Outside.word am (Or.inl (by omega_arith)) (by omega_arith), Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith)]
  refine WP.mono (Pub.restore_ok t₅ (S := s.gpr .a7) (v := fun i => s.gpr (PublicChecked.saved i)) t6 hin
    (fun i hi => Pub.sav_al alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, um, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  · intro hdv
    -- The memory apart from the working space, before the branch.
    have hOZ : Outside (s.gpr .a7) 0 ((stackArg s 0).toNat * 8) s.mem s₄.mem :=
      (o3.mono (Nat.le_refl _) (by omega_arith)).trans (a4.mono (by omega_arith) (by omega_arith))
    have hZx : (dxOf s).Z = (stackArg s 0).toNat * 8 := rfl
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .a7) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₄.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
      Pub.bytes_apart (o := 0) hOZ (by omega_arith) hq
    have bY : Spec.Rsa.bytesAt s₄.mem (dxOf s).Y (dxOf s).k =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .a2) (s.gpr .a4).toNat) (s.gpr .a4).toNat := hsep _ _ hc.sepY
    have bX : Spec.Rsa.bytesAt s₄.mem (dxOf s).X (dxOf s).xl =
        Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat := hsep _ _ hc.sepX
    have bB : bnd s₄.mem (dxOf s).D (dxOf s).k (dxOf s).L (dxOf s).p =
        bnd s.mem (s.gpr .a2) (s.gpr .a4).toNat (s.gpr .a3).toNat (dxOf s).p := by
      unfold bnd
      by_cases hq : (dxOf s).L = 3 * (dxOf s).k
      · have hq' : (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat := hq
        rw [ite_eq_left hq, ite_eq_left hq', hsep _ _ fun i hi => by
          change i < (s.gpr .a4).toNat at hi
          have h' := hc.sepD (2 * (s.gpr .a4).toNat + i) (by change _ < (s.gpr .a3).toNat; omega_arith)
          rw [← off_off] at h'; exact h']
        rfl
      · rw [ite_eq_right hq, ite_eq_right (show ¬ (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat from hq)]
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hpe : (Spec.Ffdh.domainOf (s.gpr .a4).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)).p =
        (dxOf s).p := by
      rw [Proof.Ffdh.domainOf_p _ _ hLk.1]
      show _ = Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).take (s.gpr .a4).toNat)
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega_arith)]
    have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a4).toNat) = (dxOf s).p := by
      rw [← hpe, Proof.Ffdh.domainOf_p _ _ hLk.1]
    rw [hpe] at hmod
    obtain ⟨tb, ta⟩ := tpost hmod
    rw [bY, bX, bB] at tb ta
    have hL' : (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat ∨ (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat := hL
    rw [keyStatus_dom (by omega_arith) hL' hdv, hpD, Proof.Ffdh.domainOf_g _ _ hLk.1, hpe, um, uot .a0 (by decide), ta,
      ret_status _ (by split <;> [decide; split <;> decide]), VG.Proof.Bignum.powMod_eq]
    rw [show (dxOf s).O = s.gpr .a0 from rfl, show (dxOf s).k = (s.gpr .a4).toNat from rfl] at tb
    refine ⟨rfl, ?_⟩
    rw [tb]
    generalize Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) = xv
    generalize bnd s.mem (s.gpr .a2) (s.gpr .a4).toNat (s.gpr .a3).toNat (dxOf s).p = b
    by_cases hv : 0 < xv ∧ xv < b
    · by_cases hc : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (s.gpr .a2) (s.gpr .a4).toNat) (s.gpr .a4).toNat) ^ xv %
          (dxOf s).p ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off (s.gpr .a2) (s.gpr .a4).toNat) (s.gpr .a4).toNat) ^ xv %
          (dxOf s).p < (dxOf s).p - 1
      · simp only [hv, hc, and_self, not_true_eq_false, ↓reduceIte]
      · simp [hv, hc]
    · simp [hv]

end VG.Proof.Ffdh.RISCV64.Derive
