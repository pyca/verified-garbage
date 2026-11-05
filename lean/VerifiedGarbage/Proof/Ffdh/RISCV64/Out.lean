module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ZMask
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's exchange on RISC-V: the output

`exOut_split`: with z (below p) in array 4, `zMask` leaves the mask of
`z ∉ {0, 1, p − 1}` in `s9`, `out` comes back from the header into `s10`
(`R8`), and `PublicChecked.output` writes z's `p_len` octets or zeros
(`OutPost`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-- Before the output: `out` in `s10`. -/
def R8 (x : XD) (s : State) : Prop := s.gpr .s10 = off x.O 0 ∧ RW x s

/-- What the output leaves, from `s` after the power. -/
structure OutPost (x : XD) (s t : State) : Prop where
  out : Spec.Rsa.bytesAt t.mem x.O x.k =
    if 1 < wordsVal s.mem x.S (slot x.w 4) x.w ∧ wordsVal s.mem x.S (slot x.w 4) x.w < x.p - 1 then
      Spec.Rsa.i2osp (wordsVal s.mem x.S (slot x.w 4) x.w) x.k else List.replicate x.k 0
  a0 : t.gpr .a0 = BitVec.ofNat 64
    (if 1 < wordsVal s.mem x.S (slot x.w 4) x.w ∧ wordsVal s.mem x.S (slot x.w 4) x.w < x.p - 1 then 1 else 0)
  s6 : t.gpr .s6 = x.S
  mem : ∃ m, Arr x s.mem m ∧ Outside x.O 0 x.k m t.mem

theorem bmask_sub (b : Bool) : bmask b = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> decide

/-- `zMask`, then `out` from the header, then the output. -/
theorem exOut_split {x : XD} {s : State} (hc : Ctx x s) (hr : RW x s)
    (hp : wordsVal s.mem x.S (slot x.w 0) x.w = x.p) (hodd : x.p % 2 = 1)
    (hzp : wordsVal s.mem x.S (slot x.w 4) x.w < x.p) (hpk : x.p < 256 ^ x.k) :
    WP isa zMask s fun s₁ => RW x s₁ ∧ WP isa (.block [.load .d .s10 .s6 0]) s₁ fun s₂ => R8 x s₂ ∧
      WP isa PublicChecked.output s₂ (OutPost x s) := by
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hkw : x.k ≤ 8 * x.w := by omega_arith
  have e : ∀ j, slot x.w j = hdrBytes + j * (8 * (x.w + 2)) := fun _ => rfl
  have e0 := e 0; have e4 := e 4; have e5 := e 5; have e8 := e 8; have e24 := e 24
  have hh : hdrBytes = 256 := rfl
  obtain ⟨h6, h7, h5, h0, h11⟩ := id hr
  generalize hz : wordsVal s.mem x.S (slot x.w 4) x.w = z at hzp ⊢
  refine WP.mono (zMask_ok hc.scr h7 h5 h0 (by omega_arith) hw' (by omega_arith) (by rw [hp]; exact hodd))
    fun s₁ ⟨⟨a9, o1⟩, k1⟩ => ⟨hr.keep k1 (by decide), ?_⟩
  rw [hz, hp] at a9
  have ar1 : Arr x s.mem s₁.mem := arr_of o1 (by omega_arith) (by omega_arith)
  have hc1 := hc.keep k1.2.1 k1.2.2 ar1
  have rw1 : RW x s₁ := hr.keep k1 (by decide)
  refine WP.mono (ldh_ok hc1 rw1.1 .s10 (d := 0) (by decide) (by decide)) fun s₂ ⟨⟨a10, m2⟩, k2⟩ =>
    ⟨⟨by rw [a10]; exact hc1.hO, rw1.keep k2 (by decide)⟩, ?_⟩
  have hc2 := hc1.same k2 m2
  have rw2 : RW x s₂ := rw1.keep k2 (by decide)
  have hb : decide (z ≠ 0 ∧ z ≠ 1 ∧ z ≠ x.p - 1) = decide (1 < z ∧ z < x.p - 1) := by
    apply decide_eq_decide.mpr; omega_arith
  rw [hb, bmask_sub] at a9
  have z2 : wordsVal s₂.mem x.S (slot x.w 4) x.w = z := by
    rw [m2, Outside.wordsVal o1 (by omega_arith) (by omega_arith), hz]
  refine WP.mono (Pub.output_ok (b := decide (1 < z ∧ z < x.p - 1)) hc2.scr hc2.outW hc2.nwO rw2.2.1 rw2.2.2.1
    rw2.2.2.2.2 (by rw [a10]; exact hc1.hO) ((k2.gpr (by decide)).trans a9) (by omega_arith) hkw (by omega_arith)
    hc2.sepO) fun t ⟨⟨ob, ot, t0⟩, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans rw2.1, s₂.mem,
      by rw [m2]; exact ar1, ot⟩
  · rw [hz]
    by_cases hcd : 1 < z ∧ z < x.p - 1
    · rw [ite_eq_left hcd]
      exact Pub.out_bytes hkw (by rw [← Pub.wsv_wv]; exact z2) (by omega_arith) fun i hi => by
        rw [ob i hi, ite_eq_left (decide_eq_true hcd)]
    · rw [ite_eq_right hcd]
      exact Pub.zero_bytes fun i hi => by rw [ob i hi, ite_eq_right (by simpa using hcd)]
  · rw [t0, hz]; simp only [decide_eq_true_eq]

end VG.Proof.Ffdh.RISCV64
