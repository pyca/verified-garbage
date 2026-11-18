module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublish
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! ### `Dsa.AArch64.RandomSignZero`, which this module and modules that import it used -/

section

/-! Zero the signature output on all randomized-signing failure paths. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.WriteBytes (writeW8_apply)

structure RandomZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x12, .x9] s t
  r10 : t.gpr .x12 = out + BitVec.ofNat 64 j
  r11 : t.gpr .x9 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_zeroOut_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa RandomSign.zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x12, .x9, .x0] s t := by
  unfold RandomSign.zeroOut
  refine WP.seq (WP.mono (WP.keep [.x12, .x9, .x0] (Q := fun t => t.gpr .x12 = op ∧
      t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x0 = 0 ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (show Random.oOut % 8 = 0 ∧ Random.oOut < 32768 by decide),
      exec_ldrSp (show Random.oOutLen % 8 = 0 ∧ Random.oOutLen < 32768 by decide), hsp, hs.ld (d := Random.oOut) (by decide),
      hs.ld (d := Random.oOutLen) (by decide), hO, hK]) rfl rfl rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (N := k) hk' hk1 (RandomZeroInv s₁ op k) ?_
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩ hcx) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j hj t hI hcount
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.wr, k₁.wr]; exact hout j hj
  have hax' : (t.gpr .x0).setWidth 8 = 0 := by rw [hI.keep.gpr .x0 (by decide), hax]; rfl
  have hp : BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  refine WP.mono (WP.keep [.x12, .x9] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .x12 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .x9 = BitVec.ofNat 64 (k - (j + 1)))
      (by brun [hI.r10, hI.r11, hst, hax', hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl)
      rfl rfl rfl) fun t' ⟨⟨hm, hsi', hcx'⟩, k'⟩ => ?_
  refine ⟨⟨(hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])
  · rw [hcx', hcount]
    exact hp.symm

end VG.Proof.Dsa.AArch64

end

end

/-! All exits clear failed output, wipe the nonce, and publish consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_zero_preserves_word {s t : State} {B op : Addr} {k d : Nat}
    (hf : ∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x)
    (hsep : Mem.Sep (off B d) 8 op k) (hk : k < 2 ^ 64) :
    word t.mem B d = word s.mem B d := by
  apply Mem.readW_congr
  intro i hi
  apply hf
  intro j hj he
  have hleft : ((off B d + BitVec.ofNat 64 i) - off B d).toNat < 8 := by
    rw [Mem.sub_ofNat_toNat _ (by omega_using [hi])]; exact hi
  have hright : ((off B d + BitVec.ofNat 64 i) - op).toNat < k := by
    rw [he, Mem.sub_ofNat_toNat _ (by omega_using [hk, hj])]; exact hj
  exact hsep _ hleft hright

/-- The intermediate memory records whether output clearing was required;
the final exact memory expression includes both nonce wiping and publication. -/
theorem random_finish_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hdis : ∀ d, d + 8 ≤ Random.frameBytes → Mem.Sep (off B d) 8 op k)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa RandomSign.finish s fun t =>
      t.gpr .x0 = word s.mem B Random.oStatus ∧
      (∃ m : Mem,
        (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
        (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
        (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
        t.mem = randomPublishMem m B) ∧
      Keep [.x0, .x2, .x4, .x12, .x9, .x15] s t := by
  unfold RandomSign.finish
  refine WP.seq (WP.mono (WP.keep [.x0, .x4] (Q := fun u =>
      u.mem = s.mem ∧ (u.gpr .x4 == 0#64) = (word s.mem B Random.oStatus == 1)) (by
        unfold Random.statusTest
        brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide),
          hsp, hs.ld (d := Random.oStatus) (by decide)]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
        rfl) rfl rfl rfl)
    fun u ⟨⟨hum, huz⟩, hku⟩ => ?_)
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have next (v : State) (hkv : Keep [.x0, .x12, .x9] u v)
      (hwords : ∀ d, d + 8 ≤ Random.frameBytes → word v.mem B d = word s.mem B d)
      (hgood : word s.mem B Random.oStatus = 1 → v.mem = s.mem)
      (hbad : word s.mem B Random.oStatus ≠ 1 → ∀ i < k, v.mem (op + BitVec.ofNat 64 i) = 0) :
      WP isa (.block (Random.clearNonce ++
        ([.ldrSp .x2 Random.oUsedPtr, .ldrSp .x0 Random.oUsed,
         .str .x .x0 .x2 0, .ldrSp .x0 Random.oStatus] : List Instr))) v
        (fun t => t.gpr .x0 = word s.mem B Random.oStatus ∧
          (∃ m : Mem, (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
            (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
            (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
            t.mem = randomPublishMem m B) ∧ Keep [.x0, .x2, .x4, .x12, .x9, .x15] s t) := by
    have hvs := hus.congr hkv.wr
    have hvsp := hkv.sp.trans husp
    have hvp := hwords Random.oUsedPtr (by decide)
    refine WP.mono (random_publish_ok hvs hvsp
      (by rw [hvp, hkv.wr, hku.wr]; exact hw) (by rw [hvp]; exact hsep))
      fun t ⟨hta, htm, hkt⟩ => ?_
    exact ⟨hta.trans (hwords _ (by decide)), ⟨v.mem, hgood, hbad, hwords, htm⟩,
      ((hku.trans hkv).trans hkt).mono (by decide)⟩
  refine WP.seq ?_
  by_cases h1 : word s.mem B Random.oStatus = 1
  · refine WP.ite false (by
      change some (!(u.gpr .x4 == 0#64)) = some false
      rw [huz, h1, BEq.rfl]; rfl)
      (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    exact next u (Keep.refl _ _) (fun _ _ => by rw [hum]) (fun _ => hum) (fun h => False.elim (h h1))
  · have hz : (word s.mem B Random.oStatus == 1) = false := beq_eq_false_iff_ne.mpr h1
    refine WP.ite true (by
      change some (!(u.gpr .x4 == 0#64)) = some true
      rw [huz, hz]; rfl)
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (random_zeroOut_ok (op := op) (k := k) hus husp (by rw [hum]; exact hO) (by rw [hum]; exact hK)
      hk1 hk (fun j hj => by rw [hku.wr]; exact hout j hj)) fun v ⟨hzero, hf, hkv⟩ => ?_
    exact next v (hkv.mono (by decide))
      (fun d hd => (random_zero_preserves_word hf (hdis d hd) hk).trans (by rw [hum]))
      (fun h => False.elim (h1 h)) (fun _ => hzero)

end VG.Proof.Dsa.AArch64
