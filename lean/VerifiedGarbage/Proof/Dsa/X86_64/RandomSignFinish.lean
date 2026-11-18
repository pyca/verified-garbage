module

public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomClear
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Dsa.X86_64.RandomSignZero`, which this module and modules that import it used -/

section

/-! Zero the signature output on all randomized-signing failure paths. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64
open VG.WriteBytes (writeW8_apply)

structure RandomZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.r10, .r11] s t
  r10 : t.gpr .r10 = out + BitVec.ofNat 64 j
  r11 : t.gpr .r11 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem random_zeroOut_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa RandomSign.zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.r10, .r11, .rax] s t := by
  unfold RandomSign.zeroOut
  refine WP.seq (WP.mono (WP.keep [.r10, .r11, .rax] (Q := fun t => t.gpr .r10 = op ∧
      t.gpr .r11 = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [random_ea_sp, hsp, hs.ld (d := Random.oOut) (by decide),
      hs.ld (d := Random.oOutLen) (by decide), hO, hK]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := k) (by omega_using [hk1]) (RandomZeroInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j _ hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
  have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
  refine WP.mono (WP.keep [.r10, .r11] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .r10 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .r11 = BitVec.ofNat 64 (k - (j + 1)) ∧
      t'.zf = some (decide (j + 1 = k))) (by
    xrun [State.ea, hI.r10, hI.r11, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
      ofNat64_pred (show 1 ≤ k - j by omega_using [hj]) (by omega_using [hk']), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega_using [hk'])]
    exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩) rfl)
    fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RandomSignPublish`, which this module and modules that import it used -/

section

/-! Wipe the nonce and publish the consumed-byte count and return status. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def randomPublishMem (m : Mem) (B : Addr) : Mem :=
  (randomClearMem m B).writeW (word m B Random.oUsedPtr) (word m B Random.oUsed)

theorem random_publish_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa (.block (Random.clearNonce ++
      ([.mov .rdx (.mem (Random.sp Random.oUsedPtr)), .mov .rax (.mem (Random.sp Random.oUsed)),
       .store { base := .rdx } .rax, .mov .rax (.mem (Random.sp Random.oStatus))] : List Instr))) s fun t =>
      t.gpr .rax = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B ∧
      Keep [.rax, .rdx] s t := by
  have hstatus (m : Mem) : word (m.writeW (word s.mem B Random.oUsedPtr)
      (word s.mem B Random.oUsed)) B Random.oStatus = word m B Random.oStatus :=
    Mem.readW_writeW_sep hsep (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (random_clear_ok hs hsp) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have hp : word u.mem B Random.oUsedPtr = word s.mem B Random.oUsedPtr := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hu : word u.mem B Random.oUsed = word s.mem B Random.oUsed := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have hz : word u.mem B Random.oStatus = word s.mem B Random.oStatus := by
    rw [hum]; exact (random_clear_outside _ _).word (by decide) (by decide)
  have huw : InRegions u.wr (word s.mem B Random.oUsedPtr) 8 := by rw [hku.2.2]; exact hw
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
      t.gpr .rax = word s.mem B Random.oStatus ∧ t.mem = randomPublishMem s.mem B) ?_ rfl)
    fun t ⟨h, hkt⟩ => ⟨h.1, h.2, (hku.trans hkt).mono (by decide)⟩
  xrun [random_ea_sp, random_ea_base, husp,
    hus.ld (d := Random.oUsedPtr) (by decide), hus.ld (d := Random.oUsed) (by decide),
    hus.ld (d := Random.oStatus) (by decide), hp, hu, huw, hstatus, hz]
  rw [hum]
  rfl

end VG.Proof.Dsa.X86_64

end

end

/-! All exits clear failed output, wipe the nonce, and publish consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
    (hs : Scr s B Random.frameBytes) (hsp : s.gpr .rsp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hdis : ∀ d, d + 8 ≤ Random.frameBytes → Mem.Sep (off B d) 8 op k)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa RandomSign.finish s fun t =>
      t.gpr .rax = word s.mem B Random.oStatus ∧
      (∃ m : Mem,
        (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
        (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
        (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
        t.mem = randomPublishMem m B) ∧
      Keep [.rax, .rdx, .r10, .r11] s t := by
  unfold RandomSign.finish
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = s.mem ∧ u.zf = some (word s.mem B Random.oStatus == 1)) (by
        xrun [random_ea_sp, hsp, hs.ld (d := Random.oStatus) (by decide)]
        exact sub_beq_zero _ _) rfl)
    fun u ⟨⟨hum, huz⟩, hku⟩ => ?_)
  have hus := hs.congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hsp
  have next (v : State) (hkv : Keep [.rax, .r10, .r11] u v)
      (hwords : ∀ d, d + 8 ≤ Random.frameBytes → word v.mem B d = word s.mem B d)
      (hgood : word s.mem B Random.oStatus = 1 → v.mem = s.mem)
      (hbad : word s.mem B Random.oStatus ≠ 1 → ∀ i < k, v.mem (op + BitVec.ofNat 64 i) = 0) :
      WP isa (.block (Random.clearNonce ++
        ([.mov .rdx (.mem (Random.sp Random.oUsedPtr)), .mov .rax (.mem (Random.sp Random.oUsed)),
         .store { base := .rdx } .rax, .mov .rax (.mem (Random.sp Random.oStatus))] : List Instr))) v
        (fun t => t.gpr .rax = word s.mem B Random.oStatus ∧
          (∃ m : Mem, (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
            (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
            (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
            t.mem = randomPublishMem m B) ∧ Keep [.rax, .rdx, .r10, .r11] s t) := by
    have hvs := hus.congr hkv.2.2
    have hvsp := (hkv.gpr (by decide)).trans husp
    have hvp := hwords Random.oUsedPtr (by decide)
    refine WP.mono (random_publish_ok hvs hvsp
      (by rw [hvp, hkv.2.2, hku.2.2]; exact hw) (by rw [hvp]; exact hsep))
      fun t ⟨hta, htm, hkt⟩ => ?_
    exact ⟨hta.trans (hwords _ (by decide)), ⟨v.mem, hgood, hbad, hwords, htm⟩,
      ((hku.trans hkv).trans hkt).mono (by decide)⟩
  refine WP.seq ?_
  by_cases h1 : word s.mem B Random.oStatus = 1
  · refine WP.ite false (by simp only [eval, huz, h1, BEq.rfl]; rfl)
      (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    exact next u (Keep.refl _ _) (fun _ _ => by rw [hum]) (fun _ => hum) (fun h => False.elim (h h1))
  · have hz : (word s.mem B Random.oStatus == 1) = false := beq_eq_false_iff_ne.mpr h1
    refine WP.ite true (by simp only [eval, huz, hz]; rfl)
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (random_zeroOut_ok (op := op) (k := k) hus husp (by rw [hum]; exact hO) (by rw [hum]; exact hK)
      hk1 hk (fun j hj => by rw [hku.2.2]; exact hout j hj)) fun v ⟨hzero, hf, hkv⟩ => ?_
    exact next v (hkv.mono (by decide))
      (fun d hd => (random_zero_preserves_word hf (hdis d hd) hk).trans (by rw [hum]))
      (fun h => False.elim (h1 h)) (fun _ => hzero)

end VG.Proof.Dsa.X86_64
