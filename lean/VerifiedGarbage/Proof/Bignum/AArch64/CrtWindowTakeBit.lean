module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Bignum.AArch64.CrtWindowPending`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.CrtWindowTailBit`, which this module and modules that import it used -/

section

/-! One tail bit extends a bounded pending digit. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (prepareBit)

theorem pendingDigit_value (v V shift : Nat) (hv : v < 16) (hV : V < 256) :
    ((BitVec.ofNat 64 v <<< 1) |||
      (BitVec.ofNat 64 V >>> shift &&& BitVec.setWidth 64 (1#16))) =
      BitVec.ofNat 64 (2 * v + V / 2 ^ shift % 2) := by
  have hb : V / 2 ^ shift % 2 < 2 := Nat.mod_lt _ (by decide)
  have hor : v * 2 ^ 1 ||| (V / 2 ^ shift % 2) = v * 2 ^ 1 + V / 2 ^ shift % 2 := by
    simpa only [Nat.shiftLeft_eq] using
      (Nat.shiftLeft_add_eq_or_of_lt (i := 1) hb v).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_and,BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega_using [hv]),
    Nat.mod_eq_of_lt (show V < 2 ^ 64 by omega_using [hV]),Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show v * 2 ^ 1 < 2 ^ 64 by omega_using [hv]),
    show (BitVec.setWidth 64 (1#16)).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,hor,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 * v + V / 2 ^ shift % 2 < 2 ^ 64 by omega_using [hv])]
  omega_using []

theorem prepareBit_ok {s : State} {P : Addr} {w b v V i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i < 8) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hcbit : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (.block (prepareBit i)) s fun t =>
      (t.mem = (s.mem.writeW (off P (8 * Crt.sNib))
        (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 1)) ∧
        t.gpr .x3 = BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5) ∧ Keep [.x3,.x4,.x5] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [prepareBit,hc.good.x0,hdr_enc (show Crt.sNib < 32 by decide),
    hdr_enc (show Crt.sV < 32 by decide),hdr_enc (show Crt.sBit < 32 by decide),
    hc.ld (i := Crt.sNib) (by decide),hc.ld (i := Crt.sV) (by decide),
    hc.ld (i := Crt.sBit) (by decide),hc.st (i := Crt.sNib) (by decide),
    hc.st (i := Crt.sBit) (by decide),hn,hcbit,hbyte,show 7 - i < 64 by omega,
    pendingDigit_value v V (7 - i) hv hV,
    hdrStore_hdr _ _ _ (show Crt.sNib < 32 by decide) (show Crt.sBit < 32 by decide) (by decide),
    ofNat_add_ofNat]

/-- The decision to apply a window depends only on the public pending-bit count. -/
theorem pending_test {b : Nat} (hb : b < 5) :
    (BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 = 0) ↔ b = 4 := by
  bv_omega

theorem prepareBit_ct (i : Nat) :
    RelCT isa (Two fun (P : Addr) s => s.gpr .x0 = P)
      (.block (prepareBit i)) (fun _ _ => True) := by
  apply two_taint [.x0] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! Tail-bit preparation preserves the Montgomery context and all source bytes. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (prepareBit)

theorem prepareBit_state {s : State} {P : Addr} {w b v V i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i < 8) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hb : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (.block (prepareBit i)) s fun t => TableCtx t P w mi X Xc ∧
      wv t.mem P (slot w aY) w = wv s.mem P (slot w aY) w ∧
      word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (b + 1) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep [.x3,.x4,.x5] s t ∧
      (∀ k < 32, k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) ∧
      t.gpr .x3 = BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 := by
  refine WP.mono (prepareBit_ok hc hi hv hV hn hb hbyte) fun t ⟨⟨hm,hflag⟩,kt⟩ => ?_
  have oa := writeW_outside s.mem P (d := 8 * Crt.sNib) (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2)) (by decide)
  have ob := writeW_outside (s.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2))) P
    (d := 8 * Crt.sBit) (BitVec.ofNat 64 (b + 1)) (by decide)
  rw [← hm] at ob
  have fa : Frm P (crtWinRanges w) _ _ := Frm.of_outside oa (by simp [crtWinRanges])
  have fb : Frm P (crtWinRanges w) _ _ := Frm.of_outside ob (by simp [crtWinRanges])
  have hf := fa.trans fb
  have hny : slot w aY + 8 * w ≤ 2 ^ 64 := by
    have := hc.good.scr.nowrap
    have := slot_le (w := w) (show aY < 8 by decide)
    omega_arith
  refine ⟨hc.of_win hf kt.wr (kt.gpr .x0 (by decide)),?_,?_,?_,hf,kt,?_,hflag⟩
  · rw [ob.wv (by have := hdr_lt_slot w aY (show Crt.sBit < 32 by decide); omega_using [this]) hny,
      oa.wv (by have := hdr_lt_slot w aY (show Crt.sNib < 32 by decide); omega_using [this]) hny]
  · rw [hm,hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),word_writeW_self]
  · rw [hm,word_writeW_self]
  · intro k hk hn hb
    rw [hm,hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hb),hdrStore_hdr _ _ _ (by decide) hk (Ne.symm hn)]


end VG.Proof.Bignum.AArch64.WindowFive

end

end

/-! A tail bit either extends the pending digit or executes one complete window. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (takeBit)

def nextExponent (b E d : Nat) : Nat := if b = 4 then 32 * E + d else E
def nextPending (b : Nat) : Nat := if b = 4 then 0 else b + 1
def nextDigit (b d : Nat) : Nat := if b = 4 then 0 else d

theorem rawWindowRanges_sub (w : Nat) : ∀ r ∈ rawWindowRanges w, r ∈ crtWinRanges w := by
  simp [rawWindowRanges, crtWinRanges]

theorem takeBit_ok (W : Window) {s : State} {P : Addr} {w b v V i : Nat}
    {mi : BitVec 64} {X Xc x E : Nat} {Q : Prop}
    (hc : TableCtx s P w mi X Xc) (ht : CrtWindowFive.CTab s.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv s.mem P (slot w aY) w < X)
    (hyv : Q → wv s.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hi : i < 8) (hb : b < 5) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hcbit : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    let d := 2 * v + V / 2 ^ (7 - i) % 2
    WP isa (takeBit W.code i) s fun t =>
      TableCtx t P w mi X Xc ∧ CrtWindowFive.CTab t.mem P w X Q x ∧
      wv t.mem P (slot w aY) w < X ∧
      (Q → wv t.mem P (slot w aY) w % X = x ^ nextExponent b E d * 2 ^ (64 * w) % X) ∧
      Frm P (crtWinRanges w) s.mem t.mem ∧ Keep mmRegs s t ∧
      word t.mem P (8 * Crt.sNib) = BitVec.ofNat 64 (nextDigit b d) ∧
      word t.mem P (8 * Crt.sBit) = BitVec.ofNat 64 (nextPending b) ∧
      (∀ k < 32, k ≠ Crt.sEnt → k ≠ Crt.sJ → k ≠ Crt.sNib → k ≠ Crt.sBit →
        word t.mem P (8 * k) = word s.mem P (8 * k)) := by
  dsimp only
  unfold takeBit
  refine WP.seq (WP.mono (prepareBit_state hc hi hv hV hn hcbit hbyte)
    fun u ⟨cu,yu,nu,bu,fu,ku,hu,flag⟩ => ?_)
  have tu := ht.of_win fu hc.scrT.nowrap
  have yu' : wv u.mem P (slot w aY) w < X := yu.symm ▸ hy
  have vu : Q → wv u.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X := by
    intro hQ; rw [yu]; exact hyv hQ
  by_cases h4 : b = 4
  · subst b
    refine WP.ite true (by change some (u.gpr .x3 == 0) = some true; rw [flag]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (W.ok cu tu hw hw' hR yu' vu (by omega_using [hv]) nu)
      fun t ⟨ct,tt,yt,vt,ft,kt,nt,bt,hh⟩ => ?_
    refine ⟨ct,tt,yt,vt,fu.trans (ft.mono (rawWindowRanges_sub w)),
      (ku.trans kt).mono (by decide),nt,bt,?_⟩
    intro k hk he hj hn hb
    exact (hh k hk he hj hn hb).trans (hu k hk hn hb)
  · have hz : BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 ≠ 0 :=
      fun h => h4 ((pending_test hb).mp h)
    refine WP.ite false (by change some (u.gpr .x3 == 0) = some false; rw [flag]; exact congrArg some (beq_eq_false_iff_ne.mpr hz)) (by simp) (fun _ => ?_)
    apply WP.block_nil
    refine ⟨cu,tu,yu',?_,fu,ku.mono (by decide),?_,?_,?_⟩
    · simpa only [nextExponent, ite_eq_right h4] using vu
    · simpa only [nextDigit, ite_eq_right h4] using nu
    · simpa only [nextPending, ite_eq_right h4] using bu
    · intro k hk _ _ hn hb
      exact hu k hk hn hb

end VG.Proof.Bignum.AArch64.WindowFive
