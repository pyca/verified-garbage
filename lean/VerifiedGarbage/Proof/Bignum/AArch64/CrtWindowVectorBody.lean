module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorCopy
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont

/-! ### `Bignum.AArch64.CrtWindowVectorFinish`, which only this module used -/

section

/-! Restore the scalar selector's final public header values. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)

def finish (n : Nat) : List Instr :=
  [ldh .x3 Crt.sTab, .lsl .x .x4 .x6 (if n == 64 then 6 else if n == 32 then 5 else 4), .add .x .x3 .x3 .x4,
  sth .x3 Crt.sEnt, movi .x3 n, sth .x3 Crt.sJ]

theorem shl4_stride {w : Nat} (hw : w < 2 ^ 30) :
    BitVec.ofNat 64 (8 * (w + 2)) <<< 4 = BitVec.ofNat 64 (16 * (8 * (w + 2))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show 8 * (w + 2) < 2 ^ 64 by omega_using [hw])]
  congr 1
  omega_using []

theorem shl5_stride {w : Nat} (hw : w < 2 ^ 30) :
    BitVec.ofNat 64 (8 * (w + 2)) <<< 5 = BitVec.ofNat 64 (32 * (8 * (w + 2))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show 8 * (w + 2) < 2 ^ 64 by omega_using [hw])]
  congr 1
  omega_using []

theorem finish_ok {s : State} {P : Addr} {w n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n) (hw : w < 2 ^ 30)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (finish n)) s fun t =>
      t.mem = (s.mem.writeW (off P (8 * Crt.sEnt))
        (off P (slot w 8 + n * (8 * (w + 2))))).writeW
        (off P (8 * Crt.sJ)) (BitVec.ofNat 64 n) ∧ Keep [.x3,.x4] s t := by
  rcases hN with rfl | rfl <;>
  · refine WP.keep _ ?_ rfl rfl rfl
    brun [finish, hc.good.x0, hdr_enc (show Crt.sTab < 32 by decide),
      hdr_enc (show Crt.sEnt < 32 by decide), hdr_enc (show Crt.sJ < 32 by decide),
      hc.ld (i := Crt.sTab) (by decide), hc.st (i := Crt.sEnt) (by decide),
      hc.st (i := Crt.sJ) (by decide), ht, hs, shl5_stride hw, shl4_stride hw]
    rfl

end VG.Proof.Bignum.AArch64.WindowVector

end

end


/-! The blocked selector's exact instruction shape and selected byte sequence. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)

theorem blocked_eq (n : Nat) : VG.Impl.Rsa.AArch64.WindowSelectVector.blocked n =
    .seq (.block setup) (.seq (.loop (rawStep n) (.nonzero .x .x13)) (.block (finish n))) := rfl

theorem body_ok {s : State} {P : Addr} {w v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hv : v < n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.seq (.block setup) (.loop (rawStep n) (.nonzero .x .x13))) s fun t =>
      ∃ s₀, s₀.mem = s.mem ∧ Keep mmRegs s s₀ ∧ LoopInv n s₀ P w mi X Xc v (w / 8) t := by
  apply WP.seq
  refine WP.mono (setup_ok hc hw' hNib) fun u ⟨⟨h6,h13,h17,h22,h24,hm⟩,ku⟩ => ?_
  have ctx : CExpCtx u P w mi X Xc n := hc.of_win
    (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have h0 : LoopInv n u P w mi X Xc v 0 u := ⟨ctx, by rw [hm]; exact ht,
    h6, by simpa using h17, h22, h24, Outside.refl _ _ _ _,
    fun k hk => by omega, Keep.refl _ _⟩
  exact WP.mono (blocks_ok hN hw hw' hv h0 h13) fun t hI =>
    ⟨u,hm,ku.mono (by decide),hI⟩

theorem blockedN_ok {s : State} {P : Addr} {w v n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hN : n = 16 ∨ n = 32) (hc : CExpCtx s P w mi X Xc n) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 8 = 0)
    (hv : v < n) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked n) s fun t =>
      CExpCtx t P w mi X Xc n ∧ wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hcount : 64 * (w / 8) = 8 * w := by omega_using [hd]
  have he : slot w 8 + 8 * (w + 2) * v = slot w (8 + v) := by
    simp only [slot, Nat.add_mul, Nat.mul_comm v, Nat.add_assoc]
  rw [blocked_eq]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (body_ok hN hc hw hw' hv ht hNib) fun u ⟨s₀,hm₀,k₀,hI⟩ => ?_
  have hn := hI.ctx.scrT.nowrap
  have hT := slot_le (w := w) (show Crt.aT < 8 by decide)
  have hval : wv u.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w := by
    apply wv_copy
    simpa only [hcount,he,hm₀] using hI.bytes
  have fb : Frm P (selRanges w) s.mem u.mem := by
    have ho := hI.frame
    rw [hm₀,hcount] at ho
    exact Frm.of_outside (ho.mono (o' := slot w Crt.aT) (n' := 8 * (w + 2))
      (by omega_using []) (by omega_using [])) (by simp [selRanges])
  refine WP.mono (finish_ok hN hI.ctx hw' hI.tab hI.stride) fun t ⟨hm,kt⟩ => ?_
  have o₁ := writeW_outside u.mem P (d := 8 * Crt.sEnt)
    (off P (slot w 8 + n * (8 * (w + 2)))) (by decide)
  have o₂ := writeW_outside (u.mem.writeW (off P (8 * Crt.sEnt))
    (off P (slot w 8 + n * (8 * (w + 2))))) P (d := 8 * Crt.sJ) (BitVec.ofNat 64 n) (by decide)
  rw [← hm] at o₂
  have ff : Frm P (selRanges w) u.mem t.mem :=
    (Frm.of_outside o₁ (by simp [selRanges])).trans (Frm.of_outside o₂ (by simp [selRanges]))
  refine ⟨hI.ctx.of_win (ff.mono (selRanges_sub w)) kt.wr (kt.gpr .x0 (by decide)), ?_,
    fb.trans ff, ((k₀.trans hI.keep).trans kt).mono (by decide)⟩
  rw [o₂.wv (by have := hdr_lt_slot w Crt.aT (show Crt.sJ < 32 by decide); omega_using [this]) (by omega_using [hn, hT]),
    o₁.wv (by have := hdr_lt_slot w Crt.aT (show Crt.sEnt < 32 by decide); omega_using [this]) (by omega_using [hn, hT])]
  exact hval

/-- `blockedN_ok` for RSA's table of 32 entries. -/
theorem blocked_ok {s : State} {P : Addr} {w v : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : WindowFive.TableCtx s P w mi X Xc) (hw : 8 ≤ w) (hw' : w < 2 ^ 30) (hd : w % 8 = 0)
    (hv : v < 32) (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.blocked 32) s fun t =>
      WindowFive.TableCtx t P w mi X Xc ∧ wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (blockedN_ok (Or.inr rfl) hc.toC hw hw' hd hv ht hNib) fun _ ⟨ct, h⟩ => ⟨WindowFive.TableCtx.ofC ct, h⟩

end VG.Proof.Bignum.AArch64.WindowVector
