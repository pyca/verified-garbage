module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorSetup
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMont
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff eval_zero eq_zero_iff)

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

def guard : List Instr := [ldh .x12 sW, .lsr .x .x3 .x12 3, movi .x4 7,
  .logic .and .x .x4 .x12 .x4]

theorem shr3_width {w : Nat} (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w >>> 3 = BitVec.ofNat 64 (w / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega_using [hw])]

theorem guard_ok {s : State} {P : Addr} {w n : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : CExpCtx s P w mi X Xc n) (hw : w < 2 ^ 30) :
    WP isa (.block guard) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (w / 8) ∧
        t.gpr .x4 = BitVec.ofNat 64 (w % 8)) ∧ Keep [.x12,.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [guard, hc.good.x0, hdr_enc (show sW < 32 by decide), hc.ld (i := sW) (by decide),
    hc.good.hdr.hw, shr3_width (show w < 2 ^ 64 by omega_using [hw])]
  exact BlockedRedc.mask7_ofNat (by omega_using [hw])

/-- The selection from a table of `n` entries, 16 or 32: by vectors when the
width is whole tiles, and otherwise by `fallback`, which selects as it does. -/
theorem select_ok {s : State} {P : Addr} {w v n : Nat} {mi : BitVec 64} {X Xc : Nat} {fallback : Prog isa}
    (hN : n = 16 ∨ n = 32)
    (hf : ∀ {u : State}, CExpCtx u P w mi X Xc n → word u.mem P (8 * Crt.sTab) = off P (slot w 8) →
      word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v →
      WP isa fallback u fun t => CExpCtx t P w mi X Xc n ∧
        wv t.mem P (slot w Crt.aT) w = wv u.mem P (slot w (8 + v)) w ∧
        Frm P (selRanges w) u.mem t.mem ∧ Keep mmRegs u t)
    (hc : CExpCtx s P w mi X Xc n) (hw' : w < 2 ^ 30) (hv : v < n)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hNib : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (VG.Impl.Rsa.AArch64.WindowSelectVector.select n fallback) s fun t => CExpCtx t P w mi X Xc n ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold VG.Impl.Rsa.AArch64.WindowSelectVector.select
  refine WP.seq (WP.mono (guard_ok hc hw') fun u ⟨⟨hm,h3,h4⟩,ku⟩ => ?_)
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  have tab : word u.mem P (8 * Crt.sTab) = off P (slot w 8) := by rw [hm]; exact ht
  have nib : word u.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v := by rw [hm]; exact hNib
  have slow : WP isa fallback u (fun t => CExpCtx t P w mi X Xc n ∧
      wv t.mem P (slot w Crt.aT) w = wv s.mem P (slot w (8 + v)) w ∧
      Frm P (selRanges w) s.mem t.mem ∧ Keep mmRegs s t) := WP.mono (hf ctx tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
    ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
  by_cases fast : 8 ≤ w
  · refine WP.ite true (by rw [eval_nonzero,h3,ne_zero_iff,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega_using [hw']),decide_eq_true (show w / 8 ≠ 0 by omega_using [fast])])
      (fun _ => ?_) (by simp)
    by_cases hd : w % 8 = 0
    · refine WP.ite true (by rw [eval_zero,h4,hd]; rfl) (fun _ => ?_) (by simp)
      exact WP.mono (blockedN_ok hN ctx fast hw' hd hv tab nib) fun t ⟨ct,hy,hf,kt⟩ =>
        ⟨ct,hm ▸ hy,hm ▸ hf,(ku.trans kt).mono (by decide)⟩
    · exact WP.ite false (by rw [eval_zero,h4,eq_zero_iff,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show w % 8 < 2 ^ 64 by omega_using []),decide_eq_false hd]) (by simp) (fun _ => slow)
  · exact WP.ite false (by rw [eval_nonzero,h3,show w / 8 = 0 by omega_using [fast]]; rfl) (by simp) (fun _ => slow)

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
