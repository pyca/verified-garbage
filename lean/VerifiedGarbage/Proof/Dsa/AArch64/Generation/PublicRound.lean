module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# DSA parameter generation on AArch64: the round for public candidates

`publicSel` does what the masked selection does (`publicSel_selOK`), so the
round with it is the shared round's (`publicRound_correct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aXm)

/-- The base of entry `d`, from `T_0`'s and `d` strides. -/
theorem entry_base (B : Addr) (w d : Nat) :
    off B (slot w aT0) + BitVec.ofNat 64 d * BitVec.ofNat 64 (8 * (w + 2)) = off B (slot w (aT0 + d)) := by
  rw [← BitVec.ofNat_mul, off_add]
  congr 1
  unfold slot
  rw [Nat.add_mul]
  omega_using []

/-- The selection's head: the bases of `aXm` and of entry `d`. -/
theorem publicSelHead_ok {s : State} {B : Addr} {Z w d : Nat} (h : Ws s B Z w)
    (hG : word s.mem B (8 * kG) = BitVec.ofNat 64 d) :
    WP isa (.block (ws ++ base aXm .x17 ++ base aT0 .x16 ++
      ([ldh .x9 kG, .mul .x .x9 .x9 .x11, .add .x .x16 .x16 .x9] : List Instr))) s fun t =>
      (t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.gpr .x17 = off B (slot w aXm) ∧
        t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.x9, .x11, .x12, .x16, .x17] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aXm .x17 h0₁ h11) fun s₂ ⟨⟨h17, m₂, _⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aT0 .x16 ((k₂.gpr .x0 (by decide)).trans h0₁) ((k₂.gpr .x11 (by decide)).trans h11))
    fun s₃ ⟨⟨h16, m₃, _⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (WP.keep [.x9, .x16] (Q := fun t => t.gpr .x16 = off B (slot w (aT0 + d)) ∧ t.mem = s₃.mem) (by
    brun [(k13.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kG < 32 by decide),
      (hs.congr k13.wr).ld (d := 8 * kG) (by simp only [kG]; omega_using [h256]), (by rw [m₃, m₂, m₁]; exact hG :
        word s₃.mem B (8 * kG) = BitVec.ofNat 64 d), h16, (k₂.trans k₃ |>.gpr .x11 (by decide)).trans h11,
      entry_base])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16t, hm⟩, k⟩ => ?_
  exact ⟨⟨h16t, (k₃.trans k |>.gpr .x17 (by decide)).trans h17,
    (k₂.trans k₃ |>.trans k |>.gpr .x12 (by decide)).trans h12, by rw [hm, m₃, m₂, m₁]⟩,
    (k13.trans k).mono (by decide)⟩

/-- `publicSel`: `[aXm] := T_d` for the digit `d` in `kG`, as `mrSel_ok`. -/
theorem publicSel_selOK : SelOK publicSel := by
  intro s B Z w d h hEZ hd hG
  have hn := h.scr.nowrap
  have hT := tab_fits (w := w) hEZ hd
  have hX := tab_sep_xm w (j := d)
  have hXZ := h.sl (show aXm < 16 by decide)
  simp only [publicSel, seqs]
  refine WP.seq (WP.mono (publicSelHead_ok h hG) fun s₁ ⟨⟨h16, h17, h12, m₁⟩, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.wr
  refine WP.mono (copyWords_ok h16 h17 h12 (by have := h.w1; omega_using [this])
    (by have := h.w2; omega_using [this]) (by omega_using [hn, hXZ])
    (fun i hi => hs₁.ld (by omega_using [hT, hi])) (fun i hi => hs₁.st (by omega_using [hXZ, hi]))
    (fun i hi b hb => by rw [ofs_off B (by omega_using [hn, hT, hi, hb])]; omega_using [hX, hi, hb]))
    fun t ⟨hv, _, o, _, _, k₂⟩ => ?_
  rw [m₁] at hv o
  exact ⟨hv, o, h.scr.congr (k₁.trans k₂).wr, (k₁.trans k₂).mono (by decide)⟩

theorem publicSel_ne : publicSel ≠ [] := by unfold publicSel; exact List.cons_ne_nil _ _

theorem publicWin_winOK (M : Mont) : WinOK (publicWin M.mm) := mrWinS_winOK publicSel_ne publicSel_selOK M

/-- The round for public candidates meets the shared round's contract. -/
theorem publicRound_correct (M : Mont) (s : State) (h : roundContract.pre s) :
    ∃ tr t, Exec isa (publicRound M.mm) s tr t ∧ abiPreserved s t ∧ roundContract.post s t :=
  roundW_correct (publicWin_winOK M) M s h

end VG.Proof.Dsa.AArch64.Generation
