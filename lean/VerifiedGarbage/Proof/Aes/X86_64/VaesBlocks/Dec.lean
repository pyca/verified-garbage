import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

/-!
# VAES: decrypting the lanes of the block registers

`aesDec_ok`: `Impl.Aes.X86_64.VaesBlocks.aesDec regs` decrypts both 128-bit
lanes of each register of `regs` with the key schedule at `rdi` (10, 12 or
14 rounds, as `rsi` says) and the round keys through `aesimc` at `r8`, as
`AesNi.aesDec_ok` proves of `AesNi.aesDec` on SSE registers: the VEX.256
`vpxor`, `vaesdec` and `vaesdeclast` act on each lane as `pxor`, `aesdec`
and `aesdeclast` do (`VBinOp.sse`), so each lane goes through the same
rounds (`AesNi.aesdec_st`, `aesdeclast_st`), with the round keys loaded into
both lanes of `ymm8` (`Vaes.keyOpL_ok`).
-/

namespace VG.Proof.Aes.X86_64.VaesBlocks

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesBlocks (dround aesDec)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (st DKeys pxor_st aesdec_st aesdeclast_st ea_at ofInt_natCast byte_roundKey)
open VG.Proof.Aes.X86_64.Vaes (keyOpL_ok YFrame.of_keys)
open VG.Spec.Aes (roundKey invCipher addRoundKey)
open VG.Proof.Aes (invMid invMid_succ invCipher_eq)

theorem DKeys.of_yframe {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : DKeys nr w s)
    (hf : YFrame rs s s') : DKeys nr w s' :=
  ⟨YFrame.of_keys h.keys hf, by rw [hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc⟩

/-- Both lanes of each register `b` of `regs` hold the state after `m`
middle rounds of the inverse cipher, from the states `x b l`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Nat → Spec.Aes.State) (m : Nat)
    (s : State) : Prop :=
  ∀ b ∈ regs, ∀ l < 2, st (s.lane b l) = invMid nr w m (addRoundKey (x b l) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ YFrame (.xmm8 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (keyOpL_ok .l256 .xmm8 regs .vaesdec _ s hnd h8 (by rw [ea_at]; exact hin))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, hf⟩
  rw [hv b hb l hl, ea_at]
  show st (XBinOp.eval .aesdec _ _) = _
  rw [aesdec_st _ _ _ hst, hI b hb l hl, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j)
    {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ YFrame (.xmm8 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact dround_ok regs hnd h8 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : DKeys nr w s) (hI : DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      DInv regs nr w x (nr - 10 + k) s' ∧ YFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, YFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (dround_ok' regs hnd h8 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega)
        (DKeys.of_yframe hK hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : DKeys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, st (s'.lane b l) = invCipher nr w (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.lane b l)
  have hea : s.ea (at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have kR := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := nr) (by omega)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyOpL_ok .l256 .xmm8 regs .vpxor _ s hnd h8
      (by rw [hea]; exact hK.keys.keys nr (Nat.le_refl _)))
    fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : DInv regs nr w x 0 s₁ := fun b hb l hl => by
    rw [hv₁ b hb l hl]
    show st (XBinOp.eval .pxor _ _) = _
    rw [pxor_st _ _ (roundKey w nr) (by rw [hK.keys.sched, hea]; exact kR)]; rfl
  refine WP.mono (Vaes.cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : DInv regs nr w x 0 s₁' := fun b hb l hl => by
    rw [hf₁'.lane b (by simp) l hl]; exact hI₁ b hb l hl
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        DInv regs nr w x (nr - 10) s' ∧ YFrame (.xmm8 :: regs) s s' := by
    have hrsi₁ : s₁'.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (Vaes.cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 12 w x 0 s₂ := fun b hb l hl => by
        rw [hf₂.lane b (by simp) l hl]; exact hI₁' b hb l hl
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 12 w x 0 s' ∧ YFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show DInv regs 12 w x 0 s₂ ∧ YFrame (.xmm8 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 0) (by omega) (by omega)
          (DKeys.of_yframe hK hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 1) (by omega) (by omega)
        (DKeys.of_yframe hK (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (Vaes.cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 14 w x 0 s₂ := fun b hb l hl => by
        rw [hf₂.lane b (by simp) l hl]; exact hI₁' b hb l hl
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := DKeys.of_yframe hK hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 14 w x 2 s' ∧ YFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 12) (m := 1) (by omega) (by omega)
            (DKeys.of_yframe hK₂ hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            DInv regs 14 w x (1 + 1) s' ∧ YFrame (.xmm8 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 2) (by omega) (by omega)
            (DKeys.of_yframe hK hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 3) (by omega) (by omega)
          (DKeys.of_yframe hK (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := DKeys.of_yframe hK hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok regs hnd h8 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := DKeys.of_yframe hK₂ hf₃
  have k0 := byte_roundKey s₃.mem (s₃.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  refine WP.mono (keyOpL_ok .l256 .xmm8 regs .vaesdeclast _ s₃ hnd h8
      (by rw [ea_at]; exact hK₃.keys.keys 0 (by omega)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesdeclast _ _) = _
  rw [aesdeclast_st _ _ (roundKey w 0) (by rw [hK₃.keys.sched, ea_at]; exact k0), hI₃ b hb l hl,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega]

end VG.Proof.Aes.X86_64.VaesBlocks
