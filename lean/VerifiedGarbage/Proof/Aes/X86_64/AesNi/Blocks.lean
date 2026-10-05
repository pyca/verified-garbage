import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks
import VerifiedGarbage.Proof.Aes.X86_64.Blocks

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec`. -/
section

/-!
# AES-NI: decryption

On registers holding states (`st`), `aesdec` with `InvMixColumns` of a round
key is a middle round of FIPS 197's inverse cipher, since `InvMixColumns`
is linear (the equivalent inverse cipher, §5.3.5): `aesdec_st`. With
`aesdeclast` and `aesimc` (`aesdeclast_st`, `st_aesimc`), `aesDec_ok`
proves that `Impl.Aes.X86_64.AesNi.aesDec` decrypts each register of a
list, from the round keys through `aesimc` that `imcKeys` leaves in the
scratch buffer (`imcKeys_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ keyOp imcKey imcKeys dround aesDec)
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns addRoundKey invSbox roundKey invCipher bytesAt)
open VG.Proof.Aes (rkState irnd invMid invMid_succ invCipher_eq invMixColumns_addRoundKey)

theorem invSbox_eq : aesInvSbox = invSbox := by
  funext b
  simp only [aesInvSbox, invSbox, Spec.Aes.invAffine, inv_eq, ofBits8]

theorem getD_invSubBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invSubBytes s).getD i 0 = invSbox (s.getD i 0) := by
  simp [invSubBytes, Vector.getD, h]

theorem getD_invShiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.invShiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [VG.Spec.Aes.invShiftRows, getD_ofFn h]

theorem getD_invMixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.invMixColumns s).getD i 0 =
      Spec.Aes.mul 0x0e (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0b (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0d (s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x09 (s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) := by
  rw [VG.Spec.Aes.invMixColumns, getD_ofFn h]

theorem byte_invShiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  rw [aesInvShiftRows, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvMixColumns x) i =
      aesMul 0x0e (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

/-- `aesimc` is `InvMixColumns`. -/
theorem st_aesimc (k : BitVec 128) : VG.Proof.Aes.X86_64.AesNi.st (aesInvMixColumns k) = VG.Spec.Aes.invMixColumns (VG.Proof.Aes.X86_64.AesNi.st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.byte_invMixColumns _ hi, VG.Proof.Aes.X86_64.AesNi.getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- InvSubBytes after InvShiftRows, byte by byte. -/
theorem byte_invSub (v : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (aesMapBytes aesInvSbox (aesInvShiftRows v)) i =
      (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86_64.AesNi.st v))).getD i 0 := by
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [byte_mapBytes _ _ hi, VG.Proof.Aes.X86_64.AesNi.byte_invShiftRows _ hi, VG.Proof.Aes.X86_64.AesNi.getD_invSubBytes _ hi, VG.Proof.Aes.X86_64.AesNi.getD_invShiftRows _ hi,
    getD_st _ (hs _), VG.Proof.Aes.X86_64.AesNi.invSbox_eq]

theorem st_invSub (v : BitVec 128) :
    VG.Proof.Aes.X86_64.AesNi.st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86_64.AesNi.st v)) :=
  st_ext fun i hi => by rw [getD_st _ hi, VG.Proof.Aes.X86_64.AesNi.byte_invSub _ hi]

/-- `aesdec` with `InvMixColumns` of the round key `rk` is a middle round of
the inverse cipher. -/
theorem aesdec_st (v k : BitVec 128) (rk : List Byte) (hk : VG.Proof.Aes.X86_64.AesNi.st k = VG.Spec.Aes.invMixColumns (rkState rk)) :
    VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .aesdec v k) =
      VG.Spec.Aes.invMixColumns (VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86_64.AesNi.st v))) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, ← hk, getD_st _ hi, getD_st _ hi]
  simp only [XBinOp.eval, byte_xor]
  rw [← VG.Proof.Aes.X86_64.AesNi.st_invSub, ← VG.Proof.Aes.X86_64.AesNi.st_aesimc, getD_st _ hi]

/-- `aesdeclast` is the last round of the inverse cipher. -/
theorem aesdeclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    VG.Proof.Aes.X86_64.AesNi.st (XBinOp.eval .aesdeclast v k) = VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows (VG.Proof.Aes.X86_64.AesNi.st v))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  rw [VG.Proof.Aes.X86_64.AesNi.byte_invSub _ hi]

/-! ## The rounds -/

/-- What decryption needs of the state: the key schedule at `rdi`, readable,
and round keys `1 … nr − 1` through `InvMixColumns` at `r8`. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  keys : Keys nr w s
  imc : ∀ j, 1 ≤ j → j < nr →
    InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 ∧
    VG.Proof.Aes.X86_64.AesNi.st (s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) =
      VG.Spec.Aes.invMixColumns (rkState (roundKey w j))

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s)
    (hf : XFrame rs s s') : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s' :=
  ⟨h.keys.of_frame hf, by rw [hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc⟩

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Spec.Aes.State) (m : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, VG.Proof.Aes.X86_64.AesNi.st (s.xmm b) = invMid nr w m (VG.Spec.Aes.addRoundKey (x b) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (keyOp_ok regs .aesdec _ s hnd h8 (by rw [ea_at]; exact hin))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, ea_at, VG.Proof.Aes.X86_64.AesNi.aesdec_st _ _ _ hst, hI b hb, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j) {s : State}
    (hK : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact VG.Proof.Aes.X86_64.AesNi.dround_ok regs hnd h8 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s) (hI : VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x (nr - 10 + k) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.X86_64.AesNi.st (s'.xmm b) = invCipher nr w (VG.Proof.Aes.X86_64.AesNi.st (s.xmm b))) ∧ XFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => VG.Proof.Aes.X86_64.AesNi.st (s.xmm b)
  have hea : s.ea (VG.Impl.Aes.X86_64.AesNi.at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have kR := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := nr) (by omega)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyOp_ok regs .pxor _ s hnd h8 (by rw [hea]; exact hK.keys.keys nr (Nat.le_refl _)))
    fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x 0 s₁ := fun b hb => by
    rw [hv₁ b hb, pxor_st _ _ (roundKey w nr) (by rw [hK.keys.sched, hea]; exact kR)]; rfl
  refine WP.mono (cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x 0 s₁' := fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb
  have hK₁ := hK.of_frame hf₁₁
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        VG.Proof.Aes.X86_64.AesNi.DInv regs nr w x (nr - 10) s' ∧ XFrame (.xmm8 :: regs) s s' := by
    have hrsi₁ : s₁'.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [VG.X86_64.eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [VG.X86_64.eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : VG.Proof.Aes.X86_64.AesNi.DInv regs 12 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => VG.Proof.Aes.X86_64.AesNi.DInv regs 12 w x 0 s' ∧ XFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [VG.X86_64.eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show VG.Proof.Aes.X86_64.AesNi.DInv regs 12 w x 0 s₂ ∧ XFrame (.xmm8 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 11) (m := 0) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 10) (m := 1) (by omega) (by omega)
        (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [VG.X86_64.eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : VG.Proof.Aes.X86_64.AesNi.DInv regs 14 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := hK.of_frame hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => VG.Proof.Aes.X86_64.AesNi.DInv regs 14 w x 2 s' ∧ XFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [VG.X86_64.eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 12) (m := 1) (by omega) (by omega) (hK₂.of_frame hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            VG.Proof.Aes.X86_64.AesNi.DInv regs 14 w x (1 + 1) s' ∧ XFrame (.xmm8 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 11) (m := 2) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (VG.Proof.Aes.X86_64.AesNi.dround_ok' regs hnd h8 (j := 10) (m := 3) (by omega) (by omega)
          (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := hK.of_frame hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.drounds_ok regs hnd h8 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := hK₂.of_frame hf₃
  have k0 := byte_roundKey s₃.mem (s₃.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  refine WP.mono (keyOp_ok regs .aesdeclast _ s₃ hnd h8 (by rw [ea_at]; exact hK₃.keys.keys 0 (by omega)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb, VG.Proof.Aes.X86_64.AesNi.aesdeclast_st _ _ (roundKey w 0) (by rw [hK₃.keys.sched, ea_at]; exact k0), hI₃ b hb,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega]

/-! ## The round keys through `aesimc` -/

/-- After writing the round keys `S` through `aesimc` to the scratch buffer,
from `s₀`. -/
structure ImcInv (s₀ : State) (S : List Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : ∀ r, r ≠ .xmm8 → s.xmm r = s₀.xmm r
  frame : Frame [⟨s₀.gpr .r8, 2048⟩] s₀.mem s.mem
  le : ∀ j ∈ S, j ≤ 13
  keys : ∀ j ∈ S, s.mem.readW (s₀.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128 =
    aesInvMixColumns (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128)

theorem ImcInv.refl (s₀ : State) : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ [] s₀ :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem imcKey_ok {s₀ : State} (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) {S : List Nat} {s : State}
    (hI : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) {j : Nat} (hj : j ≤ 13) :
    WP isa (.block (imcKey j)) s (VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ (j :: S)) := by
  have ofs : ∀ (p : Addr) (a : Nat), p + BitVec.ofInt 64 (a : Int) = p + BitVec.ofNat 64 a :=
    fun p a => by rw [ofInt_natCast]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 := by
    rw [hI.rd, hI.wr, hI.gpr, ofs]
    exact ⟨_, hsch, contains_offset (by omega) (by omega)⟩
  have hout : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 := by
    rw [hI.wr, hI.gpr, ofs]
    exact ⟨_, hscr, contains_offset (by omega) (by omega)⟩
  -- The schedule's block is still `s₀`'s.
  have hk : s.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128 =
      s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128 := by
    rw [ofs]
    exact hI.frame.readW (contains_offset (base := s₀.gpr .rdi) (len := 240) (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by decide)
  apply WP.of_runBlock
  simp only [imcKey, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, State.store128, ea_at, hin, hout, XBinOp.eval,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp [hr, hI.xmm r hr], ?_, fun j' hj' => ?_,
    fun j' hj' => ?_⟩
  · rw [hI.gpr]
    exact hI.frame.writeW (List.mem_singleton_self _) _
      (by rw [ofs]; exact contains_offset (by omega) (by omega))
  · rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hj
    · exact hI.le j' hj'
  · rw [hI.gpr, hk]
    rcases List.mem_cons.mp hj' with rfl | hj'
    · rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
    · by_cases he : j' = j
      · subst he; rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
      · have h13 := hI.le j' hj'
        rw [Mem.readW_writeW_sep (by
            rw [ofs, ofs]
            intro a h₁ h₂
            rw [VG.Proof.Aes.X86_64.AesNi.off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s₀.gpr .r8).isLt
            omega) (by decide), hI.keys j' hj']

theorem ImcInv.of_frame {s₀ s s' : State} {S : List Nat} (h : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) (hf : XFrame [] s s') :
    VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s' :=
  ⟨hf.gpr.trans h.gpr, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (hf.xmm r (by simp)).trans (h.xmm r hr), by rw [hf.mem]; exact h.frame, h.le,
    by rw [hf.mem]; exact h.keys⟩

/-- Some round keys through `aesimc`, those of `js`. -/
theorem imcRun_ok {s₀ : State} (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) (js : List Nat)
    (hjs : ∀ j ∈ js, j ≤ 13) {S : List Nat} {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) :
    WP isa (.block (js.flatMap imcKey)) s fun s' => ∃ S', VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S' s' ∧ ∀ j, j ∈ js ∨ j ∈ S → j ∈ S' := by
  induction js generalizing S s with
  | nil => exact WP.block_nil ⟨S, hI, fun j h => by simpa using h⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.imcKey_ok hscr hsch hsep hI (hjs j (by simp))) fun s₁ hI₁ => ?_
    refine WP.mono (ih (fun j' hj' => hjs j' (by simp [hj'])) hI₁) fun s' ⟨S', hI', hS'⟩ =>
      ⟨S', hI', fun j' hj' => hS' j' ?_⟩
    rcases hj' with hj' | hj'
    · rcases List.mem_cons.mp hj' with rfl | hj'
      · exact .inr (by simp)
      · exact .inl hj'
    · exact .inr (by simp [hj'])

theorem cmpRsi_imc {s₀ s : State} {S : List Nat} (hI : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) (c : BitVec 32) (nr : Nat)
    (hrsi : s₀.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s' :=
  WP.mono (cmpRsi_ok s c nr (by rw [hI.gpr, hrsi])) fun _ ⟨hz, hf⟩ => ⟨hz, hI.of_frame hf⟩

theorem imcKeys_ok {s₀ : State} {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hrsi : s₀.gpr .rsi = BitVec.ofNat 64 nr) (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) :
    WP isa imcKeys s₀ fun s => ∃ S, VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s ∧ ∀ j, 1 ≤ j → j < nr → j ∈ S := by
  have run := fun js hjs {S s} (hI : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) => VG.Proof.Aes.X86_64.AesNi.imcRun_ok hscr hsch hsep js hjs hI
  refine WP.seq ?_
  rw [WP.block_append_iff, show ((List.range 9).flatMap fun j => imcKey (j + 1)) =
    ((List.range 9).map (· + 1)).flatMap imcKey by simp [List.flatMap_map]]
  refine WP.mono (run _ (by decide) (ImcInv.refl s₀)) fun s₁ ⟨S₁, hI₁, hS₁⟩ => ?_
  have h9 : ∀ j, 1 ≤ j → j ≤ 9 → j ∈ S₁ := fun j h1 h2 => hS₁ j (.inl (by
    simp only [List.mem_map, List.mem_range]; exact ⟨j - 1, by omega, by omega⟩))
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.cmpRsi_imc hI₁ 10 nr hrsi) fun s₂ ⟨hz₂, hI₂⟩ => ?_
  rcases hnr with rfl | rfl | rfl
  · exact WP.ite true (by simp [VG.X86_64.eval, hz₂]) (fun _ => WP.block_nil ⟨S₁, hI₂, fun j h1 h2 => h9 j h1 (by omega)⟩)
      (fun h => absurd h (by decide))
  all_goals
    refine WP.ite false (by simp [VG.X86_64.eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff, show imcKey 10 ++ imcKey 11 = [10, 11].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₂) fun s₃ ⟨S₃, hI₃, hS₃⟩ => ?_
    have h11 : ∀ j, 1 ≤ j → j ≤ 11 → j ∈ S₃ := fun j h1 h2 => hS₃ j (by
      by_cases h : j ≤ 9
      · exact .inr (h9 j h1 h)
      · exact .inl (by simp; omega))
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.cmpRsi_imc hI₃ 12 _ hrsi) fun s₄ ⟨hz₄, hI₄⟩ => ?_
  · exact WP.ite true (by simp [VG.X86_64.eval, hz₄]) (fun _ => WP.block_nil ⟨S₃, hI₄, fun j h1 h2 => h11 j h1 (by omega)⟩)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by simp [VG.X86_64.eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [show imcKey 12 ++ imcKey 13 = [12, 13].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₄) fun s₅ ⟨S₅, hI₅, hS₅⟩ => ⟨S₅, hI₅, fun j h1 h2 => hS₅ j ?_⟩
    by_cases h : j ≤ 11
    · exact .inr (h11 j h1 h)
    · exact .inl (by simp; omega)

/-- The round keys through `aesimc`, as decryption needs them. -/
theorem dKeys_of_imc {s₀ s : State} {nr : Nat} {w : List Byte} (hK : Keys nr w s₀)
    (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) {S : List Nat}
    (hI : VG.Proof.Aes.X86_64.AesNi.ImcInv s₀ S s) (hS : ∀ j, 1 ≤ j → j < nr → j ∈ S) : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s := by
  have ofs : ∀ (p : Addr) (a : Nat), p + BitVec.ofInt 64 (a : Int) = p + BitVec.ofNat 64 a :=
    fun p a => by rw [ofInt_natCast]
  have hle := hK.le
  have hsched : VG.Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1)) = VG.Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * (nr + 1)) := by
    rw [hI.gpr]
    simp only [VG.Spec.Aes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    exact hI.frame.bytes (R := ⟨s₀.gpr .rdi, 16 * (nr + 1)⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_left (Region.sub_prefix (by omega))) (by show 16 * (nr + 1) ≤ 2 ^ 64; omega) hi
  refine ⟨⟨by rw [hsched]; exact hK.sched, hle, by rw [hI.rd, hI.wr, hI.gpr]; exact hK.keys⟩,
    fun j h1 h2 => ⟨?_, ?_⟩⟩
  · rw [hI.rd, hI.wr, hI.gpr, ofs]
    exact ⟨_, List.mem_append_right _ hscr, contains_offset (by omega) (by omega)⟩
  · rw [hI.gpr, hI.keys j (hS j h1 h2), VG.Proof.Aes.X86_64.AesNi.st_aesimc]
    refine congrArg VG.Spec.Aes.invMixColumns ?_
    apply st_ext; intro i hi
    rw [getD_st _ hi, hK.sched, byte_roundKey (L := 16 * (nr + 1)) _ _ (by omega) i hi]
    simp [rkState, Vector.getD, hi]

end VG.Proof.Aes.X86_64.AesNi

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.X86_64.AesNi.Blocks`. -/
section

/-!
# AES-NI: encryption and decryption of whole blocks

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.X86_64.AesNi.encryptBlocks` and `decryptBlocks` against the
contracts of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, through
the per-target contract of the bitsliced implementation
(`Proof.Aes.blocksX86_64`). The loops are proven once for any
transformation `f` of a list of block registers that computes `F` on each,
given what it needs of the state (`KP`, which the loops keep): `aes` and
`aesDec`. After `c` blocks, the first `c` data blocks hold `F` of the
original ones (`Inv`); the eight-block and one-block bodies are the same
code for different lists of registers (`blocks_ok`).
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ aes aesDec regs8 loadData storeData blocksLoad blocks8 blocks1
  blocksTail imcKeys)
open VG.Spec.Aes (bytesAt)

/-! ## Blocks as states -/

theorem stateAt_eq (m : Mem) (a : Addr) : Spec.Aes.stateAt m a = st (m.readW a 128) :=
  st_ext fun i hi => by
    rw [getD_st _ hi, VG.Proof.Gcm.X86_64.byte_readW _ _ hi]
    simp [Spec.Aes.stateAt, Vector.getD, hi]

/-- Load the block at `rdx + d` into `b`. -/
theorem load1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad b (at_ .rdx d)]) s fun s' =>
      s'.xmm b = s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm,
    State.load128, ea_at, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, trivial, trivial, trivial, trivial, fun r h => by simp [h]⟩

/-- Store `b` to the block at `rdx + d`. -/
theorem store1_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquStore (at_ .rdx d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) (s.xmm b) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at,
    hin, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun _ => trivial⟩

theorem loadData_ok (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length,
      InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16) :
    WP isa (.block (loadData regs j)) s fun s' =>
      (∀ k (h : k < regs.length),
        st (s'.xmm regs[k]) = Spec.Aes.stateAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.load1_ok b (16 * j) s hin0) fun s₁ ⟨x₁, g₁, m₁, rd₁, wr₁, o₁⟩ => ?_
    refine WP.mono (ih (j + 1) s₁ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd₁, wr₁, g₁, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega)))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [g₁, m₁] at hb
    refine ⟨fun k hk => ?_, g.trans g₁, m.trans m₁, rd.trans rd₁, wr.trans wr₁, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, x₁, VG.Proof.Aes.X86_64.AesNi.stateAt_eq, ofInt_natCast]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, o₁ r hr.1]

theorem storeData_ok (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length,
      InRegions s.wr (s.gpr .rdx + BitVec.ofInt 64 ((16 * (j + k) : Nat) : Int)) 16)
    (hw : (s.gpr .rdx).toNat + 16 * (j + regs.length) ≤ 2 ^ 64) :
    WP isa (.block (storeData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), Spec.Aes.stateAt s'.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) =
        st (s.xmm regs[k])) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (VG.Proof.Aes.X86_64.AesNi.store1_ok b (16 * j) s hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := by rw [g₁]
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [wr₁, hrdx, show j + 1 + k = j + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by rw [hrdx]; omega)) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    rw [hrdx] at hb hf
    rw [ofInt_natCast] at m₁
    refine ⟨fun k hk => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r => (hx r).trans (x₁ r)⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [VG.Proof.Aes.X86_64.AesNi.stateAt_eq, hf.readW (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            intro a h₁ h₂
            simp only [Region.Contains] at h₁ h₂
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s.gpr .rdx).isLt
            omega) (by decide), m₁, Mem.readW_writeW_self _ _ 16 _ (by decide)]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega, hb k (by simpa using hk), x₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (by simp only [Region.Contains, BitVec.sub_self]; simp; omega)).trans
        (hf.sub fun r hr => ⟨_, List.mem_cons_self, fun a ha => ?_⟩)
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [Region.Contains] at ha ⊢
      rw [off_toNat _ _ (by omega)] at ha ⊢
      have := (a - s.gpr .rdx).isLt
      omega

/-! ## The loops, for any transformation of the blocks -/

namespace Ecb

section
variable (s₀ : State)

abbrev sp : Addr := s₀.gpr .rdi
abbrev nr : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev sR : Region := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀, 240⟩
abbrev dR : Region := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.dp s₀, 16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀⟩
abbrev scrR : Region := ⟨s₀.gpr .r8, 2048⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀) (16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1))
/-- Block `k` of the data, and where it starts. -/
abbrev bAddr (k : Nat) : Addr := VG.Proof.Aes.X86_64.AesNi.Ecb.dp s₀ + BitVec.ofNat 64 (16 * k)
abbrev orig (k : Nat) : Spec.Aes.State := Spec.Aes.stateAt s₀.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Aes.X86_64.AesNi.Ecb.sR s₀]
  wr : s₀.wr = [VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀, VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀]
  s_d : (VG.Proof.Aes.X86_64.AesNi.Ecb.sR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀)
  s_scr : (VG.Proof.Aes.X86_64.AesNi.Ecb.sR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀)
  d_scr : (VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀)
  ret_d : (VG.Proof.Aes.X86_64.AesNi.Ecb.retR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀)
  ret_scr : (VG.Proof.Aes.X86_64.AesNi.Ecb.retR s₀).Disjoint (VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀)
  wrap : (VG.Proof.Aes.X86_64.AesNi.Ecb.dp s₀).toNat + 16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ ≤ 2 ^ 64
  rounds : VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ = 10 ∨ VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ = 12 ∨ VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ = 14

theorem pre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (s₀ : State)
    (h : (Proof.Aes.blocksX86_64 f).pre s₀) : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀)
include hp

theorem nb_lt : 16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem in_blk {k : Nat} (hk : k < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) : (VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀).Contains (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k) 16 :=
  contains_offset (by omega) (by have := hp.wrap; omega)

end Pre

/-- What a transformation of the block registers needs of the state is kept
by writing data blocks and moving `rdx` and `rcx`. -/
def Stable (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s s', KP s → (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
    Frame [VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀] s.mem s'.mem → KP s'

/-- `f` computes `F` on each block register, for both lists of registers. -/
def BlkOk (f : List XReg → Prog isa) (F : Spec.Aes.State → Spec.Aes.State) (KP : State → Prop) :
    Prop :=
  ∀ rs, (rs = regs8 ∨ rs = [.xmm0]) → ∀ s, KP s →
    WP isa (f rs) s fun s' => (∀ b ∈ rs, st (s'.xmm b) = F (st (s.xmm b))) ∧ XFrame (.xmm8 :: rs) s s'

/-- After `c` blocks, with `rdx` and `rcx` at block `p`. -/
structure Inv (KP : State → Prop) (F : Spec.Aes.State → Spec.Aes.State) (s₀ : State) (c p : Nat)
    (s : State) : Prop where
  le : c ≤ VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀
  kp : KP s
  gpr : ∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  r10 : s.gpr .r10 = VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀)
  rdx : s.gpr .rdx = VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ p
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - p)
  frame : Frame [VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀, VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀] s₀.mem s.mem
  blocks : ∀ k < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀,
    Spec.Aes.stateAt s.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k) = if k < c then F (VG.Proof.Aes.X86_64.AesNi.Ecb.orig s₀ k) else VG.Proof.Aes.X86_64.AesNi.Ecb.orig s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem regs_nodup (rs : List XReg) (h : rs = regs8 ∨ rs = [.xmm0]) : rs.Nodup ∧ .xmm8 ∉ rs := by
  rcases h with rfl | rfl <;> decide

theorem run_in {d a : Addr} {nb c n : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hc : c + n ≤ nb)
    (ha : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : (a - d).toNat < 16 * nb := by
  rw [off_toNat _ _ (by omega)] at ha
  have := (a - d).isLt
  omega

theorem run_sep {d a : Addr} {nb c n k : Nat} (hw : d.toNat + 16 * nb ≤ 2 ^ 64) (hk : k < nb)
    (hc : c + n ≤ nb) (hn : ¬ (c ≤ k ∧ k < c + n))
    (h₁ : (a - (d + BitVec.ofNat 64 (16 * k))).toNat < 16)
    (h₂ : (a - (d + BitVec.ofNat 64 (16 * c))).toNat < 16 * n) : False := by
  rw [off_toNat _ _ (by omega)] at h₁ h₂
  have := (a - d).isLt
  omega

theorem beq_ofNat_zero' {k : Nat} (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

section Loops

variable {f : List XReg → Prog isa} {F : Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
  {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀) (hst : VG.Proof.Aes.X86_64.AesNi.Ecb.Stable KP s₀) (hf : VG.Proof.Aes.X86_64.AesNi.Ecb.BlkOk f F KP)
include hp hst hf

/-- The loads, `f` and the stores, for the blocks `c … c + N - 1` (`N` the
number of registers). -/
theorem blocks_ok (rs : List XReg) (hrs : rs = regs8 ∨ rs = [.xmm0]) (tail : List Instr)
    {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s)
    (hQ : ∀ s', VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (loadData rs 0)) (.seq (f rs) (.block (storeData rs 0 ++ tail)))) s Q := by
  obtain ⟨hnd, h8⟩ := VG.Proof.Aes.X86_64.AesNi.Ecb.regs_nodup rs hrs
  have hlen : 0 < rs.length := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.wrap
  have hrdxN : (s.gpr .rdx).toNat = (VG.Proof.Aes.X86_64.AesNi.Ecb.dp s₀).toNat + 16 * c := by
    rw [hI.rdx, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have addr : ∀ (t : State), t.gpr .rdx = s.gpr .rdx → ∀ k,
      t.gpr .rdx + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int) = VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ (c + k) :=
    fun t ht k => by
      rw [ht, hI.rdx, ofInt_natCast, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega]
  have addr' : ∀ k, s.gpr .rdx + BitVec.ofNat 64 (16 * (0 + k)) = VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ (c + k) :=
    fun k => by rw [← addr s rfl, ofInt_natCast]
  have hout : ∀ k, c + k < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ → InRegions s.wr (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ (c + k)) 16 := fun k hk =>
    ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀, by simp [hI.wr, hp.wr], hp.in_blk hk⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.loadData_ok rs 0 s hnd fun k hk => by
      rw [addr s rfl]; obtain ⟨r, hr, h⟩ := hout k (by omega)
      exact ⟨r, List.mem_append_right _ hr, h⟩) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  simp only [addr'] at e₁
  have hkp₁ : KP s₁ := hst s s₁ hI.kp (fun r _ _ => by rw [g₁]) rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  refine WP.seq (WP.mono (hf rs hrs s₁ hkp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have ek : ∀ k (h : k < rs.length), st (s₂.xmm rs[k]) = F (VG.Proof.Aes.X86_64.AesNi.Ecb.orig s₀ (c + k)) := fun k h => by
    rw [e₂ _ (List.getElem_mem h), e₁ k h, hI.blocks _ (by omega)]
    simp only [show ¬ c + k < c by omega, ite_false]
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, g₁]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.X86_64.AesNi.storeData_ok rs 0 s₂ (fun k hk => by
      rw [addr s₂ hrdx₂, f₂.wr, wr₁]; exact hout k (by omega)) (by rw [hrdx₂, hrdxN]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, m₁]
  rw [hm₂, hrdx₂] at fr₃
  rw [hrdx₂] at b₃
  rw [Nat.mul_zero, BitVec.add_zero, hI.rdx] at fr₃
  simp only [addr'] at b₃
  have fr₃' : Frame [VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀] s.mem s₃.mem :=
    fr₃.sub fun r hr => ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀, List.mem_singleton_self _, fun a ha => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Aes.X86_64.AesNi.Ecb.run_in hw hc ha⟩
  have g₃' : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, g₁]
  refine ⟨Nat.le_trans (by omega) hc, hst s s₃ hI.kp (fun r _ _ => g₃' r) (by rw [rd₃, f₂.rd, rd₁])
    (by rw [wr₃, f₂.wr, wr₁]) fr₃', fun r h1 h2 h3 => by rw [g₃', hI.gpr r h1 h2 h3],
    by rw [g₃', hI.r10], by rw [g₃', hI.rdx], by rw [g₃', hI.rcx],
    hI.frame.trans (fr₃'.mono fun r hr => by simp at hr; simp [hr]), ?_,
    by rw [rd₃, f₂.rd, rd₁, hI.rd], by rw [wr₃, f₂.wr, wr₁, hI.wr]⟩
  intro k hk
  have out : ¬ (c ≤ k ∧ k < c + rs.length) →
      Spec.Aes.stateAt s₃.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k) = Spec.Aes.stateAt s.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k) :=
    fun hn => by
      rw [VG.Proof.Aes.X86_64.AesNi.stateAt_eq, VG.Proof.Aes.X86_64.AesNi.stateAt_eq]
      exact congrArg st <| fr₃.readW (r := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k, 16⟩) (w := 128) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        simp only [Region.Contains, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr] at h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.Ecb.run_sep (a := a) hw hk hc hn (by omega) (by omega)) (by decide)
  by_cases hlo : k < c
  · rw [out (by omega), hI.blocks k hk]
    simp only [hlo, show k < c + rs.length by omega, ite_true]
  · by_cases hhi : k < c + rs.length
    · obtain ⟨j, rfl⟩ : ∃ j, k = c + j := ⟨k - c, by omega⟩
      have hj : j < rs.length := by omega
      rw [b₃ j hj, ek j hj]
      simp only [hhi, ite_true]
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, hhi, ite_false]

/-- The eight-block body. -/
theorem body8_ok {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s) :
    WP isa (blocks8 f) s fun s' => VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ (c + 8) (c + 8) s' ∧
      s'.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 8) < 8)) := by
  have hn := hp.nb_lt
  refine VG.Proof.Aes.X86_64.AesNi.Ecb.blocks_ok hp hst hf regs8 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c) - 8 = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 8)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 8) < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The one-block body. -/
theorem body1_ok {c : Nat} (hc : c < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s) :
    WP isa (blocks1 f) s fun s' => VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ (c + 1) (c + 1) s' ∧
      s'.zf = some (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 1) = 0)) := by
  have hn := hp.nb_lt
  refine VG.Proof.Aes.X86_64.AesNi.Ecb.blocks_ok hp hst hf [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrdx := hI₁.rdx
  have hrcx := hI₁.rcx
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e16, e1, hrdx, hrcx,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have hsub : BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c) - 1 = BitVec.ofNat 64 (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 1)) := by
    have := (s₀.gpr .rcx).isLt; bv_omega
  refine ⟨{ hI₁ with
    kp := hst _ _ hI₁.kp (fun r h1 h2 => by simp [h1, h2]) rfl rfl (Frame.refl _ _)
    gpr := fun r h1 h2 h3 => by simp [h1, h2, hI₁.gpr r h1 h2 h3]
    r10 := by simp [hI₁.r10]
    rdx := by simp only [reduceCtorEq, ↓reduceIte, VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr]; bv_omega
    rcx := by simp only [ite_true, reduceCtorEq, ite_false]; exact hsub }, ?_⟩
  rw [hsub, VG.Proof.Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (by omega)]

omit hf in
theorem test_ok {c : Nat} {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun s' =>
      VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s' ∧ s'.zf = some (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c = 0)) := by
  have hn := hp.nb_lt
  have hrcx := hI.rcx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, hrcx, BitVec.and_self, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨{ hI with kp := hst _ _ hI.kp (fun _ _ _ => rfl) rfl rfl (Frame.refl _ _) },
    by rw [VG.Proof.Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' (by omega)]⟩

/-- The blocks left after `c`, eight and then one at a time. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c₀ < 8))) :
    WP isa (blocksTail f) s₁ (VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀)) := by
  have hn := hp.nb_lt
  refine WP.seq (WP.mono (Q := fun s => ∃ c, VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c < 8 ∧ VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c₀ < 8)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c ∧ c + 8 ≤ VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ ∧ VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (blocks8 f) s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c < 8 ∧ VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.body8_ok hp hst hf hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.test_ok hp hst hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c ∧ c < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ ∧ VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blocks1 f) s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP F s₀ (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.body1_ok hp hst hf hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 1) = 0
      · have : c + 1 = VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

end Loops

/-! ## The prologue, the epilogue and the two functions -/

theorem blocksLoad_ok (s : State) :
    WP isa (.block blocksLoad) s fun s' =>
      s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * (s.gpr .rsi).toNat) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, s'.xmm r = s.xmm r) ∧ s'.cf = some (decide ((s.gpr .rcx).toNat < 8)) := by
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, blocksLoad, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, arithFlags, State.setFlags, isa, State.setReg, e8,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by bv_omega, fun r h => by simp [h], trivial, trivial, trivial, fun _ => trivial, ?_⟩
  simp

/-- `Keys` reads only the key schedule, the regions and `rdi`. -/
theorem keys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : Keys nr w s)
    (hrdi : s'.gpr .rdi = s.gpr .rdi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hm : VG.Spec.Aes.bytesAt s'.mem (s.gpr .rdi) (16 * (nr + 1)) = VG.Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1))) :
    Keys nr w s' :=
  ⟨by rw [hrdi, hm]; exact h.sched, h.le, by rw [hrd, hwr, hrdi]; exact h.keys⟩

theorem dkeys_congr {nr : Nat} {w : List Byte} {s s' : State} (h : VG.Proof.Aes.X86_64.AesNi.DKeys nr w s)
    (hrdi : s'.gpr .rdi = s.gpr .rdi) (hr8 : s'.gpr .r8 = s.gpr .r8) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr)
    (hm : VG.Spec.Aes.bytesAt s'.mem (s.gpr .rdi) (16 * (nr + 1)) = VG.Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1)))
    (hm' : ∀ j, 1 ≤ j → j < nr →
      s'.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128 =
        s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) :
    VG.Proof.Aes.X86_64.AesNi.DKeys nr w s' :=
  ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.keys_congr h.keys hrdi hrd hwr hm, fun j h1 h2 => by
    rw [hrd, hwr, hr8, hm' j h1 h2]; exact h.imc j h1 h2⟩

/-- What encryption needs, from `s₀`. -/
def KPe (s₀ : State) (s : State) : Prop :=
  Keys (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀) s ∧ s.gpr .rdi = VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀ ∧ s.gpr .rsi = s₀.gpr .rsi ∧
    s.gpr .r10 = VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀)

/-- What decryption needs, from `s₀`. -/
def KPd (s₀ : State) (s : State) : Prop :=
  VG.Proof.Aes.X86_64.AesNi.DKeys (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀) s ∧ s.gpr .rdi = VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀ ∧ s.gpr .r8 = s₀.gpr .r8 ∧ s.gpr .rsi = s₀.gpr .rsi ∧
    s.gpr .r10 = VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀)

section
variable {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀)
include hp

theorem sch_congr {m m' : Mem} (hf : Frame [VG.Proof.Aes.X86_64.AesNi.Ecb.dR s₀] m m') :
    VG.Spec.Aes.bytesAt m' (VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀) (16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1)) = VG.Spec.Aes.bytesAt m (VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀) (16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1)) := by
  have hn : 16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  simp only [VG.Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact hf.bytes (R := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.sp s₀, 16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1)⟩) (by
    simp only [List.mem_singleton, forall_eq]
    exact hp.s_d.sub_left (Region.sub_prefix hn)) (by show 16 * (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀ + 1) ≤ 2 ^ 64; omega) hi

theorem kpe_stable : VG.Proof.Aes.X86_64.AesNi.Ecb.Stable (VG.Proof.Aes.X86_64.AesNi.Ecb.KPe s₀) s₀ := fun s s' ⟨hK, hrdi, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.keys_congr hK (g _ (by decide) (by decide)) hrd hwr (by rw [hrdi]; exact VG.Proof.Aes.X86_64.AesNi.Ecb.sch_congr hp hf),
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hrsi],
    by rw [g _ (by decide) (by decide), hr10]⟩

theorem kpd_stable : VG.Proof.Aes.X86_64.AesNi.Ecb.Stable (VG.Proof.Aes.X86_64.AesNi.Ecb.KPd s₀) s₀ := fun s s' ⟨hK, hrdi, hr8, hrsi, hr10⟩ hg hrd hwr hf => by
  have g := fun r h1 h2 => hg r h1 h2
  refine ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.dkeys_congr hK (g _ (by decide) (by decide)) (g _ (by decide) (by decide)) hrd hwr
      (by rw [hrdi]; exact VG.Proof.Aes.X86_64.AesNi.Ecb.sch_congr hp hf) fun j h1 h2 => ?_,
    by rw [g _ (by decide) (by decide), hrdi], by rw [g _ (by decide) (by decide), hr8],
    by rw [g _ (by decide) (by decide), hrsi], by rw [g _ (by decide) (by decide), hr10]⟩
  have hj : j ≤ 13 := by rcases hp.rounds with h | h | h <;> omega
  rw [hr8, ofInt_natCast]
  exact hf.readW (r := ⟨s₀.gpr .r8 + BitVec.ofNat 64 (16 * j), 16⟩) (w := 128) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_scr.sub_right (Offset.sub_base _ (by omega))).symm) (by decide)

theorem aes_blkOk : VG.Proof.Aes.X86_64.AesNi.Ecb.BlkOk VG.Impl.Aes.X86_64.AesNi.aes (Spec.Aes.cipher (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀)) (VG.Proof.Aes.X86_64.AesNi.Ecb.KPe s₀) :=
  fun rs hrs s ⟨hK, hrdi, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := VG.Proof.Aes.X86_64.AesNi.Ecb.regs_nodup rs hrs
    exact aes_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

theorem aesDec_blkOk : VG.Proof.Aes.X86_64.AesNi.Ecb.BlkOk aesDec (Spec.Aes.invCipher (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀)) (VG.Proof.Aes.X86_64.AesNi.Ecb.KPd s₀) :=
  fun rs hrs s ⟨hK, hrdi, _, hrsi, hr10⟩ => by
    obtain ⟨hnd, h8⟩ := VG.Proof.Aes.X86_64.AesNi.Ecb.regs_nodup rs hrs
    exact VG.Proof.Aes.X86_64.AesNi.aesDec_ok rs hnd h8 hp.rounds s hK (by rw [hrsi]; simp) (by rw [hr10, hrdi])

/-- From the state after the loops, the postcondition. -/
theorem post_of {F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {KP : State → Prop}
    {s : State} (hI : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv KP (F (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀)) s₀ (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) s) :
    gprPreserved s₀ s ∧ (Proof.Aes.blocksX86_64 F).post s₀ s := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hI.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · refine hI.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_d
    · exact hp.ret_scr
  · show Spec.Aes.statesAt s.mem (VG.Proof.Aes.X86_64.AesNi.Ecb.dp s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀) = _
    simp only [Spec.Aes.statesAt, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    have hk := List.mem_range.mp hk
    have := hI.blocks k hk
    simp only [hk, ite_true] at this
    exact this

end

/-- The keys and the regions at the start, for `KPe`. -/
theorem keys₀ {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀) : Keys (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀) s₀ :=
  ⟨rfl, by rcases hp.rounds with h | h | h <;> omega, fun j hj => ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.sR s₀, by simp [hp.rd], by
    rw [ofInt_natCast]; exact contains_offset (by rcases hp.rounds with h | h | h <;> omega)
      (by rcases hp.rounds with h | h | h <;> omega)⟩⟩

theorem encrypt_correct {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀) :
    WP isa Impl.Aes.X86_64.AesNi.encryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.blocksLoad_ok s₀) fun s₁ ⟨r10₁, g₁, m₁, rd₁, wr₁, _, cf₁⟩ => ?_)
  have hI₁ : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv (VG.Proof.Aes.X86_64.AesNi.Ecb.KPe s₀) (Spec.Aes.cipher (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀)) s₀ 0 0 s₁ :=
    { le := Nat.zero_le _
      kp := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.keys_congr (VG.Proof.Aes.X86_64.AesNi.Ecb.keys₀ hp) (g₁ _ (by decide)) rd₁ wr₁ (by rw [m₁]), g₁ _ (by decide),
        g₁ _ (by decide), r10₁⟩
      gpr := fun r _ _ h3 => g₁ r h3
      r10 := r10₁
      rdx := by rw [g₁ _ (by decide)]; simp [VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr]
      rcx := by rw [g₁ _ (by decide)]; simp [VG.Proof.Aes.X86_64.AesNi.Ecb.nb]
      frame := by rw [m₁]; exact Frame.refl _ _
      blocks := fun k _ => by simp [m₁]
      rd := rd₁
      wr := wr₁ }
  exact WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.tail_ok hp (VG.Proof.Aes.X86_64.AesNi.Ecb.kpe_stable hp) (VG.Proof.Aes.X86_64.AesNi.Ecb.aes_blkOk hp) hI₁ (by simpa using cf₁)) fun s hI =>
    VG.Proof.Aes.X86_64.AesNi.Ecb.post_of hp hI

theorem decrypt_correct {s₀ : State} (hp : VG.Proof.Aes.X86_64.AesNi.Ecb.Pre s₀) :
    WP isa Impl.Aes.X86_64.AesNi.decryptBlocks s₀ fun s' =>
      gprPreserved s₀ s' ∧ (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s₀ s' := by
  have hscr : (VG.Proof.Aes.X86_64.AesNi.Ecb.scrR s₀) ∈ s₀.wr := by rw [hp.wr]; simp
  have hsch : (VG.Proof.Aes.X86_64.AesNi.Ecb.sR s₀) ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by rw [hp.rd]; simp)
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.imcKeys_ok hp.rounds (by simp) hscr hsch hp.s_scr)
    fun s₁ ⟨S, hS₁, hcov⟩ => ?_)
  have hK₁ := VG.Proof.Aes.X86_64.AesNi.dKeys_of_imc (VG.Proof.Aes.X86_64.AesNi.Ecb.keys₀ hp) hscr hp.s_scr hS₁ hcov
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.blocksLoad_ok s₁) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, _, cf₂⟩ => ?_)
  have g : ∀ r, r ≠ .r10 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂ r h, hS₁.gpr]
  have hI₂ : VG.Proof.Aes.X86_64.AesNi.Ecb.Inv (VG.Proof.Aes.X86_64.AesNi.Ecb.KPd s₀) (Spec.Aes.invCipher (VG.Proof.Aes.X86_64.AesNi.Ecb.nr s₀) (VG.Proof.Aes.X86_64.AesNi.Ecb.sch s₀)) s₀ 0 0 s₂ :=
    { le := Nat.zero_le _
      kp := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.dkeys_congr hK₁ (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂])
          (fun _ _ _ => by rw [m₂]), g _ (by decide), g _ (by decide), g _ (by decide),
        by rw [r10₂, hS₁.gpr]⟩
      gpr := fun r _ _ h3 => g r h3
      r10 := by rw [r10₂, hS₁.gpr]
      rdx := by rw [g _ (by decide)]; simp [VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr]
      rcx := by rw [g _ (by decide)]; simp [VG.Proof.Aes.X86_64.AesNi.Ecb.nb]
      frame := by
        rw [m₂]
        exact hS₁.frame.mono fun r hr => by simp at hr; simp [hr]
      blocks := fun k hk => by
        simp only [Nat.not_lt_zero, ite_false, VG.Proof.Aes.X86_64.AesNi.Ecb.orig]
        rw [m₂, VG.Proof.Aes.X86_64.AesNi.stateAt_eq, VG.Proof.Aes.X86_64.AesNi.stateAt_eq]
        exact congrArg st <| hS₁.frame.readW (r := ⟨VG.Proof.Aes.X86_64.AesNi.Ecb.bAddr s₀ k, 16⟩) (w := 128)
          (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.d_scr.sub_left (Offset.sub_base _ (by omega))) (by decide)
      rd := by rw [rd₂, hS₁.rd]
      wr := by rw [wr₂, hS₁.wr] }
  have hcf : s₂.cf = some (decide (VG.Proof.Aes.X86_64.AesNi.Ecb.nb s₀ - 0 < 8)) := by
    rw [cf₂, hS₁.gpr]; simp [VG.Proof.Aes.X86_64.AesNi.Ecb.nb]
  exact WP.mono (VG.Proof.Aes.X86_64.AesNi.Ecb.tail_ok hp (VG.Proof.Aes.X86_64.AesNi.Ecb.kpd_stable hp) (VG.Proof.Aes.X86_64.AesNi.Ecb.aesDec_blkOk hp) hI₂ hcf) fun s hI => VG.Proof.Aes.X86_64.AesNi.Ecb.post_of hp hI

end Ecb

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.encrypt_correct (Ecb.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.AesNi.decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, h⟩ := Ecb.decrypt_correct (Ecb.pre_of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.cipher).pub Impl.Aes.X86_64.AesNi.encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksX86_64 Spec.Aes.invCipher).pub Impl.Aes.X86_64.AesNi.decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.encryptBlocks (Spec.Aes.encryptBlocksContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Aes.X86_64.AesNi.encryptBlocks_correct VG.Proof.Aes.X86_64.AesNi.encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

theorem decryptBlocks_verified :
    Verified X86_64.target Impl.Aes.X86_64.AesNi.decryptBlocks (Spec.Aes.decryptBlocksContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Aes.X86_64.AesNi.decryptBlocks_correct VG.Proof.Aes.X86_64.AesNi.decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksX86_64, X86_64.abi,
      X86_64.argRegs] [Proof.Aes.X86_64.blocksSat] using Proof.Aes.X86_64.blocksSat)

end VG.Proof.Aes.X86_64.AesNi

end
