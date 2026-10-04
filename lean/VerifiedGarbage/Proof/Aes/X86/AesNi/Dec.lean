import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-!
# AES-NI on x86 (32-bit): decryption

On registers holding states (`st`), `aesdec` with `InvMixColumns` of a round
key is a middle round of FIPS 197's inverse cipher, since `InvMixColumns`
is linear (the equivalent inverse cipher, §5.3.5): `aesdec_st`. With
`aesdeclast` and `aesimc` (`aesdeclast_st`, `st_aesimc`), `aesDec_ok`
proves that `Impl.Aes.X86.AesNi.aesDec` decrypts each register of a list,
from the round keys through `aesimc` and the last round key that `imcKeys`
leaves in the scratch buffer (`imcKeys_ok`).
-/

namespace VG.Proof.Aes.X86.AesNi

open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ keyOpAt imcKey copyLast imcKeys dround aesDec)
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns addRoundKey invSbox roundKey invCipher bytesAt)
open VG.Proof.Aes (rkState irnd invMid invMid_succ invCipher_eq invMixColumns_addRoundKey)

theorem invSbox_eq : aesInvSbox = invSbox := by
  funext b
  simp only [aesInvSbox, invSbox, Spec.Aes.invAffine, inv_eq, ofBits8]

theorem getD_invSubBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invSubBytes s).getD i 0 = invSbox (s.getD i 0) := by
  simp [invSubBytes, Vector.getD, h]

theorem getD_invShiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invShiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [invShiftRows, getD_ofFn h]

theorem getD_invMixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invMixColumns s).getD i 0 =
      Spec.Aes.mul 0x0e (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0b (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0d (s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x09 (s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) := by
  rw [invMixColumns, getD_ofFn h]

theorem byte_invShiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvShiftRows x) i = byte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  rw [aesInvShiftRows, VG.Proof.Gcm.X86.byte_ofBytes _ h]

theorem byte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvMixColumns x) i =
      aesMul 0x0e (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, VG.Proof.Gcm.X86.byte_ofBytes _ h]

/-- `aesimc` is `InvMixColumns`. -/
theorem st_aesimc (k : BitVec 128) : st (aesInvMixColumns k) = invMixColumns (st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, byte_invMixColumns _ hi, getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- InvSubBytes after InvShiftRows, byte by byte. -/
theorem byte_invSub (v : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (aesMapBytes aesInvSbox (aesInvShiftRows v)) i =
      (invSubBytes (invShiftRows (st v))).getD i 0 := by
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [byte_mapBytes _ _ hi, byte_invShiftRows _ hi, getD_invSubBytes _ hi, getD_invShiftRows _ hi,
    getD_st _ (hs _), invSbox_eq]

theorem st_invSub (v : BitVec 128) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (invShiftRows (st v)) :=
  st_ext fun i hi => by rw [getD_st _ hi, byte_invSub _ hi]

/-- `aesdec` with `InvMixColumns` of the round key `rk` is a middle round of
the inverse cipher. -/
theorem aesdec_st (v k : BitVec 128) (rk : List Byte) (hk : st k = invMixColumns (rkState rk)) :
    st (XBinOp.eval .aesdec v k) =
      invMixColumns (addRoundKey (invSubBytes (invShiftRows (st v))) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, ← hk, getD_st _ hi, getD_st _ hi]
  simp only [XBinOp.eval, byte_xor]
  rw [← st_invSub, ← st_aesimc, getD_st _ hi]

/-- `aesdeclast` is the last round of the inverse cipher. -/
theorem aesdeclast_st (v k : BitVec 128) (rk : List Byte) (hk : ∀ i < 16, byte k i = rk.getD i 0) :
    st (XBinOp.eval .aesdeclast v k) = addRoundKey (invSubBytes (invShiftRows (st v))) rk := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_addRoundKey _ _ hi, ← hk i hi]
  simp only [XBinOp.eval, byte_xor]
  rw [byte_invSub _ hi]

/-! ## A round key from anywhere -/

theorem keyOpAt_ok (regs : List XReg) (op : XBinOp) (m : MemOp) (s : State)
    (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    WP isa (.block (keyOpAt regs op m)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.mem.readW (s.ea m) 128)) ∧
      XFrame (.xmm6 :: regs) s s' := by
  rw [keyOpAt, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm6 (s.mem.readW (s.ea m) 128), by
    simp only [isa, exec, State.load128, hin, ite_true, Option.map_some], ?_⟩
  refine WP.mono (map_ok op regs _ hnd h6) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb6 : b ≠ .xmm6 := fun h => h6 (h ▸ hb)
    rw [hv b hb, xmm_setXmm_of_ne _ _ hb6, xmm_setXmm_self]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2, xmm_setXmm_of_ne _ _ hr.1]

/-! ## The rounds -/

/-- What decryption needs of the state: the key schedule at `eax`, readable,
round keys `1 … nr − 1` through `InvMixColumns` at `edx + 16 j`, and the
last round key at `edx + 224`. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  keys : Keys nr w s
  imc : ∀ j, 1 ≤ j → j < nr →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx (16 * j))) 16 ∧
    st (s.mem.readW (s.ea (at_ .edx (16 * j))) 128) = invMixColumns (rkState (roundKey w j))
  last : InRegions (s.rd ++ s.wr) (s.ea (at_ .edx 224)) 16 ∧
    ∀ i < 16, byte (s.mem.readW (s.ea (at_ .edx 224)) 128) i = (roundKey w nr).getD i 0

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : DKeys nr w s)
    (hf : XFrame rs s s') : DKeys nr w s' :=
  ⟨h.keys.of_frame hf, by simp only [State.ea, hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc,
    by simp only [State.ea, hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.last⟩

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Spec.Aes.State) (m : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, st (s.xmm b) = invMid nr w m (addRoundKey (x b) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm6 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (keyOpAt_ok regs .aesdec _ s hnd h6 hin)
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesdec_st _ _ _ hst, hI b hb, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm6 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact dround_ok regs hnd h6 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : DKeys nr w s) (hI : DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      DInv regs nr w x (nr - 10 + k) s' ∧ XFrame (.xmm6 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (dround_ok' regs hnd h6 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega)
      (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h6 : .xmm6 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : DKeys nr w s)
    (hc : s.gpr .ecx = BitVec.ofNat 32 nr) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = invCipher nr w (st (s.xmm b))) ∧ XFrame (.xmm6 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => st (s.xmm b)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyOpAt_ok regs .pxor _ s hnd h6 hK.last.1) fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : DInv regs nr w x 0 s₁ := fun b hb => by
    rw [hv₁ b hb, pxor_st _ _ (roundKey w nr) hK.last.2]; rfl
  refine WP.mono (cmpEcx_ok s₁ 10) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : DInv regs nr w x 0 s₁' := fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb
  have hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 nr := by rw [hf₁.gpr, hc]
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .ecx (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        DInv regs nr w x (nr - 10) s' ∧ XFrame (.xmm6 :: regs) s s' := by
    have hc₁' : s₁'.gpr .ecx = BitVec.ofNat 32 nr := by rw [hf₁₁.gpr, hc]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁, hc₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [eval, hz₁, hc₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpEcx_ok s₁' 12) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 12 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 12 w x 0 s' ∧ XFrame (.xmm6 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [eval, hz₂, hc₁']) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show DInv regs 12 w x 0 s₂ ∧ XFrame (.xmm6 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (dround_ok' regs hnd h6 (j := 11) (m := 0) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (dround_ok' regs hnd h6 (j := 10) (m := 1) (by omega) (by omega)
        (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [eval, hz₁, hc₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpEcx_ok s₁' 12) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 14 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := hK.of_frame hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 14 w x 2 s' ∧ XFrame (.xmm6 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [eval, hz₂, hc₁']) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h6 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h6 (j := 12) (m := 1) (by omega) (by omega) (hK₂.of_frame hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            DInv regs 14 w x (1 + 1) s' ∧ XFrame (.xmm6 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h6 (j := 11) (m := 2) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h6 (j := 10) (m := 3) (by omega) (by omega)
          (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := hK.of_frame hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok regs hnd h6 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := hK₂.of_frame hf₃
  have k0 := hK₃.keys.bytes 0 (Nat.zero_le _)
  refine WP.mono (keyOpAt_ok regs .aesdeclast _ s₃ hnd h6 (hK₃.keys.keys 0 (Nat.zero_le _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb, aesdeclast_st _ _ (roundKey w 0) k0, hI₃ b hb,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega]

end VG.Proof.Aes.X86.AesNi
