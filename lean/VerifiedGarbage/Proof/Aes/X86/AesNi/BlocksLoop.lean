module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Aes.X86.BlocksContract
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Rounds
public import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Aes.X86.AesNi.Imc`, which this module and modules that import it used -/

section

/-! ### `Aes.X86.AesNi.Dec`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega_using [hi]
  rw [getD_st _ hi, byte_invMixColumns _ hi, getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- InvSubBytes after InvShiftRows, byte by byte. -/
theorem byte_invSub (v : BitVec 128) {i : Nat} (hi : i < 16) :
    byte (aesMapBytes aesInvSbox (aesInvShiftRows v)) i =
      (invSubBytes (invShiftRows (st v))).getD i 0 := by
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega_using []
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
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega_using [hm]) (by omega_using [hm])
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
  rw [show j = nr - 1 - m by omega_using [hj]]
  exact dround_ok regs hnd h6 (by omega_using [hj, hj0]) hK hI

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
    refine WP.mono (ih (by omega_using [hk])) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (dround_ok' regs hnd h6 (j := 9 - k) (m := nr - 10 + k) (by omega_using [hnr, hk]) (by omega_using [hk])
      (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega_using []]; exact hI',
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
      refine WP.mono (dround_ok' regs hnd h6 (j := 11) (m := 0) (by omega_using []) (by omega_using []) (hK.of_frame hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (dround_ok' regs hnd h6 (j := 10) (m := 1) (by omega_using []) (by omega_using [])
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
        refine WP.mono (dround_ok' regs hnd h6 (j := 13) (m := 0) (by omega_using []) (by omega_using []) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h6 (j := 12) (m := 1) (by omega_using []) (by omega_using []) (hK₂.of_frame hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            DInv regs 14 w x (1 + 1) s' ∧ XFrame (.xmm6 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h6 (j := 11) (m := 2) (by omega_using []) (by omega_using []) (hK.of_frame hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h6 (j := 10) (m := 3) (by omega_using []) (by omega_using [])
          (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := hK.of_frame hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega_using [h]
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok regs hnd h6 hnr' 9 (by omega_using []) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := hK₂.of_frame hf₃
  have k0 := hK₃.keys.bytes 0 (Nat.zero_le _)
  refine WP.mono (keyOpAt_ok regs .aesdeclast _ s₃ hnd h6 (hK₃.keys.keys 0 (Nat.zero_le _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb, aesdeclast_st _ _ (roundKey w 0) k0, hI₃ b hb,
    invCipher_eq, show nr - 10 + 9 = nr - 1 by omega_using [hnr]]

end VG.Proof.Aes.X86.AesNi

end

end

/-!
# AES-NI on x86 (32-bit): the round keys through `aesimc`

`imcKeys` writes `InvMixColumns` of round keys `1 … nr − 1` to
`scratch + 16 j`, and copies the last round key to `scratch + 224`
(`imcKeys_ok`); `dKeys_of_imc` turns that into what `aesDec` needs.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ imcKey copyLast imcKeys)
open VG.Proof.Aes.X86 (reg32 addr_add in_reg reg_contains in_rd part_contains part_sub_reg)
open VG.Spec.Aes (roundKey bytesAt invMixColumns)
open VG.Proof.Aes (rkState)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- Where the round keys go through `aesimc`: the key schedule at `eax`
(240 bytes, readable) and the scratch buffer at `edx` (2048 bytes,
writable), apart. -/
structure ImcSetup (s₀ : State) : Prop where
  sch : reg32 (s₀.gpr .eax) 240 ∈ s₀.rd ++ s₀.wr
  scr : reg32 (s₀.gpr .edx) 2048 ∈ s₀.wr
  fitS : (s₀.gpr .eax).toNat + 240 ≤ 2 ^ 32
  fitB : (s₀.gpr .edx).toNat + 2048 ≤ 2 ^ 32
  sep : (reg32 (s₀.gpr .eax) 240).Disjoint (reg32 (s₀.gpr .edx) 2048)

/-- After writing the round keys `S` through `aesimc` to the scratch buffer,
from `s₀`. -/
structure ImcInv (s₀ : State) (S : List Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : ∀ r, r ≠ .xmm6 → s.xmm r = s₀.xmm r
  frame : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] s₀.mem s.mem
  le : ∀ j ∈ S, j ≤ 13
  keys : ∀ j ∈ S, s.mem.readW (addr (s₀.gpr .edx) (16 * j)) 128 =
    aesInvMixColumns (s₀.mem.readW (addr (s₀.gpr .eax) (16 * j)) 128)

theorem ImcInv.refl (s₀ : State) : ImcInv s₀ [] s₀ :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem ImcInv.of_frame {s₀ s s' : State} {S : List Nat} (h : ImcInv s₀ S s) (hf : XFrame [] s s') :
    ImcInv s₀ S s' :=
  ⟨hf.gpr.trans h.gpr, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (hf.xmm r (by simp)).trans (h.xmm r hr), by rw [hf.mem]; exact h.frame, h.le,
    by rw [hf.mem]; exact h.keys⟩

section
variable {s₀ : State} (hs : ImcSetup s₀)
include hs

theorem ImcSetup.schIn {j : Nat} (hj : j ≤ 14) :
    InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .eax) (16 * j)) 16 :=
  in_reg hs.sch hs.fitS (by omega_using [hj]) (by decide)

theorem ImcSetup.scrIn {o : Nat} (ho : o + 16 ≤ 240) :
    InRegions s₀.wr (addr (s₀.gpr .edx) o) 16 :=
  in_reg hs.scr hs.fitB (by omega_using [ho]) (by decide)

/-- Writes to bytes 16 … 239 of the scratch buffer leave the schedule. -/
theorem ImcSetup.sched {m m' : Mem} (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') {j : Nat} (hj : j ≤ 14) :
    m'.readW (addr (s₀.gpr .eax) (16 * j)) 128 = m.readW (addr (s₀.gpr .eax) (16 * j)) 128 :=
  hf.readW (reg_contains hs.fitS (by omega_using [hj]) (by decide))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.sep.sub_right (part_sub_reg hs.fitB (by omega_using []))) (by decide)

theorem ImcSetup.frameIn {m m' : Mem} {o : Nat} (ho₁ : 16 ≤ o) (ho : o + 16 ≤ 240) (v : BitVec 128)
    (hf : Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m m') :
    Frame [⟨addr (s₀.gpr .edx) 16, 224⟩] m (m'.writeW (addr (s₀.gpr .edx) o) v) :=
  hf.writeW (List.mem_singleton_self _) _
    (part_contains hs.fitB (by omega_using []) ho₁ (by omega_using [ho]) (by decide))

theorem imcKey_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 13) :
    WP isa (.block (imcKey j)) s (ImcInv s₀ (j :: S)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * j))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn (by omega_using [hj])
  have hout : InRegions s.wr (s.ea (at_ .edx (16 * j))) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega_using [hj])
  have ek : s.ea (at_ .eax (16 * j)) = addr (s₀.gpr .eax) (16 * j) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx (16 * j)) = addr (s₀.gpr .edx) (16 * j) := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [imcKey, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, XBinOp.eval, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, ?_, fun j' hj' => ?_,
    fun j' hj' => ?_⟩
  · exact hs.frameIn (by omega_using [hj1]) (by omega_using [hj]) _ hI.frame
  · rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hj
    · exact hI.le j' hj'
  · rw [hs.sched hI.frame (by omega_using [hj])]
    rcases List.mem_cons.mp hj' with rfl | hj'
    · rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
    · by_cases he : j' = j
      · subst he; rw [Mem.readW_writeW_self _ _ 16 _ (by decide)]
      · have h13 := hI.le j' hj'
        rw [Mem.readW_writeW_sep (by
            rw [addr_eq (by have := hs.fitB; omega_using [h13, this]), addr_eq (by have := hs.fitB; omega_using [hj, this])]
            exact Offset.sep _ (by omega_using [he]) (by omega_using [h13]) (by omega_using [hj])) (by decide), hI.keys j' hj']

/-- Some round keys through `aesimc`, those of `js`. -/
theorem imcRun_ok (js : List Nat) (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S : List Nat} {s : State}
    (hI : ImcInv s₀ S s) :
    WP isa (.block (js.flatMap imcKey)) s fun s' => ∃ S', ImcInv s₀ S' s' ∧ ∀ j, j ∈ js ∨ j ∈ S → j ∈ S' := by
  induction js generalizing S s with
  | nil => exact WP.block_nil ⟨S, hI, fun j h => by simpa using h⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (imcKey_ok hs hI (hjs j (by simp)).1 (hjs j (by simp)).2) fun s₁ hI₁ => ?_
    refine WP.mono (ih (fun j' hj' => hjs j' (by simp [hj'])) hI₁) fun s' ⟨S', hI', hS'⟩ =>
      ⟨S', hI', fun j' hj' => hS' j' ?_⟩
    rcases hj' with hj' | hj'
    · rcases List.mem_cons.mp hj' with rfl | hj'
      · exact .inr (by simp)
      · exact .inl hj'
    · exact .inr (by simp [hj'])

/-- The last round key, `nr`, copied to `scratch + 224`. -/
theorem copyLast_ok {S : List Nat} {s : State} (hI : ImcInv s₀ S s) {nr : Nat} (hnr : nr ≤ 14) :
    WP isa (.block (copyLast nr)) s fun s' => ImcInv s₀ S s' ∧
      s'.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128 := by
  have hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax (16 * nr))) 16 := by
    rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact hs.schIn hnr
  have hout : InRegions s.wr (s.ea (at_ .edx 224)) 16 := by
    rw [hI.wr, ea_at, hI.gpr]; exact hs.scrIn (by omega_using [])
  have ek : s.ea (at_ .eax (16 * nr)) = addr (s₀.gpr .eax) (16 * nr) := by rw [ea_at, hI.gpr]
  have es : s.ea (at_ .edx 224) = addr (s₀.gpr .edx) 224 := by rw [ea_at, hI.gpr]
  apply WP.of_runBlock
  simp only [copyLast, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    isa, State.load128, State.store128, ea_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    xmm_setXmm, hin, hout, Option.map_some, Option.some.injEq, exists_eq_left']
  rw [ek, es]
  refine ⟨⟨hI.gpr, hI.rd, hI.wr, fun r hr => by simp only [xmm_setXmm, hr, ite_false]; exact hI.xmm r hr, hs.frameIn (by omega_using []) (by omega_using []) _ hI.frame,
    hI.le, fun j hj => ?_⟩, ?_⟩
  · have h13 := hI.le j hj
    rw [Mem.readW_writeW_sep (by
        rw [addr_eq (by have := hs.fitB; omega_using [h13, this]), addr_eq (by have := hs.fitB; omega_using [this])]
        exact Offset.sep _ (by omega_using [h13]) (by omega_using [h13]) (by omega_using [])) (by decide), hI.keys j hj]
  · rw [Mem.readW_writeW_self _ _ 16 _ (by decide), hs.sched hI.frame hnr]

omit hs in
theorem cmpEcx_imc {S : List Nat} {s : State} (hI : ImcInv s₀ S s) (c : BitVec 32) :
    WP isa (.block [.alu .cmp .ecx (.imm c)]) s fun s' =>
      s'.zf = some (s₀.gpr .ecx - c == 0) ∧ ImcInv s₀ S s' :=
  WP.mono (cmpEcx_ok s c) fun _ ⟨hz, hf⟩ => ⟨by rw [hz, hI.gpr], hI.of_frame hf⟩

/-- What `imcKeys` leaves. -/
def ImcDone (s₀ : State) (nr : Nat) (s : State) : Prop :=
  ∃ S, ImcInv s₀ S s ∧ (∀ j, 1 ≤ j → j < nr → j ∈ S) ∧
    s.mem.readW (addr (s₀.gpr .edx) 224) 128 = s₀.mem.readW (addr (s₀.gpr .eax) (16 * nr)) 128

theorem imcKeys_ok {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hc : s₀.gpr .ecx = BitVec.ofNat 32 nr) : WP isa imcKeys s₀ (ImcDone s₀ nr) := by
  have run := fun js (hjs : ∀ j ∈ js, 1 ≤ j ∧ j ≤ 13) {S s} (hI : ImcInv s₀ S s) => imcRun_ok hs js hjs hI
  refine WP.seq ?_
  rw [WP.block_append_iff, show ((List.range 9).flatMap fun j => imcKey (j + 1)) =
    ((List.range 9).map (· + 1)).flatMap imcKey by simp [List.flatMap_map]]
  refine WP.mono (run _ (by decide) (ImcInv.refl s₀)) fun s₁ ⟨S₁, hI₁, hS₁⟩ => ?_
  have h9 : ∀ j, 1 ≤ j → j ≤ 9 → j ∈ S₁ := fun j h1 h2 => hS₁ j (.inl (by
    simp only [List.mem_map, List.mem_range]; exact ⟨j - 1, by omega_using [h2], by omega_using [h1]⟩))
  refine WP.mono (cmpEcx_imc hI₁ 10) fun s₂ ⟨hz₂, hI₂⟩ => ?_
  rw [hc] at hz₂
  rcases hnr with rfl | rfl | rfl
  · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₂ (by decide)) fun s₃ ⟨hI₃, hl₃⟩ =>
      ⟨S₁, hI₃, fun j h1 h2 => h9 j h1 (by omega_using [h2]), hl₃⟩
  all_goals
    refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff, show imcKey 10 ++ imcKey 11 = [10, 11].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₂) fun s₃ ⟨S₃, hI₃, hS₃⟩ => ?_
    have h11 : ∀ j, 1 ≤ j → j ≤ 11 → j ∈ S₃ := fun j h1 h2 => hS₃ j (by
      by_cases h : j ≤ 9
      · exact .inr (h9 j h1 h)
      · exact .inl (by simp; omega_using [h2, h]))
    refine WP.mono (cmpEcx_imc hI₃ 12) fun s₄ ⟨hz₄, hI₄⟩ => ?_
    rw [hc] at hz₄
  · refine WP.ite true (by simp [eval, hz₄]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.mono (copyLast_ok hs hI₄ (by decide)) fun s₅ ⟨hI₅, hl₅⟩ =>
      ⟨S₃, hI₅, fun j h1 h2 => h11 j h1 (by omega_using [h2]), hl₅⟩
  · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [show imcKey 12 ++ imcKey 13 ++ copyLast 14 = [12, 13].flatMap imcKey ++ copyLast 14 by simp,
      WP.block_append_iff]
    refine WP.mono (run _ (by decide) hI₄) fun s₅ ⟨S₅, hI₅, hS₅⟩ => ?_
    exact WP.mono (copyLast_ok hs hI₅ (by decide)) fun s₆ ⟨hI₆, hl₆⟩ =>
      ⟨S₅, hI₆, fun j h1 h2 => hS₅ j (by
        by_cases h : j ≤ 11
        · exact .inr (h11 j h1 h)
        · exact .inl (by simp; omega_using [h2, h])), hl₆⟩

/-- The round keys through `aesimc`, as decryption needs them. -/
theorem dKeys_of_imc {s : State} {nr : Nat} {w : List Byte} (hK : Keys nr w s₀)
    (hd : ImcDone s₀ nr s) : DKeys nr w s := by
  obtain ⟨S, hI, hS, hl⟩ := hd
  have hle := hK.le
  have ek : ∀ j, s.ea (at_ .eax (16 * j)) = s₀.ea (at_ .eax (16 * j)) := fun j => by
    rw [ea_at, ea_at, hI.gpr]
  have hK' : Keys nr w s := ⟨hle, fun j hj => by rw [ek, hI.rd, hI.wr]; exact hK.keys j hj,
    fun j hj => by
      rw [ek, ea_at, hs.sched hI.frame (by omega_using [hle, hj]), ← ea_at]; exact hK.bytes j hj⟩
  refine ⟨hK', fun j h1 h2 => ⟨?_, ?_⟩, ⟨?_, fun i hi => ?_⟩⟩
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega_using [hle, h2]))
  · rw [ea_at, hI.gpr, hI.keys j (hS j h1 h2), st_aesimc]
    refine congrArg invMixColumns ?_
    apply st_ext; intro i hi
    rw [getD_st _ hi, ← ea_at, hK.bytes j (by omega_using [h2]) i hi]
    simp [rkState, Vector.getD, hi]
  · rw [hI.rd, hI.wr, ea_at, hI.gpr]; exact in_rd (hs.scrIn (by omega_using []))
  · rw [ea_at, hI.gpr, hl, ← ea_at]; exact hK.bytes nr (Nat.le_refl _) i hi

end

end VG.Proof.Aes.X86.AesNi

end

end

/-!
# AES-NI on x86 (32-bit): the loops over whole blocks

The loops of `vg_aes_encrypt_blocks_aesni` and `vg_aes_decrypt_blocks_aesni`
are proven once for any transformation `f` of a list of block registers
that computes `F` on each, given what it needs of the state (`KP`, which
the loops keep): `aes` and `aesDec`. After `c` blocks, the first `c` data
blocks hold `F` of the original ones (`Inv`); the turn of six blocks and
the groups of the blocks left are the same code for different lists of
registers (`blocks_ok`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ regs6 loadData storeData blocks6 blocksTail)
open VG.Proof.Aes.X86 (BPre bSchP bRounds bDatP bN bScrP bSchR bDatR bScrR bArgR bRetR reg32 in_rd)

/-! ## Blocks as states -/

theorem stateAt_eq (m : Mem) (a : Addr) : Spec.Aes.stateAt m a = st (m.readW a 128) :=
  st_ext fun i hi => by
    rw [getD_st _ hi, VG.Proof.Gcm.X86.byte_readW _ _ hi]
    simp [Spec.Aes.stateAt, Vector.getD, hi]

theorem loadData_ok (p : Reg) (regs : List XReg) (j : Nat) (s : State) (hnd : regs.Nodup)
    (hin : ∀ k < regs.length, InRegions (s.rd ++ s.wr) (addr (s.gpr p) (16 * (j + k))) 16) :
    WP isa (.block (loadData p regs j)) s fun s' =>
      (∀ k (h : k < regs.length),
        st (s'.xmm regs[k]) = Spec.Aes.stateAt s.mem (addr (s.gpr p) (16 * (j + k)))) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ regs → s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hin
    rw [loadData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega_using [])
    rw [Nat.add_zero] at hin0
    refine WP.mono (Q := fun s₁ => s₁ = s.setXmm b (s.mem.readW (addr (s.gpr p) (16 * j)) 128)) ?_
      fun s₁ e₁ => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load128, ea_at, hin0,
        ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left']
    subst e₁
    refine WP.mono (ih (j + 1) _ (List.nodup_cons.mp hnd).2 (fun k hk => by
        rw [rd_setXmm, wr_setXmm, gpr_setXmm, show j + 1 + k = j + (k + 1) by omega_using []]
        exact hin (k + 1) (by omega_using [hk])))
      fun s' ⟨hb, g, m, rd, wr, hx⟩ => ?_
    rw [gpr_setXmm, mem_setXmm] at hb
    refine ⟨fun k hk => ?_, g, m, rd, wr, fun r hr => ?_⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [hx b hbs, xmm_setXmm_self, stateAt_eq]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hb k (by simpa using hk), show j + 1 + k = j + (k + 1) by omega_using []]
    · simp only [List.mem_cons, not_or] at hr
      rw [hx r hr.2, xmm_setXmm_of_ne _ _ hr.1]

theorem storeData_ok (p : Reg) (regs : List XReg) (j : Nat) (s : State)
    (hin : ∀ k < regs.length, InRegions s.wr (addr (s.gpr p) (16 * (j + k))) 16)
    (hw : (s.gpr p).toNat + 16 * (j + regs.length) ≤ 2 ^ 32) :
    WP isa (.block (storeData p regs j)) s fun s' =>
      (∀ k (h : k < regs.length), Spec.Aes.stateAt s'.mem (addr (s.gpr p) (16 * (j + k))) =
        st (s.xmm regs[k])) ∧
      Frame [⟨addr (s.gpr p) (16 * j), 16 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, s'.xmm r = s.xmm r) := by
  induction regs generalizing j s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hw
    rw [storeData, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega_using [])
    rw [Nat.add_zero] at hin0
    let s₁ : State := { s with mem := s.mem.writeW (addr (s.gpr p) (16 * j)) (s.xmm b) }
    refine WP.mono (Q := fun t => t = s₁) ?_ fun t e => ?_
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at, hin0,
        ↓reduceIte, Option.some.injEq, exists_eq_left']
      rfl
    subst e
    have ha0 : addr (s.gpr p) (16 * j) = (s.gpr p).setWidth 64 + BitVec.ofNat 64 (16 * j) :=
      addr_eq (by omega_using [hw])
    refine WP.mono (ih (j + 1) s₁ (fun k hk => by
        rw [show j + 1 + k = j + (k + 1) by omega_using []]; exact hin (k + 1) (by omega_using [hk]))
      (by show (s.gpr p).toNat + _ ≤ _; omega_using [hw])) fun s' ⟨hb, hf, g, rd, wr, hx⟩ => ?_
    let R₀ : Region := ⟨(s.gpr p).setWidth 64 + BitVec.ofNat 64 (16 * j), 16 * (bs.length + 1)⟩
    -- The blocks after the first: apart from it, and within the whole run.
    have hrest : ∀ r ∈ [(⟨addr (s₁.gpr p) (16 * (j + 1)), 16 * bs.length⟩ : Region)],
        Region.Disjoint ⟨(s.gpr p).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ r ∧ Region.Sub r R₀ := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      by_cases hl : bs.length = 0
      · rw [hl]
        exact ⟨fun a _ h => by simp [Region.Contains] at h, fun a h => by simp [Region.Contains] at h⟩
      · rw [show s₁.gpr p = s.gpr p from rfl, addr_eq (by omega_using [hw, hl])]
        exact ⟨Offset.disjoint _ (.inl (by omega_using [])) (by omega_using [hw]) (by omega_using [hw]), Offset.sub _ (by omega_using []) (by omega_using [])⟩
    refine ⟨fun k hk => ?_, ?_, g, rd, wr, hx⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [stateAt_eq, ha0, hf.readW (Region.contains_self _ _) (fun r hr => (hrest r hr).1) (by decide),
          ← ha0]
        exact congrArg st (Mem.readW_writeW_self _ _ 16 _ (by decide))
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [show j + (k + 1) = j + 1 + k by omega_using []]
        exact hb k (by simpa using hk)
    · rw [ha0]
      have hm : R₀ ∈ [R₀] := List.mem_singleton_self _
      refine (Frame.writeW (Frame.refl _ s.mem) hm (s.xmm b) ?_).trans
        (hf.sub fun r hr => ⟨_, hm, (hrest r hr).2⟩)
      rw [ha0]; exact Offset.contains _ (Nat.le_refl _) (by omega_using []) (by omega_using [hw])

end VG.Proof.Aes.X86.AesNi
