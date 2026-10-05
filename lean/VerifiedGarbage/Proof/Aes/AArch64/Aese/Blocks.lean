import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
import VerifiedGarbage.Proof.Aes.AArch64.Blocks

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec`. -/
section

/-!
# The Armv8 AES instructions: decryption

On registers holding states (`st`), `aesd` is `AddRoundKey`, `InvShiftRows`
and `InvSubBytes` (`st_invSub`), and `aesimc` is `InvMixColumns`
(`st_aesimc`). Since `InvMixColumns` is linear, `aesd` with `InvMixColumns` of
a round key then `aesimc` is a middle round of FIPS 197's inverse cipher,
whose `AddRoundKey` is moved through the `InvMixColumns` (the equivalent
inverse cipher, §5.3.5): `dround_st`.

The register of a block holds, after `m` middle rounds, a state that the
round key to be used next (`dkey`: the last round key at first, then the
middle ones through `InvMixColumns`) turns into the specification's state
after those rounds (`DInv`). `aesDec_ok` proves that
`Impl.Aes.AArch64.Aese.aesDec` decrypts each register of a list, from the
round keys as `decSetup` leaves them (`DKeys`).
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (kreg dreg drnd dlast aesDec)
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns addRoundKey invSbox roundKey invCipher)
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

theorem vbyte_invShiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesInvShiftRows x) i = vbyte x (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  rw [aesInvShiftRows, vbyte_ofVBytes _ h]

theorem vbyte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesInvMixColumns x) i =
      aesMul 0x0e (vbyte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (vbyte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (vbyte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (vbyte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, vbyte_ofVBytes _ h]

/-- `aesimc` is `InvMixColumns`. -/
theorem st_aesimc (k : BitVec 128) : st (aesInvMixColumns k) = VG.Spec.Aes.invMixColumns (st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, VG.Proof.Aes.AArch64.Aese.vbyte_invMixColumns _ hi, VG.Proof.Aes.AArch64.Aese.getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), VG.Proof.Aes.AArch64.Aese.mul_eq]

/-- `aesd` without its `AddRoundKey`: `InvShiftRows`, then `InvSubBytes`. -/
theorem st_invSub (v : BitVec 128) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (VG.Spec.Aes.invShiftRows (st v)) := by
  apply st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [getD_st _ hi, vbyte_mapBytes _ _ hi, VG.Proof.Aes.AArch64.Aese.vbyte_invShiftRows _ hi, VG.Proof.Aes.AArch64.Aese.getD_invSubBytes _ hi,
    VG.Proof.Aes.AArch64.Aese.getD_invShiftRows _ hi, getD_st _ (hs _), VG.Proof.Aes.AArch64.Aese.invSbox_eq]

/-- `InvMixColumns` of a round key, as the bytes of a round key. -/
def imcKey (rk : List Byte) : List Byte := (VG.Spec.Aes.invMixColumns (rkState rk)).toList

theorem getD_imcKey (rk : List Byte) {i : Nat} (hi : i < 16) :
    (VG.Proof.Aes.AArch64.Aese.imcKey rk).getD i 0 = (VG.Spec.Aes.invMixColumns (rkState rk)).getD i 0 := by
  simp [VG.Proof.Aes.AArch64.Aese.imcKey, Vector.getD, hi]

/-- `aesimc` of round key `rk` in a register. -/
theorem keyIs_aesimc {k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    KeyIs (aesInvMixColumns k) (VG.Proof.Aes.AArch64.Aese.imcKey rk) := by
  intro i hi
  rw [← getD_st _ hi, VG.Proof.Aes.AArch64.Aese.st_aesimc, VG.Proof.Aes.AArch64.Aese.getD_imcKey _ hi]
  refine congrArg (fun s => (VG.Spec.Aes.invMixColumns s).getD i 0) ?_
  apply st_ext; intro j hj
  rw [getD_st _ hj, hk j hj]
  simp [rkState, Vector.getD, hj]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`aesimc`, is a middle round of the inverse cipher from `Z`, with round key
`rk`, the register then needing `InvMixColumns` of `rk`. -/
theorem dround_st {v k : BitVec 128} {K rk : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (h : VG.Spec.Aes.addRoundKey (st v) K = Z) :
    VG.Spec.Aes.addRoundKey (st (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)))))
        (VG.Proof.Aes.AArch64.Aese.imcKey rk) = VG.Spec.Aes.invMixColumns (VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows Z)) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, getD_addRoundKey _ _ hi, VG.Proof.Aes.AArch64.Aese.getD_imcKey _ hi, VG.Proof.Aes.AArch64.Aese.st_aesimc,
    VG.Proof.Aes.AArch64.Aese.st_invSub, eor_st hk, h]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`eor` with `rk₀`: the last round of the inverse cipher. -/
theorem dlast_st {v k k₀ : BitVec 128} {K rk₀ : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (hk₀ : KeyIs k₀ rk₀) (h : VG.Spec.Aes.addRoundKey (st v) K = Z) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)) ^^^ k₀) =
      VG.Spec.Aes.addRoundKey (invSubBytes (VG.Spec.Aes.invShiftRows Z)) rk₀ := by
  rw [eor_st hk₀, VG.Proof.Aes.AArch64.Aese.st_invSub, eor_st hk, h]

/-! ## The rounds -/

/-- The round key the registers need after `m` middle rounds: the last at
first, then those of the middle rounds through `InvMixColumns`. -/
def dkey (nr : Nat) (w : List Byte) (m : Nat) : List Byte :=
  if m = 0 then roundKey w nr else VG.Proof.Aes.AArch64.Aese.imcKey (roundKey w (nr - m))

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`, but for `AddRoundKey` with
`dkey m`. -/
def DInv (regs : List VReg) (nr : Nat) (w : List Byte) (x : VReg → Spec.Aes.State) (m : Nat)
    (s : State) : Prop :=
  ∀ b ∈ regs, VG.Spec.Aes.addRoundKey (st (s.v b)) (VG.Proof.Aes.AArch64.Aese.dkey nr w m) = invMid nr w m (VG.Spec.Aes.addRoundKey (x b) (roundKey w nr))

/-- What decryption needs of the state: the round keys as `decSetup` leaves
them, and `x6`, `x7` for the number of rounds. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  last : KeyIs (s.v .v30) (roundKey w nr)
  mid : ∀ j, 1 ≤ j → j < nr → KeyIs (s.v (VG.Impl.Aes.AArch64.Aese.dreg j)) (VG.Proof.Aes.AArch64.Aese.imcKey (roundKey w j))
  k0 : KeyIs (s.v .v16) (roundKey w 0)
  x6 : s.gpr .x6 = BitVec.ofNat 64 nr - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 nr - 12

theorem BlockRegs.dreg {regs : List VReg} (h : BlockRegs regs) (j : Nat) : VG.Impl.Aes.AArch64.Aese.dreg j ∉ regs := by
  unfold Impl.Aes.AArch64.Aese.dreg
  split
  · exact fun h' => (h.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
  · exact h.kreg j

theorem BlockRegs.v30 {regs : List VReg} (h : BlockRegs regs) : VReg.v30 ∉ regs :=
  fun h' => (h.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl

theorem BlockRegs.v16 {regs : List VReg} (h : BlockRegs regs) : VReg.v16 ∉ regs :=
  fun h' => (h.2 _ h').1 rfl

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.DKeys nr w s)
    (hf : VFrame rs s s') (hrs : BlockRegs rs) : VG.Proof.Aes.AArch64.Aese.DKeys nr w s' :=
  ⟨h.rounds, by rw [hf.v _ hrs.v30]; exact h.last,
    fun j h1 h2 => by rw [hf.v _ (hrs.dreg j)]; exact h.mid j h1 h2,
    by rw [hf.v _ hrs.v16]; exact h.k0, by rw [hf.gpr]; exact h.x6, by rw [hf.gpr]; exact h.x7⟩

theorem drnd_run (k b : VReg) (s : State) :
    runBlock isa [.vop (.aesd b k), .vop (.aesimc b b)] s =
      some (s.setV b (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (s.v b ^^^ s.v k))))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_setV]

/-- A middle round, with the key register holding `dkey m`. -/
theorem dround_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {k : VReg} (hkr : k ∉ regs) {s : State}
    (hk : KeyIs (s.v k) (VG.Proof.Aes.AArch64.Aese.dkey nr w m)) (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x m s) :
    WP isa (.block (drnd regs k)) s fun s' => VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (m + 1) s' ∧ VFrame regs s s' := by
  refine WP.mono (each_ok _
    (fun v k => aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k))))
    k (fun b s _ => VG.Proof.Aes.AArch64.Aese.drnd_run _ b s) regs s hr.1 hkr)
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, VG.Proof.Aes.AArch64.Aese.dkey, ite_eq_right (by omega), show nr - (m + 1) = nr - 1 - m by omega, VG.Proof.Aes.AArch64.Aese.dround_st hk (hI b hb),
    invMid_succ]
  rfl

/-- A middle round with round key `j = nr − m` (`m ≥ 1`). -/
theorem dround_ok' {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (j : Nat) {k : VReg} (e : k = VG.Impl.Aes.AArch64.Aese.dreg j) (hj : j + m = nr)
    (hj1 : 1 < j) (hm : 1 ≤ m) {s : State} (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x m s) :
    WP isa (.block (drnd regs k)) s fun s' => VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (m + 1) s' ∧ VFrame regs s s' := by
  subst e
  refine VG.Proof.Aes.AArch64.Aese.dround_ok hr (by omega) (hr.dreg j) ?_ hI
  rw [VG.Proof.Aes.AArch64.Aese.dkey, ite_eq_right (by omega), show nr - m = j by omega]
  exact hK.mid j (by omega) (by omega)

/-- Two middle rounds, with round keys `j` and `j − 1`. -/
theorem dtwo_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = VG.Impl.Aes.AArch64.Aese.dreg j)
    (e₂ : k₂ = VG.Impl.Aes.AArch64.Aese.dreg (j - 1)) (hj : j + m = nr) (hj1 : 2 < j) (hm : 1 ≤ m) {s : State}
    (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x m s) :
    WP isa (.block (drnd regs k₁ ++ drnd regs k₂)) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (m + 2) s' ∧ VFrame regs s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.dround_ok' hr j e₁ hj (by omega) hm hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (VG.Proof.Aes.AArch64.Aese.dround_ok' hr (j - 1) e₂ (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ⟨hI₂, hf₁.trans hf₂⟩

/-- The middle rounds with round keys `9 … 2`. -/
theorem drounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} (hnr : 10 ≤ nr) (k : Nat) (hk : k ≤ 8) {s : State} (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s)
    (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (nr - 9) s) :
    WP isa (.block ((List.range k).flatMap fun j => drnd regs (kreg (9 - j)))) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (nr - 9 + k) s' ∧ VFrame regs s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.dround_ok' hr (9 - k) (by simp [Impl.Aes.AArch64.Aese.dreg, show 9 - k ≠ 13 by omega])
      (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁) fun s' ⟨hI', hf'⟩ => ⟨?_, hf₁.trans hf'⟩
    rw [show nr - 9 + (k + 1) = nr - 9 + k + 1 by omega]; exact hI'

/-- The middle rounds with round keys `Nr − 1 … 10`. -/
theorem dmid_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x 1 s) :
    WP isa (.ite (.zero .x .x6) (.block [])
        (.seq (.ite (.zero .x .x7) (.block []) (.block (drnd regs .v29 ++ drnd regs .v28)))
          (.block (drnd regs .v27 ++ drnd regs .v26)))) s
      fun s' => VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (nr - 9) s' ∧ VFrame regs s s' := by
  have hx6 := hK.x6
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hx7 := hK.x7
    have h₁ : WP isa (.ite (.zero .x .x7) (.block [])
        (.block (drnd regs .v29 ++ drnd regs .v28))) s
        (fun s' => VG.Proof.Aes.AArch64.Aese.DInv regs 12 w x 1 s' ∧ VFrame regs s s') :=
      WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
        (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_)
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hx7 := hK.x7
    have h₁ : WP isa (.ite (.zero .x .x7) (.block [])
        (.block (drnd regs .v29 ++ drnd regs .v28))) s
        (fun s' => VG.Proof.Aes.AArch64.Aese.DInv regs 14 w x 3 s' ∧ VFrame regs s s') :=
      WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
        (fun h => absurd h (by decide))
        (fun _ => VG.Proof.Aes.AArch64.Aese.dtwo_ok hr 13 rfl rfl (by omega) (by omega) (by omega) hK hI)
    refine WP.seq (WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_)
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem dlast_run (b : VReg) (s : State) (hb16 : b ≠ .v16) :
    runBlock isa [.vop (.aesd b .v17), .vop (.logic .eor b b .v16)] s =
      some (s.setV b (aesMapBytes aesInvSbox (aesInvShiftRows (s.v b ^^^ s.v .v17)) ^^^ s.v .v16)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (Ne.symm hb16), setV_setV]

theorem dlast_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x (nr - 1) s) :
    WP isa (.block (dlast regs)) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = invCipher nr w (x b)) ∧ VFrame regs s s' := by
  have hnr : 2 ≤ nr := by rcases hK.rounds with h | h | h <;> omega
  have h17 : .v17 ∉ regs := fun h' => (hr.2 _ h').2.1 rfl
  have h16 : ∀ b ∈ regs, b ≠ .v16 := fun b h' => (hr.2 _ h').1
  have e : ∀ (rs : List VReg) (s : State), rs.Nodup → .v17 ∉ rs → (∀ b ∈ rs, b ≠ .v16) →
      WP isa (.block (dlast rs)) s fun s' =>
        (∀ b ∈ rs, s'.v b = aesMapBytes aesInvSbox (aesInvShiftRows (s.v b ^^^ s.v .v17)) ^^^ s.v .v16) ∧
        VFrame rs s s' := by
    intro rs
    induction rs with
    | nil => intro s _ _ _; exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
    | cons b bs ih =>
      intro s hnd hk h16'
      have hb17 : b ≠ .v17 := fun h => hk (h ▸ List.mem_cons_self ..)
      have hb16 : b ≠ .v16 := h16' b List.mem_cons_self
      have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
      rw [Impl.Aes.AArch64.Aese.dlast, List.flatMap_cons, WP.block_append_iff]
      refine WP.of_runBlock ⟨_, VG.Proof.Aes.AArch64.Aese.dlast_run b s hb16, ?_⟩
      refine WP.mono (ih _ (List.nodup_cons.mp hnd).2 (fun h => hk (List.mem_cons_of_mem _ h))
        (fun c hc => h16' c (List.mem_cons_of_mem _ hc))) fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [hfr.v _ hbs]; simp [State.setV]
        · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
          rw [hv c hc]; simp [State.setV, hcb, Ne.symm hb17, Ne.symm hb16]
      · refine ⟨hfr.gpr, hfr.sp, hfr.mem, hfr.rd, hfr.wr, fun r hr => ?_⟩
        simp only [List.mem_cons, not_or] at hr
        rw [hfr.v r hr.2]; simp [State.setV, hr.1]
  refine WP.mono (e regs s hr.1 h17 h16) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  have hk1 : KeyIs (s.v .v17) (VG.Proof.Aes.AArch64.Aese.dkey nr w (nr - 1)) := by
    rw [VG.Proof.Aes.AArch64.Aese.dkey, ite_eq_right (by omega), show nr - (nr - 1) = 1 by omega]
    exact hK.mid 1 (by omega) (by omega)
  rw [hv b hb, VG.Proof.Aes.AArch64.Aese.dlast_st hk1 hK.k0 (hI b hb), invCipher_eq]

theorem aesDec_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : VG.Proof.Aes.AArch64.Aese.DKeys nr w s) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = invCipher nr w (st (s.v b))) ∧ VFrame regs s s' := by
  have hnr : 10 ≤ nr := by rcases hK.rounds with h | h | h <;> omega
  let x : VReg → Spec.Aes.State := fun b => st (s.v b)
  have hI₀ : VG.Proof.Aes.AArch64.Aese.DInv regs nr w x 0 s := fun b _ => by simp [VG.Proof.Aes.AArch64.Aese.dkey, invMid, x]
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.dround_ok hr (m := 0) (by omega) hr.v30 (by simpa [VG.Proof.Aes.AArch64.Aese.dkey] using hK.last) hI₀)
    fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.dmid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.drounds_ok hr hnr 8 (by omega) (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s₃ ⟨hI₃, hf₃⟩ => ?_
  rw [show nr - 9 + 8 = nr - 1 by omega] at hI₃
  exact WP.mono (VG.Proof.Aes.AArch64.Aese.dlast_ok hr (hK.of_frame (hf₁.trans (hf₂.trans hf₃)) hr) hI₃)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans (hf₃.trans hf'))⟩

end VG.Proof.Aes.AArch64.Aese

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks`. -/
section

/-!
# AES on whole blocks with the Armv8 Cryptographic Extension

`encryptBlocks_verified` and `decryptBlocks_verified` prove
`Impl.Aes.AArch64.Aese.encryptBlocks` and `decryptBlocks` against
`Proof.Aes.blocksAArch64` (the contract the bitsliced functions are proven
against), and so against the shared contracts.

Both are `blocks` around a transformation of the block registers: `aes`
(`aes_ok`) or `aesDec` (`aesDec_ok`), which needs the round keys as its
setup leaves them (`Keys` or `DKeys`): a `BlockFn`. The loops keep, after `c`
blocks, the first `c` data blocks transformed and the others as they were
(`EcbInv`, as for the bitsliced functions): each group is loaded into the
registers (`ldData_ok`), transformed, and stored back (`stData_ok`).
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese
open VG.Proof.Aes.AArch64 (EcbInv ecbOut ecbInv_orig)
open VG.Spec.Aes (roundKey)

/-- A transformation of the block registers, `F nr w` of each, given what
`K nr w` says of the state, which survives the transformation and anything
that leaves `v16`–`v30`, `x6` and `x7` alone. -/
structure BlockFn where
  f : List VReg → Prog isa
  F : Nat → List Byte → Spec.Aes.State → Spec.Aes.State
  K : Nat → List Byte → State → Prop
  of_v : ∀ {nr w} {vs : List VReg} {s s' : State}, K nr w s → BlockRegs vs →
    (∀ r, r ∉ vs → s'.v r = s.v r) → s'.gpr .x6 = s.gpr .x6 → s'.gpr .x7 = s.gpr .x7 → K nr w s'
  ok : ∀ {regs : List VReg} {nr w} {s : State}, BlockRegs regs → K nr w s →
    WP isa (f regs) s fun s' => (∀ b ∈ regs, st (s'.v b) = F nr w (st (s.v b))) ∧ VFrame regs s s'

theorem DKeys.of_v {nr : Nat} {w : List Byte} {vs : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.DKeys nr w s)
    (hrs : BlockRegs vs) (hv : ∀ r, r ∉ vs → s'.v r = s.v r) (h6 : s'.gpr .x6 = s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr .x7) : VG.Proof.Aes.AArch64.Aese.DKeys nr w s' :=
  ⟨h.rounds, by rw [hv _ hrs.v30]; exact h.last,
    fun j h1 h2 => by rw [hv _ (hrs.dreg j)]; exact h.mid j h1 h2,
    by rw [hv _ hrs.v16]; exact h.k0, by rw [h6]; exact h.x6, by rw [h7]; exact h.x7⟩

def encFn : VG.Proof.Aes.AArch64.Aese.BlockFn :=
  ⟨VG.Impl.Aes.AArch64.Aese.aes, Spec.Aes.cipher, Keys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7, fun hr hK => aes_ok hr hK⟩

def decFn : VG.Proof.Aes.AArch64.Aese.BlockFn :=
  ⟨aesDec, Spec.Aes.invCipher, VG.Proof.Aes.AArch64.Aese.DKeys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7,
    fun hr hK => VG.Proof.Aes.AArch64.Aese.aesDec_ok hr hK⟩

/-! ## The precondition and the loop invariant -/

section
variable (s₀ : State)

abbrev bkp : Addr := s₀.gpr .x0
abbrev bnr : Nat := (s₀.gpr .x1).toNat
abbrev bdp : Addr := s₀.gpr .x2
abbrev bnb : Nat := (s₀.gpr .x3).toNat
abbrev bdR : Region := ⟨VG.Proof.Aes.AArch64.Aese.bdp s₀, 16 * VG.Proof.Aes.AArch64.Aese.bnb s₀⟩
/-- The key schedule. -/
abbrev bsch : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.Aes.AArch64.Aese.bkp s₀) (16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ + 1))

end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨VG.Proof.Aes.AArch64.Aese.bkp s₀, 240⟩]
  wr : s₀.wr = [VG.Proof.Aes.AArch64.Aese.bdR s₀, ⟨s₀.gpr .x4, 2048⟩]
  s_d : Region.Disjoint ⟨VG.Proof.Aes.AArch64.Aese.bkp s₀, 240⟩ (VG.Proof.Aes.AArch64.Aese.bdR s₀)
  d_s : Region.Disjoint (VG.Proof.Aes.AArch64.Aese.bdR s₀) ⟨s₀.gpr .x4, 2048⟩
  wrap : (VG.Proof.Aes.AArch64.Aese.bdp s₀).toNat + 16 * VG.Proof.Aes.AArch64.Aese.bnb s₀ ≤ 2 ^ 64
  rounds : VG.Proof.Aes.AArch64.Aese.bnr s₀ = 10 ∨ VG.Proof.Aes.AArch64.Aese.bnr s₀ = 12 ∨ VG.Proof.Aes.AArch64.Aese.bnr s₀ = 14

theorem bpre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksAArch64 f).pre s₀) : VG.Proof.Aes.AArch64.Aese.BPre s₀ := by
  obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h5, h6, h7⟩

namespace BPre
variable {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀)
include hp

theorem nb16 : 16 * VG.Proof.Aes.AArch64.Aese.bnb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem dat : VG.Proof.Aes.AArch64.Aese.bdR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem n16 : 16 * VG.Proof.Aes.AArch64.Aese.bnb s₀ < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => hp.d_s (s₀.gpr .x4) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (s₀.gpr .x4 - VG.Proof.Aes.AArch64.Aese.bdp s₀).isLt
  omega

theorem key_in {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨VG.Proof.Aes.AArch64.Aese.bkp s₀, 240⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega)⟩

end BPre

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure BInv (B : VG.Proof.Aes.AArch64.Aese.BlockFn) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀
  keys : B.K (VG.Proof.Aes.AArch64.Aese.bnr s₀) (VG.Proof.Aes.AArch64.Aese.bsch s₀) s
  x2 : s.gpr .x2 = VG.Proof.Aes.AArch64.Aese.bdp s₀ + BitVec.ofNat 64 (16 * p)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ - p)
  frame : Frame [VG.Proof.Aes.AArch64.Aese.bdR s₀] s₀.mem s.mem
  data : EcbInv s₀.mem s.mem (VG.Proof.Aes.AArch64.Aese.bdp s₀) (VG.Proof.Aes.AArch64.Aese.bnb s₀) c (ecbOut B.F s₀.mem (VG.Proof.Aes.AArch64.Aese.bdp s₀) (VG.Proof.Aes.AArch64.Aese.bnr s₀) (VG.Proof.Aes.AArch64.Aese.bsch s₀))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## Loading and storing the blocks -/

theorem st_readW (m : Mem) (p : Addr) : st (m.readW p 128) = Spec.Aes.stateAt m p := by
  apply Vector.ext; intro i hi
  simp only [st, Spec.Aes.stateAt, Vector.getElem_ofFn]
  exact vbyte_readW m p hi

theorem ldData_ok : ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → j + regs.length ≤ 4096 →
    (∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + k))) 16) →
    WP isa (.block (ldData regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.v regs[k] = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      Fr [] regs s s'
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Fr.refl _ _ _⟩
  | b :: bs, j, s, hnd, hj, hin => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hj
    rw [ldData, WP.block_cons_iff]
    refine ⟨_, exec_ldrq (by omega) (by simpa using hin 0 (by simp)), ?_⟩
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.ldData_ok bs (j + 1) _ (List.nodup_cons.mp hnd).2 (by omega) fun k hk => by
      have := hin (k + 1) (by simp; omega)
      simpa [State.setV, show j + 1 + k = j + (k + 1) by omega] using this)
      fun s' ⟨e, f⟩ => ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; rw [f.v _ hbs, setV_v_self]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk)]
        simp [State.setV, show j + 1 + k = j + (k + 1) by omega]
    · exact ⟨fun r _ => by rw [f.gpr r (by simp)]; rfl, fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        rw [f.v r hr.2, setV_v_of_ne _ _ hr.1], f.sp, f.mem, f.rd, f.wr⟩

theorem off_toNat' (D : Addr) {i k : Nat} (hi : i < 2 ^ 64) (hk : k < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 k)).toNat =
      if k ≤ i then i - k else 2 ^ 64 + i - k := Offset.sub_toNat' D hk hi

/-- One block stored, by a 16-byte store. -/
theorem ecbInv_write {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : EcbInv m₀ m D n k F)
    (hv : ∀ t < 16, vbyte v t = (F k).getD t 0) :
    EcbInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) D n (k + 1) F ∧
      Frame [⟨D, 16 * n⟩] m (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [VG.Proof.Aes.AArch64.Aese.off_toNat' D (by omega) (by omega)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega)]
        show vbyte _ _ = _
        rw [hv _ h2, show i / 16 = k by omega, show i % 16 = i - 16 * k by omega]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega), h i hi,
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have := (x - D).isLt
    rw [Offset.sub_add_eq] at hlt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega)] at hlt
    omega

theorem stData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} (hn : 16 * n ≤ 2 ^ 64) :
    ∀ (regs : List VReg) (j : Nat) (s : State),
    s.gpr .x2 = D + BitVec.ofNat 64 (16 * c) → j + regs.length ≤ 4096 → c + j + regs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.wr → EcbInv m₀ s.mem D n (c + j) F →
    (∀ k (h : k < regs.length), ∀ t < 16, vbyte (s.v regs[k]) t = (F (c + j + k)).getD t 0) →
    WP isa (.block (stData regs j)) s fun s' =>
      EcbInv m₀ s'.mem D n (c + j + regs.length) F ∧ Frame [⟨D, 16 * n⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, hD, _ => WP.block_nil ⟨by simpa using hD, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl⟩
  | b :: bs, j, s, hx2, hj, hc, hw, hD, hF => by
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x2 + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hx2, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega)]
    rw [stData, WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega) (by rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega) (by omega)⟩), ?_⟩
    rw [ha]
    have hst := VG.Proof.Aes.AArch64.Aese.ecbInv_write hn (by omega) hD (v := s.v b) fun t ht => by
      have := hF 0 (by simp) t ht
      simpa using this
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.stData_ok (m₀ := m₀) (c := c) (F := F) hn bs (j + 1) _ hx2 (by omega) (by omega) hw
      (by rw [show c + (j + 1) = c + j + 1 by omega]; exact hst.1) (fun k hk t ht => by
        have := hF (k + 1) (by simp; omega) t ht
        simp only [List.getElem_cons_succ] at this
        rw [show c + (j + 1) + k = c + j + (k + 1) by omega]; exact this))
      fun s' ⟨d', f', g', v', sp', rd', wr'⟩ => ⟨?_, hst.2.trans f', g', v', sp', rd', wr'⟩
    rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega]; exact d'

/-! ## The loop bodies -/

theorem bregs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) : BlockRegs rs := by
  rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Load, transform and store the blocks `c … c + N − 1` (`N` the number of
registers). -/
theorem group_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s) (hQ : ∀ s', VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ldData rs 0)) (.seq (B.f rs) (.block (stData rs 0 ++ tail)))) s Q := by
  have hbr := VG.Proof.Aes.AArch64.Aese.bregs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hn := hp.n16
  have hin : ∀ k < rs.length, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by
      rw [hI.rd, hI.wr, hI.x2, Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega)]
      exact ⟨_, List.mem_append_right _ hp.dat, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.ldData_ok rs 0 s hbr.1 (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have hK₁ := B.of_v hI.keys hbr f₁.v (f₁.gpr _ (by simp)) (f₁.gpr _ (by simp))
  refine WP.seq (WP.mono (B.ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  rw [WP.block_append_iff]
  have hx2 : s₂.gpr .x2 = VG.Proof.Aes.AArch64.Aese.bdp s₀ + BitVec.ofNat 64 (16 * c) := by
    rw [f₂.gpr, f₁.gpr _ (by simp), hI.x2]
  have hF : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = (ecbOut B.F s₀.mem (VG.Proof.Aes.AArch64.Aese.bdp s₀) (VG.Proof.Aes.AArch64.Aese.bnr s₀) (VG.Proof.Aes.AArch64.Aese.bsch s₀) (c + 0 + k)).getD t 0 := by
    intro k h t ht
    rw [← getD_st _ ht, e₂ _ (List.getElem_mem h), e₁ k h, VG.Proof.Aes.AArch64.Aese.st_readW, hI.x2,
      Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + 0 + k) by omega),
      ecbInv_orig hI.data (by omega) (by omega)]
    rfl
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.stData_ok (m₀ := s₀.mem) (D := VG.Proof.Aes.AArch64.Aese.bdp s₀) (c := c) hp.nb16 rs 0 s₂ hx2 (by omega)
      (by omega) (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.dat)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) hF)
    fun s₃ ⟨d₃, fr₃, g₃, v₃, sp₃, rd₃, wr₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have g : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, f₁.gpr r (by simp)]
  refine ⟨hc, ?_, by rw [g]; exact hI.x2, by rw [g]; exact hI.x3,
    by rw [hm₂] at fr₃; exact hI.frame.trans fr₃, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  exact B.of_v (B.of_v hK₁ hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])) hbr
    (fun r _ => by rw [v₃]) (by rw [g₃]) (by rw [g₃])

theorem btail8_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 8) c s) :
    WP isa (.block [.addImm .x .x2 .x2 128, .subImm .x .x3 .x3 8, .lsr .x .x13 .x3 3]) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have h4 : BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega), show VG.Proof.Aes.AArch64.Aese.bnb s₀ - c - 8 = VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8) by omega]
  refine ⟨⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩, ?_⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    exact h4
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [h4, ushr3 (by omega)]

theorem btail1_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) {c : Nat} (hc : c + 1 ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 1) c s) :
    WP isa (.block [.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1]) s (VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 1) (c + 1)) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega), show VG.Proof.Aes.AArch64.Aese.bnb s₀ - c - 1 = VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 1) by omega]

theorem blk8_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s) :
    WP isa (blk8 B.f) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8)) / 8) :=
  VG.Proof.Aes.AArch64.Aese.group_ok B hp regs8 (.inl rfl) _ hc hI fun _ hI' => VG.Proof.Aes.AArch64.Aese.btail8_ok B hp hc hI'

theorem blk1_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) {c : Nat} (hc : c + 1 ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s) : WP isa (blk1 B.f) s (VG.Proof.Aes.AArch64.Aese.BInv B s₀ (c + 1) (c + 1)) :=
  VG.Proof.Aes.AArch64.Aese.group_ok B hp [.v0] (.inr rfl) _ hc hI fun _ hI' => VG.Proof.Aes.AArch64.Aese.btail1_ok B hp hc hI'

/-- The loops, from the state after the setup. -/
theorem loops_ok (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) {s₁ : State} (hI₁ : VG.Proof.Aes.AArch64.Aese.BInv B s₀ 0 0 s₁)
    (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8)) :
    WP isa (.seq (.ite (.zero .x .x13) (.block []) (.loop (blk8 B.f) (.nonzero .x .x13)))
      (.ite (.zero .x .x3) (.block []) (.loop (blk1 B.f) (.nonzero .x .x3)))) s₁
      (VG.Proof.Aes.AArch64.Aese.BInv B s₀ (VG.Proof.Aes.AArch64.Aese.bnb s₀) (VG.Proof.Aes.AArch64.Aese.bnb s₀)) := by
  have hn := hp.n16
  refine WP.seq (WP.mono (Q := fun s => ∃ c, VG.Proof.Aes.AArch64.Aese.bnb s₀ - c < 8 ∧ VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8 = 0)) (eval_zero h13 (by omega)) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.AArch64.Aese.bnb s₀ - c ∧ c + 8 ≤ VG.Proof.Aes.AArch64.Aese.bnb s₀ ∧ VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (blk8 B.f) s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, VG.Proof.Aes.AArch64.Aese.bnb s₀ - c < 8 ∧ VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.AArch64.Aese.blk8_ok B hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [eval_nonzero h13' (by omega)]
        by_cases hlt : VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega, c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega, VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (VG.Proof.Aes.AArch64.Aese.bnb s₀) s₁ ⟨0, rfl, by simp at h; omega, hI₁⟩
  refine WP.ite (decide (VG.Proof.Aes.AArch64.Aese.bnb s₀ - c = 0)) (eval_zero hI₂.x3 (by omega)) (fun h => ?_) (fun h => ?_)
  · have : c = VG.Proof.Aes.AArch64.Aese.bnb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.AArch64.Aese.bnb s₀ - c ∧ c < VG.Proof.Aes.AArch64.Aese.bnb s₀ ∧ VG.Proof.Aes.AArch64.Aese.BInv B s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blk1 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x3) s' = some false ∧ VG.Proof.Aes.AArch64.Aese.BInv B s₀ (VG.Proof.Aes.AArch64.Aese.bnb s₀) (VG.Proof.Aes.AArch64.Aese.bnb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.AArch64.Aese.blk1_ok B hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x3 (by omega)]
      by_cases hlast : VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 1) = 0
      · have : c + 1 = VG.Proof.Aes.AArch64.Aese.bnb s₀ := by omega
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], VG.Proof.Aes.AArch64.Aese.bnb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < VG.Proof.Aes.AArch64.Aese.bnb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (VG.Proof.Aes.AArch64.Aese.bnb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

/-! ## The setups -/

/-- What `keysCommon` leaves. -/
structure Common (s₀ s : State) : Prop where
  kreg : ∀ j < 13, s.v (kreg j) = s₀.mem.readW (VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * j)) 128
  v30 : s.v .v30 = s₀.mem.readW (VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.bnr s₀)) 128
  x9 : s.gpr .x9 = VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.bnr s₀)
  x6 : s.gpr .x6 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnr s₀) - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnr s₀) - 12
  x13 : s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem common_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) : WP isa (.block keysCommon) s₀ (VG.Proof.Aes.AArch64.Aese.Common s₀) := by
  have hR := hp.rounds
  have hn := hp.nb16
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnr s₀) := by simp [VG.Proof.Aes.AArch64.Aese.bnr]
  have hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀) := by simp [VG.Proof.Aes.AArch64.Aese.bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.bnr s₀) := by
    rw [g, g, shl4]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, f₁.rd, f₁.wr⟩
  · simp only [State.setV, State.write, (kreg_ne j).2, ite_false]
    rw [e₁ j hj]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx3]
    exact ushr3 (by omega)
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

theorem encSetup_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) :
    WP isa (.block encSetup) s₀ fun s => VG.Proof.Aes.AArch64.Aese.BInv VG.Proof.Aes.AArch64.Aese.encFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.common_ok hp) fun s₁ c₁ => ?_
  have e9' : VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.bnr s₀) - BitVec.ofNat 64 16 =
      VG.Proof.Aes.AArch64.Aese.bkp s₀ + BitVec.ofNat 64 (16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * VG.Proof.Aes.AArch64.Aese.bnr s₀ - 16 = 16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ - 1) by omega]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ VG.Proof.Aes.AArch64.Aese.bnr s₀ → 16 * j + 16 ≤ 16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ + 1) := fun j hj => by omega
  refine ⟨⟨Nat.zero_le _, ⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega)]
    exact keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [VG.Proof.Aes.AArch64.Aese.bnb]
  · simp only [State.setV, State.write, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    simp only [State.setV, State.write, c₁.mem]
    rw [ite_eq_right (by omega)]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]

theorem dreg_inj : ∀ j < 13, ∀ i < 13, VG.Impl.Aes.AArch64.Aese.dreg (j + 1) = VG.Impl.Aes.AArch64.Aese.dreg (i + 1) → j = i := by decide

/-- `aesimc` of the first `k` middle round keys. -/
theorem imcs_ok (s : State) :
    ∀ k ≤ 13, WP isa (.block ((List.range k).map fun j => .vop (.aesimc (VG.Impl.Aes.AArch64.Aese.dreg (j + 1)) (VG.Impl.Aes.AArch64.Aese.dreg (j + 1))))) s
      fun s' => (∀ j < 13, s'.v (VG.Impl.Aes.AArch64.Aese.dreg (j + 1)) =
          if j < k then aesInvMixColumns (s.v (VG.Impl.Aes.AArch64.Aese.dreg (j + 1))) else s.v (VG.Impl.Aes.AArch64.Aese.dreg (j + 1))) ∧
        (∀ r, (∀ j < 13, r ≠ VG.Impl.Aes.AArch64.Aese.dreg (j + 1)) → s'.v r = s.v r) ∧
        s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun j _ => by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.imcs_ok s k (by omega)) fun s₁ ⟨e₁, o₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, isa, exec,
        VOp.eval, Option.map_some]; rfl, ?_⟩
    refine ⟨fun j hj => ?_, fun r hr => ?_, g₁, m₁, rd₁, wr₁⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [setV_v_self, e₁ j hj, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [setV_v_of_ne _ _ fun h => hjk (VG.Proof.Aes.AArch64.Aese.dreg_inj j hj k (by omega) h), e₁ j hj]
        by_cases hjk' : j < k
        · rw [ite_eq_left hjk', ite_eq_left (by omega)]
        · rw [ite_eq_right hjk', ite_eq_right (by omega)]
    · rw [setV_v_of_ne _ _ (hr k (by omega)), o₁ r hr]

theorem dreg_ne : ∀ j < 13, VG.Impl.Aes.AArch64.Aese.dreg (j + 1) ≠ .v30 ∧ VG.Impl.Aes.AArch64.Aese.dreg (j + 1) ≠ .v16 := by decide

theorem decSetup_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀) :
    WP isa (.block decSetup) s₀ fun s => VG.Proof.Aes.AArch64.Aese.BInv VG.Proof.Aes.AArch64.Aese.decFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.common_ok hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega)), WP.block_nil ?_⟩
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hL : ∀ j, j ≤ VG.Proof.Aes.AArch64.Aese.bnr s₀ → 16 * j + 16 ≤ 16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ + 1) := fun j hj => by omega
  have x0 : s₁.gpr .x0 = VG.Proof.Aes.AArch64.Aese.bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  -- The middle round keys, before `aesimc`.
  have pre : ∀ j, 1 ≤ j → j ≤ 13 → j < VG.Proof.Aes.AArch64.Aese.bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (VG.Impl.Aes.AArch64.Aese.dreg j))
        (roundKey (VG.Proof.Aes.AArch64.Aese.bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (VG.Proof.Aes.AArch64.Aese.bkp s₀) (L := 16 * (VG.Proof.Aes.AArch64.Aese.bnr s₀ + 1)) (j := 13) (hL 13 (by omega))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega)]
      exact keyIs_readW _ _ (hL j (by omega))
  refine ⟨⟨Nat.zero_le _, ⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₂ _ fun j hj => (VG.Proof.Aes.AArch64.Aese.dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega
    have := e₂ (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, ite_eq_left (by omega)] at this
    rw [this]
    exact VG.Proof.Aes.AArch64.Aese.keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (VG.Proof.Aes.AArch64.Aese.dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega)
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [VG.Proof.Aes.AArch64.Aese.bnb]
  · rw [m₂]; simp only [State.setV, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    rw [m₂]; simp only [State.setV, c₁.mem]
    rw [ite_eq_right (by omega)]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]
  · rw [g₂]; simp only [State.setV, c₁.x13]

/-! ## The whole functions -/

theorem post_of (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {s₀ : State} {s : State} (hI : VG.Proof.Aes.AArch64.Aese.BInv B s₀ (VG.Proof.Aes.AArch64.Aese.bnb s₀) (VG.Proof.Aes.AArch64.Aese.bnb s₀) s) :
    (Proof.Aes.blocksAArch64 B.F).post s₀ s := by
  show Spec.Aes.statesAt s.mem (VG.Proof.Aes.AArch64.Aese.bdp s₀) (VG.Proof.Aes.AArch64.Aese.bnb s₀) = _
  rw [Proof.Aes.AArch64.statesAt_of_ecbInv hI.data]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

theorem bcorrect (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {setup : List Instr} {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.BPre s₀)
    (hs : WP isa (.block setup) s₀ fun s => VG.Proof.Aes.AArch64.Aese.BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8)) :
    WP isa (VG.Impl.Aes.AArch64.Aese.blocks setup B.f) s₀ ((Proof.Aes.blocksAArch64 B.F).post s₀) :=
  WP.seq (WP.mono hs fun _ ⟨hI₁, h13⟩ => WP.mono (VG.Proof.Aes.AArch64.Aese.loops_ok B hp hI₁ h13) fun _ hI => VG.Proof.Aes.AArch64.Aese.post_of B hI)

theorem blocks_correct (B : VG.Proof.Aes.AArch64.Aese.BlockFn) {setup : List Instr}
    (hs : ∀ s₀, VG.Proof.Aes.AArch64.Aese.BPre s₀ → WP isa (.block setup) s₀ fun s =>
      VG.Proof.Aes.AArch64.Aese.BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.bnb s₀ / 8))
    (hg : (VG.Impl.Aes.AArch64.Aese.blocks setup B.f).allInstrs (fun i => preserved.all fun r => dstOf i != some r) = true)
    (hnc : (VG.Impl.Aes.AArch64.Aese.blocks setup B.f).noCalls = true) (hv : (VG.Impl.Aes.AArch64.Aese.blocks setup B.f).allInstrs keepsV = true)
    (s : State) (hp : (Proof.Aes.blocksAArch64 B.F).pre s) :
    ∃ t s', Exec isa (VG.Impl.Aes.AArch64.Aese.blocks setup B.f) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 B.F).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved) (VG.Proof.Aes.AArch64.Aese.bcorrect B (VG.Proof.Aes.AArch64.Aese.bpre_of hp) (hs s (VG.Proof.Aes.AArch64.Aese.bpre_of hp))) hg hnc
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' :=
  VG.Proof.Aes.AArch64.Aese.blocks_correct VG.Proof.Aes.AArch64.Aese.encFn (fun _ hp => VG.Proof.Aes.AArch64.Aese.encSetup_ok hp) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' :=
  VG.Proof.Aes.AArch64.Aese.blocks_correct VG.Proof.Aes.AArch64.Aese.decFn (fun _ hp => VG.Proof.Aes.AArch64.Aese.decSetup_ok hp) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) s hs

theorem encryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decryptBlocks_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub decryptBlocks := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocks_verified :
    Verified AArch64.target encryptBlocks (Spec.Aes.encryptBlocksContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Aes.AArch64.Aese.encryptBlocks_correct VG.Proof.Aes.AArch64.Aese.encryptBlocks_ct (by
    sig_implies [Spec.Aes.encryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat)

theorem decryptBlocks_verified :
    Verified AArch64.target decryptBlocks (Spec.Aes.decryptBlocksContract AArch64.abi) :=
  Verified.of_correct VG.Proof.Aes.AArch64.Aese.decryptBlocks_correct VG.Proof.Aes.AArch64.Aese.decryptBlocks_ct (by
    sig_implies [Spec.Aes.decryptBlocksContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat)

end VG.Proof.Aes.AArch64.Aese

end
