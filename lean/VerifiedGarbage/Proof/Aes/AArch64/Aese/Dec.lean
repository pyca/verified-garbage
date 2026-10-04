import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks

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
    (invShiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [invShiftRows, getD_ofFn h]

theorem getD_invMixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (invMixColumns s).getD i 0 =
      Spec.Aes.mul 0x0e (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0b (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x0d (s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x09 (s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) := by
  rw [invMixColumns, getD_ofFn h]

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
theorem st_aesimc (k : BitVec 128) : st (aesInvMixColumns k) = invMixColumns (st k) := by
  apply st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [getD_st _ hi, vbyte_invMixColumns _ hi, getD_invMixColumns _ hi]
  simp only [getD_st _ (hr _), mul_eq]

/-- `aesd` without its `AddRoundKey`: `InvShiftRows`, then `InvSubBytes`. -/
theorem st_invSub (v : BitVec 128) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows v)) = invSubBytes (invShiftRows (st v)) := by
  apply st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + 4 - j % 4) % 4) < 16 := fun j => by omega
  rw [getD_st _ hi, vbyte_mapBytes _ _ hi, vbyte_invShiftRows _ hi, getD_invSubBytes _ hi,
    getD_invShiftRows _ hi, getD_st _ (hs _), invSbox_eq]

/-- `InvMixColumns` of a round key, as the bytes of a round key. -/
def imcKey (rk : List Byte) : List Byte := (invMixColumns (rkState rk)).toList

theorem getD_imcKey (rk : List Byte) {i : Nat} (hi : i < 16) :
    (imcKey rk).getD i 0 = (invMixColumns (rkState rk)).getD i 0 := by
  simp [imcKey, Vector.getD, hi]

/-- `aesimc` of round key `rk` in a register. -/
theorem keyIs_aesimc {k : BitVec 128} {rk : List Byte} (hk : KeyIs k rk) :
    KeyIs (aesInvMixColumns k) (imcKey rk) := by
  intro i hi
  rw [← getD_st _ hi, st_aesimc, getD_imcKey _ hi]
  refine congrArg (fun s => (invMixColumns s).getD i 0) ?_
  apply st_ext; intro j hj
  rw [getD_st _ hj, hk j hj]
  simp [rkState, Vector.getD, hj]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`aesimc`, is a middle round of the inverse cipher from `Z`, with round key
`rk`, the register then needing `InvMixColumns` of `rk`. -/
theorem dround_st {v k : BitVec 128} {K rk : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (h : addRoundKey (st v) K = Z) :
    addRoundKey (st (aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)))))
        (imcKey rk) = invMixColumns (addRoundKey (invSubBytes (invShiftRows Z)) rk) := by
  apply st_ext; intro i hi
  rw [invMixColumns_addRoundKey _ _ hi, getD_addRoundKey _ _ hi, getD_imcKey _ hi, st_aesimc,
    st_invSub, eor_st hk, h]

/-- `aesd` with the round key `K` that turns the register into `Z`, then
`eor` with `rk₀`: the last round of the inverse cipher. -/
theorem dlast_st {v k k₀ : BitVec 128} {K rk₀ : List Byte} {Z : Spec.Aes.State} (hk : KeyIs k K)
    (hk₀ : KeyIs k₀ rk₀) (h : addRoundKey (st v) K = Z) :
    st (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k)) ^^^ k₀) =
      addRoundKey (invSubBytes (invShiftRows Z)) rk₀ := by
  rw [eor_st hk₀, st_invSub, eor_st hk, h]

/-! ## The rounds -/

/-- The round key the registers need after `m` middle rounds: the last at
first, then those of the middle rounds through `InvMixColumns`. -/
def dkey (nr : Nat) (w : List Byte) (m : Nat) : List Byte :=
  if m = 0 then roundKey w nr else imcKey (roundKey w (nr - m))

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`, but for `AddRoundKey` with
`dkey m`. -/
def DInv (regs : List VReg) (nr : Nat) (w : List Byte) (x : VReg → Spec.Aes.State) (m : Nat)
    (s : State) : Prop :=
  ∀ b ∈ regs, addRoundKey (st (s.v b)) (dkey nr w m) = invMid nr w m (addRoundKey (x b) (roundKey w nr))

/-- What decryption needs of the state: the round keys as `decSetup` leaves
them, and `x6`, `x7` for the number of rounds. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  last : KeyIs (s.v .v30) (roundKey w nr)
  mid : ∀ j, 1 ≤ j → j < nr → KeyIs (s.v (dreg j)) (imcKey (roundKey w j))
  k0 : KeyIs (s.v .v16) (roundKey w 0)
  x6 : s.gpr .x6 = BitVec.ofNat 64 nr - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 nr - 12

theorem BlockRegs.dreg {regs : List VReg} (h : BlockRegs regs) (j : Nat) : dreg j ∉ regs := by
  unfold Impl.Aes.AArch64.Aese.dreg
  split
  · exact fun h' => (h.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
  · exact h.kreg j

theorem BlockRegs.v30 {regs : List VReg} (h : BlockRegs regs) : VReg.v30 ∉ regs :=
  fun h' => (h.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl

theorem BlockRegs.v16 {regs : List VReg} (h : BlockRegs regs) : VReg.v16 ∉ regs :=
  fun h' => (h.2 _ h').1 rfl

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List VReg} {s s' : State} (h : DKeys nr w s)
    (hf : VFrame rs s s') (hrs : BlockRegs rs) : DKeys nr w s' :=
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
    (hk : KeyIs (s.v k) (dkey nr w m)) (hI : DInv regs nr w x m s) :
    WP isa (.block (drnd regs k)) s fun s' => DInv regs nr w x (m + 1) s' ∧ VFrame regs s s' := by
  refine WP.mono (each_ok _
    (fun v k => aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k))))
    k (fun b s _ => drnd_run _ b s) regs s hr.1 hkr)
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, dkey, ite_eq_right (by omega), show nr - (m + 1) = nr - 1 - m by omega, dround_st hk (hI b hb),
    invMid_succ]
  rfl

/-- A middle round with round key `j = nr − m` (`m ≥ 1`). -/
theorem dround_ok' {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (j : Nat) {k : VReg} (e : k = dreg j) (hj : j + m = nr)
    (hj1 : 1 < j) (hm : 1 ≤ m) {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (drnd regs k)) s fun s' => DInv regs nr w x (m + 1) s' ∧ VFrame regs s s' := by
  subst e
  refine dround_ok hr (by omega) (hr.dreg j) ?_ hI
  rw [dkey, ite_eq_right (by omega), show nr - m = j by omega]
  exact hK.mid j (by omega) (by omega)

/-- Two middle rounds, with round keys `j` and `j − 1`. -/
theorem dtwo_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = dreg j)
    (e₂ : k₂ = dreg (j - 1)) (hj : j + m = nr) (hj1 : 2 < j) (hm : 1 ≤ m) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (drnd regs k₁ ++ drnd regs k₂)) s fun s' =>
      DInv regs nr w x (m + 2) s' ∧ VFrame regs s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (dround_ok' hr j e₁ hj (by omega) hm hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (dround_ok' hr (j - 1) e₂ (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ⟨hI₂, hf₁.trans hf₂⟩

/-- The middle rounds with round keys `9 … 2`. -/
theorem drounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} (hnr : 10 ≤ nr) (k : Nat) (hk : k ≤ 8) {s : State} (hK : DKeys nr w s)
    (hI : DInv regs nr w x (nr - 9) s) :
    WP isa (.block ((List.range k).flatMap fun j => drnd regs (kreg (9 - j)))) s fun s' =>
      DInv regs nr w x (nr - 9 + k) s' ∧ VFrame regs s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (dround_ok' hr (9 - k) (by simp [Impl.Aes.AArch64.Aese.dreg, show 9 - k ≠ 13 by omega])
      (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁) fun s' ⟨hI', hf'⟩ => ⟨?_, hf₁.trans hf'⟩
    rw [show nr - 9 + (k + 1) = nr - 9 + k + 1 by omega]; exact hI'

/-- The middle rounds with round keys `Nr − 1 … 10`. -/
theorem dmid_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x 1 s) :
    WP isa (.ite (.zero .x .x6) (.block [])
        (.seq (.ite (.zero .x .x7) (.block []) (.block (drnd regs .v29 ++ drnd regs .v28)))
          (.block (drnd regs .v27 ++ drnd regs .v26)))) s
      fun s' => DInv regs nr w x (nr - 9) s' ∧ VFrame regs s s' := by
  have hx6 := hK.x6
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hx7 := hK.x7
    have h₁ : WP isa (.ite (.zero .x .x7) (.block [])
        (.block (drnd regs .v29 ++ drnd regs .v28))) s
        (fun s' => DInv regs 12 w x 1 s' ∧ VFrame regs s s') :=
      WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
        (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_)
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hx7 := hK.x7
    have h₁ : WP isa (.ite (.zero .x .x7) (.block [])
        (.block (drnd regs .v29 ++ drnd regs .v28))) s
        (fun s' => DInv regs 14 w x 3 s' ∧ VFrame regs s s') :=
      WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
        (fun h => absurd h (by decide))
        (fun _ => dtwo_ok hr 13 rfl rfl (by omega) (by omega) (by omega) hK hI)
    refine WP.seq (WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_)
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem dlast_run (b : VReg) (s : State) (hb16 : b ≠ .v16) :
    runBlock isa [.vop (.aesd b .v17), .vop (.logic .eor b b .v16)] s =
      some (s.setV b (aesMapBytes aesInvSbox (aesInvShiftRows (s.v b ^^^ s.v .v17)) ^^^ s.v .v16)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (Ne.symm hb16), setV_setV]

theorem dlast_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x (nr - 1) s) :
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
      refine WP.of_runBlock ⟨_, dlast_run b s hb16, ?_⟩
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
  have hk1 : KeyIs (s.v .v17) (dkey nr w (nr - 1)) := by
    rw [dkey, ite_eq_right (by omega), show nr - (nr - 1) = 1 by omega]
    exact hK.mid 1 (by omega) (by omega)
  rw [hv b hb, dlast_st hk1 hK.k0 (hI b hb), invCipher_eq]

theorem aesDec_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : DKeys nr w s) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = invCipher nr w (st (s.v b))) ∧ VFrame regs s s' := by
  have hnr : 10 ≤ nr := by rcases hK.rounds with h | h | h <;> omega
  let x : VReg → Spec.Aes.State := fun b => st (s.v b)
  have hI₀ : DInv regs nr w x 0 s := fun b _ => by simp [dkey, invMid, x]
  refine WP.seq (WP.mono (dround_ok hr (m := 0) (by omega) hr.v30 (by simpa [dkey] using hK.last) hI₀)
    fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (dmid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok hr hnr 8 (by omega) (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s₃ ⟨hI₃, hf₃⟩ => ?_
  rw [show nr - 9 + 8 = nr - 1 by omega] at hI₃
  exact WP.mono (dlast_ok hr (hK.of_frame (hf₁.trans (hf₂.trans hf₃)) hr) hI₃)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans (hf₃.trans hf'))⟩

end VG.Proof.Aes.AArch64.Aese
