import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Aes.InvBitsliced
import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks

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
  rw [aesInvShiftRows, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

theorem byte_invMixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    byte (aesInvMixColumns x) i =
      aesMul 0x0e (byte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0b (byte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x0d (byte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x09 (byte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesInvMixColumns, aesMixWith, VG.Proof.Gcm.X86_64.byte_ofBytes _ h]

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

/-! ## The rounds -/

/-- What decryption needs of the state: the key schedule at `rdi`, readable,
and round keys `1 … nr − 1` through `InvMixColumns` at `r8`. -/
structure DKeys (nr : Nat) (w : List Byte) (s : State) : Prop where
  keys : Keys nr w s
  imc : ∀ j, 1 ≤ j → j < nr →
    InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16 ∧
    st (s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 128) =
      invMixColumns (rkState (roundKey w j))

theorem DKeys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : DKeys nr w s)
    (hf : XFrame rs s s') : DKeys nr w s' :=
  ⟨h.keys.of_frame hf, by rw [hf.rd, hf.wr, hf.gpr, hf.mem]; exact h.imc⟩

/-- Each register `b` of `regs` holds the state after `m` middle rounds of
the inverse cipher, from the state `x b`. -/
def DInv (regs : List XReg) (nr : Nat) (w : List Byte) (x : XReg → Spec.Aes.State) (m : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, st (s.xmm b) = invMid nr w m (addRoundKey (x b) (roundKey w nr))

theorem dround_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {m : Nat} (hm : m + 1 < nr) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs (nr - 1 - m))) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  obtain ⟨hin, hst⟩ := hK.imc (nr - 1 - m) (by omega) (by omega)
  refine WP.mono (keyOp_ok regs .aesdec _ s hnd h8 (by rw [ea_at]; exact hin))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, ea_at, aesdec_st _ _ _ hst, hI b hb, invMid_succ]
  rfl

/-- `dround_ok`, with the round key's index given. -/
theorem dround_ok' (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {j m : Nat} (hj : j + m + 1 = nr) (hj0 : 0 < j) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (dround regs j)) s fun s' =>
      DInv regs nr w x (m + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  rw [show j = nr - 1 - m by omega]
  exact dround_ok regs hnd h8 (by omega) hK hI

/-- Middle rounds `nr − 10 … nr − 2`, with round keys `9 … 1`. -/
theorem drounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : 10 ≤ nr) {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (hk : k ≤ 9) (s : State)
    (hK : DKeys nr w s) (hI : DInv regs nr w x (nr - 10) s) :
    WP isa (.block ((List.range k).flatMap fun j => dround regs (9 - j))) s fun s' =>
      DInv regs nr w x (nr - 10 + k) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (dround_ok' regs hnd h8 (j := 9 - k) (m := nr - 10 + k) (by omega) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨by rw [show nr - 10 + (k + 1) = nr - 10 + k + 1 by omega]; exact hI',
        hf₁.trans hf'⟩

theorem aesDec_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : DKeys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = invCipher nr w (st (s.xmm b))) ∧ XFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => st (s.xmm b)
  have hea : s.ea (at_ .r10 0) = s.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have kR := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := nr) (by omega)
  -- `AddRoundKey` with the last round key.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keyOp_ok regs .pxor _ s hnd h8 (by rw [hea]; exact hK.keys.keys nr (Nat.le_refl _)))
    fun s₁ ⟨hv₁, hf₁⟩ => ?_
  have hI₁ : DInv regs nr w x 0 s₁ := fun b hb => by
    rw [hv₁ b hb, pxor_st _ _ (roundKey w nr) (by rw [hK.keys.sched, hea]; exact kR)]; rfl
  refine WP.mono (cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  have hI₁' : DInv regs nr w x 0 s₁' := fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb
  have hK₁ := hK.of_frame hf₁₁
  -- The middle rounds with round keys `nr − 1 … 10`.
  have h₂ : WP isa (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10))))) s₁' fun s' =>
        DInv regs nr w x (nr - 10) s' ∧ XFrame (.xmm8 :: regs) s s' := by
    have hrsi₁ : s₁'.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁', hf₁₁⟩)
        (fun h => absurd h (by decide))
    · -- 12 rounds: round keys 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 12 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 12 w x 0 s' ∧ XFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite true (by simp [eval, hz₂]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact WP.block_nil (show DInv regs 12 w x 0 s₂ ∧ XFrame (.xmm8 :: regs) s s₂ from ⟨hI₂, hf₁₂⟩)
      rw [WP.block_append_iff]
      refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 0) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
        fun s₄ ⟨hI₄, hf₄⟩ => ?_
      exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 1) (by omega) (by omega)
        (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
    · -- 14 rounds: round keys 13, 12, 11 and 10.
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq (WP.mono (cmpRsi_ok s₁' 12 _ hrsi₁) fun s₂ ⟨hz₂, hf₂⟩ => ?_)
      have hI₂ : DInv regs 14 w x 0 s₂ := fun b hb => by rw [hf₂.xmm b (by simp)]; exact hI₁' b hb
      have hf₁₂ := hf₁₁.trans (hf₂.mono (by simp))
      have hK₂ := hK.of_frame hf₁₂
      refine WP.seq ?_
      refine WP.mono (Q := fun s' => DInv regs 14 w x 2 s' ∧ XFrame (.xmm8 :: regs) s s') ?_
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      · refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
        rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 13) (m := 0) (by omega) (by omega) hK₂ hI₂)
          fun s₃ ⟨hI₃, hf₃⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 12) (m := 1) (by omega) (by omega) (hK₂.of_frame hf₃) hI₃)
          fun s' ⟨hI', hf'⟩ => (⟨hI', hf₁₂.trans (hf₃.trans hf')⟩ :
            DInv regs 14 w x (1 + 1) s' ∧ XFrame (.xmm8 :: regs) s s')
      · rw [WP.block_append_iff]
        refine WP.mono (dround_ok' regs hnd h8 (j := 11) (m := 2) (by omega) (by omega) (hK.of_frame hf₃) hI₃)
          fun s₄ ⟨hI₄, hf₄⟩ => ?_
        exact WP.mono (dround_ok' regs hnd h8 (j := 10) (m := 3) (by omega) (by omega)
          (hK.of_frame (hf₃.trans hf₄)) hI₄) fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans (hf₄.trans hf')⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  -- Round keys `9 … 1`, and the last round.
  have hK₂ := hK.of_frame hf₂
  have hnr' : 10 ≤ nr := by rcases hnr with h | h | h <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok regs hnd h8 hnr' 9 (by omega) s₂ hK₂ hI₂) fun s₃ ⟨hI₃, hf₃⟩ => ?_
  have hK₃ := hK₂.of_frame hf₃
  have k0 := byte_roundKey s₃.mem (s₃.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  refine WP.mono (keyOp_ok regs .aesdeclast _ s₃ hnd h8 (by rw [ea_at]; exact hK₃.keys.keys 0 (by omega)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans (hf₃.trans hf')⟩
  rw [hv b hb, aesdeclast_st _ _ (roundKey w 0) (by rw [hK₃.keys.sched, ea_at]; exact k0), hI₃ b hb,
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

theorem ImcInv.refl (s₀ : State) : ImcInv s₀ [] s₀ :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil⟩

theorem imcKey_ok {s₀ : State} (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) {S : List Nat} {s : State}
    (hI : ImcInv s₀ S s) {j : Nat} (hj : j ≤ 13) :
    WP isa (.block (imcKey j)) s (ImcInv s₀ (j :: S)) := by
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
            rw [off_toNat _ _ (by omega)] at h₁ h₂
            have := (a - s₀.gpr .r8).isLt
            omega) (by decide), hI.keys j' hj']

theorem ImcInv.of_frame {s₀ s s' : State} {S : List Nat} (h : ImcInv s₀ S s) (hf : XFrame [] s s') :
    ImcInv s₀ S s' :=
  ⟨hf.gpr.trans h.gpr, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (hf.xmm r (by simp)).trans (h.xmm r hr), by rw [hf.mem]; exact h.frame, h.le,
    by rw [hf.mem]; exact h.keys⟩

/-- Some round keys through `aesimc`, those of `js`. -/
theorem imcRun_ok {s₀ : State} (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) (js : List Nat)
    (hjs : ∀ j ∈ js, j ≤ 13) {S : List Nat} {s : State} (hI : ImcInv s₀ S s) :
    WP isa (.block (js.flatMap imcKey)) s fun s' => ∃ S', ImcInv s₀ S' s' ∧ ∀ j, j ∈ js ∨ j ∈ S → j ∈ S' := by
  induction js generalizing S s with
  | nil => exact WP.block_nil ⟨S, hI, fun j h => by simpa using h⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (imcKey_ok hscr hsch hsep hI (hjs j (by simp))) fun s₁ hI₁ => ?_
    refine WP.mono (ih (fun j' hj' => hjs j' (by simp [hj'])) hI₁) fun s' ⟨S', hI', hS'⟩ =>
      ⟨S', hI', fun j' hj' => hS' j' ?_⟩
    rcases hj' with hj' | hj'
    · rcases List.mem_cons.mp hj' with rfl | hj'
      · exact .inr (by simp)
      · exact .inl hj'
    · exact .inr (by simp [hj'])

theorem cmpRsi_imc {s₀ s : State} {S : List Nat} (hI : ImcInv s₀ S s) (c : BitVec 32) (nr : Nat)
    (hrsi : s₀.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ ImcInv s₀ S s' :=
  WP.mono (cmpRsi_ok s c nr (by rw [hI.gpr, hrsi])) fun _ ⟨hz, hf⟩ => ⟨hz, hI.of_frame hf⟩

theorem imcKeys_ok {s₀ : State} {nr : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hrsi : s₀.gpr .rsi = BitVec.ofNat 64 nr) (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsch : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) :
    WP isa imcKeys s₀ fun s => ∃ S, ImcInv s₀ S s ∧ ∀ j, 1 ≤ j → j < nr → j ∈ S := by
  have run := fun js hjs {S s} (hI : ImcInv s₀ S s) => imcRun_ok hscr hsch hsep js hjs hI
  refine WP.seq ?_
  rw [WP.block_append_iff, show ((List.range 9).flatMap fun j => imcKey (j + 1)) =
    ((List.range 9).map (· + 1)).flatMap imcKey by simp [List.flatMap_map]]
  refine WP.mono (run _ (by decide) (ImcInv.refl s₀)) fun s₁ ⟨S₁, hI₁, hS₁⟩ => ?_
  have h9 : ∀ j, 1 ≤ j → j ≤ 9 → j ∈ S₁ := fun j h1 h2 => hS₁ j (.inl (by
    simp only [List.mem_map, List.mem_range]; exact ⟨j - 1, by omega, by omega⟩))
  refine WP.mono (cmpRsi_imc hI₁ 10 nr hrsi) fun s₂ ⟨hz₂, hI₂⟩ => ?_
  rcases hnr with rfl | rfl | rfl
  · exact WP.ite true (by simp [eval, hz₂]) (fun _ => WP.block_nil ⟨S₁, hI₂, fun j h1 h2 => h9 j h1 (by omega)⟩)
      (fun h => absurd h (by decide))
  all_goals
    refine WP.ite false (by simp [eval, hz₂]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq ?_
    rw [WP.block_append_iff, show imcKey 10 ++ imcKey 11 = [10, 11].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₂) fun s₃ ⟨S₃, hI₃, hS₃⟩ => ?_
    have h11 : ∀ j, 1 ≤ j → j ≤ 11 → j ∈ S₃ := fun j h1 h2 => hS₃ j (by
      by_cases h : j ≤ 9
      · exact .inr (h9 j h1 h)
      · exact .inl (by simp; omega))
    refine WP.mono (cmpRsi_imc hI₃ 12 _ hrsi) fun s₄ ⟨hz₄, hI₄⟩ => ?_
  · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil ⟨S₃, hI₄, fun j h1 h2 => h11 j h1 (by omega)⟩)
      (fun h => absurd h (by decide))
  · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
    rw [show imcKey 12 ++ imcKey 13 = [12, 13].flatMap imcKey by simp]
    refine WP.mono (run _ (by decide) hI₄) fun s₅ ⟨S₅, hI₅, hS₅⟩ => ⟨S₅, hI₅, fun j h1 h2 => hS₅ j ?_⟩
    by_cases h : j ≤ 11
    · exact .inr (h11 j h1 h)
    · exact .inl (by simp; omega)

/-- The round keys through `aesimc`, as decryption needs them. -/
theorem dKeys_of_imc {s₀ s : State} {nr : Nat} {w : List Byte} (hK : Keys nr w s₀)
    (hscr : (⟨s₀.gpr .r8, 2048⟩ : Region) ∈ s₀.wr)
    (hsep : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r8, 2048⟩) {S : List Nat}
    (hI : ImcInv s₀ S s) (hS : ∀ j, 1 ≤ j → j < nr → j ∈ S) : DKeys nr w s := by
  have ofs : ∀ (p : Addr) (a : Nat), p + BitVec.ofInt 64 (a : Int) = p + BitVec.ofNat 64 a :=
    fun p a => by rw [ofInt_natCast]
  have hle := hK.le
  have hsched : bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1)) = bytesAt s₀.mem (s₀.gpr .rdi) (16 * (nr + 1)) := by
    rw [hI.gpr]
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    exact hI.frame.bytes (R := ⟨s₀.gpr .rdi, 16 * (nr + 1)⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_left (Region.sub_prefix (by omega))) (by show 16 * (nr + 1) ≤ 2 ^ 64; omega) hi
  refine ⟨⟨by rw [hsched]; exact hK.sched, hle, by rw [hI.rd, hI.wr, hI.gpr]; exact hK.keys⟩,
    fun j h1 h2 => ⟨?_, ?_⟩⟩
  · rw [hI.rd, hI.wr, hI.gpr, ofs]
    exact ⟨_, List.mem_append_right _ hscr, contains_offset (by omega) (by omega)⟩
  · rw [hI.gpr, hI.keys j (hS j h1 h2), st_aesimc]
    refine congrArg invMixColumns ?_
    apply st_ext; intro i hi
    rw [getD_st _ hi, hK.sched, byte_roundKey (L := 16 * (nr + 1)) _ _ (by omega) i hi]
    simp [rkState, Vector.getD, hi]

end VG.Proof.Aes.X86_64.AesNi
