module

public import VerifiedGarbage.Proof.Aes.Rounds
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Residue.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.Residue.AArch64
meta import VerifiedGarbage.TCB.AArch64.Residue
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
public import VerifiedGarbage.Proof.Aes.InvRounds
public import VerifiedGarbage.Proof.Aes.Vector -- shake: keep (exports the existing inverse-round value interface)
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks
meta import VerifiedGarbage.Proof.Aes.InvRounds
meta import VerifiedGarbage.Proof.Aes.Vector
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
import VerifiedGarbage.Proof.Aes.InvSboxSpec
import VerifiedGarbage.Proof.Aes.InvBitsliced
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Impl.Aes.AArch64.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
meta import VerifiedGarbage.Proof.Aes.InvSboxSpec
meta import VerifiedGarbage.Proof.Aes.InvBitsliced
meta import VerifiedGarbage.Proof.Aes.Rounds

/-! ### `Aes.AArch64.Blocks`, which this module and modules that import it used -/

section

/-! ### `Aes.AArch64.Ecb`, which this module and modules that import it used -/

section

/-!
# AES on whole blocks on AArch64: the data's invariant

The data's invariant (`EcbInv`) says that the first `k` blocks hold the
transformation of the original ones (`ecbOut`), and the others are still
the original ones (`ecbInv_orig`); a write apart from the data keeps it
(`ecbInv_frame`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-! ## Storing -/

/-- The data after `k` blocks: the first `k` of the `n` blocks at `D` are
`F`'s, the others are still `m₀`'s. -/
def EcbInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem ecbInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : EcbInv m₀ m D n k F) : EcbInv m₀ m' D n k F := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_using [hn]) hi

/-- Before `k` blocks are stored, a block not yet stored is still `m₀`'s. -/
theorem ecbInv_orig {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n k F) {j : Nat} (hj : k ≤ j) (hjn : j < n) :
    Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * j)) = Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_using [hjn, hi]), ite_eq_right (show ¬ 16 * j + i < 16 * k by omega_using [hj])]

/-! ## A group -/

/-- The results: `f R w` of each block of `m₀`'s data. -/
def ecbOut (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (m₀ : Mem) (D : Addr) (R : Nat)
    (w : List Byte) (j : Nat) : Spec.Aes.State :=
  f R w (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

end VG.Proof.Aes.AArch64

end

end

/-!
# AES on whole blocks on AArch64: the contract

The AArch64 contract of `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`
(`blocksAArch64`), a state satisfying it (`blocksSat`), the moves of the
arguments (`blocksSetup_ok`), and the data after the last group, as states
(`statesAt_of_ecbInv`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksAArch64 (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x2).toNat + 16 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).map
        (f (s.gpr .x1).toNat (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

theorem blocksSetup_ok (s : State) :
    ∃ s', runBlock isa blocksSetup s = some s' ∧ s'.gpr .x5 = s.gpr .x4 ∧ s'.gpr .x4 = s.gpr .x3 ∧
      s'.gpr .x3 = s.gpr .x2 ∧ (∀ r, r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by rw [blocksSetup, movR, movR, movR, runBlock_cons, exec_addImm_x (by decide),
    runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
    exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  exact ⟨by simp [State.write, State.read], by simp [State.write, State.read],
    by simp [State.write, State.read], fun r h1 h2 h3 => by simp [State.write, h1, h2, h3],
    rfl, rfl, rfl, rfl⟩

/-- The data after the last group, as states. -/
theorem statesAt_of_ecbInv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Aes.State}
    (h : EcbInv m₀ m D n n F) : Spec.Aes.statesAt m D n = (List.range n).map F := by
  simp only [Spec.Aes.statesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro t ht
  simp only [Spec.Aes.stateAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_arith), ite_eq_left (show 16 * j + t < 16 * n by omega_arith),
    show (16 * j + t) / 16 = j by omega_arith, show (16 * j + t) % 16 = t by omega_arith, getD_eq _ ht]

/-! ## The two functions -/

/-- A state satisfying the precondition (one block). -/
def blocksSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 2048⟩]

end VG.Proof.Aes.AArch64

end

end

/-! ### `Aes.AArch64.Aese.Dec`, which this module and modules that import it used -/

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

@[expose] public section

namespace VG.Proof.Aes.AArch64.Aese

open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (kreg dreg drnd dlast aesDec)
open VG.Spec.Aes (invSubBytes invShiftRows invMixColumns addRoundKey invSbox roundKey invCipher)
open VG.Proof.Aes (rkState irnd invMid invMid_succ invCipher_eq invMixColumns_addRoundKey)

export VG.Proof.Aes.Vector (
  invSbox_eq getD_invSubBytes getD_invShiftRows getD_invMixColumns vbyte_invShiftRows vbyte_invMixColumns st_aesimc st_invSub imcKey getD_imcKey keyIs_aesimc dround_st dlast_st)

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
  refine dround_ok hr (by omega_using [hj, hj1]) (hr.dreg j) ?_ hI
  rw [dkey, ite_eq_right (by omega_using [hm]), show nr - m = j by omega_using [hj]]
  exact hK.mid j (by omega_using [hj1]) (by omega_using [hj, hm])

/-- Two middle rounds, with round keys `j` and `j − 1`. -/
theorem dtwo_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {m : Nat} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = dreg j)
    (e₂ : k₂ = dreg (j - 1)) (hj : j + m = nr) (hj1 : 2 < j) (hm : 1 ≤ m) {s : State}
    (hK : DKeys nr w s) (hI : DInv regs nr w x m s) :
    WP isa (.block (drnd regs k₁ ++ drnd regs k₂)) s fun s' =>
      DInv regs nr w x (m + 2) s' ∧ VFrame regs s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (dround_ok' hr j e₁ hj (by omega_using [hj1]) hm hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (dround_ok' hr (j - 1) e₂ (by omega_using [hj, hj1]) (by omega_using [hj1]) (by omega_using []) (hK.of_frame hf₁ hr) hI₁)
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
    refine WP.mono (ih (by omega_using [hk])) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (dround_ok' hr (9 - k) (by simp [Impl.Aes.AArch64.Aese.dreg, show 9 - k ≠ 13 by omega_using []])
      (by omega_using [hnr, hk]) (by omega_using [hk]) (by omega_using [hnr]) (hK.of_frame hf₁ hr) hI₁) fun s' ⟨hI', hf'⟩ => ⟨?_, hf₁.trans hf'⟩
    rw [show nr - 9 + (k + 1) = nr - 9 + k + 1 by omega_using []]; exact hI'

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
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega_using []) (by omega_using []) (by omega_using []) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hx7 := hK.x7
    have h₁ : WP isa (.ite (.zero .x .x7) (.block [])
        (.block (drnd regs .v29 ++ drnd regs .v28))) s
        (fun s' => DInv regs 14 w x 3 s' ∧ VFrame regs s s') :=
      WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
        (fun h => absurd h (by decide))
        (fun _ => dtwo_ok hr 13 rfl rfl (by omega_using []) (by omega_using []) (by omega_using []) hK hI)
    refine WP.seq (WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_)
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega_using []) (by omega_using []) (by omega_using []) (hK.of_frame hf₁ hr) hI₁)
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
  have hnr : 2 ≤ nr := by rcases hK.rounds with h | h | h <;> omega_using [h]
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
    rw [dkey, ite_eq_right (by omega_using [hnr]), show nr - (nr - 1) = 1 by omega_using [hnr]]
    exact hK.mid 1 (by omega_using []) (by omega_using [hnr])
  rw [hv b hb, dlast_st hk1 hK.k0 (hI b hb), invCipher_eq]

theorem aesDec_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : DKeys nr w s) :
    WP isa (aesDec regs) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = invCipher nr w (st (s.v b))) ∧ VFrame regs s s' := by
  have hnr : 10 ≤ nr := by rcases hK.rounds with h | h | h <;> omega_using [h]
  let x : VReg → Spec.Aes.State := fun b => st (s.v b)
  have hI₀ : DInv regs nr w x 0 s := fun b _ => by simp [dkey, invMid, x]
  refine WP.seq (WP.mono (dround_ok hr (m := 0) (by omega_using [hnr]) hr.v30 (by simpa [dkey] using hK.last) hI₀)
    fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (dmid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok hr hnr 8 (by omega_using []) (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s₃ ⟨hI₃, hf₃⟩ => ?_
  rw [show nr - 9 + 8 = nr - 1 by omega_using [hnr]] at hI₃
  exact WP.mono (dlast_ok hr (hK.of_frame (hf₁.trans (hf₂.trans hf₃)) hr) hI₃)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans (hf₃.trans hf'))⟩

end VG.Proof.Aes.AArch64.Aese

end

end

/-!
# AES on whole blocks with the Armv8 Cryptographic Extension

`encryptBlocks_correct`, `decryptBlocks_correct` and their `_ct` prove
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

@[expose] public section

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

theorem DKeys.of_v {nr : Nat} {w : List Byte} {vs : List VReg} {s s' : State} (h : DKeys nr w s)
    (hrs : BlockRegs vs) (hv : ∀ r, r ∉ vs → s'.v r = s.v r) (h6 : s'.gpr .x6 = s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr .x7) : DKeys nr w s' :=
  ⟨h.rounds, by rw [hv _ hrs.v30]; exact h.last,
    fun j h1 h2 => by rw [hv _ (hrs.dreg j)]; exact h.mid j h1 h2,
    by rw [hv _ hrs.v16]; exact h.k0, by rw [h6]; exact h.x6, by rw [h7]; exact h.x7⟩

def encFn : BlockFn :=
  ⟨aes, Spec.Aes.cipher, Keys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7, fun hr hK => aes_ok hr hK⟩

def decFn : BlockFn :=
  ⟨aesDec, Spec.Aes.invCipher, DKeys, fun h hrs hv h6 h7 => h.of_v hrs hv h6 h7,
    fun hr hK => aesDec_ok hr hK⟩

/-! ## The precondition and the loop invariant -/

section
variable (s₀ : State)

abbrev bkp : Addr := s₀.gpr .x0
abbrev bnr : Nat := (s₀.gpr .x1).toNat
abbrev bdp : Addr := s₀.gpr .x2
abbrev bnb : Nat := (s₀.gpr .x3).toNat
abbrev bdR : Region := ⟨bdp s₀, 16 * bnb s₀⟩
/-- The key schedule. -/
abbrev bsch : List Byte := Spec.Aes.bytesAt s₀.mem (bkp s₀) (16 * (bnr s₀ + 1))

end

structure BPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨bkp s₀, 240⟩]
  wr : s₀.wr = [bdR s₀, ⟨s₀.gpr .x4, 2048⟩]
  s_d : Region.Disjoint ⟨bkp s₀, 240⟩ (bdR s₀)
  d_s : Region.Disjoint (bdR s₀) ⟨s₀.gpr .x4, 2048⟩
  wrap : (bdp s₀).toNat + 16 * bnb s₀ ≤ 2 ^ 64
  rounds : bnr s₀ = 10 ∨ bnr s₀ = 12 ∨ bnr s₀ = 14

theorem bpre_of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State}
    (h : (Proof.Aes.blocksAArch64 f).pre s₀) : BPre s₀ := by
  obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h5, h6, h7⟩

namespace BPre
variable {s₀ : State} (hp : BPre s₀)
include hp

theorem nb16 : 16 * bnb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega_using [this]

theorem dat : bdR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem n16 : 16 * bnb s₀ < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => hp.d_s (s₀.gpr .x4) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (s₀.gpr .x4 - bdp s₀).isLt
  omega_using [hc]

theorem key_in {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (bkp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨bkp s₀, 240⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega_using [h])⟩

end BPre

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure BInv (B : BlockFn) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ bnb s₀
  keys : B.K (bnr s₀) (bsch s₀) s
  x2 : s.gpr .x2 = bdp s₀ + BitVec.ofNat 64 (16 * p)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (bnb s₀ - p)
  frame : Frame [bdR s₀] s₀.mem s.mem
  data : EcbInv s₀.mem s.mem (bdp s₀) (bnb s₀) c (ecbOut B.F s₀.mem (bdp s₀) (bnr s₀) (bsch s₀))
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
    refine ⟨_, exec_ldrq (by omega_using [hj]) (by simpa using hin 0 (by simp)), ?_⟩
    refine WP.mono (ldData_ok bs (j + 1) _ (List.nodup_cons.mp hnd).2 (by omega_using [hj]) fun k hk => by
      have := hin (k + 1) (by simp; omega_using [hk])
      simpa [State.setV, show j + 1 + k = j + (k + 1) by omega_using []] using this)
      fun s' ⟨e, f⟩ => ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; rw [f.v _ hbs, setV_v_self]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk)]
        simp [State.setV, show j + 1 + k = j + (k + 1) by omega_using []]
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
    rw [off_toNat' D (by omega_using [hn, hi]) (by omega_using [hn, hk])]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega_using [h2])]
        show vbyte _ _ = _
        rw [hv _ h2, show i / 16 = k by omega_using [h1, h2], show i % 16 = i - 16 * k by omega_using [h1, h2]]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_using [h1]),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_using [h2])]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_using [hn, hk]), h i hi,
        ite_eq_left (show i < 16 * k by omega_using [h1]), ite_eq_left (show i < 16 * (k + 1) by omega_using [h1])]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have := (x - D).isLt
    rw [Offset.sub_add_eq] at hlt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega_using [hn, hk])] at hlt
    omega_using [hk, hlt]

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
      rw [hx2, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega_using [])]
    rw [stData, WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega_using [hj]) (by rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega_using [hc]) (by omega_using [hn, hc])⟩), ?_⟩
    rw [ha]
    have hst := ecbInv_write hn (by omega_using [hc]) hD (v := s.v b) fun t ht => by
      have := hF 0 (by simp) t ht
      simpa using this
    refine WP.mono (stData_ok (m₀ := m₀) (c := c) (F := F) hn bs (j + 1) _ hx2 (by omega_using [hj]) (by omega_using [hc]) hw
      (by rw [show c + (j + 1) = c + j + 1 by omega_using []]; exact hst.1) (fun k hk t ht => by
        have := hF (k + 1) (by simp; omega_using [hk]) t ht
        simp only [List.getElem_cons_succ] at this
        rw [show c + (j + 1) + k = c + j + (k + 1) by omega_using []]; exact this))
      fun s' ⟨d', f', g', v', sp', rd', wr'⟩ => ⟨?_, hst.2.trans f', g', v', sp', rd', wr'⟩
    rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega_using []]; exact d'

/-! ## The loop bodies -/

theorem bregs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) : BlockRegs rs := by
  rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Load, transform and store the blocks `c … c + N − 1` (`N` the number of
registers). -/
theorem group_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) (hQ : ∀ s', BInv B s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ldData rs 0)) (.seq (B.f rs) (.block (stData rs 0 ++ tail)))) s Q := by
  have hbr := bregs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hn := hp.n16
  have hin : ∀ k < rs.length, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by
      rw [hI.rd, hI.wr, hI.x2, Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_using [])]
      exact ⟨_, List.mem_append_right _ hp.dat, Offset.contains_base _ (by omega_using [hc, hk]) (by omega_using [hc, hn, hk])⟩
  refine WP.seq (WP.mono (ldData_ok rs 0 s hbr.1 (by omega_using [hlen]) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have hK₁ := B.of_v hI.keys hbr f₁.v (f₁.gpr _ (by simp)) (f₁.gpr _ (by simp))
  refine WP.seq (WP.mono (B.ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  rw [WP.block_append_iff]
  have hx2 : s₂.gpr .x2 = bdp s₀ + BitVec.ofNat 64 (16 * c) := by
    rw [f₂.gpr, f₁.gpr _ (by simp), hI.x2]
  have hF : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = (ecbOut B.F s₀.mem (bdp s₀) (bnr s₀) (bsch s₀) (c + 0 + k)).getD t 0 := by
    intro k h t ht
    rw [← getD_st _ ht, e₂ _ (List.getElem_mem h), e₁ k h, st_readW, hI.x2,
      Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + 0 + k) by omega_using []),
      ecbInv_orig hI.data (by omega_using []) (by omega_using [hc, h])]
    rfl
  refine WP.mono (stData_ok (m₀ := s₀.mem) (D := bdp s₀) (c := c) hp.nb16 rs 0 s₂ hx2 (by omega_using [hlen])
      (by omega_using [hc]) (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.dat)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) hF)
    fun s₃ ⟨d₃, fr₃, g₃, v₃, sp₃, rd₃, wr₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have g : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, f₁.gpr r (by simp)]
  refine ⟨hc, ?_, by rw [g]; exact hI.x2, by rw [g]; exact hI.x3,
    by rw [hm₂] at fr₃; exact hI.frame.trans fr₃, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  exact B.of_v (B.of_v hK₁ hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])) hbr
    (fun r _ => by rw [v₃]) (by rw [g₃]) (by rw [g₃])

theorem btail8_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 8 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ (c + 8) c s) :
    WP isa (.block [.addImm .x .x2 .x2 128, .subImm .x .x3 .x3 8, .lsr .x .x13 .x3 3]) s fun s' =>
      BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((bnb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have h4 : BitVec.ofNat 64 (bnb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (bnb s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show bnb s₀ - c - 8 = bnb s₀ - (c + 8) by omega_using []]
  refine ⟨⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩, ?_⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    exact h4
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [h4, ushr3 (by omega_using [hn])]

theorem btail1_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 1 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ (c + 1) c s) :
    WP isa (.block [.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1]) s (BInv B s₀ (c + 1) (c + 1)) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨hI.le, B.of_v hI.keys (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show bnb s₀ - c - 1 = bnb s₀ - (c + 1) by omega_using []]

theorem blk8_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 8 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) :
    WP isa (blk8 B.f) s fun s' =>
      BInv B s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((bnb s₀ - (c + 8)) / 8) :=
  group_ok B hp regs8 (.inl rfl) _ hc hI fun _ hI' => btail8_ok B hp hc hI'

theorem blk1_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {c : Nat} (hc : c + 1 ≤ bnb s₀) {s : State}
    (hI : BInv B s₀ c c s) : WP isa (blk1 B.f) s (BInv B s₀ (c + 1) (c + 1)) :=
  group_ok B hp [.v0] (.inr rfl) _ hc hI fun _ hI' => btail1_ok B hp hc hI'

/-- The loops, from the state after the setup. -/
theorem loops_ok (B : BlockFn) {s₀ : State} (hp : BPre s₀) {s₁ : State} (hI₁ : BInv B s₀ 0 0 s₁)
    (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)) :
    WP isa (.seq (.ite (.zero .x .x13) (.block []) (.loop (blk8 B.f) (.nonzero .x .x13)))
      (.ite (.zero .x .x3) (.block []) (.loop (blk1 B.f) (.nonzero .x .x3)))) s₁
      (BInv B s₀ (bnb s₀) (bnb s₀)) := by
  have hn := hp.n16
  refine WP.seq (WP.mono (Q := fun s => ∃ c, bnb s₀ - c < 8 ∧ BInv B s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (bnb s₀ / 8 = 0)) (eval_zero h13 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega_using [h], hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = bnb s₀ - c ∧ c + 8 ≤ bnb s₀ ∧ BInv B s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa (blk8 B.f) s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, bnb s₀ - c < 8 ∧ BInv B s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (blk8_ok B hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [eval_nonzero h13' (by omega_using [hn])]
        by_cases hlt : bnb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega_using [hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega_using [hlt], bnb s₀ - (c + 8), by omega_using [hc], c + 8, rfl, by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I8 hstep (bnb s₀) s₁ ⟨0, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.ite (decide (bnb s₀ - c = 0)) (eval_zero hI₂.x3 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · have : c = bnb s₀ := by have := hI₂.le; simp at h; omega_using [this, h]
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = bnb s₀ - c ∧ c < bnb s₀ ∧ BInv B s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa (blk1 B.f) s (fun s' =>
        (AArch64.eval (.nonzero .x .x3) s' = some false ∧ BInv B s₀ (bnb s₀) (bnb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (blk1_ok B hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x3 (by omega_using [hn])]
      by_cases hlast : bnb s₀ - (c + 1) = 0
      · have : c + 1 = bnb s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], bnb s₀ - (c + 1), by omega_using [hc], c + 1, rfl, by omega_using [hlast], hI'⟩
    have hlt : c < bnb s₀ := by have := hI₂.le; simp at h; omega_using [h]
    exact WP.loop (M := isa) I1 hstep (bnb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

/-! ## The setups -/

/-- What `keysCommon` leaves. -/
structure Common (s₀ s : State) : Prop where
  kreg : ∀ j < 13, s.v (kreg j) = s₀.mem.readW (bkp s₀ + BitVec.ofNat 64 (16 * j)) 128
  v30 : s.v .v30 = s₀.mem.readW (bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀)) 128
  x9 : s.gpr .x9 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀)
  x6 : s.gpr .x6 = BitVec.ofNat 64 (bnr s₀) - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 (bnr s₀) - 12
  x13 : s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)
  gpr : ∀ r, r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x13 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem common_ok {s₀ : State} (hp : BPre s₀) : WP isa (.block keysCommon) s₀ (Common s₀) := by
  have hR := hp.rounds
  have hn := hp.nb16
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (bnr s₀) := by simp [bnr]
  have hx3 : s₀.gpr .x3 = BitVec.ofNat 64 (bnb s₀) := by simp [bnb]
  rw [keysCommon, WP.block_append_iff]
  refine WP.mono (loads_ok s₀ (fun j hj => hp.key_in (by omega_using [hj])) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) := by
    rw [g, g, shl4]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega_using [hR])), ?_⟩
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
    exact ushr3 (by omega_using [hn])
  · simp only [State.setV, State.write, h1, h2, h3, h4, ite_false, g]
  · exact f₁.mem

theorem encSetup_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block encSetup) s₀ fun s => BInv encFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [encSetup, WP.block_append_iff]
  refine WP.mono (common_ok hp) fun s₁ c₁ => ?_
  have e9' : bkp s₀ + BitVec.ofNat 64 (16 * bnr s₀) - BitVec.ofNat 64 16 =
      bkp s₀ + BitVec.ofNat 64 (16 * (bnr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega_using [hR]), show 16 * bnr s₀ - 16 = 16 * (bnr s₀ - 1) by omega_using []]
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9,
      e9', BitVec.add_zero, c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [hR])), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  refine ⟨⟨Nat.zero_le _, ⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.setV, State.write, (kreg_ne j).1, ite_false]
    rw [c₁.kreg j (by omega_using [hR, hj])]
    exact keyIs_readW _ _ (hL j (by omega_using [hj]))
  · simp only [State.setV, State.write, State.read, ite_true, BitVec.setWidth_eq, c₁.x9, e9',
      BitVec.add_zero, c₁.mem]
    exact keyIs_readW _ _ (hL _ (by omega_using []))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x6]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x7]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · simp only [State.setV, State.write, reduceCtorEq, ite_false]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [bnb]
  · simp only [State.setV, State.write, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    simp only [State.setV, State.write, c₁.mem]
    rw [ite_eq_right (by omega_using [])]
  · simp only [State.setV, State.write, c₁.rd]
  · simp only [State.setV, State.write, c₁.wr]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, c₁.x13]

theorem dreg_inj : ∀ j < 13, ∀ i < 13, dreg (j + 1) = dreg (i + 1) → j = i := by decide

/-- `aesimc` of the first `k` middle round keys. -/
theorem imcs_ok (s : State) :
    ∀ k ≤ 13, WP isa (.block ((List.range k).map fun j => .vop (.aesimc (dreg (j + 1)) (dreg (j + 1))))) s
      fun s' => (∀ j < 13, s'.v (dreg (j + 1)) =
          if j < k then aesInvMixColumns (s.v (dreg (j + 1))) else s.v (dreg (j + 1))) ∧
        (∀ r, (∀ j < 13, r ≠ dreg (j + 1)) → s'.v r = s.v r) ∧
        s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun j _ => by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (imcs_ok s k (by omega_using [hk])) fun s₁ ⟨e₁, o₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, isa, exec,
        VOp.eval, Option.map_some]; rfl, ?_⟩
    refine ⟨fun j hj => ?_, fun r hr => ?_, g₁, m₁, rd₁, wr₁⟩
    · by_cases hjk : j = k
      · subst hjk
        rw [setV_v_self, e₁ j hj, ite_eq_right (by omega_using []), ite_eq_left (by omega_using [])]
      · rw [setV_v_of_ne _ _ fun h => hjk (dreg_inj j hj k (by omega_using [hk]) h), e₁ j hj]
        by_cases hjk' : j < k
        · rw [ite_eq_left hjk', ite_eq_left (by omega_using [hjk'])]
        · rw [ite_eq_right hjk', ite_eq_right (by omega_using [hjk, hjk'])]
    · rw [setV_v_of_ne _ _ (hr k (by omega_using [hk])), o₁ r hr]

theorem dreg_ne : ∀ j < 13, dreg (j + 1) ≠ .v30 ∧ dreg (j + 1) ≠ .v16 := by decide

theorem decSetup_ok {s₀ : State} (hp : BPre s₀) :
    WP isa (.block decSetup) s₀ fun s => BInv decFn s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8) := by
  have hR := hp.rounds
  rw [decSetup, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (common_ok hp) fun s₁ c₁ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldrq (off := 208) (by decide) (by
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide), c₁.rd, c₁.wr]
    exact hp.key_in (by omega_using [])), WP.block_nil ?_⟩
  refine WP.mono (imcs_ok _ 13 (Nat.le_refl _)) fun s₂ ⟨e₂, o₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  have hL : ∀ j, j ≤ bnr s₀ → 16 * j + 16 ≤ 16 * (bnr s₀ + 1) := fun j hj => by omega_using [hj]
  have x0 : s₁.gpr .x0 = bkp s₀ := c₁.gpr _ (by decide) (by decide) (by decide) (by decide)
  -- The middle round keys, before `aesimc`.
  have pre : ∀ j, 1 ≤ j → j ≤ 13 → j < bnr s₀ →
      KeyIs ((s₁.setV .v29 (s₁.mem.readW (s₁.gpr .x0 + BitVec.ofNat 64 208) 128)).v (dreg j))
        (roundKey (bsch s₀) j) := by
    intro j h1 h2 h3
    by_cases h13 : j = 13
    · subst h13
      simp only [Impl.Aes.AArch64.Aese.dreg, ite_true, setV_v_self, x0, c₁.mem]
      have := keyIs_readW s₀.mem (bkp s₀) (L := 16 * (bnr s₀ + 1)) (j := 13) (hL 13 (by omega_using [h3]))
      simpa using this
    · simp only [Impl.Aes.AArch64.Aese.dreg, h13, ite_false]
      rw [setV_v_of_ne _ _ (kreg_ne j).1, c₁.kreg j (by omega_using [h2, h13])]
      exact keyIs_readW _ _ (hL j (by omega_using [h3]))
  refine ⟨⟨Nat.zero_le _, ⟨hR, ?_, fun j h1 h2 => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o₂ _ fun j hj => (dreg_ne j hj).1.symm, setV_v_of_ne _ _ (by decide), c₁.v30]
    exact keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · have hj13 : j ≤ 13 := by omega_using [hR, h2]
    have := e₂ (j - 1) (by omega_using [hj13])
    rw [show j - 1 + 1 = j by omega_using [h1], ite_eq_left (by omega_using [hj13])] at this
    rw [this]
    exact keyIs_aesimc (pre j h1 hj13 h2)
  · rw [o₂ _ fun j hj => (dreg_ne j hj).2.symm, setV_v_of_ne _ _ (by decide)]
    have := c₁.kreg 0 (by omega_using [])
    simp only [Impl.Aes.AArch64.Aese.kreg] at this
    rw [this]
    exact keyIs_readW _ _ (hL 0 (by omega_using []))
  · rw [g₂]; simp only [State.setV]; exact c₁.x6
  · rw [g₂]; simp only [State.setV]; exact c₁.x7
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp
  · rw [g₂]; simp only [State.setV]
    rw [c₁.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp [bnb]
  · rw [m₂]; simp only [State.setV, c₁.mem]; exact Frame.refl _ _
  · intro i hi
    rw [m₂]; simp only [State.setV, c₁.mem]
    rw [ite_eq_right (by omega_using [])]
  · rw [rd₂]; simp only [State.setV, c₁.rd]
  · rw [wr₂]; simp only [State.setV, c₁.wr]
  · rw [g₂]; simp only [State.setV, c₁.x13]

/-! ## The whole functions -/

theorem post_of (B : BlockFn) {s₀ : State} {s : State} (hI : BInv B s₀ (bnb s₀) (bnb s₀) s) :
    (Proof.Aes.blocksAArch64 B.F).post s₀ s := by
  show Spec.Aes.statesAt s.mem (bdp s₀) (bnb s₀) = _
  rw [Proof.Aes.AArch64.statesAt_of_ecbInv hI.data]
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

theorem bcorrect (B : BlockFn) {setup : List Instr} {s₀ : State} (hp : BPre s₀)
    (hs : WP isa (.block setup) s₀ fun s => BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8)) :
    WP isa (blocks setup B.f) s₀ ((Proof.Aes.blocksAArch64 B.F).post s₀) :=
  WP.seq (WP.mono hs fun _ ⟨hI₁, h13⟩ => WP.mono (loops_ok B hp hI₁ h13) fun _ hI => post_of B hI)

theorem blocks_correct (B : BlockFn) {setup : List Instr}
    (hs : ∀ s₀, BPre s₀ → WP isa (.block setup) s₀ fun s =>
      BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8))
    (hg : (blocks setup B.f).allInstrs (fun i => preserved.all fun r => !clobbers i r) = true)
    (hnc : (blocks setup B.f).noCalls = true) (hv : (blocks setup B.f).allInstrs keepsV = true)
    (s : State) (hp : (Proof.Aes.blocksAArch64 B.F).pre s) :
    ∃ t s', Exec isa (blocks setup B.f) s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 B.F).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved) (bcorrect B (bpre_of hp) (hs s (bpre_of hp))) hg hnc
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he hv⟩, h₂⟩

/-- A run of the functions changes no byte outside the data. -/
theorem blocks_frame (B : BlockFn) {setup : List Instr}
    (hs : ∀ s₀, BPre s₀ → WP isa (.block setup) s₀ fun s =>
      BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8))
    {s : State} (hp : BPre s) {t : List Leak} {s' : State} (he : Exec isa (blocks setup B.f) s t s') :
    Frame [bdR s] s.mem s'.mem := by
  obtain ⟨t', s'', he', hf⟩ : WP isa (blocks setup B.f) s fun s' => Frame [bdR s] s.mem s'.mem :=
    WP.seq (WP.mono (hs s hp) fun _ ⟨hI₁, h13⟩ => WP.mono (loops_ok B hp hI₁ h13) fun _ hI => hI.frame)
  obtain ⟨-, rfl⟩ := Exec.det he he'
  exact hf

/-- So they write none of `scratch` (`Artifact.written`). -/
theorem blocks_scratch (B : BlockFn) {setup : List Instr}
    (hs : ∀ s₀, BPre s₀ → WP isa (.block setup) s₀ fun s =>
      BInv B s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (bnb s₀ / 8))
    {s : State} (hp : BPre s) {t : List Leak} {s' : State} (he : Exec isa (blocks setup B.f) s t s')
    {i : Nat} (hi : i < 2048) :
    s'.mem (s.gpr .x4 + BitVec.ofNat 64 i) = s.mem (s.gpr .x4 + BitVec.ofNat 64 i) :=
  blocks_frame B hs hp he _ fun r hr hc => by
    rw [List.mem_singleton] at hr
    subst hr
    exact hp.d_s _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

theorem encryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' :=
  blocks_correct encFn (fun _ hp => encSetup_ok hp) (by lit_decide) (by lit_decide)
    (by lit_decide) s hs

theorem decryptBlocks_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocks s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' :=
  blocks_correct decFn (fun _ hp => decSetup_ok hp) (by lit_decide) (by lit_decide)
    (by lit_decide) s hs

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

theorem encryptBlocks_implies :
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).Implies (Proof.Aes.encryptBlocksRoundsContract AArch64.abi) := by
  sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
    AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat

theorem decryptBlocks_implies :
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).Implies (Proof.Aes.decryptBlocksRoundsContract AArch64.abi) := by
  sig_implies [Proof.Aes.decryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
    AArch64.abi, AArch64.argRegs] [Proof.Aes.AArch64.blocksSat] using Proof.Aes.AArch64.blocksSat

theorem encryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.encryptBlocksRoundsContract AArch64.abi).pre s) (he : Exec isa encryptBlocks s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := bpre_of (encryptBlocks_implies.pre s hs)
  simp [Sig.writtenWithin, AArch64.abi, AArch64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  exact fun i h => blocks_scratch encFn (fun _ hp => encSetup_ok hp) hp he (by simpa [Elem.size] using h)

theorem decryptBlocks_written (s : State) (t : List Leak) (s' : State)
    (hs : (Proof.Aes.decryptBlocksRoundsContract AArch64.abi).pre s) (he : Exec isa decryptBlocks s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Aes.blocksSig [("scratch", 0)] s s' := by
  have hp := bpre_of (decryptBlocks_implies.pre s hs)
  simp [Sig.writtenWithin, AArch64.abi, AArch64.argRegs, Abi.withConsts, Spec.Aes.blocksSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  exact fun i h => blocks_scratch decFn (fun _ hp => decSetup_ok hp) hp he (by simpa [Elem.size] using h)

/-! ## Returning without secret residue

`encryptBlocks` and `decryptBlocks` leave the blocks in `v0`–`v7` and the
round keys in `v16`–`v30`. The functions that callers call by name keep them
(a caller that calls them for each block clears once, at its own end), and
`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt`, which are their code, clear
them before they return (`AesEcb.AArch64.encryptRegs`). -/

/-- The vector registers `encryptBlocks` and `decryptBlocks` leave secrets in. -/
def blocksLeft : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30]

theorem encryptBlocks_noResidue (k : Contract isa) :
    NoResidue (Impl.Residue.AArch64.withClears [] blocksLeft none encryptBlocks) k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

theorem decryptBlocks_noResidue (k : Contract isa) :
    NoResidue (Impl.Residue.AArch64.withClears [] blocksLeft none decryptBlocks) k 0 :=
  RTaint.noResidue_of_check ⟨_, by taint_decide⟩ k

end VG.Proof.Aes.AArch64.Aese
