module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the cipher loop is shared by block modes and CTR.
/-! # POWER8 AES round loop -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (key mask byteMask)
open VG.Spec.Aes (roundKey addRoundKey subBytes shiftRows mixColumns invSubBytes invShiftRows invMixColumns)

def keyIndex (inverse : Bool) (nr j : Nat) : Nat := if inverse then nr-j else j

def middle (inverse : Bool) (nr : Nat) (w : List Byte) (input : Spec.Aes.State) (j : Nat) : Spec.Aes.State :=
  if inverse then Proof.Aes.invMid nr w j (addRoundKey input (roundKey w nr))
  else Proof.Aes.Vector.rnds w input j

def transform (inverse last : Bool) (rk : List Byte) (x : Spec.Aes.State) : Spec.Aes.State :=
  if inverse then
    let y := addRoundKey (invSubBytes (invShiftRows x)) rk
    if last then y else invMixColumns y
  else addRoundKey (if last then shiftRows (subBytes x) else mixColumns (shiftRows (subBytes x))) rk

def result (inverse : Bool) (nr : Nat) (w : List Byte) (input : Spec.Aes.State) : Spec.Aes.State :=
  if inverse then Spec.Aes.invCipher nr w input else Spec.Aes.cipher nr w input

theorem vcipher_transform (inverse last : Bool) {v k : BitVec 128} {rk : List Byte} (hk : IsKey k rk) :
    aesState (vcipher inverse last v k) = transform inverse last rk (aesState v) := by
  cases inverse
  · exact cipher_state last hk
  · exact invCipher_state last hk

theorem middle_zero (inverse : Bool) (nr : Nat) (w : List Byte) (input : Spec.Aes.State) :
    middle inverse nr w input 0 = addRoundKey input (roundKey w (keyIndex inverse nr 0)) := by
  cases inverse <;> simp only [middle, keyIndex, Bool.false_eq_true, ite_false, ite_true,
    Proof.Aes.Vector.rnds_zero, Proof.Aes.invMid, List.range_zero, List.foldl_nil, Nat.sub_zero]

theorem middle_succ (inverse : Bool) (nr : Nat) (w : List Byte) (input : Spec.Aes.State) (j : Nat) :
    transform inverse false (roundKey w (keyIndex inverse nr (j+1))) (middle inverse nr w input j) =
      middle inverse nr w input (j+1) := by
  cases inverse
  · simp only [middle, keyIndex, transform, Bool.false_eq_true, ite_false, Proof.Aes.Vector.rnds_succ]
  · simp only [middle, keyIndex, transform, ite_true, Bool.false_eq_true, ite_false,
      Proof.Aes.invMid_succ, Proof.Aes.irnd, Nat.sub_sub]
    rw [Nat.add_comm j 1]

theorem middle_last (inverse : Bool) (nr : Nat) (w : List Byte) (input : Spec.Aes.State) :
    transform inverse true (roundKey w (keyIndex inverse nr nr)) (middle inverse nr w input (nr-1)) =
      result inverse nr w input := by
  cases inverse
  · simp only [middle, keyIndex, transform, result, Bool.false_eq_true, ite_false, ite_true,
      Proof.Aes.Vector.cipher_eq]
  · simp only [middle, keyIndex, transform, result, ite_true, Nat.sub_self, Proof.Aes.invCipher_eq]

theorem start_run (inverse : Bool) (s : State) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.keyStart inverse)) s
      (· = s.write .r9 (if inverse then s.gpr .r3 + (s.gpr .r4 <<< 4) else s.gpr .r3)) := by
  cases inverse <;> apply WP.of_runBlock
  · simp only [Impl.Aes.PPC64LE.Crypto.keyStart, Impl.Aes.PPC64LE.Crypto.mov,
      Bool.false_eq_true, ite_false, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, BitVec.or_self, Option.some.injEq, exists_eq_left']
  · simp only [Impl.Aes.PPC64LE.Crypto.keyStart, ite_true, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, show 4 < 64 by decide, ite_true, RegUpd.gpr_write, reduceCtorEq, ite_false,
      write_overwrite, Option.some.injEq, exists_eq_left']

theorem advance_run (inverse : Bool) (source : Reg) (s : State) (hs : source ≠ .r9) (h0 : source ≠ .r0) :
    WP isa (.block [Impl.Aes.PPC64LE.Crypto.keyStep inverse, .subi .r10 source 1]) s
      (· = (s.write .r9 (if inverse then s.gpr .r9 - 16 else s.gpr .r9 + 16)).write .r10 (s.gpr source - 1)) := by
  cases inverse <;> apply WP.of_runBlock <;>
    simp only [Impl.Aes.PPC64LE.Crypto.keyStep, Bool.false_eq_true, ite_false, ite_true,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, h0, ne_eq, not_false_eq_true,
      show 16 < 2^15 by decide, show 1 ≤ 2^15 by decide,
      show 16 ≤ 2^15 by decide, RegUpd.gpr_write, hs, reduceCtorEq,
      and_self, BitVec.ofNat_eq_ofNat, Option.some.injEq, exists_eq_left']


abbrev schedule (nr : Nat) (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .r3) (16*(nr+1))

structure Inputs (nr : Nat) (s : State) : Prop where
  zero : s.gpr .r0 = 0
  mask : s.vpr mask = byteMask
  rounds : s.gpr .r4 = BitVec.ofNat 64 nr
  min : 1 < nr
  max : nr < 15
  reads : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (16*j)) 16

structure RInv (inverse : Bool) (rs : List VReg) (s₀ : State) (nr j : Nat) (s : State) : Prop where
  effects : Local [.r9, .r10] (key :: rs) s₀ s
  ptr : s.gpr .r9 = s₀.gpr .r3 + BitVec.ofNat 64 (16*keyIndex inverse nr (j+1))
  left : s.gpr .r10 = BitVec.ofNat 64 (nr-1-j)
  val : ∀ b ∈ rs, aesState (s.vpr b) = middle inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) j

theorem keyIndex_le (inverse : Bool) {nr j : Nat} (hj : j ≤ nr) : keyIndex inverse nr j ≤ nr := by
  cases inverse <;> simp only [keyIndex, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem pointer_step (inverse : Bool) (base : Addr) {nr j : Nat} (hj : j < nr) :
    (if inverse then (base + BitVec.ofNat 64 (16*keyIndex inverse nr j)) - 16
      else (base + BitVec.ofNat 64 (16*keyIndex inverse nr j)) + 16) =
      base + BitVec.ofNat 64 (16*keyIndex inverse nr (j+1)) := by
  cases inverse
  · simp only [keyIndex, Bool.false_eq_true, ite_false]
    change base + BitVec.ofNat 64 (16*j) + BitVec.ofNat 64 16 = _
    rw [Offset.add_add]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)
  · simp only [keyIndex, ite_true]
    change base + BitVec.ofNat 64 (16*(nr-j)) - BitVec.ofNat 64 16 = _
    rw [Offset.add_ofNat_sub base (by omega)]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega)

theorem pointer_next (inverse : Bool) (base : Addr) {nr j : Nat} (hj : j < nr-1) :
    (if inverse then (base + BitVec.ofNat 64 (16*keyIndex inverse nr (j+1))) - 16
      else (base + BitVec.ofNat 64 (16*keyIndex inverse nr (j+1))) + 16) =
      base + BitVec.ofNat 64 (16*keyIndex inverse nr (j+2)) :=
  pointer_step inverse base (by omega)

theorem middleBody_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr j : Nat} (hp : Inputs nr s₀) (hj : j < nr-1) (h : RInv inverse rs s₀ nr j s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.middleBody inverse rs)) s (RInv inverse rs s₀ nr (j+1)) := by
  have hidx : keyIndex inverse nr (j+1) ≤ nr := keyIndex_le inverse (by omega)
  have hz : s.gpr .r0 = 0 := (h.effects.keep.gpr (by decide)).trans hp.zero
  have hmask : s.vpr mask = byteMask := (h.effects.v mask (by simp [hm, key, mask])).trans hp.mask
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16 := by
    rw [h.effects.keep.2.1, h.effects.keep.2.2, h.ptr]
    exact hp.reads _ hidx
  have hkey : IsKey (rev128 (s.mem.read (s.gpr .r9) 16)) (roundKey (schedule nr s₀) (keyIndex inverse nr (j+1))) := by
    rw [h.effects.mem, h.ptr]
    exact key_read s₀.mem (s₀.gpr .r3) (by omega)
  rw [Impl.Aes.PPC64LE.Crypto.middleBody, WP.block_append_iff]
  refine WP.mono (round_ok inverse false rs s hn hk hz hmask hr) fun u ⟨hv, ho⟩ => ?_
  have hy : ∀ b ∈ rs, aesState (u.vpr b) = middle inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) (j+1) := by
    intro b hb
    rw [hv b hb, vcipher_transform inverse false hkey, h.val b hb]
    exact middle_succ inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) j
  refine WP.mono (advance_run inverse .r10 u (by decide) (by decide)) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hf := (h.effects.trans (Local.of_vector ho)).trans
      ((Local.write u .r9 (if inverse then u.gpr .r9 - 16 else u.gpr .r9 + 16)).trans
        (Local.write _ .r10 (u.gpr .r10 - 1)))
    exact hf.weaken (by simp) (by simp [or_left_comm])
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, ho.gpr, h.ptr]
    exact pointer_next inverse (s₀.gpr .r3) hj
  · simp only [RegUpd.gpr_write_self, ho.gpr, h.left]
    change BitVec.ofNat 64 (nr-1-j) - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · simpa only [vpr_write] using hy


theorem initialBody_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs)
    {s : State} {nr : Nat} (hp : Inputs nr s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.initialBody inverse rs)) s (RInv inverse rs s nr 0) := by
  rw [Impl.Aes.PPC64LE.Crypto.initialBody]
  repeat rw [WP.block_append_iff]
  refine WP.mono (start_run inverse s) fun t ht => ?_
  subst t
  let p : Addr := if inverse then s.gpr .r3 + (s.gpr .r4 <<< 4) else s.gpr .r3
  have hpidx : (s.write .r9 p).gpr .r9 = s.gpr .r3 + BitVec.ofNat 64 (16*keyIndex inverse nr 0) := by
    rw [RegUpd.gpr_write_self]
    cases inverse
    · simp only [p, keyIndex, Bool.false_eq_true, ite_false, Nat.mul_zero, BitVec.add_zero]
    · simp only [p, keyIndex, ite_true, Nat.sub_zero, hp.rounds]
      rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 4 = BitVec.ofNat 64 16 from rfl,
        BitVec.ofNat_mul_ofNat, Nat.mul_comm nr 16]
  have hr : InRegions ((s.write .r9 p).rd ++ (s.write .r9 p).wr) ((s.write .r9 p).gpr .r9) 16 := by
    rw [RegUpd.rd_write, RegUpd.wr_write, hpidx]
    exact hp.reads _ (keyIndex_le inverse (by omega))
  have hz : (s.write .r9 p).gpr .r0 = 0 := by
    simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hp.zero
  have hm : (s.write .r9 p).vpr mask = byteMask := by simpa only [vpr_write] using hp.mask
  have hkey : IsKey (rev128 ((s.write .r9 p).mem.read ((s.write .r9 p).gpr .r9) 16))
      (roundKey (schedule nr s) (keyIndex inverse nr 0)) := by
    rw [RegUpd.mem_write, hpidx]
    exact key_read s.mem (s.gpr .r3) (by
      have hidx := keyIndex_le inverse (show 0 ≤ nr by omega)
      have := hp.max
      omega)
  rw [← WP.block_append_iff]
  change WP isa (.block (Impl.Aes.PPC64LE.Crypto.load key .r9 ++ Impl.Aes.PPC64LE.Crypto.xorKey rs))
    (s.write .r9 p) _
  refine WP.mono (keyed_ok (fun b => .vop (.logic .xor b b key)) (· ^^^ ·) (fun _ _ => rfl)
      rs (s.write .r9 p) hn hk hz hm hr) fun u ⟨hv, ho⟩ => ?_
  have hy : ∀ b ∈ rs, aesState (u.vpr b) = middle inverse nr (schedule nr s) (aesState (s.vpr b)) 0 := by
    intro b hb
    rw [hv b hb, xor_state hkey, vpr_write]
    exact (middle_zero inverse nr (schedule nr s) (aesState (s.vpr b))).symm
  refine WP.mono (advance_run inverse .r4 u (by decide) (by decide)) fun t ht => ?_
  subst t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hf := ((Local.write s .r9 p).trans (Local.of_vector ho)).trans
      ((Local.write u .r9 (if inverse then u.gpr .r9 - 16 else u.gpr .r9 + 16)).trans
        (Local.write _ .r10 (u.gpr .r4 - 1)))
    exact hf.weaken (by simp) (by simp)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, ho.gpr]
    have hpvalue : p = s.gpr .r3 + BitVec.ofNat 64 (16*keyIndex inverse nr 0) :=
      (RegUpd.gpr_write_self s .r9 p).symm.trans hpidx
    rw [hpvalue]
    exact pointer_step inverse (s.gpr .r3) (j := 0) (by have := hp.min; omega)
  · simp only [RegUpd.gpr_write_self, ho.gpr, RegUpd.gpr_write, reduceCtorEq, ite_false, hp.rounds,
      Nat.sub_zero]
    change BitVec.ofNat 64 nr - BitVec.ofNat 64 1 = _
    rw [Offset.ofNat_sub_ofNat (by have := hp.min; omega)]
  · simpa only [vpr_write] using hy


theorem middleLoop_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr : Nat} (hp : Inputs nr s₀) (h : RInv inverse rs s₀ nr 0 s) :
    WP isa (.loop (.block (Impl.Aes.PPC64LE.Crypto.middleBody inverse rs)) (.nonzero .d .r10)) s
      (RInv inverse rs s₀ nr (nr-1)) := by
  let I : Nat → State → Prop := fun m t => ∃ j, m = nr-1-j ∧ j < nr-1 ∧ RInv inverse rs s₀ nr j t
  have step : ∀ m t, I m t → WP isa (.block (Impl.Aes.PPC64LE.Crypto.middleBody inverse rs)) t fun u =>
      (eval (.nonzero .d .r10) u = some false ∧ RInv inverse rs s₀ nr (nr-1) u) ∨
      (eval (.nonzero .d .r10) u = some true ∧ ∃ m' < m, I m' u) := by
    rintro m t ⟨j, rfl, hj, ht⟩
    refine WP.mono (middleBody_ok inverse rs hn hk hm hp hj ht) fun u hu => ?_
    have he : eval (.nonzero .d .r10) u = some (BitVec.ofNat 64 (nr-1-(j+1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hu.left]
    by_cases hl : j+1 = nr-1
    · left
      rw [hl, Nat.sub_self] at he
      exact ⟨he.trans (by decide), hl ▸ hu⟩
    · right
      have hne : BitVec.ofNat 64 (nr-1-(j+1)) ≠ 0 := by
        intro hz
        have hzero := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.max; omega)] at hzero
        have h0 : (0 : BitVec 64).toNat = 0 := rfl
        rw [h0] at hzero
        omega
      exact ⟨he.trans (by simpa using hne), nr-1-(j+1), by omega, j+1, rfl, by omega, hu⟩
  exact WP.loop (M := isa) I step (nr-1) s ⟨0, by omega, by have := hp.min; omega, h⟩

theorem last_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr : Nat} (hp : Inputs nr s₀) (h : RInv inverse rs s₀ nr (nr-1) s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.round inverse true rs)) s fun t =>
      (∀ b ∈ rs, aesState (t.vpr b) = result inverse nr (schedule nr s₀) (aesState (s₀.vpr b))) ∧
      Local [.r9, .r10] (key :: rs) s₀ t := by
  have hz : s.gpr .r0 = 0 := (h.effects.keep.gpr (by decide)).trans hp.zero
  have hmask : s.vpr mask = byteMask := (h.effects.v mask (by simp [hm, key, mask])).trans hp.mask
  have he : nr-1+1 = nr := by have := hp.min; omega
  have hptr : s.gpr .r9 = s₀.gpr .r3 + BitVec.ofNat 64 (16*keyIndex inverse nr nr) := by
    simpa only [he] using h.ptr
  have hidx : keyIndex inverse nr nr ≤ nr := keyIndex_le inverse (Nat.le_refl _)
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r9) 16 := by
    rw [h.effects.keep.2.1, h.effects.keep.2.2, hptr]
    exact hp.reads _ hidx
  have hkey : IsKey (rev128 (s.mem.read (s.gpr .r9) 16)) (roundKey (schedule nr s₀) (keyIndex inverse nr nr)) := by
    rw [h.effects.mem, hptr]
    exact key_read s₀.mem (s₀.gpr .r3) (by omega)
  refine WP.mono (round_ok inverse true rs s hn hk hz hmask hr) fun t ⟨hv, ho⟩ => ⟨?_, ?_⟩
  · intro b hb
    rw [hv b hb, vcipher_transform inverse true hkey, h.val b hb]
    exact middle_last inverse nr (schedule nr s₀) (aesState (s₀.vpr b))
  · exact (h.effects.trans (Local.of_vector ho)).weaken (by simp) (by simp [or_left_comm])

theorem aes_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s : State} {nr : Nat} (hp : Inputs nr s) :
    WP isa (Impl.Aes.PPC64LE.Crypto.aes inverse rs) s fun t =>
      (∀ b ∈ rs, aesState (t.vpr b) = result inverse nr (schedule nr s) (aesState (s.vpr b))) ∧
      Local [.r9, .r10] (key :: rs) s t := by
  rw [Impl.Aes.PPC64LE.Crypto.aes]
  refine WP.seq (WP.mono (initialBody_ok inverse rs hn hk hp) fun t ht => ?_)
  exact WP.seq (WP.mono (middleLoop_ok inverse rs hn hk hm hp ht) fun u hu => last_ok inverse rs hn hk hm hp hu)

end VG.Proof.Aes.PPC64LE.Crypto
