module

public import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Rounds
public import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.Layout
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.Sm4.AArch64.Sm4e.Ecb
meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Rounds
meta import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Spec.Sm4.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM4 ECB with the Armv8 SM4 instructions

`ecb_verified`: `Impl.Sm4.AArch64.Sm4e.ecb dir` (`vg_sm4_ecb_encrypt_sm4`,
`vg_sm4_ecb_decrypt_sm4`) meets the ECB contracts of `Spec/Sm4/Contract.lean`
on AArch64, with no stack.

* A block register holds, between `rev32 .16b` and the final reversal, the
  four words of the state, word `e` in lane `e` (`vec`), and a round key
  register the four round keys of a group of rounds (`rkVec`): `sm4e` is then
  a `quad` of the specification's rounds (`sm4E_eq`), and the eight of them
  its 32 rounds (`rounds_ok`, `Proof.Sm4.crypt_eq`).
* A block loaded and through `rev32 .16b` is the block's big-endian words
  (`rev32b_readW`); `rev64 .16b` and `ext #8` reverse the sixteen bytes
  (`vbyte_revBytes`), which leaves the output block's bytes in memory order
  (`vbyte_out`).
* The schedule's sixteen bytes at `16 r` are the round keys `4 r … 4 r + 3`
  (`encKey_readW`); `rev64 .4s` and `ext #8` reverse the four words
  (`vword_revWords`), so those at `16 (7 - r)` become the round keys
  `31 - 4 r … 28 - 4 r` (`decKey_readW`): the rounds' keys of each direction
  (`dirKey`).
* The loops keep, after `c` blocks, the first `c` data blocks transformed and
  the others as they were (`Proof.Sm4.DInv`, `BInv`): each group is loaded
  (`ldData_ok`), transformed (`crypt_ok`) and stored back (`stData_ok`).

Constant time is the taint analysis's, from the pointers, `n` and the stack
pointer.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Sm4e

open VG VG.AArch64
open VG.Impl.Sm4.AArch64 (Dir)
open VG.Impl.Sm4.AArch64.Sm4e
open VG.Spec.Sm4 (Word Block blockAt scheduleAt)
open VG.Proof.Sm4 (quads quad ofBlock outBlock DInv)
open VG.Proof.Aes.AArch64.Aese (VFrame Fr each_ok setV_v_self setV_v_of_ne setV_setV exec_ldrq exec_strq
  ushr3 eval_zero eval_nonzero vbyte_readW ext_vbyte)

/-- The specification's direction. -/
def dirOf : Dir → Spec.Sm4.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-! ## Vectors -/

/-- `ext v, v, v, #8`: the two halves swapped. -/
def swap8 (x : BitVec 128) : BitVec 128 := ((x ++ x) >>> (8 * 8)).extractLsb' 0 128

theorem vbyte_swap8 (x : BitVec 128) {i : Nat} (hi : i < 16) : vbyte (swap8 x) i = vbyte x ((i + 8) % 16) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vbyte, swap8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hj,
    decide_true, Bool.true_and, Nat.zero_add, show 8 * i + j < 128 by omega_using [hi, hj]]
  by_cases h : i < 8
  · rw [ite_eq_left (by omega_using [h, hj])]
    exact congrArg x.getLsbD (by omega_using [h])
  · rw [ite_eq_right (by omega_using [h, hj])]
    exact congrArg x.getLsbD (by omega_using [h, hi])

/-- A bit of a lane is a bit of one of its bytes. -/
theorem getLsbD_vword (x : BitVec 128) (e : Nat) {j : Nat} (hj : j < 32) :
    (vword x e).getLsbD j = (vbyte x (4 * e + j / 8)).getLsbD (j % 8) := by
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    show j % 8 < 8 by omega_using []]
  exact congrArg x.getLsbD (by omega_using [])

/-- `rev64 .4s` and `ext #8` reverse the four words. -/
theorem vword_revWords (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (swap8 (VRevOp.rev64s.eval x)) e = vword x (3 - e) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_vword _ _ hj, getLsbD_vword _ _ hj, vbyte_swap8 _ (by omega_using [he, hj])]
  simp only [VRevOp.eval]
  rw [vbyte_ofVBytes _ (by omega_using [])]
  exact congrArg (fun k => (vbyte x k).getLsbD (j % 8)) (by omega_using [he, hj])

/-- `rev64 .16b` and `ext #8` reverse the sixteen bytes. -/
theorem vbyte_revBytes (x : BitVec 128) {t : Nat} (ht : t < 16) :
    vbyte (swap8 (VRevOp.rev64b.eval x)) t = vbyte x (15 - t) := by
  rw [vbyte_swap8 _ ht]
  simp only [VRevOp.eval]
  rw [vbyte_ofVBytes _ (by omega_using [])]
  exact congrArg (vbyte x) (by omega_using [ht])

theorem four_getElem (z : Nat → Word) : ∀ {e : Nat} (he : e < 4), [z 0, z 1, z 2, z 3][e] = z e
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- The bytes stored are the output block's. -/
theorem vbyte_out (z : Nat → Word) {t : Nat} (ht : t < 16) :
    vbyte (swap8 (VRevOp.rev64b.eval (vec z))) t = (outBlock z).getD t 0 := by
  rw [vbyte_revBytes _ ht]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [Proof.Sm4.getLsbD_outBlock z ht hj]
  have h := getLsbD_vword (vec z) (3 - t / 4) (j := 8 * (3 - t % 4) + j) (by omega_using [hj])
  rw [show 4 * (3 - t / 4) + (8 * (3 - t % 4) + j) / 8 = 15 - t by omega_using [ht, hj],
    show (8 * (3 - t % 4) + j) % 8 = j by omega_using [hj]] at h
  rw [← h, vec, vword_ofVWords _ _ _ _ (by omega_using [])]
  exact congrArg (BitVec.getLsbD · _) (four_getElem z (by omega_using []))

/-! ## Blocks and round keys in memory -/

/-- The register of the round keys `K (4 r) … K (4 r + 3)`. -/
def rkVec (K : Nat → Word) (r : Nat) : BitVec 128 :=
  ofVWords (K (4 * r)) (K (4 * r + 1)) (K (4 * r + 2)) (K (4 * r + 3))

theorem vword_rkVec (K : Nat → Word) (r : Nat) : ∀ {e : Nat} (_ : e < 4), vword (rkVec K r) e = K (4 * r + e)
  | 0, _ => vword_ofVWords_0 ..
  | 1, _ => vword_ofVWords_1 ..
  | 2, _ => vword_ofVWords_2 ..
  | 3, _ => vword_ofVWords_3 ..

theorem vword_readW (m : Mem) (p : Addr) {e : Nat} (he : e < 4) :
    vword (m.readW p 128) e = m.readW (p + BitVec.ofNat 64 (4 * e)) 32 :=
  vword_read16 m p he

/-- A block loaded and its words' bytes reversed: the block's words. -/
theorem rev32b_readW (m : Mem) (p : Addr) :
    VRevOp.rev32b.eval (m.readW p 128) = vec (ofBlock (blockAt m p)) := by
  refine vec_ext fun e he => ?_
  rw [vword_rev32b _ he, vword_readW m p he, rev32_readW, vec, vword_ofVWords _ _ _ _ he, four_getElem _ he]
  simp only [ofBlock, Spec.Sm4.wordAt, Proof.Sm4.blockAt_getD m p (show 4 * e < 16 by omega_using [he]),
    Proof.Sm4.blockAt_getD m p (show 4 * e + 1 < 16 by omega_using [he]),
    Proof.Sm4.blockAt_getD m p (show 4 * e + 2 < 16 by omega_using [he]),
    Proof.Sm4.blockAt_getD m p (show 4 * e + 3 < 16 by omega_using [he])]
  rw [show p + BitVec.ofNat 64 (4 * e) + 1 = p + BitVec.ofNat 64 (4 * e + 1) from Offset.add_add_eq p rfl,
    show p + BitVec.ofNat 64 (4 * e + 1) + 1 = p + BitVec.ofNat 64 (4 * e + 2) from Offset.add_add_eq p rfl,
    show p + BitVec.ofNat 64 (4 * e + 2) + 1 = p + BitVec.ofNat 64 (4 * e + 3) from Offset.add_add_eq p rfl]

/-- Round key `i` of a stored schedule is its little-endian word `i`. -/
theorem schedule_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 32) :
    (scheduleAt m p).getD i 0 = m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := by
  have e : (scheduleAt m p).getD i 0 = (scheduleAt m p)[i]'hi := by simp [Vector.getD, hi]
  rw [e]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_readW32 m p i hj]
  have := Proof.Sm4.getLsbD_scheduleAt m p hi (c := j / 8) (j := j % 8) (by omega_using [hj]) (by omega_using [])
  rw [show 8 * (j / 8) + j % 8 = j by omega_using []] at this
  rw [this, show (32 * i + j) / 8 = 4 * i + j / 8 by omega_using [], show (32 * i + j) % 8 = j % 8 by omega_using []]

/-- The round keys of each direction, in the order the rounds use them. -/
def dirKey (sch : Spec.Sm4.Schedule) : Dir → Nat → Word
  | .encrypt => fun i => sch.getD i 0
  | .decrypt => fun i => sch.getD (31 - i) 0

/-- Encryption's register `r`. -/
theorem encKey_readW (m : Mem) (p : Addr) {r : Nat} (hr : r < 8) :
    m.readW (p + BitVec.ofNat 64 (16 * r)) 128 = rkVec (dirKey (scheduleAt m p) .encrypt) r := by
  refine vec_ext fun e he => ?_
  rw [vword_readW _ _ he, vword_rkVec _ _ he]
  show _ = Vector.getD (scheduleAt m p) (4 * r + e) 0
  rw [schedule_getD m p (by omega_using [hr, he]),
    Offset.add_add_eq p (show 16 * r + 4 * e = 4 * (4 * r + e) by omega_using [])]

/-- Decryption's register `r`. -/
theorem decKey_readW (m : Mem) (p : Addr) {r : Nat} (hr : r < 8) :
    swap8 (VRevOp.rev64s.eval (m.readW (p + BitVec.ofNat 64 (16 * (7 - r))) 128)) =
      rkVec (dirKey (scheduleAt m p) .decrypt) r := by
  refine vec_ext fun e he => ?_
  rw [vword_revWords _ he, vword_readW _ _ (by omega_using []), vword_rkVec _ _ he]
  show _ = Vector.getD (scheduleAt m p) (31 - (4 * r + e)) 0
  rw [schedule_getD m p (by omega_using [hr, he]),
    Offset.add_add_eq p (show 16 * (7 - r) + 4 * (3 - e) = 4 * (31 - (4 * r + e)) by omega_using [hr, he])]

/-- The specification's block function is the eight groups of rounds. -/
theorem blockFn_eq (sch : Spec.Sm4.Schedule) (dir : Dir) (b : Block) :
    Proof.Sm4.blockFn sch (dirOf dir) b = outBlock (quads .enc (dirKey sch dir) 8 (ofBlock b)) := by
  cases dir
  · show Spec.Sm4.encryptBlock sch b = _
    simp only [Spec.Sm4.encryptBlock, dirKey]
    exact Proof.Sm4.crypt_eq _ b
  · show Spec.Sm4.decryptBlock sch b = _
    simp only [Spec.Sm4.decryptBlock, dirKey]
    exact Proof.Sm4.crypt_eq _ b

/-! ## The instructions on the block registers -/

theorem kreg_cases (r : Nat) : kreg r = .v16 ∨ kreg r = .v17 ∨ kreg r = .v18 ∨ kreg r = .v19 ∨
    kreg r = .v20 ∨ kreg r = .v21 ∨ kreg r = .v22 ∨ kreg r = .v23 :=
  match r with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 => by simp [kreg]

theorem kreg_inj : ∀ i < 8, ∀ j < 8, kreg i = kreg j → i = j := by decide

/-- The registers the blocks may be in: distinct, and none a round key's. -/
def BRegs (regs : List VReg) : Prop := regs.Nodup ∧ ∀ r, kreg r ∉ regs

theorem bregs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) : BRegs rs := by
  rcases h with rfl | rfl <;> refine ⟨by decide, fun r => ?_⟩ <;>
    rcases kreg_cases r with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

/-- The round keys `K`, four to a register. -/
def KeysOk (K : Nat → Word) (s : State) : Prop := ∀ r < 8, s.v (kreg r) = rkVec K r

theorem KeysOk.of_v {K : Nat → Word} {s s' : State} (h : KeysOk K s)
    (hv : ∀ r, s'.v (kreg r) = s.v (kreg r)) : KeysOk K s' := fun r hr => (hv r).trans (h r hr)

theorem toWords_run (b : VReg) (s : State) :
    runBlock isa [.vop (.rev .rev32b b b)] s = some (s.setV b (VRevOp.rev32b.eval (s.v b))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, reduceVOpEval, Option.map_some]

theorem sm4e_run (k b : VReg) (s : State) :
    runBlock isa [.vop (.sm4e b k)] s = some (s.setV b (sm4E (s.v b) (s.v k))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, reduceVOpEval, Option.map_some]

theorem rev_ext_run (op : VRevOp) (b : VReg) (s : State) :
    runBlock isa [.vop (.rev op b b), .vop (.ext b b b 8)] s = some (s.setV b (swap8 (op.eval (s.v b)))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, reduceVOpEval, Option.map_some,
    Nat.reduceLT, ↓reduceIte]
  rw [setV_v_self, setV_setV]
  rfl

theorem toWords_ok (regs : List VReg) (s : State) (hr : BRegs regs) :
    WP isa (.block (toWords regs)) s fun s' =>
      (∀ b ∈ regs, s'.v b = VRevOp.rev32b.eval (s.v b)) ∧ VFrame regs s s' :=
  each_ok (fun b => [.vop (.rev .rev32b b b)]) (fun x _ => VRevOp.rev32b.eval x) .v16
    (fun b s _ => toWords_run b s) regs s hr.1 (hr.2 0)

theorem fromWords_ok (regs : List VReg) (s : State) (hr : BRegs regs) :
    WP isa (.block (fromWords regs)) s fun s' =>
      (∀ b ∈ regs, s'.v b = swap8 (VRevOp.rev64b.eval (s.v b))) ∧ VFrame regs s s' :=
  each_ok (fun b => [.vop (.rev .rev64b b b), .vop (.ext b b b 8)])
    (fun x _ => swap8 (VRevOp.rev64b.eval x)) .v16 (fun b s _ => rev_ext_run .rev64b b s) regs s hr.1 (hr.2 0)

theorem round4_ok (regs : List VReg) (r : Nat) (s : State) (hr : BRegs regs) :
    WP isa (.block (round4 regs (kreg r))) s fun s' =>
      (∀ b ∈ regs, s'.v b = sm4E (s.v b) (s.v (kreg r))) ∧ VFrame regs s s' :=
  each_ok (fun b => [.vop (.sm4e b (kreg r))]) sm4E (kreg r) (fun b s _ => sm4e_run (kreg r) b s) regs s
    hr.1 (hr.2 r)

/-- The first `n` groups of four rounds of each block. -/
theorem rounds_ok {regs : List VReg} (hr : BRegs regs) {K : Nat → Word} {s : State} (hK : KeysOk K s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun r => round4 regs (kreg r))) s fun s' =>
      (∀ b ∈ regs, ∀ x, s.v b = vec x → s'.v b = vec (quads .enc K n x)) ∧ VFrame regs s s'
  | 0, _ => WP.block_nil ⟨fun _ _ _ h => h, VFrame.refl _ _⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_ok hr hK n (by omega_using [hn])) fun s₁ ⟨e₁, f₁⟩ => ?_
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (round4_ok regs n s₁ hr) fun s₂ ⟨e₂, f₂⟩ => ⟨fun b hb x hx => ?_, f₁.trans f₂⟩
    rw [e₂ b hb, e₁ b hb x hx, f₁.v _ (hr.2 n), hK n (by omega_using [hn])]
    exact sm4E_eq K n _

/-- SM4 of each block register, with the round keys `K`. -/
theorem crypt_ok {regs : List VReg} (hr : BRegs regs) {K : Nat → Word} {s : State} (hK : KeysOk K s) :
    WP isa (.block (crypt regs)) s fun s' =>
      (∀ b ∈ regs, ∀ x, VRevOp.rev32b.eval (s.v b) = vec x →
        s'.v b = swap8 (VRevOp.rev64b.eval (vec (quads .enc K 8 x)))) ∧ VFrame regs s s' := by
  rw [crypt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (toWords_ok regs s hr) fun s₁ ⟨e₁, f₁⟩ => ?_
  refine WP.mono (rounds_ok hr (hK.of_v fun r => f₁.v _ (hr.2 r)) 8 (Nat.le_refl _)) fun s₂ ⟨e₂, f₂⟩ => ?_
  refine WP.mono (fromWords_ok regs s₂ hr) fun s₃ ⟨e₃, f₃⟩ => ⟨fun b hb x hx => ?_, (f₁.trans f₂).trans f₃⟩
  rw [e₃ b hb, e₂ b hb x ((e₁ b hb).trans hx)]

/-! ## The precondition and the loop invariant -/

/-- The ECB contracts on AArch64 with no stack, as `sig_pre` evaluates them. -/
def ecbAArch64 (dir : Dir) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 16⟩
    s.rd = [sched] ∧ s.wr = [data] ∧ sched.Disjoint data ∧
      (s.gpr .x0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 16 ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.Sm4.ecb (scheduleAt s.mem (s.gpr .x0)) (dirOf dir)
        (Spec.Sm4.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .x0
abbrev dp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev dR : Region := ⟨dp s₀, nb s₀ * 16⟩

/-- The round keys in the order `dir`'s rounds use them. -/
abbrev keyOf (dir : Dir) : Nat → Word := dirKey (scheduleAt s₀.mem (kp s₀)) dir

/-- Block `i` of the result. -/
def outOf (K : Nat → Word) (i : Nat) : Block :=
  outBlock (quads .enc K 8 (ofBlock (blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * i)))))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, 128⟩]
  wr : s₀.wr = [dR s₀]
  wrap : (dp s₀).toNat + nb s₀ * 16 ≤ 2 ^ 64

theorem pre_of {dir : Dir} {s₀ : State} (h : (ecbAArch64 dir).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, _, _, h5⟩ := h
  exact ⟨h1, h2, h5⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem nb16 : 16 * nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega_using [this]

theorem dat : (⟨dp s₀, 16 * nb s₀⟩ : Region) ∈ s₀.wr := by rw [hp.wr, Nat.mul_comm]; exact List.mem_singleton_self _

theorem key_in {o : Nat} (h : o + 16 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (kp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨kp s₀, 128⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega_using [h])⟩

end Pre

/-- After `c` blocks, with the data pointer and count at block `p`. -/
structure BInv (K : Nat → Word) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  keys : KeysOk K s
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (16 * p)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - p)
  data : DInv s₀.mem s.mem (dp s₀) (nb s₀) c (outOf s₀ K)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-! ## Loading and storing the blocks -/

theorem ldData_ok (p : Reg) : ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → j + regs.length ≤ 4096 →
    (∀ k < regs.length, InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 (16 * (j + k))) 16) →
    WP isa (.block (ldData p regs j)) s fun s' =>
      (∀ k (h : k < regs.length), s'.v regs[k] = s.mem.readW (s.gpr p + BitVec.ofNat 64 (16 * (j + k))) 128) ∧
      VFrame regs s s'
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), VFrame.refl _ _⟩
  | b :: bs, j, s, hnd, hj, hin => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hj
    rw [ldData, WP.block_cons_iff]
    refine ⟨_, exec_ldrq (by omega_using [hj]) (by simpa using hin 0 (by simp)), ?_⟩
    refine WP.mono (ldData_ok p bs (j + 1) _ (List.nodup_cons.mp hnd).2 (by omega_using [hj]) fun k hk => by
      have := hin (k + 1) (by simp; omega_using [hk])
      simpa [State.setV, show j + 1 + k = j + (k + 1) by omega_using []] using this)
      fun s' ⟨e, f⟩ => ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => simp only [List.getElem_cons_zero, Nat.add_zero]; rw [f.v _ hbs, setV_v_self]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk)]
        simp [State.setV, show j + 1 + k = j + (k + 1) by omega_using []]
    · exact ⟨f.gpr, f.sp, f.mem, f.rd, f.wr, fun r hr => by
        simp only [List.mem_cons, not_or] at hr
        rw [f.v r hr.2, setV_v_of_ne _ _ hr.1]⟩

/-- A block not yet transformed is the original. -/
theorem dinv_orig {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Block} (h : DInv m₀ m D n c F) {j : Nat}
    (hc : c ≤ j) (hj : j < n) :
    blockAt m (D + BitVec.ofNat 64 (16 * j)) = blockAt m₀ (D + BitVec.ofNat 64 (16 * j)) := by
  apply Vector.ext; intro t ht
  simp only [blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega_using [hj, ht]), ite_eq_right (by omega_using [hc])]

/-- One block stored, by a 16-byte store. -/
theorem dinv_write {m₀ m : Mem} {D : Addr} {n k : Nat} {F : Nat → Block} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : DInv m₀ m D n k F)
    (hv : ∀ t < 16, vbyte v t = (F k).getD t 0) :
    DInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16 v) D n (k + 1) F := by
  intro i hi
  show (if _ then _ else _) = _
  rw [Offset.sub_toNat' D (show 16 * k < 2 ^ 64 by omega_using [hn, hk]) (show i < 2 ^ 64 by omega_using [hn, hi])]
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

/-- The registers stored to the blocks `c + j …` of the `n` at `D`, the address
of block `c` in `p`: nothing else is written (bytes within `16 n` of `D` only). -/
theorem stData_ok (p : Reg) {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Block} (hn : 16 * n ≤ 2 ^ 64) :
    ∀ (regs : List VReg) (j : Nat) (s : State),
    s.gpr p = D + BitVec.ofNat 64 (16 * c) → j + regs.length ≤ 4096 → c + j + regs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.wr → DInv m₀ s.mem D n (c + j) F →
    (∀ k (h : k < regs.length), ∀ t < 16, vbyte (s.v regs[k]) t = (F (c + j + k)).getD t 0) →
    WP isa (.block (stData p regs j)) s fun s' =>
      DInv m₀ s'.mem D n (c + j + regs.length) F ∧
      s'.gpr = s.gpr ∧ s'.v = s.v ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ x, ¬ (x - D).toNat < 16 * n → s'.mem x = s.mem x
  | [], _, s, _, _, _, _, hD, _ => WP.block_nil ⟨by simpa using hD, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | b :: bs, j, s, hx1, hj, hc, hw, hD, hF => by
    simp only [List.length_cons] at hj hc
    have ha : s.gpr p + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hx1, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega_using [])]
    rw [stData, WP.block_cons_iff]
    refine ⟨_, exec_strq (by omega_using [hj]) (by rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega_using [hc]) (by omega_using [hn, hc])⟩), ?_⟩
    rw [ha]
    have hst := dinv_write hn (by omega_using [hc]) hD (v := s.v b) fun t ht => by
      have := hF 0 (by simp) t ht
      simpa using this
    refine WP.mono (stData_ok p (m₀ := m₀) (c := c) (F := F) hn bs (j + 1) _ hx1 (by omega_using [hj]) (by omega_using [hc]) hw
      (by rw [show c + (j + 1) = c + j + 1 by omega_using []]; exact hst) (fun k hk t ht => by
        have := hF (k + 1) (by simp; omega_using [hk]) t ht
        simp only [List.getElem_cons_succ] at this
        rw [show c + (j + 1) + k = c + j + (k + 1) by omega_using []]; exact this))
      fun s' ⟨d', g', v', sp', rd', wr', fr'⟩ => ⟨?_, g', v', sp', rd', wr', fun x hx => ?_⟩
    · rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega_using []]; exact d'
    · rw [fr' x hx]
      exact Mem.write_apply fun h => hx (by
        have := (Offset.lt_iff x D (d := 16 * (c + j)) (n := 16) (by omega_using [hn, hc])).mp h
        omega_using [this, hc])

/-! ## The loop bodies -/

/-- Load, transform and store the blocks `c … c + N − 1` (`N` the number of
registers). -/
theorem group_ok {K : Nat → Word} {s₀ : State} (hp : Pre s₀) (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ nb s₀) {s : State}
    (hI : BInv K s₀ c c s) (hQ : ∀ s', BInv K s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.block (ldData .x1 rs 0 ++ crypt rs ++ stData .x1 rs 0 ++ tail)) s Q := by
  have hbr := bregs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hn := hp.nb16
  have hin : ∀ k < rs.length, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * (0 + k))) 16 :=
    fun k hk => by
      rw [hI.rd, hI.wr, hI.x1, Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + k) by omega_using [])]
      exact ⟨_, List.mem_append_right _ hp.dat, Offset.contains_base _ (by omega_using [hc, hk]) (by omega_using [hc, hn, hk])⟩
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldData_ok .x1 rs 0 s hbr.1 (by omega_using [hlen]) hin) fun s₁ ⟨e₁, f₁⟩ => ?_
  have hK₁ : KeysOk K s₁ := hI.keys.of_v fun r => f₁.v _ (hbr.2 r)
  refine WP.mono (crypt_ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_
  have hx1 : s₂.gpr .x1 = dp s₀ + BitVec.ofNat 64 (16 * c) := by rw [f₂.gpr, f₁.gpr, hI.x1]
  have hF : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = (outOf s₀ K (c + 0 + k)).getD t 0 := by
    intro k h t ht
    rw [e₂ _ (List.getElem_mem h) (ofBlock (blockAt s₀.mem (dp s₀ + BitVec.ofNat 64 (16 * (c + 0 + k))))) (by
      rw [e₁ k h, rev32b_readW, hI.x1,
        Offset.add_add_eq _ (show 16 * c + 16 * (0 + k) = 16 * (c + 0 + k) by omega_using []),
        dinv_orig hI.data (by omega_using []) (by omega_using [hc, h])])]
    exact vbyte_out _ ht
  refine WP.mono (stData_ok .x1 (m₀ := s₀.mem) (D := dp s₀) (c := c) hp.nb16 rs 0 s₂ hx1 (by omega_using [hlen])
      (by omega_using [hc]) (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.dat)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) hF)
    fun s₃ ⟨d₃, g₃, v₃, sp₃, rd₃, wr₃, _⟩ => hQ s₃ ?_
  have g : ∀ r, s₃.gpr r = s.gpr r := fun r => by rw [g₃, f₂.gpr, f₁.gpr]
  exact ⟨hc, (hK₁.of_v fun r => f₂.v _ (hbr.2 r)).of_v fun r => by rw [v₃], by rw [g]; exact hI.x1,
    by rw [g]; exact hI.x2, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩

theorem tail8_ok {K : Nat → Word} {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : BInv K s₀ (c + 8) c s) :
    WP isa (.block [.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 8, .lsr .x .x13 .x2 3]) s fun s' =>
      BInv K s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((nb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have h4 : BitVec.ofNat 64 (nb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (nb s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show nb s₀ - c - 8 = nb s₀ - (c + 8) by omega_using []]
  refine ⟨⟨hI.le, hI.keys.of_v fun _ => rfl, ?_, ?_, hI.data, hI.rd, hI.wr⟩, ?_⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x1]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    exact h4
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    rw [h4, ushr3 (by omega_using [hn])]

theorem tail1_ok {K : Nat → Word} {s₀ : State} {c : Nat} (hc : c + 1 ≤ nb s₀) {s : State}
    (hI : BInv K s₀ (c + 1) c s) :
    WP isa (.block [.addImm .x .x1 .x1 16, .subImm .x .x2 .x2 1]) s (BInv K s₀ (c + 1) (c + 1)) := by
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨hI.le, hI.keys.of_v fun _ => rfl, ?_, ?_, hI.data, hI.rd, hI.wr⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x1]
    exact Offset.add_add_eq _ (by omega_using [])
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x2]
    rw [Offset.ofNat_sub_ofNat (by omega_using [hc]), show nb s₀ - c - 1 = nb s₀ - (c + 1) by omega_using []]

theorem blk8_ok {K : Nat → Word} {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ nb s₀) {s : State}
    (hI : BInv K s₀ c c s) :
    WP isa blk8 s fun s' =>
      BInv K s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((nb s₀ - (c + 8)) / 8) :=
  group_ok hp regs8 (.inl rfl) _ hc hI fun _ hI' => tail8_ok hp hc hI'

theorem blk1_ok {K : Nat → Word} {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 1 ≤ nb s₀) {s : State}
    (hI : BInv K s₀ c c s) : WP isa blk1 s (BInv K s₀ (c + 1) (c + 1)) :=
  group_ok hp [.v0] (.inr rfl) _ hc hI fun _ hI' => tail1_ok hc hI'

/-- The loops, from the state after the setup. -/
theorem loops_ok {K : Nat → Word} {s₀ : State} (hp : Pre s₀) {s₁ : State} (hI₁ : BInv K s₀ 0 0 s₁)
    (h13 : s₁.gpr .x13 = BitVec.ofNat 64 (nb s₀ / 8)) :
    WP isa (.seq (.ite (.zero .x .x13) (.block []) (.loop blk8 (.nonzero .x .x13)))
      (.ite (.zero .x .x2) (.block []) (.loop blk1 (.nonzero .x .x2)))) s₁
      (BInv K s₀ (nb s₀) (nb s₀)) := by
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nb s₀ - c < 8 ∧ BInv K s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nb s₀ / 8 = 0)) (eval_zero h13 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega_using [h], hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c + 8 ≤ nb s₀ ∧ BInv K s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa blk8 s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, nb s₀ - c < 8 ∧ BInv K s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (blk8_ok hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [eval_nonzero h13' (by omega_using [hn])]
        by_cases hlt : nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega_using [hlt], c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega_using [hlt], nb s₀ - (c + 8), by omega_using [hc], c + 8, rfl, by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I8 hstep (nb s₀) s₁ ⟨0, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.ite (decide (nb s₀ - c = 0)) (eval_zero hI₂.x2 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · have : c = nb s₀ := by have := hI₂.le; simp at h; omega_using [this, h]
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nb s₀ - c ∧ c < nb s₀ ∧ BInv K s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa blk1 s (fun s' =>
        (AArch64.eval (.nonzero .x .x2) s' = some false ∧ BInv K s₀ (nb s₀) (nb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (blk1_ok hp hc hI) fun s' hI' => ?_
      rw [eval_nonzero hI'.x2 (by omega_using [hn])]
      by_cases hlast : nb s₀ - (c + 1) = 0
      · have : c + 1 = nb s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], nb s₀ - (c + 1), by omega_using [hc], c + 1, rfl, by omega_using [hlast], hI'⟩
    have hlt : c < nb s₀ := by have := hI₂.le; simp at h; omega_using [h]
    exact WP.loop (M := isa) I1 hstep (nb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

/-! ## The round keys -/

/-- Registers `kreg 0 … kreg (k − 1)` set in turn, each by `f i` to `val i`. -/
theorem keys_ok (f : Nat → List Instr) (val : Nat → BitVec 128) (s : State)
    (hf : ∀ i < 8, ∀ s' : State, s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      runBlock isa (f i) s' = some (s'.setV (kreg i) (val i))) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap f)) s fun s' =>
      (∀ j < k, s'.v (kreg j) = val j) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega_using []), rfl, rfl, rfl, rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (keys_ok f val s hf k (by omega_using [hk])) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.of_runBlock ⟨_, hf k (by omega_using [hk]) s₁ g₁ m₁ rd₁ wr₁, fun j hj => ?_, g₁, m₁, rd₁, wr₁⟩
    by_cases hjk : j = k
    · subst hjk; exact setV_v_self _ _ _
    · rw [setV_v_of_ne _ _ fun h => hjk (kreg_inj j (by omega_using [hj, hk]) k (by omega_using [hk]) h)]
      exact e₁ j (by omega_using [hj, hjk])

/-- The round keys of the schedule at `x0`, which is readable. -/
theorem dirKeys_ok (dir : Dir) {s₀ : State}
    (hin : ∀ o, o + 16 ≤ 128 → InRegions (s₀.rd ++ s₀.wr) (kp s₀ + BitVec.ofNat 64 o) 16) :
    WP isa (.block (dirKeys dir)) s₀ fun s' =>
      KeysOk (keyOf s₀ dir) s' ∧ s'.gpr = s₀.gpr ∧ s'.mem = s₀.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  cases dir
  · refine WP.mono (keys_ok (fun i => [.ldrq (kreg i) .x0 (16 * i)])
      (fun i => s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (16 * i)) 128) s₀ (fun i hi s' g m rd wr => ?_) 8
      (Nat.le_refl _)) fun s' ⟨e, h⟩ => ⟨fun r hr => ?_, h⟩
    · rw [runBlock_cons, exec_ldrq (by omega_using [hi]) (by rw [g, rd, wr]; exact hin _ (by omega_using [hi])),
        runStep_some, runBlock_nil, g, m]
    · rw [e r hr]; exact encKey_readW _ _ hr
  · refine WP.mono (keys_ok (fun i => .ldrq (kreg i) .x0 (16 * (7 - i)) :: revWords (kreg i))
      (fun i => swap8 (VRevOp.rev64s.eval (s₀.mem.readW (kp s₀ + BitVec.ofNat 64 (16 * (7 - i))) 128))) s₀
      (fun i hi s' g m rd wr => ?_) 8 (Nat.le_refl _)) fun s' ⟨e, h⟩ => ⟨fun r hr => ?_, h⟩
    · rw [runBlock_cons, exec_ldrq (by omega_using [hi]) (by rw [g, rd, wr]; exact hin _ (by omega_using [hi])),
        runStep_some, revWords, rev_ext_run, setV_v_self, setV_setV, g, m]
    · rw [e r hr]; exact decKey_readW _ _ hr

theorem setup_ok (dir : Dir) {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (setup dir)) s₀ fun s =>
      BInv (keyOf s₀ dir) s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (nb s₀ / 8) := by
  unfold setup
  rw [WP.block_append_iff]
  refine WP.mono (dirKeys_ok dir fun _ h => hp.key_in h) fun s₁ ⟨hK, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have hx2 : s₀.gpr .x2 = BitVec.ofNat 64 (nb s₀) := by simp [nb]
  refine ⟨⟨Nat.zero_le _, hK.of_v fun _ => rfl, ?_, ?_, fun i hi => ?_, rd₁, wr₁⟩, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, g₁]; simp
  · simp only [State.write, reduceCtorEq, ite_false, g₁]; simp [nb]
  · show s₁.mem _ = _
    rw [m₁, ite_eq_right (by omega_using [])]
  · simp only [State.write, State.read, ite_true, BitVec.setWidth_eq, g₁, hx2]
    exact ushr3 (s₀.gpr .x2).isLt

/-! ## The whole functions -/

theorem post_of (dir : Dir) {s₀ s : State} (hI : BInv (keyOf s₀ dir) s₀ (nb s₀) (nb s₀) s) :
    (ecbAArch64 dir).post s₀ s := by
  show Spec.Sm4.blocksAt s.mem (dp s₀) (nb s₀) = _
  rw [Proof.Sm4.blocksAt_of_dinv hI.data, Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact (blockFn_eq _ dir _).symm

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : Pre s₀) : WP isa (ecb dir) s₀ ((ecbAArch64 dir).post s₀) :=
  WP.seq (WP.mono (setup_ok dir hp) fun _ ⟨hI₁, h13⟩ => WP.mono (loops_ok hp hI₁ h13) fun _ hI => post_of dir hI)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbAArch64 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbAArch64 dir).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved) (ecb_wp dir (pre_of hs))
    (by cases dir <;> lit_decide) (by cases dir <;> lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by cases dir <;> lit_decide)⟩, h₂⟩

theorem ecbTaint_agree (dir : Dir) (s₁ s₂ : State) (_ : (ecbAArch64 dir).pre s₁)
    (_ : (ecbAArch64 dir).pre s₂) (hp : (ecbAArch64 dir).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2]) s₁ s₂ := by
  obtain ⟨hsp, h1, h2, h3⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbAArch64 dir).pre (ecbAArch64 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) (ecbTaint_agree .decrypt)
      (by taint_decide)

/-- A state satisfying the precondition: the schedule at `0x1000`, one block
at `0x3000`. -/
def ecbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

/-- `vg_sm4_ecb_encrypt_sm4` and `vg_sm4_ecb_decrypt_sm4`. -/
theorem ecb_verified (dir : Dir) :
    Verified AArch64.target (ecb dir) (Spec.Sm4.ecbContract AArch64.abi (dirOf dir)) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, ecbAArch64, dirOf,
      AArch64.abi, AArch64.argRegs] [ecbSat] using ecbSat)

end VG.Proof.Sm4.AArch64.Sm4e
