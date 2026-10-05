import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Aes.AArch64.Aese
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Aes.AArch64.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Gcm.Be64

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds`. -/
section

/-!
# The Armv8 AES instructions are FIPS 197's rounds

A vector register holds an AES state as its 16 bytes in memory order (`st`):
byte `r + 4c` is `s[r, c]`, as FIPS 197 §3.4 lays the state out and as the Arm
ARM's AES instructions read it. On such registers `eor` is `AddRoundKey`
(`eor_st`), `aese` is `AddRoundKey`, `SubBytes` and `ShiftRows` (`aese_st`),
and `aesmc` is `MixColumns` (`aesmc_st`); the S-box of the ISA model, computed
by repeated squaring, is the one of `Spec/Aes.lean` (`sbox_eq`).

`aes_ok`: `Impl.Aes.AArch64.Aese.aes regs` encrypts each register of `regs`
with the round keys in `v16`–`v30`, whatever the list of registers.
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG.AArch64
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

/-! ## GF(2⁸) -/

theorem mul_eq : aesMul = Spec.Aes.mul := rfl

/-- Both square and multiply `b²`, `b⁴`, …, `b¹²⁸` in the same order: unfolded
to the same term (no evaluation left for the kernel). -/
theorem inv_eq (b : BitVec 8) : aesInv b = Spec.Aes.inv b := by
  simp (config := {decide := true}) only [aesInv, Spec.Aes.inv, Spec.Aes.pow, List.range_succ,
    List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, VG.Proof.Aes.AArch64.Aese.mul_eq,
    ite_true, ite_false]

theorem sbox_eq : aesSbox = VG.Spec.Aes.sbox := by
  funext b
  simp only [aesSbox, VG.Spec.Aes.sbox, VG.Proof.Aes.AArch64.Aese.inv_eq, ofBits8]

theorem mul_one' : ∀ b : BitVec 8, Spec.Aes.mul 1 b = b := by decide +kernel

/-! ## Bytes of vectors -/

/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat} (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofVBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofVBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofVBytes, VG.Proof.Aes.AArch64.Aese.getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem vbyte_ofVBytes (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) : vbyte (ofVBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]
  exact VG.Proof.Aes.AArch64.Aese.getLsbD_ofVBytes f hi hr

theorem ext_vbyte {a b : BitVec 128} (h : ∀ i < 16, vbyte a i = vbyte b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (BitVec.getLsbD · (j % 8)) (h (j / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt j (by omega : 8 > 0)),
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem vbyte_readW (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    vbyte (m.readW p 128) i = m (p + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m p (n := 16) hi]
  simp only [vbyte, Mem.readW]
  rfl

theorem vbyte_xor (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hj, decide_true, Bool.true_and]

/-! ## States in registers -/

/-- The AES state held by a register. -/
def st (v : BitVec 128) : Spec.Aes.State := Vector.ofFn fun i => vbyte v i

theorem getD_ofFn {f : Fin 16 → Byte} {i : Nat} (h : i < 16) :
    (Vector.ofFn f).getD i 0 = f ⟨i, h⟩ := by
  simp [Vector.getD, h]

theorem getD_st (v : BitVec 128) {i : Nat} (h : i < 16) : (VG.Proof.Aes.AArch64.Aese.st v).getD i 0 = vbyte v i := by
  rw [VG.Proof.Aes.AArch64.Aese.st, VG.Proof.Aes.AArch64.Aese.getD_ofFn h]

theorem st_ext {s t : Spec.Aes.State} (h : ∀ i < 16, s.getD i 0 = t.getD i 0) : s = t := by
  apply Vector.ext; intro i hi
  have := h i hi
  simpa [Vector.getD, hi] using this

/-! ## FIPS 197's transformations, byte by byte -/

theorem getD_addRoundKey (s : Spec.Aes.State) (rk : List Byte) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.addRoundKey s rk).getD i 0 = s.getD i 0 ^^^ rk.getD i 0 := by
  rw [VG.Spec.Aes.addRoundKey, VG.Proof.Aes.AArch64.Aese.getD_ofFn h]

theorem getD_subBytes (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (subBytes s).getD i 0 = VG.Spec.Aes.sbox (s.getD i 0) := by
  simp [subBytes, Vector.getD, h]

theorem getD_shiftRows (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.shiftRows s).getD i 0 = s.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [VG.Spec.Aes.shiftRows, VG.Proof.Aes.AArch64.Aese.getD_ofFn h]

theorem getD_mixColumns (s : Spec.Aes.State) {i : Nat} (h : i < 16) :
    (VG.Spec.Aes.mixColumns s).getD i 0 =
      Spec.Aes.mul 0x02 (s.getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) ^^^
      Spec.Aes.mul 0x03 (s.getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) ^^^
      s.getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0 ^^^ s.getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0 := by
  rw [VG.Spec.Aes.mixColumns, VG.Proof.Aes.AArch64.Aese.getD_ofFn h]

theorem vbyte_mapBytes (f : BitVec 8 → BitVec 8) (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMapBytes f x) i = f (vbyte x i) := by
  rw [aesMapBytes, VG.Proof.Aes.AArch64.Aese.vbyte_ofVBytes _ h]

theorem vbyte_shiftRows (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesShiftRows x) i = vbyte x (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  rw [aesShiftRows, VG.Proof.Aes.AArch64.Aese.vbyte_ofVBytes _ h]

theorem vbyte_mixColumns (x : BitVec 128) {i : Nat} (h : i < 16) :
    vbyte (aesMixColumns x) i =
      aesMul 0x02 (vbyte x ((i % 4 + 0) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x03 (vbyte x ((i % 4 + 1) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 2) % 4 + 4 * (i / 4))) ^^^
      aesMul 0x01 (vbyte x ((i % 4 + 3) % 4 + 4 * (i / 4))) := by
  rw [aesMixColumns, aesMixWith, VG.Proof.Aes.AArch64.Aese.vbyte_ofVBytes _ h]

/-! ## The instructions -/

/-- A round key in a register: its bytes are those of `rk`. -/
def KeyIs (k : BitVec 128) (rk : List Byte) : Prop := ∀ i < 16, vbyte k i = rk.getD i 0

/-- `eor` with a round key is `AddRoundKey`. -/
theorem eor_st {v k : BitVec 128} {rk : List Byte} (hk : VG.Proof.Aes.AArch64.Aese.KeyIs k rk) :
    VG.Proof.Aes.AArch64.Aese.st (v ^^^ k) = VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st v) rk := by
  apply VG.Proof.Aes.AArch64.Aese.st_ext; intro i hi
  rw [VG.Proof.Aes.AArch64.Aese.getD_st _ hi, VG.Proof.Aes.AArch64.Aese.getD_addRoundKey _ _ hi, VG.Proof.Aes.AArch64.Aese.getD_st _ hi, ← hk i hi]
  exact VG.Proof.Aes.AArch64.Aese.vbyte_xor v k i

/-- `aese` with a round key is `AddRoundKey`, then `SubBytes` and `ShiftRows`. -/
theorem aese_st {v k : BitVec 128} {rk : List Byte} (hk : VG.Proof.Aes.AArch64.Aese.KeyIs k rk) :
    VG.Proof.Aes.AArch64.Aese.st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))) = VG.Spec.Aes.shiftRows (subBytes (VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st v) rk)) := by
  apply VG.Proof.Aes.AArch64.Aese.st_ext; intro i hi
  have hs : ∀ j, j % 4 + 4 * ((j / 4 + j % 4) % 4) < 16 := fun j => by omega
  rw [VG.Proof.Aes.AArch64.Aese.getD_st _ hi, VG.Proof.Aes.AArch64.Aese.getD_shiftRows _ hi, VG.Proof.Aes.AArch64.Aese.getD_subBytes _ (hs _), VG.Proof.Aes.AArch64.Aese.getD_addRoundKey _ _ (hs _),
    VG.Proof.Aes.AArch64.Aese.getD_st _ (hs _), ← hk _ (hs _), VG.Proof.Aes.AArch64.Aese.vbyte_mapBytes _ _ hi, VG.Proof.Aes.AArch64.Aese.vbyte_shiftRows _ hi, VG.Proof.Aes.AArch64.Aese.vbyte_xor, VG.Proof.Aes.AArch64.Aese.sbox_eq]

/-- `aesmc` is `MixColumns`. -/
theorem aesmc_st (v : BitVec 128) : VG.Proof.Aes.AArch64.Aese.st (aesMixColumns v) = VG.Spec.Aes.mixColumns (VG.Proof.Aes.AArch64.Aese.st v) := by
  apply VG.Proof.Aes.AArch64.Aese.st_ext; intro i hi
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  rw [VG.Proof.Aes.AArch64.Aese.getD_st _ hi, VG.Proof.Aes.AArch64.Aese.getD_mixColumns _ hi, VG.Proof.Aes.AArch64.Aese.vbyte_mixColumns _ hi]
  simp only [VG.Proof.Aes.AArch64.Aese.getD_st _ (hr _), VG.Proof.Aes.AArch64.Aese.mul_eq, VG.Proof.Aes.AArch64.Aese.mul_one']

/-! ## The cipher -/

/-- The state after `AddRoundKey` and `k` full rounds. -/
def rnds (w : List Byte) (x : Spec.Aes.State) (k : Nat) : Spec.Aes.State :=
  (List.range k).foldl
    (fun s j => VG.Spec.Aes.addRoundKey (VG.Spec.Aes.mixColumns (VG.Spec.Aes.shiftRows (subBytes s))) (roundKey w (j + 1)))
    (VG.Spec.Aes.addRoundKey x (roundKey w 0))

theorem rnds_zero (w : List Byte) (x : Spec.Aes.State) :
    VG.Proof.Aes.AArch64.Aese.rnds w x 0 = VG.Spec.Aes.addRoundKey x (roundKey w 0) := rfl

theorem rnds_succ (w : List Byte) (x : Spec.Aes.State) (k : Nat) :
    VG.Proof.Aes.AArch64.Aese.rnds w x (k + 1) =
      VG.Spec.Aes.addRoundKey (VG.Spec.Aes.mixColumns (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.AArch64.Aese.rnds w x k)))) (roundKey w (k + 1)) := by
  simp only [VG.Proof.Aes.AArch64.Aese.rnds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem cipher_eq (nr : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher nr w x = VG.Spec.Aes.addRoundKey (VG.Spec.Aes.shiftRows (subBytes (VG.Proof.Aes.AArch64.Aese.rnds w x (nr - 1)))) (roundKey w nr) := rfl

/-- A full round: `aese` with round key `j`, then `aesmc`. The register
holds the state before the `AddRoundKey` of round key `j`. -/
theorem round_st {v k : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {j : Nat}
    (hk : VG.Proof.Aes.AArch64.Aese.KeyIs k (roundKey w j)) (h : VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st v) (roundKey w j) = VG.Proof.Aes.AArch64.Aese.rnds w x j) :
    VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))) (roundKey w (j + 1)) =
      VG.Proof.Aes.AArch64.Aese.rnds w x (j + 1) := by
  rw [VG.Proof.Aes.AArch64.Aese.rnds_succ, VG.Proof.Aes.AArch64.Aese.aesmc_st, VG.Proof.Aes.AArch64.Aese.aese_st hk, h]

/-- The last round: `aese` with round key `Nr − 1`, then `eor` with round key `Nr`. -/
theorem last_st {v k k' : BitVec 128} {w : List Byte} {x : Spec.Aes.State} {nr : Nat}
    (hk : VG.Proof.Aes.AArch64.Aese.KeyIs k (roundKey w (nr - 1))) (hk' : VG.Proof.Aes.AArch64.Aese.KeyIs k' (roundKey w nr))
    (h : VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st v) (roundKey w (nr - 1)) = VG.Proof.Aes.AArch64.Aese.rnds w x (nr - 1)) :
    VG.Proof.Aes.AArch64.Aese.st (aesMapBytes aesSbox (aesShiftRows (v ^^^ k)) ^^^ k') = cipher nr w x := by
  rw [VG.Proof.Aes.AArch64.Aese.eor_st hk', VG.Proof.Aes.AArch64.Aese.aese_st hk, h, VG.Proof.Aes.AArch64.Aese.cipher_eq]

/-- Round key `j`, loaded from the schedule. -/
theorem keyIs_readW (m : Mem) (p : Addr) {L j : Nat} (hj : 16 * j + 16 ≤ L) :
    VG.Proof.Aes.AArch64.Aese.KeyIs (m.readW (p + BitVec.ofNat 64 (16 * j)) 128) (roundKey (VG.Spec.Aes.bytesAt m p L) j) := by
  intro i hi
  rw [VG.Proof.Aes.AArch64.Aese.vbyte_readW _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  simp [roundKey, VG.Spec.Aes.bytesAt, List.getD, hi, show 16 * j + i < L by omega]

end VG.Proof.Aes.AArch64.Aese

/-!
## Encrypting the block registers
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese (kreg rnd last aes)
open VG.Spec.Aes (roundKey cipher addRoundKey)

/-- `s'` is `s` but for the vector registers `rs`. -/
structure VFrame (rs : List VReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  v : ∀ r, r ∉ rs → s'.v r = s.v r

theorem VFrame.refl (rs : List VReg) (s : State) : VG.Proof.Aes.AArch64.Aese.VFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem VFrame.trans {rs : List VReg} {s s' s'' : State} (h : VG.Proof.Aes.AArch64.Aese.VFrame rs s s') (h' : VG.Proof.Aes.AArch64.Aese.VFrame rs s' s'') :
    VG.Proof.Aes.AArch64.Aese.VFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.sp.trans h.sp, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.v r hr).trans (h.v r hr)⟩

theorem VFrame.mono {rs rs' : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.VFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Aes.AArch64.Aese.VFrame rs' s s' :=
  ⟨h.gpr, h.sp, h.mem, h.rd, h.wr, fun r hr => h.v r fun h' => hr (hs r h')⟩

/-- Two instructions that set `b` to `g (b) (k)`, for each register `b` of `regs`. -/
theorem each_ok (f : VReg → List Instr) (g : BitVec 128 → BitVec 128 → BitVec 128) (k : VReg)
    (hf : ∀ b s, b ≠ k → runBlock isa (f b) s = some (s.setV b (g (s.v b) (s.v k)))) :
    ∀ (regs : List VReg) (s : State), regs.Nodup → k ∉ regs →
    WP isa (.block (regs.flatMap f)) s fun s' =>
      (∀ b ∈ regs, s'.v b = g (s.v b) (s.v k)) ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
  | b :: bs, s, hnd, hk => by
    have hbk : b ≠ k := fun h => hk (h ▸ List.mem_cons_self ..)
    have hk' : k ∉ bs := fun h => hk (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.of_runBlock ⟨_, hf b s hbk, ?_⟩
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.each_ok f g k hf bs _ (List.nodup_cons.mp hnd).2 hk') fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hfr.v _ hbs]; simp [State.setV]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc]; simp [State.setV, hcb, Ne.symm hbk]
    · refine ⟨hfr.gpr, hfr.sp, hfr.mem, hfr.rd, hfr.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hfr.v r hr.2]; simp [State.setV, hr.1]

theorem setV_v_self (s : State) (r : VReg) (x : BitVec 128) : (s.setV r x).v r = x := by
  simp [State.setV]

theorem setV_v_of_ne (s : State) {r r' : VReg} (x : BitVec 128) (h : r' ≠ r) :
    (s.setV r x).v r' = s.v r' := by
  simp [State.setV, h]

theorem setV_setV (s : State) (r : VReg) (x y : BitVec 128) : (s.setV r x).setV r y = s.setV r y := by
  simp only [State.setV]
  congr 1
  funext r'
  split <;> rfl

theorem rnd_run (k b : VReg) (s : State) :
    runBlock isa [.vop (.aese b k), .vop (.aesmc b b)] s =
      some (s.setV b (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v k))))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [VG.Proof.Aes.AArch64.Aese.setV_v_self, VG.Proof.Aes.AArch64.Aese.setV_setV]

theorem last_run (b : VReg) (s : State) (hb30 : b ≠ .v30) :
    runBlock isa [.vop (.aese b .v29), .vop (.logic .eor b b .v30)] s =
      some (s.setV b (aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [VG.Proof.Aes.AArch64.Aese.setV_v_self, VG.Proof.Aes.AArch64.Aese.setV_v_of_ne _ _ (Ne.symm hb30), VG.Proof.Aes.AArch64.Aese.setV_setV]

/-- The registers the blocks may be in. -/
def BlockRegs (regs : List VReg) : Prop :=
  regs.Nodup ∧ ∀ r ∈ regs, r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19 ∧ r ≠ .v20 ∧ r ≠ .v21 ∧
    r ≠ .v22 ∧ r ≠ .v23 ∧ r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v26 ∧ r ≠ .v27 ∧ r ≠ .v28 ∧ r ≠ .v29 ∧
    r ≠ .v30

theorem BlockRegs.kreg {regs : List VReg} (h : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) (j : Nat) : VG.Impl.Aes.AArch64.Aese.kreg j ∉ regs := by
  intro hj
  have := (h.2 _ hj)
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | _ + 12 => simp [Impl.Aes.AArch64.Aese.kreg] at this

/-- Each register `b` of `regs` holds the state before the `AddRoundKey` of
round key `j`, from the state `x b`. -/
def RInv (regs : List VReg) (w : List Byte) (x : VReg → Spec.Aes.State) (j : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, VG.Spec.Aes.addRoundKey (VG.Proof.Aes.AArch64.Aese.st (s.v b)) (roundKey w j) = VG.Proof.Aes.AArch64.Aese.rnds w (x b) j

/-- What the rounds need of the state: the round keys in `v16`–`v30`, and
`x6`, `x7` for the number of rounds. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  full : ∀ j, j + 2 ≤ nr → VG.Proof.Aes.AArch64.Aese.KeyIs (s.v (VG.Impl.Aes.AArch64.Aese.kreg j)) (roundKey w j)
  k29 : VG.Proof.Aes.AArch64.Aese.KeyIs (s.v .v29) (roundKey w (nr - 1))
  k30 : VG.Proof.Aes.AArch64.Aese.KeyIs (s.v .v30) (roundKey w nr)
  x6 : s.gpr .x6 = BitVec.ofNat 64 nr - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 nr - 12

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.Keys nr w s)
    (hf : VG.Proof.Aes.AArch64.Aese.VFrame rs s s') (hrs : VG.Proof.Aes.AArch64.Aese.BlockRegs rs) : VG.Proof.Aes.AArch64.Aese.Keys nr w s' :=
  ⟨h.rounds, fun j hj => by rw [hf.v _ (hrs.kreg j)]; exact h.full j hj,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl]; exact h.k29,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl]; exact h.k30,
    by rw [hf.gpr]; exact h.x6, by rw [hf.gpr]; exact h.x7⟩

theorem round_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {j : Nat} (hj : j + 2 ≤ nr) {s : State} (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s)
    (hI : VG.Proof.Aes.AArch64.Aese.RInv regs w x j s) :
    WP isa (.block (VG.Impl.Aes.AArch64.Aese.rnd regs (VG.Impl.Aes.AArch64.Aese.kreg j))) s fun s' => VG.Proof.Aes.AArch64.Aese.RInv regs w x (j + 1) s' ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s' := by
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.each_ok _ (fun v k => aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))
    (VG.Impl.Aes.AArch64.Aese.kreg j) (fun b s _ => VG.Proof.Aes.AArch64.Aese.rnd_run _ b s) regs s hr.1 (hr.kreg j))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb]
  exact VG.Proof.Aes.AArch64.Aese.round_st (hK.full j hj) (hI b hb)

theorem rounds_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.RInv regs w x 0 s) :
    ∀ k, k + 1 ≤ nr →
    WP isa (.block ((List.range k).flatMap fun i => VG.Impl.Aes.AArch64.Aese.rnd regs (VG.Impl.Aes.AArch64.Aese.kreg i))) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.RInv regs w x k s' ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s'
  | 0, _ => by
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.rounds_ok hr hK hI k (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.round_ok hr (j := k) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem last_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.RInv regs w x (nr - 1) s) :
    WP isa (.block (last regs)) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.AArch64.Aese.st (s'.v b) = cipher nr w (x b)) ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s' := by
  have h29 : .v29 ∉ regs := fun h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
  have h30 : ∀ b ∈ regs, b ≠ .v30 := fun b h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- `last` is `each_ok` for `v29`, with `v30` read by each step (and not written).
  have e : ∀ (rs : List VReg) (s : State), rs.Nodup → .v29 ∉ rs → (∀ b ∈ rs, b ≠ .v30) →
      WP isa (.block (last rs)) s fun s' =>
        (∀ b ∈ rs, s'.v b = aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30) ∧
        VG.Proof.Aes.AArch64.Aese.VFrame rs s s' := by
    intro rs
    induction rs with
    | nil => intro s _ _ _; exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
    | cons b bs ih =>
      intro s hnd hk h30'
      have hb29 : b ≠ .v29 := fun h => hk (h ▸ List.mem_cons_self ..)
      have hb30 : b ≠ .v30 := h30' b List.mem_cons_self
      have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
      rw [Impl.Aes.AArch64.Aese.last, List.flatMap_cons, WP.block_append_iff]
      refine WP.of_runBlock ⟨_, VG.Proof.Aes.AArch64.Aese.last_run b s hb30, ?_⟩
      refine WP.mono (ih _ (List.nodup_cons.mp hnd).2 (fun h => hk (List.mem_cons_of_mem _ h))
        (fun c hc => h30' c (List.mem_cons_of_mem _ hc))) fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [hfr.v _ hbs]; simp [State.setV]
        · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
          rw [hv c hc]; simp [State.setV, hcb, Ne.symm hb29, Ne.symm hb30]
      · refine ⟨hfr.gpr, hfr.sp, hfr.mem, hfr.rd, hfr.wr, fun r hr => ?_⟩
        simp only [List.mem_cons, not_or] at hr
        rw [hfr.v r hr.2]; simp [State.setV, hr.1]
  refine WP.mono (e regs s hr.1 h29 h30) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb]
  exact VG.Proof.Aes.AArch64.Aese.last_st hK.k29 hK.k30 (hI b hb)

/-- Two full rounds, with round keys `j` and `j + 1`. -/
theorem two_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = VG.Impl.Aes.AArch64.Aese.kreg j)
    (e₂ : k₂ = VG.Impl.Aes.AArch64.Aese.kreg (j + 1)) (hj : j + 3 ≤ nr) (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.RInv regs w x j s) :
    WP isa (.block (VG.Impl.Aes.AArch64.Aese.rnd regs k₁ ++ VG.Impl.Aes.AArch64.Aese.rnd regs k₂)) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.RInv regs w x (j + 2) s' ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s' := by
  subst e₁ e₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.round_ok hr (by omega) hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (VG.Proof.Aes.AArch64.Aese.round_ok hr (by omega) (hK.of_frame hf₁ hr) hI₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ⟨hI₂, hf₁.trans hf₂⟩

/-- The full rounds with round keys `9 … Nr − 2`. -/
theorem mid_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s) (hI : VG.Proof.Aes.AArch64.Aese.RInv regs w x 9 s) :
    WP isa (.ite (.zero .x .x6) (.block [])
        (.seq (.block (VG.Impl.Aes.AArch64.Aese.rnd regs .v25 ++ VG.Impl.Aes.AArch64.Aese.rnd regs .v26))
          (.ite (.zero .x .x7) (.block []) (.block (VG.Impl.Aes.AArch64.Aese.rnd regs .v27 ++ VG.Impl.Aes.AArch64.Aese.rnd regs .v28))))) s
      fun s' => VG.Proof.Aes.AArch64.Aese.RInv regs w x (nr - 1) s' ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s' := by
  have hx6 := hK.x6
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 12 - 12 := by rw [hf₃.gpr]; exact hK.x7
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun _ => WP.block_nil ⟨hI₃, hf₃⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 14 - 12 := by rw [hf₃.gpr]; exact hK.x7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.mono (VG.Proof.Aes.AArch64.Aese.two_ok hr 11 rfl rfl (by omega) (hK.of_frame hf₃ hr) hI₃)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans hf'⟩

theorem aes_ok {regs : List VReg} (hr : VG.Proof.Aes.AArch64.Aese.BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : VG.Proof.Aes.AArch64.Aese.Keys nr w s) :
    WP isa (VG.Impl.Aes.AArch64.Aese.aes regs) s fun s' =>
      (∀ b ∈ regs, VG.Proof.Aes.AArch64.Aese.st (s'.v b) = cipher nr w (VG.Proof.Aes.AArch64.Aese.st (s.v b))) ∧ VG.Proof.Aes.AArch64.Aese.VFrame regs s s' := by
  have hI₀ : VG.Proof.Aes.AArch64.Aese.RInv regs w (fun b => VG.Proof.Aes.AArch64.Aese.st (s.v b)) 0 s := fun b _ => (VG.Proof.Aes.AArch64.Aese.rnds_zero w _).symm
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.rounds_ok hr hK hI₀ 9 (by have := hK.rounds; omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.mid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  exact WP.mono (VG.Proof.Aes.AArch64.Aese.last_ok hr (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans hf')⟩

end VG.Proof.Aes.AArch64.Aese

end

/- Proofs formerly in `VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32`. -/
section

/-!
# AES counter mode with the Armv8 Cryptographic Extension

`ctr32_verified` proves `Impl.Aes.AArch64.Aese.ctr32` against
`Proof.Aes.ctr32AArch64` (the contract `vg_aes_ctr32` is proven against), and
so against the shared contract.

`ctrs_ok`: `ctrs regs i` puts the counter blocks `inc₃₂^(c+i)(CB)`, … into
the registers `regs`; `xorData_ok`: `xorData regs j` XORs them, encrypted,
into the data blocks; both for any list of registers, by induction. The
loops keep, after `c` blocks, the counter `c₀ + c` in `w10` and the first `c`
data blocks encrypted (`DataInv`).
-/

namespace VG.Proof.Aes.AArch64.Aese

open VG VG.AArch64
open VG.Impl.Aes.AArch64.Aese
open VG.Spec.Aes (cipher)

/-! ## Instructions -/

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 128)) := by
  simp only [exec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ho, and_self, ite_true,
    Option.bind_some, State.load, h, Option.map_some, Mem.readW]
  rfl

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show off % 16 = 0 ∧ off < 4096 * 16 from ho, and_self, ite_true,
    Option.bind_some, State.store, h]

theorem inRegions_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## Bytes of vectors -/

theorem setLane_bit_lo (x : BitVec 128) (v : BitVec 32) {j t : Nat} (h : j < 12) (ht : t < 8) :
    (setLane x 32 3 v).getLsbD (8 * j + t) = x.getLsbD (8 * j + t) := by
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) only [decide_eq_true, Bool.not_true, Bool.not_false, Bool.and_false,
    Bool.and_true, Bool.false_and, Bool.true_and, Bool.or_false]

theorem setLane_bit_hi (x : BitVec 128) (v : BitVec 32) {j t : Nat} (h : ¬ j < 12) (hj : j < 16)
    (ht : t < 8) : (setLane x 32 3 v).getLsbD (8 * j + t) = v.getLsbD (8 * (j - 12) + t) := by
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.not_true, Bool.not_false,
    Bool.and_false, Bool.and_true, Bool.true_and, Bool.false_or]
  exact congrArg _ (by omega)

theorem vbyte_setLane (x : BitVec 128) (v : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 3 v) j = if j < 12 then vbyte x j else v.extractLsb' (8 * (j - 12)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  by_cases h : j < 12
  · rw [ite_eq_left h]
    simp only [vbyte, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
    exact VG.Proof.Aes.AArch64.Aese.setLane_bit_lo x v h ht
  · rw [ite_eq_right h]
    simp only [vbyte, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
    exact VG.Proof.Aes.AArch64.Aese.setLane_bit_hi x v h hj ht

theorem exec_addImm_w {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d (s.read .w n + BitVec.ofNat _ imm)) := by
  simp [exec, h]

theorem rev32_byte (v : BitVec 32) {q : Nat} (hq : q < 4) :
    (rev32 v).extractLsb' (8 * q) 8 = v.extractLsb' (8 * (3 - q)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit v hq ht]

/-- A counter block in a register, as an AES state. -/
theorem ctrVec_st (m : Mem) (p : Addr) (k : Nat) :
    VG.Proof.Aes.AArch64.Aese.st (setLane (m.readW (p + BitVec.ofNat 64 0) 128) 32 3
      (rev32 ((Spec.Gcm.blockAt m p).extractLsb' 0 32 + BitVec.ofNat 32 k))) =
      ctrState (Spec.Gcm.blockAt m p) k := by
  apply VG.Proof.Aes.AArch64.Aese.st_ext; intro j hj
  rw [VG.Proof.Aes.AArch64.Aese.getD_st _ hj, ctrState, VG.Proof.Aes.AArch64.Aese.getD_ofFn hj, ctrBlock_byte _ _ hj, VG.Proof.Aes.AArch64.Aese.vbyte_setLane _ _ hj]
  by_cases h : j < 12
  · rw [ite_eq_left h, ite_eq_left h, VG.Proof.Aes.AArch64.Aese.vbyte_readW _ _ hj, toBytes_blockAt _ _ hj, BitVec.add_zero]
  · rw [ite_eq_right h, ite_eq_right h, VG.Proof.Aes.AArch64.Aese.rev32_byte _ (by omega),
      show 3 - (j - 12) = 15 - j by omega]

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp

/-! ## The counter blocks -/

/-- `s'` is `s` but for the registers `gs` and the vector registers `vs`. -/
structure Fr (gs : List Reg) (vs : List VReg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ gs → s'.gpr r = s.gpr r
  v : ∀ r, r ∉ vs → s'.v r = s.v r
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Fr.refl (gs : List Reg) (vs : List VReg) (s : State) : VG.Proof.Aes.AArch64.Aese.Fr gs vs s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.trans {gs : List Reg} {vs : List VReg} {s s' s'' : State} (h : VG.Proof.Aes.AArch64.Aese.Fr gs vs s s')
    (h' : VG.Proof.Aes.AArch64.Aese.Fr gs vs s' s'') : VG.Proof.Aes.AArch64.Aese.Fr gs vs s s'' :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), fun r hr => (h'.v r hr).trans (h.v r hr),
    h'.sp.trans h.sp, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Fr.mono {gs gs' : List Reg} {vs vs' : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.Fr gs vs s s')
    (hg : ∀ r ∈ gs, r ∈ gs') (hv : ∀ r ∈ vs, r ∈ vs') : VG.Proof.Aes.AArch64.Aese.Fr gs' vs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hg r h'), fun r hr => h.v r fun h' => hr (hv r h'),
    h.sp, h.mem, h.rd, h.wr⟩

theorem VFrame.fr {vs : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.VFrame vs s s') : VG.Proof.Aes.AArch64.Aese.Fr [] vs s s' :=
  ⟨fun r _ => by rw [h.gpr], h.v, h.sp, h.mem, h.rd, h.wr⟩

/-- The counter block `C + i` into `b`, `C` the counter in `w10`. -/
theorem ctr1_ok (b : VReg) (i : Nat) (s : State) (hi : i < 4096)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16) :
    WP isa (.block (ctr1 b i)) s fun s' =>
      s'.v b = setLane (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128) 32 3
        (rev32 (s.read .w .x10 + BitVec.ofNat 32 i)) ∧ VG.Proof.Aes.AArch64.Aese.Fr [.x12] [b] s s' := by
  rw [ctr1, WP.block_cons_iff]
  refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_addImm_w hi, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide) hin, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, WP.block_nil ?_⟩
  refine ⟨?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp [State.setV, State.write, State.read, VG.Proof.Aes.AArch64.Aese.sw32]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]
  · simp only [List.mem_singleton] at hr
    simp [State.setV, State.write, hr]

/-- The counter block `C + i`, as `ctr1` builds it. -/
abbrev ctrVec (m : Mem) (p : Addr) (C : BitVec 32) (i : Nat) : BitVec 128 :=
  setLane (m.readW (p + BitVec.ofNat 64 0) 128) 32 3 (rev32 (C + BitVec.ofNat 32 i))

theorem ctrs_ok : ∀ (regs : List VReg) (i : Nat) (s : State), regs.Nodup → i + regs.length ≤ 4096 →
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16 →
    WP isa (.block (ctrs regs i)) s fun s' =>
      (∀ k (h : k < regs.length), s'.v regs[k] = VG.Proof.Aes.AArch64.Aese.ctrVec s.mem (s.gpr .x2) (s.read .w .x10) (i + k)) ∧
      VG.Proof.Aes.AArch64.Aese.Fr [.x12] regs s s'
  | [], _, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (by simp), Fr.refl _ _ _⟩
  | b :: bs, i, s, hnd, hi, hin => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    simp only [List.length_cons] at hi
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.ctr1_ok b i s (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_
    have h2 : s₁.gpr .x2 = s.gpr .x2 := f₁.gpr _ (by decide)
    have h10 : s₁.read .w .x10 = s.read .w .x10 := by
      simp only [State.read, f₁.gpr _ (by decide : Reg.x10 ∉ [Reg.x12])]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.ctrs_ok bs (i + 1) s₁ (List.nodup_cons.mp hnd).2 (by omega)
      (by rw [f₁.rd, f₁.wr, h2]; exact hin)) fun s' ⟨e, f⟩ => ⟨?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [f.v _ hbs, e₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [e k (by simpa using hk), f₁.mem, h2, h10, show i + 1 + k = i + (k + 1) by omega]
    · refine (f₁.mono (fun r h => h) (fun r h => by simp_all)).trans
        (f.mono (fun r h => h) (fun r h => List.mem_cons_of_mem _ h))

/-! ## The data -/

/-- XOR `b` into the block at `x3 + 16 j`. -/
theorem xor1_ok (b : VReg) (j : Nat) (s : State) (hb : b ≠ .v31) (hj : j < 4096)
    (hin : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 16) :
    WP isa (.block (xor1 b j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 16
        (s.v b ^^^ s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 128) ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .v31 → s'.v r = s.v r) := by
  rw [xor1, WP.block_cons_iff]
  refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_ldrq (by omega) (VG.Proof.Aes.AArch64.Aese.inRegions_wr hin), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_strq (by omega) hin, WP.block_nil ?_⟩
  refine ⟨?_, rfl, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  simp [State.setV, hb]

theorem off_ofNat_toNat (D : Addr) {i k : Nat} (hi : i < 2 ^ 64) (hk : k < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 k)).toNat =
      if k ≤ i then i - k else 2 ^ 64 + i - k := Offset.sub_toNat' D hk hi

theorem xor_zero' (x : Byte) : x ^^^ 0 = x := BitVec.xor_zero

/-- One block of keystream XORed in, by a 16-byte store. -/
theorem dataInv_write {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : DataInv m₀ m D n k ks)
    (hv : ∀ t < 16, vbyte v t = ks (16 * k + t)) :
    DataInv m₀ (m.write (D + BitVec.ofNat 64 (16 * k)) 16
        (v ^^^ m.readW (D + BitVec.ofNat 64 (16 * k)) 128)) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (m.write (D + BitVec.ofNat 64 (16 * k)) 16
        (v ^^^ m.readW (D + BitVec.ofNat 64 (16 * k)) 128)) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [VG.Proof.Aes.AArch64.Aese.off_ofNat_toNat D (by omega) (by omega)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega)]
        show vbyte _ _ = _
        rw [VG.Proof.Aes.AArch64.Aese.vbyte_xor, hv _ h2, VG.Proof.Aes.AArch64.Aese.vbyte_readW _ _ h2, Offset.add_add_eq D (show 16 * k + (i - 16 * k) = i by omega),
          h i hi, ite_eq_right (show ¬ i < 16 * k by omega), show 16 * k + (i - 16 * k) = i by omega,
          VG.Proof.Aes.AArch64.Aese.xor_zero', BitVec.xor_comm]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega), h i hi,
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have e := Offset.toNat_sub_add x D (d := 16 * k) (by omega)
    rw [Offset.sub_add_eq] at hlt
    have := (x - D).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega)] at hlt
    omega

theorem xorData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {ks : Nat → Byte} (hn : 16 * n ≤ 2 ^ 64) :
    ∀ (regs : List VReg) (j : Nat) (s : State), regs.Nodup → .v31 ∉ regs →
    s.gpr .x3 = D + BitVec.ofNat 64 (16 * c) → j + regs.length ≤ 4096 → c + j + regs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.wr → DataInv m₀ s.mem D n (c + j) ks →
    (∀ k (h : k < regs.length), ∀ t < 16, vbyte (s.v regs[k]) t = ks (16 * (c + j + k) + t)) →
    WP isa (.block (xorData regs j)) s fun s' =>
      DataInv m₀ s'.mem D n (c + j + regs.length) ks ∧ Frame [⟨D, 16 * n⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .v31 → r ∉ regs → s'.v r = s.v r)
  | [], _, s, _, _, _, _, _, _, hD, _ =>
    WP.block_nil ⟨hD, Frame.refl _ _, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h31, hx3, hj, hc, hw, hD, hks => by
    have hb31 : b ≠ .v31 := fun h => h31 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h31' : .v31 ∉ bs := fun h => h31 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hj hc
    have ha : s.gpr .x3 + BitVec.ofNat 64 (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := by
      rw [hx3, Offset.add_add_eq D (show 16 * c + 16 * j = 16 * (c + j) by omega)]
    rw [xorData, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.xor1_ok b j s hb31 (by omega) (by
        rw [ha]; exact ⟨_, hw, Offset.contains_base D (by omega) (by omega)⟩))
      fun s₁ ⟨m₁, g₁, sp₁, rd₁, wr₁, v₁⟩ => ?_
    rw [ha] at m₁
    have hst := VG.Proof.Aes.AArch64.Aese.dataInv_write hn (by omega) hD (v := s.v b) fun t ht => by
      have := hks 0 (by simp) t ht
      simpa using this
    rw [← m₁] at hst
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.xorData_ok (m₀ := m₀) (c := c) (ks := ks) hn bs (j + 1) s₁ (List.nodup_cons.mp hnd).2 h31'
      (by rw [g₁]; exact hx3) (by omega) (by omega) (by rw [wr₁]; exact hw)
      (by rw [show c + (j + 1) = c + j + 1 by omega]; exact hst.1) (fun k hk t ht => by
        rw [v₁ _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h31' (h ▸ List.getElem_mem hk))]
        have := hks (k + 1) (by simp; omega) t ht
        simp only [List.getElem_cons_succ] at this
        rw [this, show c + j + (k + 1) = c + (j + 1) + k by omega]))
      fun s' ⟨d', f', g', sp', rd', wr', v'⟩ => ⟨?_, hst.2.trans f', g'.trans g₁, sp'.trans sp₁,
        rd'.trans rd₁, wr'.trans wr₁, fun r h1 h2 => ?_⟩
    · rw [List.length_cons, show c + j + (bs.length + 1) = c + (j + 1) + bs.length by omega]; exact d'
    · simp only [List.mem_cons, not_or] at h2
      rw [v' r h1 h2.2, v₁ r h2.1 h1]

/-! ## The precondition and the loop invariant -/

section
variable (s₀ : State)

abbrev kp : Addr := s₀.gpr .x0
abbrev nr : Nat := (s₀.gpr .x1).toNat
abbrev cp : Addr := s₀.gpr .x2
abbrev dp : Addr := s₀.gpr .x3
abbrev nb : Nat := (s₀.gpr .x4).toNat
abbrev dR : Region := ⟨VG.Proof.Aes.AArch64.Aese.dp s₀, 16 * VG.Proof.Aes.AArch64.Aese.nb s₀⟩
/-- The key schedule. -/
abbrev sch : List Byte := Spec.Aes.bytesAt s₀.mem (VG.Proof.Aes.AArch64.Aese.kp s₀) (16 * (VG.Proof.Aes.AArch64.Aese.nr s₀ + 1))
/-- The initial counter block, and its counter. -/
abbrev cb : Spec.Gcm.Block := Spec.Gcm.blockAt s₀.mem (VG.Proof.Aes.AArch64.Aese.cp s₀)
abbrev c0 : BitVec 32 := (VG.Proof.Aes.AArch64.Aese.cb s₀).extractLsb' 0 32
/-- The keystream, byte by byte. -/
abbrev kst : Nat → Byte := keyStream (VG.Proof.Aes.AArch64.Aese.nr s₀) (VG.Proof.Aes.AArch64.Aese.sch s₀) (VG.Proof.Aes.AArch64.Aese.cb s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨VG.Proof.Aes.AArch64.Aese.kp s₀, 240⟩]
  wr : s₀.wr = [⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩, VG.Proof.Aes.AArch64.Aese.dR s₀, ⟨s₀.gpr .x5, 2048⟩]
  s_c : Region.Disjoint ⟨VG.Proof.Aes.AArch64.Aese.kp s₀, 240⟩ ⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩
  s_d : Region.Disjoint ⟨VG.Proof.Aes.AArch64.Aese.kp s₀, 240⟩ (VG.Proof.Aes.AArch64.Aese.dR s₀)
  c_d : Region.Disjoint ⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩ (VG.Proof.Aes.AArch64.Aese.dR s₀)
  wrap : (VG.Proof.Aes.AArch64.Aese.dp s₀).toNat + 16 * VG.Proof.Aes.AArch64.Aese.nb s₀ ≤ 2 ^ 64
  rounds : VG.Proof.Aes.AArch64.Aese.nr s₀ = 10 ∨ VG.Proof.Aes.AArch64.Aese.nr s₀ = 12 ∨ VG.Proof.Aes.AArch64.Aese.nr s₀ = 14

theorem pre_of {s₀ : State} (h : Proof.Aes.ctr32AArch64.pre s₀) : VG.Proof.Aes.AArch64.Aese.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, _, h6, _, _, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h6, h9, h10⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀)
include hp

theorem nb16 : 16 * VG.Proof.Aes.AArch64.Aese.nb s₀ ≤ 2 ^ 64 := by have := hp.wrap; omega

theorem dat : VG.Proof.Aes.AArch64.Aese.dR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem n16 : 16 * VG.Proof.Aes.AArch64.Aese.nb s₀ < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => hp.c_d (VG.Proof.Aes.AArch64.Aese.cp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (VG.Proof.Aes.AArch64.Aese.cp s₀ - VG.Proof.Aes.AArch64.Aese.dp s₀).isLt
  omega

theorem ctr_in : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 0) 16 :=
  ⟨⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem key_in {o : Nat} (h : o + 16 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Aes.AArch64.Aese.kp s₀ + BitVec.ofNat 64 o) 16 :=
  ⟨⟨VG.Proof.Aes.AArch64.Aese.kp s₀, 240⟩, by rw [hp.rd]; simp, Offset.contains_base _ h (by omega)⟩

/-- Memory that only differs from the initial memory in the data. -/
theorem cb_frame {m : Mem} (hf : Frame [VG.Proof.Aes.AArch64.Aese.dR s₀] s₀.mem m) : Spec.Gcm.blockAt m (VG.Proof.Aes.AArch64.Aese.cp s₀) = VG.Proof.Aes.AArch64.Aese.cb s₀ :=
  Proof.Gcm.blockAt_congr fun _ hk => hf.bytes (R := ⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩)
    (by simp only [List.mem_singleton, forall_eq]; exact hp.c_d)
    (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

end Pre

/-- After `c` blocks, with `x3`, `x4` and the counter at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ VG.Proof.Aes.AArch64.Aese.nb s₀
  keys : VG.Proof.Aes.AArch64.Aese.Keys (VG.Proof.Aes.AArch64.Aese.nr s₀) (VG.Proof.Aes.AArch64.Aese.sch s₀) s
  x2 : s.gpr .x2 = VG.Proof.Aes.AArch64.Aese.cp s₀
  x3 : s.gpr .x3 = VG.Proof.Aes.AArch64.Aese.dp s₀ + BitVec.ofNat 64 (16 * p)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nb s₀ - p)
  x10 : s.read .w .x10 = VG.Proof.Aes.AArch64.Aese.c0 s₀ + BitVec.ofNat 32 p
  frame : Frame [VG.Proof.Aes.AArch64.Aese.dR s₀] s₀.mem s.mem
  data : DataInv s₀.mem s.mem (VG.Proof.Aes.AArch64.Aese.dp s₀) (VG.Proof.Aes.AArch64.Aese.nb s₀) c (VG.Proof.Aes.AArch64.Aese.kst s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Keys.of_v {nr : Nat} {w : List Byte} {vs : List VReg} {s s' : State} (h : VG.Proof.Aes.AArch64.Aese.Keys nr w s)
    (hrs : VG.Proof.Aes.AArch64.Aese.BlockRegs vs) (hv : ∀ r, r ∉ vs → s'.v r = s.v r) (h6 : s'.gpr .x6 = s.gpr .x6)
    (h7 : s'.gpr .x7 = s.gpr .x7) : VG.Proof.Aes.AArch64.Aese.Keys nr w s' :=
  ⟨h.rounds, fun j hj => by rw [hv _ (hrs.kreg j)]; exact h.full j hj,
    by rw [hv _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl]; exact h.k29,
    by rw [hv _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl]; exact h.k30,
    by rw [h6]; exact h.x6, by rw [h7]; exact h.x7⟩

theorem Keys.of_fr {nr : Nat} {w : List Byte} {gs : List Reg} {vs : List VReg} {s s' : State}
    (h : VG.Proof.Aes.AArch64.Aese.Keys nr w s) (hf : VG.Proof.Aes.AArch64.Aese.Fr gs vs s s') (h6 : .x6 ∉ gs) (h7 : .x7 ∉ gs) (hrs : VG.Proof.Aes.AArch64.Aese.BlockRegs vs) :
    VG.Proof.Aes.AArch64.Aese.Keys nr w s' := h.of_v hrs hf.v (hf.gpr _ h6) (hf.gpr _ h7)

theorem regs_ok (rs : List VReg) (h : rs = regs8 ∨ rs = [.v0]) :
    VG.Proof.Aes.AArch64.Aese.BlockRegs rs ∧ .v31 ∉ rs ∧ VG.Proof.Aes.AArch64.Aese.BlockRegs (.v31 :: rs) := by
  rcases h with rfl | rfl <;> refine ⟨⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩⟩

theorem keyStream_eq {R c k t : Nat} {w : List Byte} {icb : Spec.Gcm.Block} (ht : t < 16) :
    keyStream R w icb (16 * (c + k) + t) = (cipher R w (ctrState icb (c + k))).getD t 0 := by
  rw [keyStream, show (16 * (c + k) + t) / 16 = c + k by omega,
    show (16 * (c + k) + t) % 16 = t by omega]

/-- The counter blocks, AES and the XOR into the data, for the blocks
`c … c + N - 1` (`N` the number of registers). -/
theorem blocks_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) (rs : List VReg) (hrs : rs = regs8 ∨ rs = [.v0])
    (tail : List Instr) {Q : State → Prop} {c : Nat} (hc : c + rs.length ≤ VG.Proof.Aes.AArch64.Aese.nb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s) (hQ : ∀ s', VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + rs.length) c s' → WP isa (.block tail) s' Q) :
    WP isa (.seq (.block (ctrs rs 0)) (.seq (VG.Impl.Aes.AArch64.Aese.aes rs) (.block (xorData rs 0 ++ tail)))) s Q := by
  obtain ⟨hbr, h31, hbr31⟩ := VG.Proof.Aes.AArch64.Aese.regs_ok rs hrs
  have hlen : rs.length ≤ 8 := by rcases hrs with rfl | rfl <;> decide
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16 := by
    rw [hI.rd, hI.wr, hI.x2]; exact hp.ctr_in
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.ctrs_ok rs 0 s hbr.1 (by omega) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  have hK₁ := hI.keys.of_fr f₁ (by decide) (by decide) hbr
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.aes_ok hbr hK₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < rs.length), ∀ t < 16,
      vbyte (s₂.v rs[k]) t = VG.Proof.Aes.AArch64.Aese.kst s₀ (16 * (c + 0 + k) + t) := by
    intro k h t ht
    show _ = keyStream _ _ _ _
    rw [Nat.add_zero, VG.Proof.Aes.AArch64.Aese.keyStream_eq ht, ← VG.Proof.Aes.AArch64.Aese.getD_st _ ht, e₂ _ (List.getElem_mem h), e₁ k h, hI.x10,
      hI.x2, VG.Proof.Aes.AArch64.Aese.ctrVec, VG.Proof.Aes.AArch64.Aese.c0, Nat.zero_add, BitVec.add_assoc, ← BitVec.ofNat_add, ← hp.cb_frame hI.frame,
      VG.Proof.Aes.AArch64.Aese.ctrVec_st]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.xorData_ok (m₀ := s₀.mem) (D := VG.Proof.Aes.AArch64.Aese.dp s₀) (c := c) hp.nb16 rs 0 s₂ hbr.1 h31
      (by rw [f₂.gpr, f₁.gpr _ (by decide), hI.x3]) (by omega) (by omega)
      (by rw [f₂.wr, f₁.wr, hI.wr]; exact hp.dat)
      (by rw [f₂.mem, f₁.mem, Nat.add_zero]; exact hI.data) ks)
    fun s₃ ⟨d₃, fr₃, g₃, sp₃, rd₃, wr₃, v₃⟩ => hQ s₃ ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  have g : ∀ r, r ≠ .x12 → s₃.gpr r = s.gpr r := fun r hr => by
    rw [g₃, f₂.gpr, f₁.gpr r (by simp [hr])]
  refine ⟨by omega, ?_, by rw [g _ (by decide), hI.x2], by rw [g _ (by decide), hI.x3],
    by rw [g _ (by decide), hI.x4], by simp only [State.read]; rw [g _ (by decide)]; exact hI.x10,
    by rw [hm₂] at fr₃; exact hI.frame.trans fr₃, by rw [Nat.add_zero] at d₃; exact d₃,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩
  refine (hK₁.of_v hbr f₂.v (by rw [f₂.gpr]) (by rw [f₂.gpr])).of_v hbr31 (fun r hr => ?_)
    (by rw [g₃]) (by rw [g₃])
  simp only [List.mem_cons, not_or] at hr
  exact v₃ r hr.1 hr.2

/-! ## The loop bodies -/

theorem ushr3 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem eval_zero {s : State} {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    AArch64.eval (.zero .x r) s = some (decide (k = 0)) := by
  simp only [AArch64.eval, State.read, h, BitVec.setWidth_eq, Option.some.injEq]
  by_cases h0 : k = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 k ≠ 0 := fun e => h0 (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h0]

theorem eval_nonzero {s : State} {r : Reg} {k : Nat} (h : s.gpr r = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) : AArch64.eval (.nonzero .x r) s = some (!decide (k = 0)) := by
  have := VG.Proof.Aes.AArch64.Aese.eval_zero h hk
  simp only [AArch64.eval, Option.some.injEq] at this ⊢
  rw [bne, this]

theorem tail8_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.AArch64.Aese.nb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 8) c s) :
    WP isa (.block [.addImm .w .x10 .x10 8, .addImm .x .x3 .x3 128, .subImm .x .x4 .x4 8,
        .lsr .x .x13 .x4 3]) s fun s' =>
      VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8)) / 8) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_addImm_w (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 8) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have h4 : BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nb s₀ - c) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8)) := by
    rw [Offset.ofNat_sub_ofNat (by omega), show VG.Proof.Aes.AArch64.Aese.nb s₀ - c - 8 = VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8) by omega]
  refine ⟨⟨hI.le, hI.keys.of_v (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    by simp [State.write, hI.x2], ?_, ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩, ?_⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x4]
    exact h4
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, VG.Proof.Aes.AArch64.Aese.sw32]
    rw [show BitVec.setWidth Size.w.bits (s.gpr .x10) = s.read .w .x10 from rfl, hI.x10,
      BitVec.add_assoc, BitVec.ofNat_add]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x4]
    rw [h4, VG.Proof.Aes.AArch64.Aese.ushr3 (by omega)]

theorem tail1_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) {c : Nat} (hc : c + 1 ≤ VG.Proof.Aes.AArch64.Aese.nb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 1) c s) :
    WP isa (.block [.addImm .w .x10 .x10 1, .addImm .x .x3 .x3 16, .subImm .x .x4 .x4 1]) s
      (VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 1) (c + 1)) := by
  have hn := hp.nb16
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_addImm_w (imm := 1) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_addImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  refine ⟨hI.le, hI.keys.of_v (vs := []) ⟨List.nodup_nil, by simp⟩ (fun _ _ => rfl) rfl rfl,
    by simp [State.write, hI.x2], ?_, ?_, ?_, hI.frame, hI.data, hI.rd, hI.wr⟩
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x3]
    exact Offset.add_add_eq _ (by omega)
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, hI.x4]
    rw [Offset.ofNat_sub_ofNat (by omega), show VG.Proof.Aes.AArch64.Aese.nb s₀ - c - 1 = VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 1) by omega]
  · simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, VG.Proof.Aes.AArch64.Aese.sw32]
    rw [show BitVec.setWidth Size.w.bits (s.gpr .x10) = s.read .w .x10 from rfl, hI.x10,
      BitVec.add_assoc, BitVec.ofNat_add]

theorem body8_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) {c : Nat} (hc : c + 8 ≤ VG.Proof.Aes.AArch64.Aese.nb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s) :
    WP isa body8 s fun s' =>
      VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 8) (c + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8)) / 8) :=
  VG.Proof.Aes.AArch64.Aese.blocks_ok hp regs8 (.inl rfl) _ hc hI fun _ hI' => VG.Proof.Aes.AArch64.Aese.tail8_ok hp hc hI'

theorem body1_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) {c : Nat} (hc : c + 1 ≤ VG.Proof.Aes.AArch64.Aese.nb s₀) {s : State}
    (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s) : WP isa body1 s (VG.Proof.Aes.AArch64.Aese.Inv s₀ (c + 1) (c + 1)) :=
  VG.Proof.Aes.AArch64.Aese.blocks_ok hp [.v0] (.inr rfl) _ hc hI fun _ hI' => VG.Proof.Aes.AArch64.Aese.tail1_ok hp hc hI'

/-! ## The prologue and the epilogue -/

theorem kreg_inj : ∀ j < 13, ∀ i < 13, VG.Impl.Aes.AArch64.Aese.kreg j = VG.Impl.Aes.AArch64.Aese.kreg i → j = i := by decide

theorem kreg_ne (j : Nat) : VG.Impl.Aes.AArch64.Aese.kreg j ≠ .v29 ∧ VG.Impl.Aes.AArch64.Aese.kreg j ≠ .v30 := by
  unfold VG.Impl.Aes.AArch64.Aese.kreg; split <;> decide

/-- The first `k` round keys, into `kreg 0 … kreg (k − 1)`. -/
theorem loads_ok (s : State)
    (hin : ∀ j < 13, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * j)) 16) :
    ∀ k ≤ 13, WP isa (.block ((List.range k).map fun j => .ldrq (VG.Impl.Aes.AArch64.Aese.kreg j) .x0 (16 * j))) s fun s' =>
      (∀ j < k, s'.v (VG.Impl.Aes.AArch64.Aese.kreg j) = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * j)) 128) ∧
      VG.Proof.Aes.AArch64.Aese.Fr [] ((List.range k).map VG.Impl.Aes.AArch64.Aese.kreg) s s'
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (by omega), Fr.refl _ _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Aes.AArch64.Aese.loads_ok s hin k (by omega)) fun s₁ ⟨e₁, f₁⟩ => ?_
    have g₀ : s₁.gpr .x0 = s.gpr .x0 := f₁.gpr _ (by simp)
    refine WP.of_runBlock ⟨_, by
      simp only [List.map_cons, List.map_nil, runBlock_cons]
      rw [VG.Proof.Aes.AArch64.Aese.exec_ldrq (by omega) (by rw [f₁.rd, f₁.wr, g₀]; exact hin k (by omega)), runStep_some,
        runBlock_nil], ?_⟩
    refine ⟨fun j hj => ?_, ⟨fun r _ => f₁.gpr r (by simp), fun r hr => ?_, f₁.sp, f₁.mem, f₁.rd,
      f₁.wr⟩⟩
    · by_cases hjk : j = k
      · subst hjk; rw [VG.Proof.Aes.AArch64.Aese.setV_v_self, f₁.mem, g₀]
      · rw [VG.Proof.Aes.AArch64.Aese.setV_v_of_ne _ _ fun h => hjk (VG.Proof.Aes.AArch64.Aese.kreg_inj j (by omega) k (by omega) h), e₁ j (by omega)]
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton,
        not_or] at hr
      rw [VG.Proof.Aes.AArch64.Aese.setV_v_of_ne _ _ hr.2, f₁.v r hr.1]

theorem exec_lsl_x {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) := by
  simp [exec, Size.bits, h]

theorem setup_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) :
    WP isa (.block setup) s₀ fun s => VG.Proof.Aes.AArch64.Aese.Inv s₀ 0 0 s ∧ s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nb s₀ / 8) := by
  have hR := hp.rounds
  have hn := hp.nb16
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nr s₀) := by simp [VG.Proof.Aes.AArch64.Aese.nr]
  rw [setup, WP.block_append_iff]
  refine WP.mono (VG.Proof.Aes.AArch64.Aese.loads_ok s₀ (fun j hj => hp.key_in (by omega)) 13 (Nat.le_refl _))
    fun s₁ ⟨e₁, f₁⟩ => ?_
  have g : ∀ r, s₁.gpr r = s₀.gpr r := fun r => f₁.gpr r (by simp)
  have e9 : s₁.gpr .x0 + s₁.gpr .x1 <<< 4 = VG.Proof.Aes.AArch64.Aese.kp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.nr s₀) := by
    rw [g, g, shl4]
  have e9' : VG.Proof.Aes.AArch64.Aese.kp s₀ + BitVec.ofNat 64 (16 * VG.Proof.Aes.AArch64.Aese.nr s₀) - BitVec.ofNat 64 16 =
      VG.Proof.Aes.AArch64.Aese.kp s₀ + BitVec.ofNat 64 (16 * (VG.Proof.Aes.AArch64.Aese.nr s₀ - 1)) := by
    rw [Offset.add_ofNat_sub _ (by omega), show 16 * VG.Proof.Aes.AArch64.Aese.nr s₀ - 16 = 16 * (VG.Proof.Aes.AArch64.Aese.nr s₀ - 1) by omega]
  have rdwr : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [f₁.rd, f₁.wr]
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_lsl_x (sh := 4) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_add, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide) (by
    simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, BitVec.setWidth_eq, e9,
      BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 16) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, rdwr]
    exact hp.key_in (by omega)), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 10) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 12) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_w (off := 12) (by decide) (by
    simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, rdwr, g]
    exact ⟨⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_lsr_x (sh := 3) (by decide), WP.block_nil ?_⟩
  have hL : ∀ j, j ≤ VG.Proof.Aes.AArch64.Aese.nr s₀ → 16 * j + 16 ≤ 16 * (VG.Proof.Aes.AArch64.Aese.nr s₀ + 1) := fun j hj => by omega
  have hx4 : s₀.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Aes.AArch64.Aese.nb s₀) := by simp [VG.Proof.Aes.AArch64.Aese.nb]
  refine ⟨⟨Nat.zero_le _, ⟨hR, fun j hj => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [State.setV, State.write, (VG.Proof.Aes.AArch64.Aese.kreg_ne j).1, (VG.Proof.Aes.AArch64.Aese.kreg_ne j).2, ite_false]
    rw [e₁ j (by omega)]
    exact VG.Proof.Aes.AArch64.Aese.keyIs_readW _ _ (hL j (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, e9', BitVec.add_zero, f₁.mem]
    exact VG.Proof.Aes.AArch64.Aese.keyIs_readW _ _ (hL _ (by omega))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, e9, BitVec.add_zero, f₁.mem]
    exact VG.Proof.Aes.AArch64.Aese.keyIs_readW _ _ (hL _ (Nat.le_refl _))
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx1]; rfl
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g, Nat.mul_zero, BitVec.add_zero]
  · simp only [State.setV, State.write, reduceCtorEq, ite_false, g, Nat.sub_zero, hx4]
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false, VG.Proof.Aes.AArch64.Aese.sw32, g,
      f₁.mem, BitVec.add_zero]
    exact icb_lo _ _
  · exact f₁.mem ▸ Frame.refl _ _
  · intro i hi
    show s₁.mem _ = _
    rw [f₁.mem, ite_eq_right (by omega), VG.Proof.Aes.AArch64.Aese.xor_zero']
  · exact f₁.rd
  · exact f₁.wr
  · simp only [State.setV, State.write, State.read, ite_true, reduceCtorEq, ite_false,
      BitVec.setWidth_eq, g, hx4]
    exact VG.Proof.Aes.AArch64.Aese.ushr3 (by omega)

theorem ctrStore_ok {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) {s : State} (hI : VG.Proof.Aes.AArch64.Aese.Inv s₀ (VG.Proof.Aes.AArch64.Aese.nb s₀) (VG.Proof.Aes.AArch64.Aese.nb s₀) s) :
    WP isa (.block ctrStore) s (Proof.Aes.ctr32AArch64.post s₀) := by
  have hn := hp.n16
  have hw : InRegions s.wr (VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 12) 4 :=
    ⟨⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩, by rw [hI.wr, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [ctrStore, WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_w (off := 12) (by decide) (by
    simp only [State.write, reduceCtorEq, ite_false, hI.x2]; exact hw), WP.block_nil ?_⟩
  simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, hI.x2, VG.Proof.Aes.AArch64.Aese.sw32]
  rw [show BitVec.setWidth 32 (s.gpr .x10) = s.read .w .x10 from rfl, hI.x10]
  -- The counter word is outside the data.
  have hf : Frame [⟨VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 12, 4⟩] s.mem
      (s.mem.writeW (VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 12) (rev32 (VG.Proof.Aes.AArch64.Aese.c0 s₀ + BitVec.ofNat 32 (VG.Proof.Aes.AArch64.Aese.nb s₀)))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd : ∀ r ∈ [(⟨VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 12, 4⟩ : Region)], Region.Disjoint (VG.Proof.Aes.AArch64.Aese.dR s₀) r := by
    simp only [List.mem_singleton, forall_eq]
    exact hp.c_d.symm.sub_right (Offset.sub_base _ (by omega))
  refine ⟨ctr32_of_dataInv (dataInv_frame hf hd hn hI.data), ctr_after fun k hk => ?_⟩
  show (s.mem.writeW (VG.Proof.Aes.AArch64.Aese.cp s₀ + BitVec.ofNat 64 12) (rev32 (VG.Proof.Aes.AArch64.Aese.c0 s₀ + BitVec.ofNat 32 (VG.Proof.Aes.AArch64.Aese.nb s₀)))) _ = _
  rw [writeW_apply, off_toNat _ (by omega) (by omega)]
  by_cases h : 12 ≤ k
  · rw [ite_eq_left h, ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right (show ¬ k < 12 by omega),
      icb_lo, BitVec.setWidth_eq]
    congr 3
    apply BitVec.eq_of_toNat_eq; simp
  · rw [ite_eq_right h, ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega),
      ite_eq_left (show k < 12 by omega)]
    exact hI.frame.bytes (R := ⟨VG.Proof.Aes.AArch64.Aese.cp s₀, 16⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact hp.c_d) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Aes.AArch64.Aese.Pre s₀) :
    WP isa ctr32 s₀ (Proof.Aes.ctr32AArch64.post s₀) := by
  have hn := hp.n16
  refine WP.seq (WP.mono (VG.Proof.Aes.AArch64.Aese.setup_ok hp) fun s₁ ⟨hI₁, h13⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ c, VG.Proof.Aes.AArch64.Aese.nb s₀ - c < 8 ∧ VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s) ?_
    fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Aes.AArch64.Aese.nb s₀ / 8 = 0)) (VG.Proof.Aes.AArch64.Aese.eval_zero h13 (by omega)) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simp at h; omega, hI₁⟩
    · let I8 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.AArch64.Aese.nb s₀ - c ∧ c + 8 ≤ VG.Proof.Aes.AArch64.Aese.nb s₀ ∧ VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s
      have hstep : ∀ m s, I8 m s → WP isa body8 s (fun s' =>
          (AArch64.eval (.nonzero .x .x13) s' = some false ∧ ∃ c, VG.Proof.Aes.AArch64.Aese.nb s₀ - c < 8 ∧ VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s') ∨
          (AArch64.eval (.nonzero .x .x13) s' = some true ∧ ∃ m' < m, I8 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (VG.Proof.Aes.AArch64.Aese.body8_ok hp hc hI) fun s' ⟨hI', h13'⟩ => ?_
        rw [VG.Proof.Aes.AArch64.Aese.eval_nonzero h13' (by omega)]
        by_cases hlt : VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8) < 8
        · exact .inl ⟨by simp; omega, c + 8, hlt, hI'⟩
        · exact .inr ⟨by simp; omega, VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I8 hstep (VG.Proof.Aes.AArch64.Aese.nb s₀) s₁ ⟨0, rfl, by simp at h; omega, hI₁⟩
  refine WP.seq (WP.mono (Q := VG.Proof.Aes.AArch64.Aese.Inv s₀ (VG.Proof.Aes.AArch64.Aese.nb s₀) (VG.Proof.Aes.AArch64.Aese.nb s₀)) ?_ fun s₄ hI₄ => VG.Proof.Aes.AArch64.Aese.ctrStore_ok hp hI₄)
  refine WP.ite (decide (VG.Proof.Aes.AArch64.Aese.nb s₀ - c = 0)) (VG.Proof.Aes.AArch64.Aese.eval_zero hI₂.x4 (by omega)) (fun h => ?_) (fun h => ?_)
  · have : c = VG.Proof.Aes.AArch64.Aese.nb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₂)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = VG.Proof.Aes.AArch64.Aese.nb s₀ - c ∧ c < VG.Proof.Aes.AArch64.Aese.nb s₀ ∧ VG.Proof.Aes.AArch64.Aese.Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa body1 s (fun s' =>
        (AArch64.eval (.nonzero .x .x4) s' = some false ∧ VG.Proof.Aes.AArch64.Aese.Inv s₀ (VG.Proof.Aes.AArch64.Aese.nb s₀) (VG.Proof.Aes.AArch64.Aese.nb s₀) s') ∨
        (AArch64.eval (.nonzero .x .x4) s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (VG.Proof.Aes.AArch64.Aese.body1_ok hp hc hI) fun s' hI' => ?_
      rw [VG.Proof.Aes.AArch64.Aese.eval_nonzero hI'.x4 (by omega)]
      by_cases hlast : VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 1) = 0
      · have : c + 1 = VG.Proof.Aes.AArch64.Aese.nb s₀ := by omega
        exact .inl ⟨by simp [hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [hlast], VG.Proof.Aes.AArch64.Aese.nb s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < VG.Proof.Aes.AArch64.Aese.nb s₀ := by have := hI₂.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (VG.Proof.Aes.AArch64.Aese.nb s₀ - c) s₂ ⟨c, rfl, hlt, hI₂⟩

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32 s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ :=
    WP.gprs (rs := preserved) (VG.Proof.Aes.AArch64.Aese.correct (VG.Proof.Aes.AArch64.Aese.pre_of hs)) (by decide +kernel) (by decide +kernel)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_verified :
    Verified AArch64.target ctr32 (Spec.Gcm.ctr32Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.Aes.AArch64.Aese.ctr32_correct VG.Proof.Aes.AArch64.Aese.ctr32_ct (by
    sig_implies [Spec.Gcm.ctr32Contract, Spec.Gcm.ctr32Sig, Proof.Aes.ctr32AArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Aes.AArch64.satState] using Proof.Aes.AArch64.satState)

end VG.Proof.Aes.AArch64.Aese

end
