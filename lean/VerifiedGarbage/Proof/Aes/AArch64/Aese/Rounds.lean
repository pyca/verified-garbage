module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Impl.Aes.AArch64.Aese
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Aes.Vector -- shake: keep (exports the existing AES round value interface)
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

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

@[expose] public section

namespace VG.Proof.Aes.AArch64.Aese

open VG.AArch64
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey sbox roundKey cipher bytesAt)

export VG.Proof.Aes.Vector (
  mul_eq inv_eq sbox_eq mul_one' vbyte_ofVBytes ext_vbyte vbyte_readW vbyte_xor st getD_ofFn getD_st st_ext getD_addRoundKey getD_subBytes getD_shiftRows getD_mixColumns vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns KeyIs eor_st aese_st aesmc_st rnds rnds_zero rnds_succ cipher_eq round_st last_st keyIs_readW getLsbD_append_block getLsbD_ofVBytes)

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

theorem VFrame.refl (rs : List VReg) (s : State) : VFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem VFrame.trans {rs : List VReg} {s s' s'' : State} (h : VFrame rs s s') (h' : VFrame rs s' s'') :
    VFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.sp.trans h.sp, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.v r hr).trans (h.v r hr)⟩

theorem VFrame.mono {rs rs' : List VReg} {s s' : State} (h : VFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VFrame rs' s s' :=
  ⟨h.gpr, h.sp, h.mem, h.rd, h.wr, fun r hr => h.v r fun h' => hr (hs r h')⟩

/-- Two instructions that set `b` to `g (b) (k)`, for each register `b` of `regs`. -/
theorem each_ok (f : VReg → List Instr) (g : BitVec 128 → BitVec 128 → BitVec 128) (k : VReg)
    (hf : ∀ b s, b ≠ k → runBlock isa (f b) s = some (s.setV b (g (s.v b) (s.v k)))) :
    ∀ (regs : List VReg) (s : State), regs.Nodup → k ∉ regs →
    WP isa (.block (regs.flatMap f)) s fun s' =>
      (∀ b ∈ regs, s'.v b = g (s.v b) (s.v k)) ∧ VFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
  | b :: bs, s, hnd, hk => by
    have hbk : b ≠ k := fun h => hk (h ▸ List.mem_cons_self ..)
    have hk' : k ∉ bs := fun h => hk (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.of_runBlock ⟨_, hf b s hbk, ?_⟩
    refine WP.mono (each_ok f g k hf bs _ (List.nodup_cons.mp hnd).2 hk') fun s' ⟨hv, hfr⟩ => ⟨?_, ?_⟩
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
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, reduceVOpEval, Option.map_some]
  rw [setV_v_self, setV_setV]

theorem last_run (b : VReg) (s : State) (hb30 : b ≠ .v30) :
    runBlock isa [.vop (.aese b .v29), .vop (.logic .eor b b .v30)] s =
      some (s.setV b (aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, reduceVOpEval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (Ne.symm hb30), setV_setV]

/-- The registers the blocks may be in. -/
def BlockRegs (regs : List VReg) : Prop :=
  regs.Nodup ∧ ∀ r ∈ regs, r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19 ∧ r ≠ .v20 ∧ r ≠ .v21 ∧
    r ≠ .v22 ∧ r ≠ .v23 ∧ r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v26 ∧ r ≠ .v27 ∧ r ≠ .v28 ∧ r ≠ .v29 ∧
    r ≠ .v30

theorem BlockRegs.kreg {regs : List VReg} (h : BlockRegs regs) (j : Nat) : kreg j ∉ regs := by
  intro hj
  have := (h.2 _ hj)
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | _ + 12 => simp [Impl.Aes.AArch64.Aese.kreg] at this

/-- Each register `b` of `regs` holds the state before the `AddRoundKey` of
round key `j`, from the state `x b`. -/
def RInv (regs : List VReg) (w : List Byte) (x : VReg → Spec.Aes.State) (j : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, addRoundKey (st (s.v b)) (roundKey w j) = rnds w (x b) j

/-- What the rounds need of the state: the round keys in `v16`–`v30`, and
`x6`, `x7` for the number of rounds. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  rounds : nr = 10 ∨ nr = 12 ∨ nr = 14
  full : ∀ j, j + 2 ≤ nr → KeyIs (s.v (kreg j)) (roundKey w j)
  k29 : KeyIs (s.v .v29) (roundKey w (nr - 1))
  k30 : KeyIs (s.v .v30) (roundKey w nr)
  x6 : s.gpr .x6 = BitVec.ofNat 64 nr - 10
  x7 : s.gpr .x7 = BitVec.ofNat 64 nr - 12

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List VReg} {s s' : State} (h : Keys nr w s)
    (hf : VFrame rs s s') (hrs : BlockRegs rs) : Keys nr w s' :=
  ⟨h.rounds, fun j hj => by rw [hf.v _ (hrs.kreg j)]; exact h.full j hj,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl]; exact h.k29,
    by rw [hf.v _ fun h' => (hrs.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl]; exact h.k30,
    by rw [hf.gpr]; exact h.x6, by rw [hf.gpr]; exact h.x7⟩

theorem round_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {j : Nat} (hj : j + 2 ≤ nr) {s : State} (hK : Keys nr w s)
    (hI : RInv regs w x j s) :
    WP isa (.block (rnd regs (kreg j))) s fun s' => RInv regs w x (j + 1) s' ∧ VFrame regs s s' := by
  refine WP.mono (each_ok _ (fun v k => aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))))
    (kreg j) (fun b s _ => rnd_run _ b s) regs s hr.1 (hr.kreg j))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb]
  exact round_st (hK.full j hj) (hI b hb)

theorem rounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x 0 s) :
    ∀ k, k + 1 ≤ nr →
    WP isa (.block ((List.range k).flatMap fun i => rnd regs (kreg i))) s fun s' =>
      RInv regs w x k s' ∧ VFrame regs s s'
  | 0, _ => by
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (rounds_ok hr hK hI k (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (round_ok hr (j := k) (by omega) (hK.of_frame hf₁ hr) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

theorem last_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x (nr - 1) s) :
    WP isa (.block (last regs)) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = cipher nr w (x b)) ∧ VFrame regs s s' := by
  have h29 : .v29 ∉ regs := fun h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl
  have h30 : ∀ b ∈ regs, b ≠ .v30 := fun b h' => (hr.2 _ h').2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- `last` is `each_ok` for `v29`, with `v30` read by each step (and not written).
  have e : ∀ (rs : List VReg) (s : State), rs.Nodup → .v29 ∉ rs → (∀ b ∈ rs, b ≠ .v30) →
      WP isa (.block (last rs)) s fun s' =>
        (∀ b ∈ rs, s'.v b = aesMapBytes aesSbox (aesShiftRows (s.v b ^^^ s.v .v29)) ^^^ s.v .v30) ∧
        VFrame rs s s' := by
    intro rs
    induction rs with
    | nil => intro s _ _ _; exact WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VFrame.refl _ _⟩
    | cons b bs ih =>
      intro s hnd hk h30'
      have hb29 : b ≠ .v29 := fun h => hk (h ▸ List.mem_cons_self ..)
      have hb30 : b ≠ .v30 := h30' b List.mem_cons_self
      have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
      rw [Impl.Aes.AArch64.Aese.last, List.flatMap_cons, WP.block_append_iff]
      refine WP.of_runBlock ⟨_, last_run b s hb30, ?_⟩
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
  exact last_st hK.k29 hK.k30 (hI b hb)

/-- Two full rounds, with round keys `j` and `j + 1`. -/
theorem two_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (j : Nat) {k₁ k₂ : VReg} (e₁ : k₁ = kreg j)
    (e₂ : k₂ = kreg (j + 1)) (hj : j + 3 ≤ nr) (hK : Keys nr w s) (hI : RInv regs w x j s) :
    WP isa (.block (rnd regs k₁ ++ rnd regs k₂)) s fun s' =>
      RInv regs w x (j + 2) s' ∧ VFrame regs s s' := by
  subst e₁ e₂
  rw [WP.block_append_iff]
  refine WP.mono (round_ok hr (by omega) hK hI) fun s₁ ⟨hI₁, hf₁⟩ => ?_
  exact WP.mono (round_ok hr (by omega) (hK.of_frame hf₁ hr) hI₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ⟨hI₂, hf₁.trans hf₂⟩

/-- The full rounds with round keys `9 … Nr − 2`. -/
theorem mid_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : Keys nr w s) (hI : RInv regs w x 9 s) :
    WP isa (.ite (.zero .x .x6) (.block [])
        (.seq (.block (rnd regs .v25 ++ rnd regs .v26))
          (.ite (.zero .x .x7) (.block []) (.block (rnd regs .v27 ++ rnd regs .v28))))) s
      fun s' => RInv regs w x (nr - 1) s' ∧ VFrame regs s s' := by
  have hx6 := hK.x6
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.ite true (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun _ => WP.block_nil ⟨hI, VFrame.refl _ _⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 12 - 12 := by rw [hf₃.gpr]; exact hK.x7
    exact WP.ite true (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun _ => WP.block_nil ⟨hI₃, hf₃⟩) (fun h => absurd h (by decide))
  · refine WP.ite false (by simp only [AArch64.eval, State.read, hx6]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.seq (WP.mono (two_ok hr 9 rfl rfl (by omega) hK hI) fun s₃ ⟨hI₃, hf₃⟩ => ?_)
    have hx7 : s₃.gpr .x7 = BitVec.ofNat 64 14 - 12 := by rw [hf₃.gpr]; exact hK.x7
    refine WP.ite false (by simp only [AArch64.eval, State.read, hx7]; decide)
      (fun h => absurd h (by decide)) fun _ => ?_
    exact WP.mono (two_ok hr 11 rfl rfl (by omega) (hK.of_frame hf₃ hr) hI₃)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₃.trans hf'⟩

theorem aes_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte} {s : State}
    (hK : Keys nr w s) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, st (s'.v b) = cipher nr w (st (s.v b))) ∧ VFrame regs s s' := by
  have hI₀ : RInv regs w (fun b => st (s.v b)) 0 s := fun b _ => (rnds_zero w _).symm
  refine WP.seq (WP.mono (rounds_ok hr hK hI₀ 9 (by have := hK.rounds; omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  exact WP.mono (last_ok hr (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s' ⟨hv, hf'⟩ => ⟨hv, hf₁.trans (hf₂.trans hf')⟩

end VG.Proof.Aes.AArch64.Aese
