module

public import VerifiedGarbage.Impl.AesGcm.AArch64.InitAese
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesGcm.AArch64.InitAeseLit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.AesGcm.AArch64.InitAese
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesGcm.AArch64.InitAeseLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range

/-!
# AES-GCM key setup with the AES instructions on AArch64

`init_verified` proves `Impl.AesGcm.AArch64.InitAese.init` against
`Spec.Gcm.initContract` (with no stack): the words of the key schedule as
`vg_aes_expand_key_scratch_aes` computes and stores them (`Key.word_ok`),
and between them, once a round key is complete, the round of `H` it takes
(`hstep_ok`), in `v3`, from the zero block. `HS c` says what `v3` holds
after `c` round keys; after all `Nr + 1`, `H = CIPH_K(0¹²⁸)`, which is
stored at `ctx + 240`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.InitAese

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Proof.Aes.AArch64.Aese.Key
open VG.Impl.AesGcm.AArch64.InitAese (hstep initN init)
open VG.Impl.Aes.AArch64.Aese (wreg wregs word subW)
open VG.Spec.Aes (roundKey cipher addRoundKey shiftRows subBytes bytesAt rounds)
open VG.Spec.Gcm (KeyRepr)

/-- `vg_aes_gcm_init(key = x0, key_len = x1, ctx = x2)`, using no working space. -/
def initAeseAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let ctx : Region := ⟨s.gpr .x2, 256⟩
    s.rd = [key] ∧ s.wr = [ctx] ∧ key.Disjoint ctx ∧ (s.gpr .x2).toNat + 256 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .x2) (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

/-! ## Round keys from pairs of words -/

/-- `orr` of a word with another rotated by 32: the two words, as a register holds them. -/
theorem pair_eq (a b : BitVec 32) : a.setWidth 64 ||| (b.setWidth 64).rotateRight 32 = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_rotateRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, Nat.reduceMod, Nat.reduceSub]
  by_cases h : t < 32
  · simp [h, ht]
  · have h1 : ¬ t < 32 := h
    have h2 : t - 32 < 32 := by omega
    have h3 : t - 32 < 64 := by omega
    simp [h1, h2, h3, ht, BitVec.getLsbD_of_ge a t (by omega)]

/-- Inserting a doubleword in the upper half. -/
theorem setLane_hi (p x q : BitVec 64) : setLane (ofVDwords p x) 64 1 q = ofVDwords p q := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  have ht' : t < 128 := ht
  simp only [setLane, ofVDwords, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_append,
    Nat.mul_one]
  by_cases h : t < 64
  · simp [h, ht']
  · have h2 : t - 64 < 64 := by omega
    have h3 : t - 64 < 128 := by omega
    simp [h, h2, h3, ht']

theorem vbyte_quad (a b c d : BitVec 32) {k : Nat} (hk : k < 16) :
    vbyte (ofVDwords (b ++ a) (d ++ c)) k =
      (if k < 4 then a else if k < 8 then b else if k < 12 then c else d).extractLsb' (8 * (k % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, ht, decide_true,
    Bool.true_and]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h
  · have e1 : 8 * k + t < 64 := by omega
    have e2 : 8 * k + t < 32 := by omega
    simp [e1, e2, h]; congr 1; omega
  · have e1 : 8 * k + t < 64 := by omega
    have e2 : ¬ 8 * k + t < 32 := by omega
    have e3 : ¬ k < 4 := by omega
    have e4 : k < 8 := by omega
    simp [e1, e2, e3, e4]; congr 1; omega
  · have e1 : ¬ 8 * k + t < 64 := by omega
    have e2 : 8 * k + t - 64 < 32 := by omega
    have e3 : ¬ k < 4 := by omega
    have e4 : ¬ k < 8 := by omega
    have e5 : k < 12 := by omega
    simp [e1, e2, e3, e4, e5]; congr 1; omega
  · have e1 : ¬ 8 * k + t < 64 := by omega
    have e2 : ¬ 8 * k + t - 64 < 32 := by omega
    have e3 : ¬ k < 4 := by omega
    have e4 : ¬ k < 8 := by omega
    have e5 : ¬ k < 12 := by omega
    simp [e1, e2, e3, e4, e5]; congr 1; omega

/-- The schedule as words is the schedule as bytes. -/
theorem flatten_wv (f : Nat → BitVec 32) : ∀ K,
    ((List.range K).map fun i => wv (f i)).flatten =
      (List.range (4 * K)).map fun t => (f (t / 4)).extractLsb' (8 * (t % 4)) 8
  | 0 => rfl
  | K + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_wv f K, List.map_singleton,
      List.flatten_singleton, show 4 * (K + 1) = 4 * K + 4 by omega, List.range_add, List.map_append,
      List.map_map]
    refine congrArg (_ ++ ·) ?_
    simp only [wv]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [show (4 * K + j) / 4 = K by omega, show (4 * K + j) % 4 = j by omega]

theorem rk_getD (f : Nat → BitVec 32) {K j k : Nat} (hj : 16 * j + 16 ≤ 4 * K) (hk : k < 16) :
    (roundKey (((List.range K).map fun i => wv (f i)).flatten) j).getD k 0 =
      (f (4 * j + k / 4)).extractLsb' (8 * (k % 4)) 8 := by
  rw [flatten_wv, roundKey]
  simp [List.getD_eq_getElem?_getD, hk, show 16 * j + k < 4 * K by omega]
  rw [show (16 * j + k) / 4 = 4 * j + k / 4 by omega, show (16 * j + k) % 4 = k % 4 by omega]

/-- Round key `j`, from its words in pairs. -/
theorem key_is (f : Nat → BitVec 32) {K j : Nat} (hj : 16 * j + 16 ≤ 4 * K) :
    KeyIs (ofVDwords (f (4 * j + 1) ++ f (4 * j)) (f (4 * j + 3) ++ f (4 * j + 2)))
      (roundKey (((List.range K).map fun i => wv (f i)).flatten) j) := by
  intro k hk
  rw [vbyte_quad _ _ _ _ hk, rk_getD f hj hk]
  rcases (by omega : k < 4 ∨ (4 ≤ k ∧ k < 8) ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h | h <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right] <;>
    exact congrArg (fun q => (f q).extractLsb' (8 * (k % 4)) 8) (by omega)

/-! ## `H` -/

/-- `v3` after the rounds with the first `c` round keys of `w`, from the block `x`. -/
def HS (nr : Nat) (w : List Byte) (x : Spec.Aes.State) (c : Nat) (v : BitVec 128) : Prop :=
  if c < nr then addRoundKey (st v) (roundKey w c) = rnds w x c
  else if c = nr then st v = shiftRows (subBytes (rnds w x (nr - 1)))
  else st v = cipher nr w x

theorem hs_full {nr c : Nat} {w : List Byte} {x : Spec.Aes.State} {v k : BitVec 128}
    (hc : c + 2 ≤ nr) (hk : KeyIs k (roundKey w c)) (h : HS nr w x c v) :
    HS nr w x (c + 1) (aesMixColumns (aesMapBytes aesSbox (aesShiftRows (v ^^^ k)))) := by
  unfold HS at h ⊢
  rw [ite_eq_left (by omega)] at h
  rw [ite_eq_left (by omega)]
  exact round_st hk h

theorem hs_pen {nr c : Nat} {w : List Byte} {x : Spec.Aes.State} {v k : BitVec 128}
    (hc : c + 1 = nr) (hk : KeyIs k (roundKey w c)) (h : HS nr w x c v) :
    HS nr w x (c + 1) (aesMapBytes aesSbox (aesShiftRows (v ^^^ k))) := by
  unfold HS at h ⊢
  rw [ite_eq_left (by omega)] at h
  rw [ite_eq_right (by omega), ite_eq_left hc, aese_st hk, h, show nr - 1 = c by omega]

theorem hs_last {nr c : Nat} {w : List Byte} {x : Spec.Aes.State} {v k : BitVec 128}
    (hc : c = nr) (hk : KeyIs k (roundKey w nr)) (h : HS nr w x c v) :
    HS nr w x (c + 1) (v ^^^ k) := by
  unfold HS at h ⊢
  rw [ite_eq_right (by omega), ite_eq_left hc] at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), eor_st hk, h, cipher_eq]

/-! ## The instructions -/

theorem exec_orrRor {s : State} {d n m : Reg} :
    exec (.logicRor .orr .x d n m 32) s =
      some (s.write .x d (s.gpr n ||| (s.gpr m).rotateRight 32)) := by
  simp [exec, State.read, show 32 < Size.x.bits by decide]

theorem exec_dup_d2 {s : State} {d : VReg} {n : Reg} :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (ofVDwords (s.gpr n) (s.gpr n))) := rfl

theorem wregs_ne' : ∀ a < 8, wregs.getD a .x4 ≠ .x14 ∧ wregs.getD a .x4 ≠ .x15 := by decide

theorem wreg_ne' {nk : Nat} (h8 : nk ≤ 8) (h0 : 0 < nk) (j : Nat) :
    wreg nk j ≠ .x14 ∧ wreg nk j ≠ .x15 :=
  wregs_ne' _ (by have := Nat.mod_lt j h0; omega)

/-- The round key into `v2`, from its words in pairs. -/
theorem pack_ok {nk : Nat} (h8 : nk ≤ 8) (h0 : 0 < nk) (i : Nat) (s : State) :
    ∃ s', runBlock isa [.logicRor .orr .x .x14 (wreg nk (i - 3)) (wreg nk (i - 2)) 32,
        .logicRor .orr .x .x15 (wreg nk (i - 1)) (wreg nk i) 32, .vop (.dup .d2 .v2 .x14),
        .vop (.ins .d2 .v2 1 .x15)] s = some s' ∧
      s'.v .v2 = ofVDwords (s.gpr (wreg nk (i - 3)) ||| (s.gpr (wreg nk (i - 2))).rotateRight 32)
        (s.gpr (wreg nk (i - 1)) ||| (s.gpr (wreg nk i)).rotateRight 32) ∧
      Fr [.x14, .x15] [.v2] s s' := by
  have n1 := (wreg_ne' h8 h0 (i - 1)).1
  have n0 := (wreg_ne' h8 h0 i).1
  refine ⟨_, by rw [runBlock_cons, exec_orrRor, runStep_some, runBlock_cons, exec_orrRor, runStep_some,
    runBlock_cons, exec_dup_d2, runStep_some, runBlock_cons, exec_ins (by decide), runStep_some,
    runBlock_nil], ?_, ?_⟩
  · rw [setV_v_self, setV_v_self, setLane_hi]
    simp [State.write, State.setV, n1, n0]
  · exact (((Fr.write (by simp) _).trans (Fr.write (by simp) _)).trans (Fr.setV (by simp) _)).trans
      (Fr.setV (by simp) _)

theorem aese_run (s : State) :
    runBlock isa [.vop (.aese .v3 .v2)] s =
      some (s.setV .v3 (aesMapBytes aesSbox (aesShiftRows (s.v .v3 ^^^ s.v .v2)))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]

theorem eor_run (s : State) :
    runBlock isa [.vop (.logic .eor .v3 .v3 .v2)] s = some (s.setV .v3 (s.v .v3 ^^^ s.v .v2)) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]

/-! ## The invariant -/

section
variable (s₀ : State)

/-- The key schedule of the `nk`-word key, as bytes. -/
abbrev wf (nk : Nat) : List Byte := ((List.range (4 * (rounds nk + 1))).map fun i => wv (Key.Ws s₀ nk i)).flatten

end

/-- Words `0 … i − 1` are stored, the last `Nk` in their registers, and `v3`
has taken the rounds of the round keys among them. -/
structure J (s₀ : State) (nk i : Nat) (s : State) : Prop where
  k : KInv s₀ nk i s
  h : HS (rounds nk) (wf s₀ nk) (st 0) (i / 4) (s.v .v3)

theorem kinv_of_fr {s₀ : State} {nk i : Nat} {s s' : State} (h : KInv s₀ nk i s) (h8 : nk ≤ 8)
    (h0 : 0 < nk) (hf : Fr [.x14, .x15] [.v2, .v3] s s') : KInv s₀ nk i s' :=
  ⟨by rw [hf.gpr _ (by simp)]; exact h.x0, by rw [hf.gpr _ (by simp)]; exact h.x2,
    by rw [hf.v _ (by simp)]; exact h.v0,
    fun j h₁ h₂ => by
      rw [hf.gpr _ (by simp [(wreg_ne' h8 h0 j).1, (wreg_ne' h8 h0 j).2])]; exact h.win j h₁ h₂,
    by rw [hf.mem]; exact h.frame, by rw [hf.mem]; exact h.good, by rw [hf.rd]; exact h.rd,
    by rw [hf.wr]; exact h.wr⟩

theorem word_v3 (nk i : Nat) : ∀ x ∈ word nk i, vdstOf x ≠ some .v3 := by
  simp only [word]
  by_cases h1 : i < nk
  · simp [h1, vdstOf]
  by_cases h2 : i % nk = 0
  · simp [h1, h2, subW, vdstOf, VOp.dst]
  by_cases h3 : nk > 6 ∧ i % nk = 4
  · simp [h1, h3, subW, vdstOf, VOp.dst]
  · simp [h1, h2, h3, vdstOf]

/-- A word keeps `v3`. -/
theorem word_ok' {s₀ : State} (hp : Key.Pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : Key.klen s₀ = 4 * nk) {i : Nat} (hi : i < 4 * (nk + 7)) {s : State} (hI : KInv s₀ nk i s) :
    WP isa (.block (word nk i)) s fun s' => KInv s₀ nk (i + 1) s' ∧ s'.v .v3 = s.v .v3 := by
  obtain ⟨t, s', he, hq⟩ := word_ok hp hnk hl hi hI
  exact ⟨t, s', he, hq, Exec.vec (c := .block (word nk i)) (fun x hx => word_v3 nk i x hx) he⟩

theorem hstep_nil {nk i : Nat} (h : ¬ i % 4 = 3) : hstep nk i = [] := by
  simp [hstep, h]

theorem step_ok {s₀ : State} (hp : Key.Pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : Key.klen s₀ = 4 * nk) {i : Nat} (hi : i < 4 * (nk + 7)) {s : State} (hJ : J s₀ nk i s) :
    WP isa (.block (word nk i ++ hstep nk i)) s (J s₀ nk (i + 1)) := by
  have h8 : nk ≤ 8 := by omega
  have h0 : 0 < nk := by omega
  refine WP.block_append (WP.mono (word_ok' hp hnk hl hi hJ.k) fun s₁ ⟨hK, hv⟩ => ?_)
  by_cases h3 : i % 4 = 3
  · -- A round key is complete: its round of `H`.
    obtain ⟨c, rfl⟩ : ∃ c, i = 4 * c + 3 := ⟨i / 4, by omega⟩
    have hc4 : (4 * c + 3) / 4 = c := by omega
    have hc : (4 * c + 3 + 1) / 4 = c + 1 := by omega
    obtain ⟨s₂, run₂, v₂, f₂⟩ := pack_ok h8 h0 (4 * c + 3) s₁
    simp only [show 4 * c + 3 - 3 = 4 * c by omega, show 4 * c + 3 - 2 = 4 * c + 1 by omega,
      show 4 * c + 3 - 1 = 4 * c + 2 by omega] at run₂ v₂
    rw [hK.win (4 * c) (by omega) (by omega), hK.win (4 * c + 1) (by omega) (by omega),
      hK.win (4 * c + 2) (by omega) (by omega), hK.win (4 * c + 3) (by omega) (by omega), pair_eq,
      pair_eq] at v₂
    have hk : KeyIs (s₂.v .v2) (roundKey (wf s₀ nk) c) := by
      rw [v₂]; exact key_is _ (by simp only [rounds]; omega)
    have hK₂ : KInv s₀ nk (4 * c + 3 + 1) s₂ := kinv_of_fr hK h8 h0 (f₂.mono (by simp) (by simp))
    have hH₂ : HS (rounds nk) (wf s₀ nk) (st 0) c (s₂.v .v3) := by
      rw [f₂.v _ (by simp), hv, ← hc4]; exact hJ.h
    rw [hstep, ite_eq_left (show (4 * c + 3) % 4 = 3 by omega), hc4]
    simp only [show 4 * c + 3 - 3 = 4 * c by omega, show 4 * c + 3 - 2 = 4 * c + 1 by omega,
      show 4 * c + 3 - 1 = 4 * c + 2 by omega]
    rw [WP.block_append_iff]
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    by_cases hf : c + 2 ≤ nk + 6
    · rw [ite_eq_left hf]
      refine WP.of_runBlock ⟨_, rnd_run .v2 .v3 s₂, ?_, ?_⟩
      · exact kinv_of_fr hK₂ h8 h0 ((Fr.setV (by simp) _))
      · rw [hc, setV_v_self]
        exact hs_full (by simp only [rounds]; omega) hk hH₂
    rw [ite_eq_right hf]
    by_cases hp' : c + 1 = nk + 6
    · rw [ite_eq_left hp']
      refine WP.of_runBlock ⟨_, aese_run s₂, ?_, ?_⟩
      · exact kinv_of_fr hK₂ h8 h0 ((Fr.setV (by simp) _))
      · rw [hc, setV_v_self]
        exact hs_pen (by simp only [rounds]; omega) hk hH₂
    rw [ite_eq_right hp']
    have hcn : c = rounds nk := by simp only [rounds]; omega
    refine WP.of_runBlock ⟨_, eor_run s₂, ?_, ?_⟩
    · exact kinv_of_fr hK₂ h8 h0 ((Fr.setV (by simp) _))
    · rw [hc, setV_v_self]
      exact hs_last hcn (hcn ▸ hk) hH₂
  · rw [hstep_nil h3]
    refine WP.block_nil ⟨hK, ?_⟩
    rw [hv, show (i + 1) / 4 = i / 4 by omega]
    exact hJ.h

theorem initN_ok {s₀ : State} (hp : Key.Pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : Key.klen s₀ = 4 * nk) {s : State} (hJ : J s₀ nk 0 s) :
    WP isa (.block (initN nk)) s (J s₀ nk (4 * (nk + 7))) := by
  unfold initN
  exact wp_range_flatMap (M := isa) (f := fun i => word nk i ++ hstep nk i) (J s₀ nk)
    (fun _ _ hk h => step_ok hp hnk hl hk h) _ (Nat.le_refl _) s hJ

/-! ## The whole function -/

theorem pre_of {s₀ : State} (h : initAeseAArch64.pre s₀) : Key.Pre s₀ := by
  obtain ⟨h1, h2, h3, _, h5⟩ := h
  exact ⟨h1, ⟨256, by decide, by rw [h2]; simp⟩, h3.sub_right (Region.sub_prefix (by decide)), h5⟩

theorem st_zero : st 0 = Vector.ofFn fun i => (Spec.Gcm.toBytes (0 : Spec.Gcm.Block)).getD i 0 := by
  apply st_ext; intro i hi
  rw [getD_st _ hi, getD_ofFn hi, Proof.Aes.toBytes_getD _ hi]
  simp [vbyte]

/-- Storing `H`. -/
theorem fin {s₀ : State} (hp : initAeseAArch64.pre s₀) {nk : Nat} (hnk : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hl : Key.klen s₀ = 4 * nk) {s : State} (hJ : J s₀ nk (4 * (nk + 7)) s) :
    WP isa (.block [.strq .v3 .x2 240]) s (initAeseAArch64.post s₀) := by
  obtain ⟨_, hwr, _, wc, _⟩ := hp
  have h0 : 0 < nk := by omega
  have hw : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 240) 16 :=
    ⟨_, by rw [hJ.k.wr, hwr]; exact List.mem_singleton_self _, by
      rw [hJ.k.x2]; exact Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_strq (by decide) hw, runStep_some, runBlock_nil], ?_⟩
  rw [hJ.k.x2]
  have hm : ∀ m : Mem, m.write (Key.schp s₀ + BitVec.ofNat 64 240) 16 (s.v .v3) =
      m.writeW (Key.schp s₀ + BitVec.ofNat 64 240) (s.v .v3) := fun m => by simp [Mem.writeW]
  show KeyRepr (s.mem.write _ 16 _) (Key.schp s₀) (bytesAt s₀.mem (Key.kp s₀) (Key.klen s₀))
  rw [hl]
  have hk : Spec.Aes.expandKey (bytesAt s₀.mem (Key.kp s₀) (4 * nk)) = wf s₀ nk := expandKey_eq s₀.mem _ h0
  have hH := hJ.h
  unfold HS at hH
  rw [ite_eq_right (by simp only [rounds]; omega), ite_eq_right (by simp only [rounds]; omega)] at hH
  refine ⟨?_, ?_⟩
  · rw [length_bytesAt, show 4 * nk / 4 = nk by omega, hk, hm,
      show 16 * (rounds nk + 1) = 4 * (4 * (rounds nk + 1)) by omega]
    exact bytesAt_eq _ _ _ _ fun i hi => by
      have hi' : i < 4 * (nk + 7) := by simp only [rounds] at hi; omega
      rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hJ.k.good i hi'
  · show Spec.Gcm.blockAt _ (Key.schp s₀ + BitVec.ofNat 64 240) = _
    rw [Spec.Gcm.aes, Spec.Gcm.aesWith, length_bytesAt, show 4 * nk / 4 = nk by omega, hk, ← st_zero,
      ← hH, Spec.Gcm.blockAt]
    refine congrArg Spec.Gcm.ofBytes (List.ext_getElem (by simp [bytesAt]) fun k h₁ h₂ => ?_)
    have hk16 : k < 16 := by simpa [bytesAt] using h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, Vector.getElem_toList, st,
      Vector.getElem_ofFn, Mem.write]
    rw [Mem.sub_ofNat_toNat _ (by omega), ite_eq_left hk16]
    rfl

theorem correct {s₀ : State} (hp : initAeseAArch64.pre s₀) :
    WP isa init s₀ (initAeseAArch64.post s₀) := by
  have hp' := pre_of hp
  have hx1 : s₀.gpr .x1 = BitVec.ofNat 64 (Key.klen s₀) := by simp [klen]
  have hlt := hp'.len_lt
  refine WP.seq ?_
  rw [WP.block_cons_iff]; refine ⟨s₀.setV .v0 0, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨(s₀.setV .v0 0).setV .v3 0, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 24) (by decide), ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_subImm_x (imm := 32) (by decide), WP.block_nil ?_⟩
  let s₂ := (s₀.setV .v0 0).setV .v3 0
  let s₁ := (s₂.write .x .x9 (s₂.read .x .x1 - BitVec.ofNat _ 24)).write .x
    .x10 ((s₂.write .x .x9 (s₂.read .x .x1 - BitVec.ofNat _ 24)).read .x .x1 - BitVec.ofNat _ 32)
  show WP isa _ s₁ _
  have hJ : ∀ nk, 0 < nk → J s₀ nk 0 s₁ := fun nk h0 =>
    ⟨⟨rfl, rfl, by simp [s₁, s₂, State.write, State.setV], fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩, by
      unfold HS
      rw [ite_eq_left (by simp only [rounds]; omega), Nat.zero_div, rnds_zero]
      simp [s₁, s₂, State.write, State.setV]⟩
  have e9 : AArch64.eval (.zero .x .x9) s₁ = some (decide (Key.klen s₀ = 24)) := by
    simp only [AArch64.eval, s₁, s₂, State.read, State.write, State.setV, reduceCtorEq, ite_false,
      ite_true, BitVec.setWidth_eq, hx1]
    rw [Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  have e10 : AArch64.eval (.zero .x .x10) s₁ = some (decide (Key.klen s₀ = 32)) := by
    simp only [AArch64.eval, s₁, s₂, State.read, State.write, State.setV, reduceCtorEq, ite_false,
      ite_true, BitVec.setWidth_eq, hx1]
    rw [Offset.ofNat_sub_ofNat_beq hlt (by decide)]
  have hite : WP isa (.ite (.zero .x .x9) (.block (initN 6))
      (.ite (.zero .x .x10) (.block (initN 8)) (.block (initN 4)))) s₁ fun s =>
      ∃ nk, (nk = 4 ∨ nk = 6 ∨ nk = 8) ∧ Key.klen s₀ = 4 * nk ∧ J s₀ nk (4 * (nk + 7)) s := by
    refine WP.ite _ e9 (fun h => ?_) (fun h => ?_)
    · have h24 : Key.klen s₀ = 24 := by simpa using h
      exact WP.mono (initN_ok hp' (nk := 6) (by decide) h24 (hJ 6 (by decide)))
        fun _ h => ⟨6, by decide, h24, h⟩
    refine WP.ite _ e10 (fun h' => ?_) (fun h' => ?_)
    · have h32 : Key.klen s₀ = 32 := by simpa using h'
      exact WP.mono (initN_ok hp' (nk := 8) (by decide) h32 (hJ 8 (by decide)))
        fun _ h => ⟨8, by decide, h32, h⟩
    · have h16 : Key.klen s₀ = 16 := by
        simp only [decide_eq_false_iff_not] at h h'; rcases hp'.lens with e | e | e <;> omega
      exact WP.mono (initN_ok hp' (nk := 4) (by decide) h16 (hJ 4 (by decide)))
        fun _ h => ⟨4, by decide, h16, h⟩
  exact WP.seq (WP.mono hite fun s ⟨nk, hnk, hl, hJ'⟩ => fin hp hnk hl hJ')

theorem init_correct (s : State) (hs : initAeseAArch64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initAeseAArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ :=
    WP.gprs (rs := preserved) (correct hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem init_ct : ConstantTime isa initAeseAArch64.pre initAeseAArch64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩]

theorem init_verified : Verified AArch64.target init (Spec.Gcm.initContract AArch64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
      initAeseAArch64, AArch64.abi, AArch64.argRegs] [initSat] using initSat)

end VG.Proof.AesGcm.AArch64.InitAese
