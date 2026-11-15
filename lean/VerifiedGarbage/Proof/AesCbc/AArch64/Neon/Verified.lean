module

public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group
public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Ctr32
public import VerifiedGarbage.Impl.AesCbc.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Correct
import VerifiedGarbage.Proof.AesCbc.AArch64.Neon.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.AesCbc.Rounds
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Verified
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Group
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Ctr32
meta import VerifiedGarbage.Impl.AesCbc.AArch64.Neon
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Result
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Correct
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# CBC decryption, bitsliced in AdvSIMD registers, on AArch64

`verified`: `Impl.AesCbc.AArch64.Neon.decrypt` against the contract of the
CBC decryptions that leave `scratch` to their caller to wipe
(`Proof.AesCbc.decryptRoundsContract`), as the decryptions with the
Cryptographic Extension are (`Decrypt/`), whose invariant this proof keeps:
the blocks stored so far are `Decrypt.output`'s (`EcbInv`), and the chaining
value is `Decrypt.chaining`'s, in `v31` within a group and at `iv` between
groups.

A group loads its blocks (`Neon.loadFrom_wp`), deciphers them
(`Neon.decrypt8_ok`), and chains and stores them (`chainFrom_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Neon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.Impl.AesCbc.AArch64.Neon
open VG.Proof.Aes.AArch64 (EcbInv ecbInv_frame ecbInv_orig)
open VG.Proof.Aes.AArch64.Neon (KeysAt EncPre ScrIn decrypt8_cryptOk inRel_st vbyte_of_inRel QA QB
  loadFrom_wp advance_wp keyLoop_ok KInv keyMasks_ok eval_nz blk_addr keysAt_frame B_inj B_ne31)
open VG.Proof.Aes.Vector (st vbyte_xor getD_ofFn)
open VG.Proof.AesCbc.AArch64.Decrypt (chaining output data_done chaining_bytes data_size
  original_word)

/-! ## Chaining and storing the blocks of a group -/

theorem chain1_ok {s : State} {k : Nat} (hk : k < 8)
    (hin : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (.block (chain1 k)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 16 (s.v (B k) ^^^ s.v .v31) ∧
      s'.v .v31 = s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 128 ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ B k → r ≠ .v31 → s'.v r = s.v r) := by
  have hb := B_ne31 k hk
  rw [chain1, WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Aes.AArch64.Aese.exec_ldrq (by omega_using [hk]) (Proof.Aes.AArch64.Aese.inRegions_wr hin), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Aes.AArch64.Aese.exec_strq (by omega_using [hk]) hin, WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  · simp [State.setV, hb]
  · simp [State.setV]

/-- Block `8 g + k`: chained, and stored. -/
theorem chainStep {s s₀ : State} {g k : Nat} (hk8 : k < 8)
    (h3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g))) (hkn : 8 * g + k < N s₀)
    (hn : 16 * N s₀ < 2 ^ 64) (hwr : dataR s₀ ∈ s.wr)
    (hinv : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (8 * g + k) (output s₀))
    (h31 : s.v .v31 = chaining s₀ (8 * g + k))
    (hB : ∀ t < 16, vbyte (s.v (B k)) t =
      (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ (8 * g + k)))).getD t 0) :
    WP isa (.block (chain1 k)) s fun s' =>
      EcbInv s₀.mem s'.mem (Dp s₀) (N s₀) (8 * g + k + 1) (output s₀) ∧
      s'.v .v31 = chaining s₀ (8 * g + k + 1) ∧ Frame [dataR s₀] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ B k → r ≠ .v31 → s'.v r = s.v r) := by
  have ha : s.gpr .x3 + BitVec.ofNat 64 (16 * k) = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g + k)) := by
    rw [h3, Offset.add_add_eq _ (show 16 * (8 * g) + 16 * k = 16 * (8 * g + k) by omega_using [])]
  refine WP.mono (chain1_ok hk8 (by
      rw [ha]
      exact ⟨_, hwr, Offset.contains_base _ (by omega_using [hkn]) (by omega_using [hn, hkn])⟩))
    fun s' ⟨m', v', g', rd', wr', o'⟩ => ?_
  rw [ha] at m' v'
  have hs := Proof.Aes.AArch64.Aese.ecbInv_write (by omega_using [hn]) hkn hinv (v := s.v (B k) ^^^ s.v .v31)
    fun t ht => by rw [vbyte_xor, hB t ht, h31, output, getD_ofFn ht]
  rw [← m'] at hs
  refine ⟨hs.1, ?_, hs.2, g', rd', wr', o'⟩
  rw [v', original_word hinv (Nat.le_refl _) hkn]
  rfl

/-- The blocks `k`, … of group `g` chained and stored, while there are
blocks left. -/
theorem chainFrom_wp (fuel : Nat) : ∀ (k : Nat), k + fuel = 7 → ∀ {s s₀ : State} {g : Nat}
    {P : State → Prop},
    s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g)) →
    s.gpr .x4 = BitVec.ofNat 64 (N s₀ - 8 * g) → 8 * g + k < N s₀ → 16 * N s₀ < 2 ^ 64 →
    dataR s₀ ∈ s.wr → EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (8 * g + k) (output s₀) →
    s.v .v31 = chaining s₀ (8 * g + k) →
    (∀ i, k ≤ i → i < 8 → 8 * g + i < N s₀ → ∀ t < 16, vbyte (s.v (B i)) t =
      (Spec.Aes.invCipher (R s₀) (wK s₀)
        (Spec.Aes.stateAt s₀.mem (blk s₀ (8 * g + i)))).getD t 0) →
    (∀ s', EcbInv s₀.mem s'.mem (Dp s₀) (N s₀) (min (N s₀) (8 * g + 8)) (output s₀) →
      s'.v .v31 = chaining s₀ (min (N s₀) (8 * g + 8)) → Frame [dataR s₀] s.mem s'.mem →
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') →
    WP isa (chainFrom fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s s₀ g P h3 h4 hkn hn hwr hinv h31 hB hP
    have hk7 : k = 7 := by omega_using [hk]
    subst hk7
    simp only [chainFrom]
    refine WP.mono (chainStep (by decide) h3 hkn hn hwr hinv h31
      (hB 7 (Nat.le_refl _) (by decide) hkn)) fun s₁ ⟨d₁, c₁, f₁, g₁, rd₁, wr₁, _⟩ => ?_
    have e : min (N s₀) (8 * g + 8) = 8 * g + 7 + 1 := by omega_using [hkn]
    refine hP s₁ ?_ ?_ f₁ (fun r _ => by rw [g₁]) rd₁ wr₁
    · rw [e]; exact d₁
    · rw [e]; exact c₁
  | succ fuel ih =>
    intro k hk s s₀ g P h3 h4 hkn hn hwr hinv h31 hB hP
    have hk8 : k < 8 := by omega_using [hk]
    simp only [chainFrom]
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine WP.mono (chainStep hk8 h3 hkn hn hwr hinv h31 (hB k (Nat.le_refl _) hk8 hkn))
      fun s₁ ⟨d₁, c₁, f₁, g₁, rd₁, wr₁, v₁⟩ => ?_
    let t := s₁.write .x .x6 (s₁.read .x .x4 - BitVec.ofNat 64 (k + 1))
    refine WP.of_runBlock ⟨t, by
      rw [runBlock_cons, exec_subImm_x (by omega_using [hk8]), runStep_some, runBlock_nil], ?_⟩
    have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
      show (if r = Reg.x6 then _ else s₁.gpr r) = _
      rw [ite_eq_right hr, g₁]
    have t6 : t.gpr .x6 = BitVec.ofNat 64 (N s₀ - 8 * g - (k + 1)) := by
      have e : t.gpr .x6 = s₁.gpr .x4 - BitVec.ofNat 64 (k + 1) := by
        simp [t, State.write, State.read]
      rw [e, g₁, h4, Offset.ofNat_sub_ofNat (by omega_using [hkn])]
    refine WP.ite _ (eval_nz t6 (by omega_using [hn])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : 8 * g + (k + 1) < N s₀ := by
        have : N s₀ - 8 * g - (k + 1) ≠ 0 := by simpa using hb
        omega_using [this]
      refine ih (k + 1) (by omega_using [hk]) (s := t) (s₀ := s₀) (g := g)
        ((tg .x3 (by decide)).trans h3) ((tg .x4 (by decide)).trans h4) hlt hn
        (by show _ ∈ s₁.wr; rw [wr₁]; exact hwr) d₁ c₁
        (fun i hki hi8 hin tt ht => by
          show vbyte (s₁.v (B i)) tt = _
          rw [v₁ _ (fun h => by
            have := B_inj i hi8 k hk8 h
            omega_using [this, hki]) (B_ne31 i hi8)]
          exact hB i (by omega_using [hki]) hi8 hin tt ht)
        fun s' hd hc hf hg hrd' hwr' => hP s' hd hc (f₁.trans hf)
          (fun r hr => (hg r hr).trans (tg r hr)) (hrd'.trans rd₁) (hwr'.trans wr₁)
    · have heq : N s₀ = 8 * g + k + 1 := by
        have : N s₀ - 8 * g - (k + 1) = 0 := by simpa using hb
        omega_using [this, hkn]
      have e : min (N s₀) (8 * g + 8) = 8 * g + k + 1 := by omega_using [heq, hk8]
      refine WP.block_nil (hP t ?_ ?_ f₁ tg rd₁ wr₁)
      · rw [e]; exact d₁
      · rw [e]; exact c₁

/-! ## The groups -/

/-- Before group `g`, with the chaining values `ch` and the results `out`
(CBC's here, CFB's in `Proof/AesCfb/AArch64/Neon.lean`). -/
structure NInv (ch : Nat → BitVec 128) (out : Nat → Spec.Aes.State) (s₀ : State) (g : Nat)
    (s : State) : Prop where
  hg : 8 * g < N s₀
  x1 : s.gpr .x1 = BitVec.ofNat 64 (R s₀)
  x2 : s.gpr .x2 = Iv s₀
  x3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g))
  x4 : s.gpr .x4 = BitVec.ofNat 64 (N s₀ - 8 * g)
  x5 : s.gpr sb = S s₀
  chain : s.mem.readW (Iv s₀) 128 = ch (8 * g)
  keys : KeysAt s.mem (S s₀) (R s₀) (wK s₀)
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (8 * g) out
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- After the last group. -/
structure NDone (ch : Nat → BitVec 128) (out : Nat → Spec.Aes.State) (s₀ s : State) : Prop where
  chain : s.mem.readW (Iv s₀) 128 = ch (N s₀)
  data : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (N s₀) out

theorem post_of_done {s₀ s : State} (hd : NDone (chaining s₀) (output s₀) s₀ s) :
    (cbcAArch64 false).post s₀ s := by
  refine ⟨data_done hd.data, ?_⟩
  show Spec.Aes.bytesAt s.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) (blks s₀)
  rw [bytesAt_toList, ← VG.Proof.Aes.AArch64.Neon.st_readW, hd.chain,
    chaining_bytes _ _ (Nat.le_refl _), List.take_of_length_le (by rw [length_blocksAt])]

/-- One group: from before group `g`, to after the last group (`x4` zero) or
before group `g + 1`. -/
theorem nGroup_ok {s₀ : State} (hp : UPre s₀) {g : Nat} {s : State}
    (hi : NInv (chaining s₀) (output s₀) s₀ g s) :
    WP isa decGroup s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ NDone (chaining s₀) (output s₀) s₀ s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧
        NInv (chaining s₀) (output s₀) s₀ (g + 1) s') := by
  have hR := hp.rounds
  have hR14 : R s₀ ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have n16 := data_size hp
  have hg := hi.hg
  have hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hivw : ivR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hscr : ScrIn (S s₀) s₀.wr := ⟨2176, by decide, by decide, by rw [hp.wr]; simp⟩
  have d96 : ∀ r ∈ [(⟨S s₀, 96⟩ : Region)], (dataR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_scr.sub_right (Region.sub_prefix (by omega_using []))
  have i96 : ∀ r ∈ [(⟨S s₀, 96⟩ : Region)], (ivR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_scr.sub_right (Region.sub_prefix (by omega_using []))
  unfold decGroup
  -- The loads.
  refine WP.seq (loadFrom_wp 7 0 rfl (c := N s₀ - 8 * g) hi.x4 (by omega_using [hg])
    (by omega_using [n16]) (fun i hi8 hic => ⟨dataR s₀, List.mem_append_right _ (hi.wr ▸ hdat), by
      rw [hi.x3, blk_addr]
      exact Offset.contains_base _ (by omega_using [hic]) (by omega_using [hic, n16])⟩)
    fun s₁ hv₁ _ hg₁ hm₁ hrd₁ hwr₁ _ => ?_)
  -- The inverse cipher.
  have hb₁ : s₁.gpr sb = S s₀ := (hg₁ sb (by decide)).trans hi.x5
  have hpe : EncPre s₁ (R s₀) (wK s₀) :=
    ⟨by rw [hb₁, hwr₁, hi.wr]; exact hscr, hR, (hg₁ .x1 (by decide)).trans hi.x1,
      by rw [hm₁, hb₁]; exact hi.keys⟩
  refine WP.seq (WP.mono (decrypt8_cryptOk hpe (inRel_st (QA s₁))) fun s₂ h₂ => ?_)
  obtain ⟨hc₂, hin₂⟩ := h₂
  have keep₂ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → s₂.gpr r = s.gpr r :=
    fun r h6 h7 hk hc => (hc₂.keep r h6 h7 hk hc).trans (hg₁ r h6)
  have x2₂ : s₂.gpr .x2 = Iv s₀ :=
    (keep₂ .x2 (by decide) (by decide) (by decide) (by decide)).trans hi.x2
  have rd₂ : s₂.rd = s₀.rd := by rw [hc₂.rd, hrd₁, hi.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [hc₂.wr, hwr₁, hi.wr]
  have fr₂ : Frame [⟨S s₀, 96⟩] s.mem s₂.mem := by
    have := hc₂.frame
    rwa [hb₁, hm₁] at this
  have data₂ : EcbInv s₀.mem s₂.mem (Dp s₀) (N s₀) (8 * g) (output s₀) :=
    ecbInv_frame fr₂ d96 n16 hi.data
  have chain₂ : s₂.mem.readW (Iv s₀) 128 = chaining s₀ (8 * g) := by
    rw [fr₂.readW (r := ivR s₀) (Region.contains_self _ _) i96 (by decide)]
    exact hi.chain
  have hB : ∀ i, 0 ≤ i → i < 8 → 8 * g + i < N s₀ → ∀ t < 16, vbyte (s₂.v (B i)) t =
      (Spec.Aes.invCipher (R s₀) (wK s₀)
        (Spec.Aes.stateAt s₀.mem (blk s₀ (8 * g + i)))).getD t 0 := by
    intro i _ hi8 hin t ht
    have hst : st (s₁.v (A i)) =
        Spec.Aes.stateAt s₀.mem (Dp s₀ + BitVec.ofNat 64 (16 * (8 * g + i))) := by
      rw [hv₁ i (Nat.zero_le _) hi8 (by omega_using [hin]), hi.x3, blk_addr,
        VG.Proof.Aes.AArch64.Neon.st_readW]
      exact ecbInv_orig hi.data (by omega_using []) hin
    rw [vbyte_of_inRel hin₂ hi8 ht]
    show (Spec.Aes.invCipher _ _ (st (s₁.v (A i)))).getD t 0 = _
    rw [hst]
  -- The chaining value.
  let s₃ := s₂.setV .v31 (s₂.mem.readW (s₂.gpr .x2 + BitVec.ofNat 64 0) 128)
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide) (by
      rw [x2₂, BitVec.add_zero, rd₂, wr₂]
      exact ⟨ivR s₀, List.mem_append_right _ hivw, Region.contains_self _ _⟩), runStep_some,
      runBlock_nil], ?_⟩)
  have v31₃ : s₃.v .v31 = chaining s₀ (8 * g) := by
    show (s₂.setV _ _).v .v31 = _
    rw [v_setV_self, x2₂, BitVec.add_zero]
    exact chain₂
  -- The blocks.
  refine WP.seq (chainFrom_wp 7 0 rfl (s := s₃) (s₀ := s₀) (g := g)
    ((keep₂ .x3 (by decide) (by decide) (by decide) (by decide)).trans hi.x3)
    ((keep₂ .x4 (by decide) (by decide) (by decide) (by decide)).trans hi.x4)
    (by omega_using [hg]) n16 (by show _ ∈ s₂.wr; rw [wr₂]; exact hdat) data₂ v31₃
    (fun i h0 hi8 hin t ht => by
      show vbyte ((s₂.setV _ _).v (B i)) t = _
      rw [v_setV_of_ne _ _ (B_ne31 i hi8)]
      exact hB i h0 hi8 hin t ht)
    fun s₄ d₄ c₄ f₄ g₄ rd₄ wr₄ => ?_)
  -- The chaining value, back to `iv`.
  have x2₄ : s₄.gpr .x2 = Iv s₀ := (g₄ .x2 (by decide)).trans x2₂
  let s₅ : State := { s₄ with mem := s₄.mem.write (s₄.gpr .x2 + BitVec.ofNat 64 0) 16 (s₄.v .v31) }
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_strq (off := 0) (by decide) (by
      rw [x2₄, BitVec.add_zero, wr₄]
      show InRegions s₂.wr _ _
      rw [wr₂]
      exact ⟨ivR s₀, hivw, Region.contains_self _ _⟩), runStep_some, runBlock_nil], ?_⟩)
  have m₅ : s₅.mem = s₄.mem.write (Iv s₀) 16 (s₄.v .v31) := by
    show s₄.mem.write _ 16 _ = _
    rw [x2₄, BitVec.add_zero]
  have f₅ : Frame [ivR s₀] s₄.mem s₅.mem := by
    rw [m₅]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have chain₅ : s₅.mem.readW (Iv s₀) 128 = chaining s₀ (min (N s₀) (8 * g + 8)) := by
    have hm : (s₄.mem.write (Iv s₀) 16 (s₄.v .v31)).readW (Iv s₀) 128 = s₄.v .v31 :=
      Mem.readW_writeW_self s₄.mem (Iv s₀) 16 (s₄.v .v31) (by decide)
    rw [m₅, hm]
    exact c₄
  have data₅ : EcbInv s₀.mem s₅.mem (Dp s₀) (N s₀) (min (N s₀) (8 * g + 8)) (output s₀) :=
    ecbInv_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.symm) n16 d₄
  -- On to the next group.
  refine advance_wp (s := s₅) (c := N s₀ - 8 * g)
    (show s₄.gpr .x4 = _ from (g₄ .x4 (by decide)).trans
      ((keep₂ .x4 (by decide) (by decide) (by decide) (by decide)).trans hi.x4))
    (by omega_using [hg]) (by omega_using [n16])
    fun s₆ hmore hlast g₆ _ m₆ rd₆ wr₆ _ => ?_
  by_cases h8 : 8 < N s₀ - 8 * g
  · obtain ⟨x3₆, x4₆⟩ := hmore h8
    have keep₆ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → r ≠ .x3 → r ≠ .x4 →
        s₆.gpr r = s.gpr r := fun r h6 h7 hk hc h3 h4 =>
      (g₆ r h6 h3 h4).trans ((g₄ r h6).trans (keep₂ r h6 h7 hk hc))
    refine .inr ⟨(eval_nz x4₆ (by omega_using [n16])).trans (by
        simp [show N s₀ - 8 * g - 8 ≠ 0 by omega_using [h8]]),
      { hg := by omega_using [h8]
        x1 := (keep₆ .x1 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hi.x1
        x2 := (keep₆ .x2 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hi.x2
        x3 := by
          show s₆.gpr .x3 = _
          rw [x3₆]
          show s₄.gpr .x3 + _ = _
          rw [g₄ .x3 (by decide)]
          show s₂.gpr .x3 + _ = _
          rw [keep₂ .x3 (by decide) (by decide) (by decide) (by decide), hi.x3, BitVec.add_assoc,
            ← BitVec.ofNat_add, show 16 * (8 * g) + 128 = 16 * (8 * (g + 1)) by omega_using []]
        x4 := by rw [x4₆, show N s₀ - 8 * g - 8 = N s₀ - 8 * (g + 1) by omega_using []]
        x5 := (keep₆ sb (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans hi.x5
        chain := by
          rw [m₆]
          have := chain₅
          rwa [show min (N s₀) (8 * g + 8) = 8 * (g + 1) by omega_using [h8]] at this
        keys := by
          rw [m₆]
          refine keysAt_frame hR14 f₅ (fun r hr => ?_) (keysAt_frame hR14 f₄ (fun r hr => ?_)
            (keysAt_frame hR14 fr₂ (fun r hr => ?_) hi.keys))
          · simp only [List.mem_singleton] at hr; subst hr
            exact (hp.iv_scr.sub_right (Offset.sub_base _ (by omega_using []))).symm
          · simp only [List.mem_singleton] at hr; subst hr
            exact (hp.data_scr.sub_right (Offset.sub_base _ (by omega_using []))).symm
          · simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
        data := by
          rw [m₆]
          have := data₅
          rwa [show min (N s₀) (8 * g + 8) = 8 * (g + 1) by omega_using [h8]] at this
        rd := by rw [rd₆]; show s₄.rd = _; rw [rd₄]; exact rd₂
        wr := by rw [wr₆]; show s₄.wr = _; rw [wr₄]; exact wr₂ }⟩
  · have x4₆ := hlast h8
    have e : min (N s₀) (8 * g + 8) = N s₀ := by omega_using [h8, hg]
    refine .inl ⟨(eval_nz x4₆ (by decide)).trans (by simp), ?_, ?_⟩
    · rw [m₆, ← e]; exact chain₅
    · rw [m₆]
      have := data₅
      rwa [e] at this

/-- The loop over the groups, each as `hG` has it. -/
theorem nGroups_ok {ch : Nat → BitVec 128} {out : Nat → Spec.Aes.State} {G : Prog isa}
    {s₀ : State}
    (hG : ∀ g s, NInv ch out s₀ g s → WP isa G s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ NDone ch out s₀ s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ NInv ch out s₀ (g + 1) s'))
    {s : State} (hi : NInv ch out s₀ 0 s) :
    WP isa (.loop G (.nonzero .x .x4)) s (NDone ch out s₀) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = N s₀ - 8 * g ∧ NInv ch out s₀ g s)
    (fun k s hs => ?_) (N s₀) s ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hi⟩ := hs
  refine WP.mono (hG g s hi) fun s' h => ?_
  rcases h with ⟨hz, hd⟩ | ⟨hz, hi'⟩
  · exact .inl ⟨hz, hd⟩
  · exact .inr ⟨hz, N s₀ - 8 * (g + 1), by have := hi'.hg; omega_using [this], g + 1, rfl, hi'⟩

/-! ## The function -/

/-- `whole G`: the round keys bitsliced, and the groups, each as `hG` has
it. -/
theorem whole_wp {ch : Nat → BitVec 128} {out : Nat → Spec.Aes.State} {G : Prog isa}
    {s₀ : State} (hp : UPre s₀) (hch : ch 0 = s₀.mem.readW (Iv s₀) 128)
    (hG : ∀ g s, NInv ch out s₀ g s → WP isa G s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ NDone ch out s₀ s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ NInv ch out s₀ (g + 1) s')) :
    WP isa (whole G) s₀ (NDone ch out s₀) := by
  have n16 := data_size hp
  have hR := hp.rounds
  have hR14 : R s₀ ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have hx4 : s₀.gpr .x4 = BitVec.ofNat 64 (N s₀) := by simp [N]
  have hscr : ScrIn (S s₀) s₀.wr := ⟨2176, by decide, by decide, by rw [hp.wr]; simp⟩
  unfold whole
  refine WP.ite (decide (N s₀ = 0)) (Proof.Aes.AArch64.Aese.eval_zero hx4 (by omega_using [n16])) (fun h0 => ?_)
    (fun h0 => ?_)
  · have hn0 : N s₀ = 0 := by simpa using h0
    exact WP.block_nil ⟨by rw [hn0, hch], fun i hi => absurd hi (by omega_using [hn0])⟩
  · have hn0 : N s₀ ≠ 0 := by simpa using h0
    -- The masks, and where the round keys go.
    refine WP.seq ?_
    simp only [keySetup]
    rw [WP.block_append_iff (M := isa)]
    obtain ⟨s₂, h₂, mask₂, -, g₂, m₂, rd₂, wr₂, sp₂⟩ := keyMasks_ok 8 (Nat.le_refl 8) s₀
    refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
    let s₃ := s₂.write .x .x7 (s₂.read .x sb + BitVec.ofNat 64 128)
    let s₄ := s₃.write .x kp (s₃.read .x .x1 + BitVec.ofNat 64 1)
    refine WP.of_runBlock ⟨s₄, by
      rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
    have g₄ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₄.gpr r = s₀.gpr r := fun r h6 h7 hk => by
      simp [s₄, s₃, State.write, h7, hk, g₂ r h6]
    have x7₄ : s₄.gpr .x7 = S s₀ + BitVec.ofNat 64 128 := by
      have e : s₄.gpr .x7 = s₂.gpr sb + BitVec.ofNat 64 128 := by
        simp [s₄, s₃, State.write, State.read, kp]
      rw [e, g₂ sb (by decide)]; rfl
    have kp₄ : s₄.gpr kp = BitVec.ofNat 64 (R s₀ + 1) := by
      have e : s₄.gpr kp = s₂.gpr .x1 + BitVec.ofNat 64 1 := by
        simp [s₄, s₃, State.write, State.read, kp]
      rw [e, g₂ .x1 (by decide), BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hi₀ : KInv s₄ (W s₀) (S s₀) (R s₀) (wK s₀) 0 s₄ :=
      { hx0 := by rw [g₄ .x0 (by decide) (by decide) (by decide)]; simp
        hx7 := x7₄
        hkp := kp₄
        keep := fun _ _ _ _ => rfl
        mask := mask₂
        rd := rfl
        wr := rfl
        sp := rfl
        keys := fun i hi => absurd hi (by omega_using [])
        frame := Frame.refl _ _ }
    refine WP.seq (WP.mono (keyLoop_ok (S := W s₀) (b := S s₀) (R := R s₀) (w := wK s₀)
      (by show _ ∈ s₂.rd; rw [rd₂, hp.rd]; simp) (by show ScrIn _ s₂.wr; rw [wr₂]; exact hscr)
      (hp.sch_scr.sub_right (Region.sub_prefix (by omega_using []))) hR14
      (by show _ = Spec.Aes.bytesAt s₂.mem _ _; rw [m₂]) hi₀) fun s₅ hk₅ => ?_)
    -- The groups.
    have g₅ : ∀ r, r ≠ .x0 → r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₅.gpr r = s₀.gpr r :=
      fun r h0 h6 h7 hk => (hk₅.keep r h0 h7 hk).trans (g₄ r h6 h7 hk)
    have fr₅ : Frame [⟨S s₀, 2048⟩] s₀.mem s₅.mem := by
      have := hk₅.frame
      rwa [show s₄.mem = s₀.mem from m₂] at this
    have hi : NInv ch out s₀ 0 s₅ :=
      { hg := by omega_using [hn0]
        x1 := by rw [g₅ .x1 (by decide) (by decide) (by decide) (by decide)]; simp [R]
        x2 := g₅ .x2 (by decide) (by decide) (by decide) (by decide)
        x3 := by rw [g₅ .x3 (by decide) (by decide) (by decide) (by decide)]; simp
        x4 := (g₅ .x4 (by decide) (by decide) (by decide) (by decide)).trans (by rw [hx4]; simp)
        x5 := g₅ sb (by decide) (by decide) (by decide) (by decide)
        chain := by
          rw [Nat.mul_zero, hch]
          exact fr₅.readW (r := ivR s₀) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hp.iv_scr.sub_right (Region.sub_prefix (by omega_using []))) (by decide)
        keys := fun j hj => hk₅.keys j (by omega_using [hj])
        data := ecbInv_frame fr₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.data_scr.sub_right (Region.sub_prefix (by omega_using []))) n16
          fun i hi => by simp
        rd := hk₅.rd.trans rd₂
        wr := hk₅.wr.trans wr₂ }
    exact nGroups_ok hG hi

theorem decrypt_wp {s₀ : State} (hp : UPre s₀) :
    WP isa decrypt s₀ fun t => (cbcAArch64 false).post s₀ t :=
  WP.mono (whole_wp hp rfl fun _ _ hi => nGroup_ok hp hi) fun _ hd => post_of_done hd

theorem correct (s : State) (hp : (cbcAArch64 false).pre s) :
    ∃ tr t, Exec isa decrypt s tr t ∧ abiPreserved s t ∧ (cbcAArch64 false).post s t := by
  obtain ⟨tr, t, he, hq, hg⟩ :=
    WP.gprs (rs := preserved) (decrypt_wp (UPre.of hp)) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, ⟨hg, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hq⟩

theorem ct : ConstantTime isa (cbcAArch64 false).pre (cbcAArch64 false).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem verified :
    Verified AArch64.target decrypt (Proof.AesCbc.decryptRoundsContract AArch64.abi) :=
  Verified.of_correct correct ct Decrypt.implies

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

end VG.Proof.AesCbc.AArch64.Neon
