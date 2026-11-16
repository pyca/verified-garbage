module

public import VerifiedGarbage.Proof.AesCfb.Rounds
public import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
public import VerifiedGarbage.Proof.AesCbc.AArch64.Neon.Verified
public import VerifiedGarbage.Impl.AesCfb.AArch64.Neon
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCfb.AArch64.Neon.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.AesCfb.Rounds
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Neon.Verified
meta import VerifiedGarbage.Impl.AesCfb.AArch64.Neon
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# CFB128 decryption, bitsliced in AdvSIMD registers, on AArch64

`verified`: `Impl.AesCfb.AArch64.Neon.decrypt` against
`Proof.AesCfb.decryptRoundsContract`, as the decryption with the
Cryptographic Extension is (`Decrypt/`), whose results (`Decrypt.output`)
and chaining values (`Decrypt.chaining`) this proof keeps, in the invariant
of CBC's decryption in AdvSIMD registers (`AesCbc.AArch64.Neon.NInv`,
`whole_wp`).

A group loads the inputs of the block cipher (`loadPrev_wp`), enciphers them
(`Neon.encrypt8_ok`), and XORs each into its ciphertext block
(`cfbFrom_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Neon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.Impl.AesCfb.AArch64.Neon
open VG.Impl.Aes.AArch64.Aese (xor1 outR)
open VG.AArch64.StraightV (vAddr)
open VG.Proof.Aes.AArch64 (EcbInv ecbInv_frame ecbInv_orig)
open VG.Proof.Aes.AArch64.Neon (KeysAt EncPre ScrIn encrypt8_cryptOk inRel_st vbyte_of_inRel QA QB
  advance_wp eval_nz blk_addr keysAt_frame B_inj B_ne31 A_inj ldrq_ok)
open VG.Proof.Aes.Vector (st vbyte_xor getD_ofFn)
open VG.Proof.AesCbc VG.Proof.AesCbc.AArch64
open VG.Proof.AesCbc.AArch64.Neon (NInv NDone whole_wp)
open VG.Proof.AesCfb.AArch64.Decrypt (chaining output data_done chaining_bytes original_word)

/-! ## The inputs of a group -/

/-- The blocks `k`, … of a group loaded into `A (k + 1)`, …, while they have
a block after them (`c` blocks are left). -/
theorem loadPrev_wp (fuel : Nat) : ∀ (k : Nat), k + fuel = 6 → ∀ {s : State} {c : Nat}
    {P : State → Prop}, s.gpr .x4 = BitVec.ofNat 64 c → k + 1 < c → c < 2 ^ 64 →
    (∀ i < 7, i + 1 < c → InRegions (s.rd ++ s.wr) (vAddr (s.gpr .x3) i) 16) →
    (∀ s', (∀ i, k ≤ i → i < 7 → i + 1 < c →
        s'.v (A (i + 1)) = s.mem.readW (vAddr (s.gpr .x3) i) 128) →
      (∀ r, (∀ i, k ≤ i → i < 7 → r ≠ A (i + 1)) → s'.v r = s.v r) →
      (∀ g, g ≠ .x6 → s'.gpr g = s.gpr g) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      P s') →
    WP isa (loadPrev fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s c P h4 hkc hc hin hP
    have hk6 : k = 6 := by omega_using [hk]
    subst hk6
    simp only [loadPrev]
    refine WP.of_runBlock ⟨s.setV (A 7) (s.mem.readW (vAddr (s.gpr .x3) 6) 128), by
      rw [runBlock_cons, ldrq_ok (by decide) (hin 6 (by decide) hkc), runStep_some, runBlock_nil],
      hP _ (fun i hi hi7 _ => ?_) (fun r hr => ?_) (fun _ _ => rfl) rfl rfl rfl⟩
    · have : i = 6 := by omega_using [hi, hi7]
      subst this; exact v_setV_self _ _ _
    · exact v_setV_of_ne _ _ (hr 6 (Nat.le_refl _) (by decide))
  | succ fuel ih =>
    intro k hk s c P h4 hkc hc hin hP
    have hk7 : k < 7 := by omega_using [hk]
    simp only [loadPrev]
    let u := s.setV (A (k + 1)) (s.mem.readW (vAddr (s.gpr .x3) k) 128)
    let t := u.write .x .x6 (u.read .x .x4 - BitVec.ofNat 64 (k + 2))
    have ht : runBlock isa [.ldrq (A (k + 1)) .x3 (16 * k), .subImm .x .x6 .x4 (k + 2)] s =
        some t := by
      rw [runBlock_cons, ldrq_ok (by omega_using [hk7]) (hin k hk7 hkc), runStep_some, runBlock_cons,
        exec_subImm_x (by omega_using [hk7]), runStep_some, runBlock_nil]
    have tg : ∀ g, g ≠ .x6 → t.gpr g = s.gpr g := fun g hg => by
      show (if g = Reg.x6 then _ else s.gpr g) = _
      rw [ite_eq_right hg]
    have t6 : t.gpr .x6 = BitVec.ofNat 64 (c - (k + 2)) := by
      have e : t.gpr .x6 = s.gpr .x4 - BitVec.ofNat 64 (k + 2) := by
        simp [t, u, State.write, State.read, State.setV]
      rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [hkc])]
    refine WP.seq (WP.of_runBlock ⟨t, ht, ?_⟩)
    refine WP.ite _ (eval_nz t6 (by omega_using [hc])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : k + 1 + 1 < c := by
        have : c - (k + 2) ≠ 0 := by simpa using hb
        omega_using [this]
      refine ih (k + 1) (by omega_using [hk]) (c := c) ((tg .x4 (by decide)).trans h4) hlt hc
        (fun i hi7 hic => by
          rw [tg .x3 (by decide)]; exact hin i hi7 hic)
        fun s' hv ho hg hm hrd hwr => hP s' (fun i hki hi7 hic => ?_) (fun r hr => ?_)
          (fun g hg6 => (hg g hg6).trans (tg g hg6)) hm hrd hwr
      · by_cases hik : i = k
        · subst hik
          rw [ho (A (i + 1)) fun j hj hj7 => fun e => by
            have := A_inj (i + 1) (by omega_using [hi7]) (j + 1) (by omega_using [hj7]) e
            omega_using [hj, this]]
          exact v_setV_self _ _ _
        · rw [hv i (by omega_using [hki, hik]) hi7 hic, tg .x3 (by decide)]
          rfl
      · rw [ho r fun i hi hi7 => hr i (by omega_using [hi]) hi7]
        exact v_setV_of_ne _ _ (hr k (Nat.le_refl _) hk7)
    · have heq : c = k + 2 := by
        have : c - (k + 2) = 0 := by simpa using hb
        omega_using [this, hkc]
      refine WP.block_nil (hP t (fun i hki hi7 hic => ?_) (fun r hr => ?_) tg rfl rfl rfl)
      · have : i = k := by omega_using [hki, hic, heq]
        subst this; exact v_setV_self _ _ _
      · exact v_setV_of_ne _ _ (hr k (Nat.le_refl _) hk7)

/-! ## The XOR into the data -/

theorem xor1v_ok {s : State} {k : Nat} (hk : k < 8)
    (hin : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (.block (xor1 false (B k) k)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 16
        (s.v (B k) ^^^ s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 128) ∧
      s'.v .v31 = s.mem.readW (s.gpr .x3 + BitVec.ofNat 64 (16 * k)) 128 ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ B k → r ≠ .v31 → s'.v r = s.v r) := by
  have hb := B_ne31 k hk
  rw [xor1, WP.block_cons_iff]
  refine ⟨_, Proof.Aes.AArch64.Aese.exec_ldrq (by omega_using [hk])
    (Proof.Aes.AArch64.Aese.inRegions_wr hin), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Proof.Aes.AArch64.Aese.exec_strq (n := .x3) (by omega_using [hk]) hin, WP.block_nil ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl, fun r h1 h2 => by simp [State.setV, h1, h2]⟩
  · simp [State.setV, hb]
  · simp [State.setV, hb.symm]

/-- Block `8 g + k`: its enciphered input XORed into it. -/
theorem cfbStep {s s₀ : State} {g k : Nat} (hk8 : k < 8)
    (h3 : s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g))) (hkn : 8 * g + k < N s₀)
    (hn : 16 * N s₀ < 2 ^ 64) (hwr : dataR s₀ ∈ s.wr)
    (hinv : EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (8 * g + k) (output s₀))
    (hB : ∀ t < 16, vbyte (s.v (B k)) t =
      (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ (8 * g + k)))).getD t 0) :
    WP isa (.block (xor1 false (B k) k)) s fun s' =>
      EcbInv s₀.mem s'.mem (Dp s₀) (N s₀) (8 * g + k + 1) (output s₀) ∧
      s'.v .v31 = chaining s₀ (8 * g + k + 1) ∧ Frame [dataR s₀] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ B k → r ≠ .v31 → s'.v r = s.v r) := by
  have ha : s.gpr .x3 + BitVec.ofNat 64 (16 * k) = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g + k)) := by
    rw [h3, Offset.add_add_eq _ (show 16 * (8 * g) + 16 * k = 16 * (8 * g + k) by omega_using [])]
  refine WP.mono (xor1v_ok hk8 (by
      rw [ha]
      exact ⟨_, hwr, Offset.contains_base _ (by omega_using [hkn]) (by omega_using [hn, hkn])⟩))
    fun s' ⟨m', v', g', rd', wr', o'⟩ => ?_
  rw [ha, original_word hinv (Nat.le_refl _) hkn] at m' v'
  have hs := Proof.Aes.AArch64.Aese.ecbInv_write (by omega_using [hn]) hkn hinv
    (v := s.v (B k) ^^^ s₀.mem.readW (Dp s₀ + BitVec.ofNat 64 (16 * (8 * g + k))) 128)
    fun t ht => by rw [vbyte_xor, hB t ht, output, getD_ofFn ht]
  rw [← m'] at hs
  refine ⟨hs.1, ?_, hs.2, g', rd', wr', o'⟩
  rw [v']
  rfl

/-- The blocks `k`, … of group `g`, while there are blocks left. -/
theorem cfbFrom_wp (fuel : Nat) : ∀ (k : Nat), k + fuel = 7 → ∀ {s s₀ : State} {g : Nat}
    {P : State → Prop},
    s.gpr .x3 = Dp s₀ + BitVec.ofNat 64 (16 * (8 * g)) →
    s.gpr .x4 = BitVec.ofNat 64 (N s₀ - 8 * g) → 8 * g + k < N s₀ → 16 * N s₀ < 2 ^ 64 →
    dataR s₀ ∈ s.wr → EcbInv s₀.mem s.mem (Dp s₀) (N s₀) (8 * g + k) (output s₀) →
    (∀ i, k ≤ i → i < 8 → 8 * g + i < N s₀ → ∀ t < 16, vbyte (s.v (B i)) t =
      (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ (8 * g + i)))).getD t 0) →
    (∀ s', EcbInv s₀.mem s'.mem (Dp s₀) (N s₀) (min (N s₀) (8 * g + 8)) (output s₀) →
      s'.v .v31 = chaining s₀ (min (N s₀) (8 * g + 8)) → Frame [dataR s₀] s.mem s'.mem →
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') →
    WP isa (xorFrom false fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s s₀ g P h3 h4 hkn hn hwr hinv hB hP
    have hk7 : k = 7 := by omega_using [hk]
    subst hk7
    simp only [xorFrom]
    refine WP.mono (cfbStep (by decide) h3 hkn hn hwr hinv
      (hB 7 (Nat.le_refl _) (by decide) hkn)) fun s₁ ⟨d₁, c₁, f₁, g₁, rd₁, wr₁, _⟩ => ?_
    have e : min (N s₀) (8 * g + 8) = 8 * g + 7 + 1 := by omega_using [hkn]
    refine hP s₁ ?_ ?_ f₁ (fun r _ => by rw [g₁]) rd₁ wr₁
    · rw [e]; exact d₁
    · rw [e]; exact c₁
  | succ fuel ih =>
    intro k hk s s₀ g P h3 h4 hkn hn hwr hinv hB hP
    have hk8 : k < 8 := by omega_using [hk]
    simp only [xorFrom]
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine WP.mono (cfbStep hk8 h3 hkn hn hwr hinv (hB k (Nat.le_refl _) hk8 hkn))
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
        (by show _ ∈ s₁.wr; rw [wr₁]; exact hwr) d₁
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

theorem post_of_done {s₀ s : State} (hd : NDone (chaining s₀) (output s₀) s₀ s) :
    (modeAArch64 (cfbMode false)).post s₀ s := by
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
  have n16 := Decrypt.data_size hp
  have hg := hi.hg
  have hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hivw : ivR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hscr : ScrIn (S s₀) s₀.wr := ⟨2176, by decide, by decide, by rw [hp.wr]; simp⟩
  have d96 : ∀ r ∈ [(⟨S s₀, 96⟩ : Region)], (dataR s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_scr.sub_right (Region.sub_prefix (by omega_using []))
  unfold decGroup
  -- The block at `iv`.
  let u := s.setV (A 0) (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  let t := u.write .x .x6 (u.read .x .x4 - BitVec.ofNat 64 1)
  have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
    show (if r = Reg.x6 then _ else s.gpr r) = _
    rw [ite_eq_right hr]
  have t6 : t.gpr .x6 = BitVec.ofNat 64 (N s₀ - 8 * g - 1) := by
    have e : t.gpr .x6 = s.gpr .x4 - BitVec.ofNat 64 1 := by
      simp [t, u, State.write, State.read, State.setV]
    rw [e, hi.x4, Offset.ofNat_sub_ofNat (by omega_using [hg])]
  have tA0 : t.v (A 0) = chaining s₀ (8 * g) := by
    have e : t.v (A 0) = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 := by
      simp [t, u, State.write, State.setV]
    rw [e, hi.x2, BitVec.add_zero]
    exact hi.chain
  refine WP.seq (WP.of_runBlock ⟨t, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide) (by
      rw [hi.x2, BitVec.add_zero, hi.rd, hi.wr]
      exact ⟨ivR s₀, List.mem_append_right _ hivw, Region.contains_self _ _⟩), runStep_some,
      runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  -- The blocks before the others.
  refine WP.seq (WP.mono (Q := fun (s₁ : State) =>
      (∀ i < 8, 8 * g + i < N s₀ → s₁.v (A i) = chaining s₀ (8 * g + i)) ∧
      (∀ r, r ≠ .x6 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr) ?_
    fun s₁ ⟨hA, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  · refine WP.ite _ (eval_nz t6 (by omega_using [n16])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : 0 + 1 < N s₀ - 8 * g := by
        have : N s₀ - 8 * g - 1 ≠ 0 := by simpa using hb
        omega_using [this]
      refine loadPrev_wp 6 0 rfl (s := t) (c := N s₀ - 8 * g) ((tg .x4 (by decide)).trans hi.x4)
        hlt (by omega_using [n16]) (fun i hi7 hic => ⟨dataR s₀, List.mem_append_right _ (by
            show _ ∈ s.wr; rw [hi.wr]; exact hdat), by
          rw [tg .x3 (by decide), hi.x3, blk_addr]
          exact Offset.contains_base _ (by omega_using [hic]) (by omega_using [hic, n16])⟩)
        fun s₁ hv ho hg₁ hm₁ hrd₁ hwr₁ => ⟨fun i hi8 hin => ?_,
          fun r hr => (hg₁ r hr).trans (tg r hr), hm₁, hrd₁, hwr₁⟩
      cases i with
      | zero =>
        rw [ho (A 0) fun j _ hj7 => fun e => by
          have := A_inj 0 (by decide) (j + 1) (by omega_using [hj7]) e
          omega_using [this]]
        exact tA0
      | succ j =>
        rw [hv j (Nat.zero_le _) (by omega_using [hi8]) (by omega_using [hin]), tg .x3 (by decide),
          hi.x3, blk_addr]
        show s.mem.readW _ 128 = _
        rw [original_word hi.data (by omega_using []) (by omega_using [hin])]
        rfl
    · have h1 : N s₀ - 8 * g = 1 := by
        have : N s₀ - 8 * g - 1 = 0 := by simpa using hb
        omega_using [this, hg]
      refine WP.block_nil ⟨fun i _ hin => ?_, tg, rfl, rfl, rfl⟩
      have : i = 0 := by omega_using [hin, h1]
      subst this
      exact tA0
  -- The cipher.
  have hb₁ : s₁.gpr sb = S s₀ := (hg₁ sb (by decide)).trans hi.x5
  have hpe : EncPre s₁ (R s₀) (wK s₀) :=
    ⟨by rw [hb₁, hwr₁, hi.wr]; exact hscr, hR, (hg₁ .x1 (by decide)).trans hi.x1,
      by rw [hm₁, hb₁]; exact hi.keys⟩
  refine WP.seq (WP.mono (encrypt8_cryptOk hpe (inRel_st (QA s₁))) fun s₂ h₂ => ?_)
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
  have hB : ∀ i, 0 ≤ i → i < 8 → 8 * g + i < N s₀ → ∀ t < 16, vbyte (s₂.v (B i)) t =
      (Spec.Aes.cipher (R s₀) (wK s₀) (st (chaining s₀ (8 * g + i)))).getD t 0 := by
    intro i _ hi8 hin t ht
    rw [vbyte_of_inRel hin₂ hi8 ht]
    show (Spec.Aes.cipher _ _ (st (s₁.v (A i)))).getD t 0 = _
    rw [hA i hi8 hin]
  -- The blocks.
  refine WP.seq (cfbFrom_wp 7 0 rfl (s := s₂) (s₀ := s₀) (g := g)
    ((keep₂ .x3 (by decide) (by decide) (by decide) (by decide)).trans hi.x3)
    ((keep₂ .x4 (by decide) (by decide) (by decide) (by decide)).trans hi.x4)
    (by omega_using [hg]) n16 (by rw [wr₂]; exact hdat) data₂ hB
    fun s₄ d₄ c₄ f₄ g₄ rd₄ wr₄ => ?_)
  -- The last ciphertext block, to `iv`.
  have x2₄ : s₄.gpr .x2 = Iv s₀ := (g₄ .x2 (by decide)).trans x2₂
  let s₅ : State := { s₄ with mem := s₄.mem.write (s₄.gpr .x2 + BitVec.ofNat 64 0) 16 (s₄.v .v31) }
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_strq (off := 0) (by decide) (by
      rw [x2₄, BitVec.add_zero, wr₄, wr₂]
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
          rw [g₄ .x3 (by decide), keep₂ .x3 (by decide) (by decide) (by decide) (by decide), hi.x3,
            BitVec.add_assoc, ← BitVec.ofNat_add,
            show 16 * (8 * g) + 128 = 16 * (8 * (g + 1)) by omega_using []]
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

/-! ## The function -/

/-- One block, by the tables. -/
theorem decOne_wp {s : State} (hp : UPre s) (hN : (s.gpr .x4).toNat = 1) :
    WP isa decOne s (NDone (chaining s) (output s) s) := by
  have hivw : ivR s ∈ s.wr := by rw [hp.wr]; simp
  have hdat : (⟨Dp s, 16 * 1⟩ : Region) ∈ s.wr := by
    have : (⟨Dp s, 16 * (s.gpr .x4).toNat⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
    rwa [hN] at this
  have dID : Region.Disjoint (ivR s) ⟨Dp s, 16 * 1⟩ := by
    have : Region.Disjoint (ivR s) ⟨Dp s, 16 * (s.gpr .x4).toNat⟩ := hp.iv_data
    rwa [hN] at this
  unfold decOne
  -- The block at `iv`.
  let a := s.setV .v0 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  refine WP.seq (WP.of_runBlock ⟨a, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide)
      ⟨ivR s, List.mem_append_right _ hivw, by
        rw [BitVec.add_zero]; exact Region.contains_self _ _⟩, runStep_some, runBlock_nil], ?_⟩)
  have av : a.v .v0 = chaining s 0 := by
    show (s.setV _ _).v .v0 = _
    rw [v_setV_self, BitVec.add_zero]
    rfl
  -- The cipher.
  refine WP.seq (WP.mono (Proof.Aes.AArch64.Vperm.core_ok (s := a) (K := W s) (R := R s)
    (by show _ ∈ s.rd; rw [hp.rd]; simp) rfl (by
      show s.gpr .x1 = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) hp.rounds) fun b ⟨bst, bg, bm, brd, bwr, _⟩ => ?_)
  have b2 : b.gpr .x2 + BitVec.ofNat 64 0 = Iv s := by
    rw [BitVec.add_zero]; exact bg _ (by decide) (by decide) (by decide)
  have b3 : b.gpr .x3 + BitVec.ofNat 64 0 = Dp s := by
    rw [BitVec.add_zero]; exact bg _ (by decide) (by decide) (by decide)
  have hm : b.mem = s.mem := bm
  have hinD : InRegions b.wr (b.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [b3, bwr]
    exact ⟨_, hdat, by
      have := Offset.contains_base (Dp s) (d := 0) (n := 16) (k := 16 * 1) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩
  have hinI : InRegions b.wr (b.gpr .x2 + BitVec.ofNat 64 0) 16 := by
    rw [b2, bwr]
    exact ⟨ivR s, hivw, Region.contains_self _ _⟩
  -- The data, and the block to continue from.
  let c₁ := b.setV .v1 (b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)
  let c₂ := c₁.setV .v0 (c₁.v .v0 ^^^ c₁.v .v1)
  let c₃ : State := { c₂ with mem := c₂.mem.write (c₂.gpr .x3 + BitVec.ofNat 64 0) 16 (c₂.v .v0) }
  let c₄ : State := { c₃ with mem := c₃.mem.write (c₃.gpr .x2 + BitVec.ofNat 64 0) 16 (c₃.v .v1) }
  refine WP.of_runBlock ⟨c₄, by
    rw [runBlock_cons, Proof.Aes.AArch64.Aese.exec_ldrq (off := 0) (by decide)
      (Proof.Aes.AArch64.Aese.inRegions_wr hinD), runStep_some, runBlock_cons,
      show exec (veor .v0 .v0 .v1) c₁ = some c₂ from rfl, runStep_some, runBlock_cons,
      Proof.Aes.AArch64.Aese.exec_strq (s := c₂) (off := 0) (by decide) hinD, runStep_some,
      runBlock_cons, Proof.Aes.AArch64.Aese.exec_strq (s := c₃) (off := 0) (by decide) hinI,
      runStep_some, runBlock_nil], ?_⟩
  have v1₂ : c₂.v .v1 = s.mem.readW (Dp s) 128 := by
    show (c₁.setV _ _).v .v1 = _
    rw [v_setV_of_ne _ _ (by decide)]
    show (b.setV _ _).v .v1 = _
    rw [v_setV_self, b3, hm]
  have v0₂ : c₂.v .v0 = b.v .v0 ^^^ s.mem.readW (Dp s) 128 := by
    show (c₁.setV _ _).v .v0 = _
    rw [v_setV_self]
    show (b.setV _ _).v .v0 ^^^ c₁.v .v1 = _
    rw [v_setV_of_ne _ _ (by decide)]
    show _ ^^^ (b.setV _ _).v .v1 = _
    rw [v_setV_self, b3, hm]
  have m₄ : c₄.mem = (s.mem.write (Dp s) 16 (b.v .v0 ^^^ s.mem.readW (Dp s) 128)).write (Iv s) 16
      (s.mem.readW (Dp s) 128) := by
    show (b.mem.write (b.gpr .x3 + BitVec.ofNat 64 0) 16 (c₂.v .v0)).write
      (b.gpr .x2 + BitVec.ofNat 64 0) 16 (c₂.v .v1) = _
    rw [b2, b3, hm, v0₂, v1₂]
  -- What was stored.
  have e0 : Dp s + BitVec.ofNat 64 (16 * 0) = Dp s := by rw [Nat.mul_zero]; exact BitVec.add_zero _
  have hinv : EcbInv s.mem s.mem (Dp s) 1 0 (output s) := fun i _ => by simp
  have hs := Proof.Aes.AArch64.Aese.ecbInv_write (m₀ := s.mem) (m := s.mem) (D := Dp s) (n := 1)
    (k := 0) (F := output s) (v := b.v .v0 ^^^ s.mem.readW (Dp s) 128) (by decide) (by decide)
    hinv fun t ht => by
      rw [vbyte_xor, ← VG.Proof.Aes.Vector.getD_st _ ht, bst, av, output, getD_ofFn ht]
      show _ = _ ^^^ vbyte (s.mem.readW (Dp s + BitVec.ofNat 64 (16 * 0)) 128) t
      rw [e0]
      rfl
  rw [e0] at hs
  have hf : Frame [ivR s] (s.mem.write (Dp s) 16 (b.v .v0 ^^^ s.mem.readW (Dp s) 128)) c₄.mem := by
    rw [m₄]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc : c₄.mem.readW (Iv s) 128 = s.mem.readW (Dp s) 128 := by
    have h : ((s.mem.write (Dp s) 16 (b.v .v0 ^^^ s.mem.readW (Dp s) 128)).write (Iv s) 16
        (s.mem.readW (Dp s) 128)).readW (Iv s) 128 = s.mem.readW (Dp s) 128 :=
      Mem.readW_writeW_self _ (Iv s) 16 _ (by decide)
    rw [m₄]; exact h
  refine ⟨?_, ?_⟩
  · show c₄.mem.readW (Iv s) 128 = chaining s (s.gpr .x4).toNat
    rw [hN, hc]
    show _ = s.mem.readW (Dp s + BitVec.ofNat 64 (16 * 0)) 128
    rw [e0]
  · show EcbInv s.mem c₄.mem (Dp s) (s.gpr .x4).toNat (s.gpr .x4).toNat (output s)
    rw [hN]
    exact ecbInv_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dID.symm) (by decide) hs.1

theorem decrypt_wp {s₀ : State} (hp : UPre s₀) :
    WP isa decrypt s₀ fun t => (modeAArch64 (cfbMode false)).post s₀ t := by
  unfold decrypt
  let s₁ := s₀.write .x .x6 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : UPre s₁ := ⟨hp.rd, hp.wr, hp.sch_iv, hp.sch_data, hp.sch_scr, hp.iv_data, hp.iv_scr,
    hp.data_scr, hp.iv_wrap, hp.data_wrap, hp.scr_wrap, hp.rounds⟩
  have hpost : ∀ t, (modeAArch64 (cfbMode false)).post s₁ t =
      (modeAArch64 (cfbMode false)).post s₀ t := fun _ => rfl
  refine WP.ite (s₀.gpr .x4 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x4 : s₀.gpr .x4 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x4) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h4 : (s₁.gpr .x4).toNat = 1 := by
      show (s₀.gpr .x4).toNat = 1
      rw [x4]; rfl
    exact WP.mono (decOne_wp hp₁ h4) fun t hd => by rw [← hpost t]; exact post_of_done hd
  · exact WP.mono (whole_wp hp₁ rfl fun _ _ hi => nGroup_ok hp₁ hi) fun t hd => by
      rw [← hpost t]; exact post_of_done hd

theorem correct (s : State) (hp : (modeAArch64 (cfbMode false)).pre s) :
    ∃ tr t, Exec isa decrypt s tr t ∧ abiPreserved s t ∧
      (modeAArch64 (cfbMode false)).post s t := by
  obtain ⟨tr, t, he, hq, hg⟩ :=
    WP.gprs (rs := preserved) (decrypt_wp (UPre.of hp)) (by lit_decide) (by lit_decide)
  exact ⟨tr, t, he, ⟨hg, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hq⟩

theorem ct : ConstantTime isa (modeAArch64 (cfbMode false)).pre
    (modeAArch64 (cfbMode false)).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem verified :
    Verified AArch64.target decrypt (Proof.AesCfb.decryptRoundsContract AArch64.abi) :=
  Verified.of_correct correct ct Decrypt.implies

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

theorem decrypt_keepsV : decrypt.allInstrs keepsV = true := by lit_decide

end VG.Proof.AesCfb.AArch64.Neon
