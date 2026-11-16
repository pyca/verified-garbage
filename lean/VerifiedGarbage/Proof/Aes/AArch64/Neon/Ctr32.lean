module

public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
meta import VerifiedGarbage.Impl.Aes.AArch64.Neon.Ctr32
meta import VerifiedGarbage.Proof.Aes.AArch64.OneBlock
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES counter mode, bitsliced in AdvSIMD registers, on AArch64

`ctr32N_correct` and `ctr32N_ct` prove `Impl.Aes.AArch64.Neon.ctr32N`
against `Proof.Aes.ctr32AArch64`, and `ctr32ToN_correct` and `ctr32ToN_ct` its
out-of-place form against `Proof.Aes.ctr32ToAArch64`: one proof (`correct`)
of the bitsliced code `ctr32Gen to` for both, with the precondition, the postcondition and the
lemmas about the counter blocks of the code with the Cryptographic Extension
(`Aese/Ctr32.lean`), whose counter and output registers this code shares.

Before group `g` (`CInv`): the counter `c₀ + 8 g` in `w10`, the round keys
bitsliced in the scratch buffer, and the first `8 g` output blocks written
(`DataInvM`). A group builds eight counter blocks (`Aese.ctrs_ok`), encrypts
them (`encrypt8_ok`) and XORs those of the blocks left into the data
(`xorFrom_wp`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.AArch64 VG.AArch64.RegUpd VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.Impl.Aes.AArch64 (ctrFew)
open VG.Proof.Aes.Vector (st vbyte_readW vbyte_xor)
open VG.Impl.Aes.AArch64.Aese (ctrs regs8 xor1 advO ctrStore outR)
open VG.Proof.Aes.AArch64.Aese (Pre nb nr cp dp dR sch cb c0 kst op oR Post ctrVec)

/-! ## The registers -/

theorem B_ne31 : ∀ i < 8, B i ≠ .v31 := by decide

theorem regs8_eq : regs8 = (List.range 8).map A := rfl

theorem outR_ne (to : Bool) : outR to ≠ .x6 ∧ outR to ≠ .x7 ∧ outR to ≠ kp ∧ outR to ≠ cnt ∧
    outR to ≠ .x12 ∧ outR to ≠ .x4 ∧ outR to ≠ .x10 := by
  cases to <;> decide

theorem sw_ofNat (c : Nat) : (BitVec.ofNat 64 c).setWidth 32 = BitVec.ofNat 32 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd c (Nat.pow_dvd_pow 2 (by decide))

/-! ## The XOR into the data -/

/-- Block `8 g + k`: the keystream block in `B k` XORed into the data,
stored to the output. -/
theorem xorStep (to : Bool) {s : State} {m₀ : Mem} {D O : Addr} {n g k : Nat} {ks : Nat → Byte}
    (hDO : O = D ∨ Region.Disjoint ⟨D, 16 * n⟩ ⟨O, 16 * n⟩)
    (h3 : s.gpr .x3 = D + BitVec.ofNat 64 (16 * (8 * g)))
    (ho : s.gpr (outR to) = O + BitVec.ofNat 64 (16 * (8 * g))) (hk8 : k < 8)
    (hkn : 8 * g + k < n) (hn : 16 * n < 2 ^ 64) (hrd : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr)
    (hwr : (⟨O, 16 * n⟩ : Region) ∈ s.wr) (hinv : DataInvM m₀ s.mem D O n (8 * g + k) ks)
    (hsrc : ∀ i, 16 * (8 * g + k) ≤ i → i < 16 * n →
      s.mem (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i))
    (hks : ∀ t < 16, vbyte (s.v (B k)) t = ks (16 * (8 * g + k) + t)) :
    WP isa (.block (xor1 to (B k) k)) s fun s' =>
      DataInvM m₀ s'.mem D O n (8 * g + k + 1) ks ∧ Frame [⟨O, 16 * n⟩] s.mem s'.mem ∧
      (∀ i, 16 * (8 * g + k + 1) ≤ i → i < 16 * n →
        s'.mem (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i)) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ B k → r ≠ .v31 → s'.v r = s.v r) := by
  have ha : s.gpr .x3 + BitVec.ofNat 64 (16 * k) = D + BitVec.ofNat 64 (16 * (8 * g + k)) := by
    rw [h3, Offset.add_add_eq D (show 16 * (8 * g) + 16 * k = 16 * (8 * g + k) by omega_using [])]
  have hoo : s.gpr (outR to) + BitVec.ofNat 64 (16 * k) =
      O + BitVec.ofNat 64 (16 * (8 * g + k)) := by
    rw [ho, Offset.add_add_eq O (show 16 * (8 * g) + 16 * k = 16 * (8 * g + k) by omega_using [])]
  refine WP.mono (Aese.xor1_ok to (B k) k s (B_ne31 k hk8) (by omega_using [hk8])
      (by rw [ha]; exact ⟨_, hrd, Offset.contains_base D (by omega_using [hkn])
        (by omega_using [hn, hkn])⟩)
      (by rw [hoo]; exact ⟨_, hwr, Offset.contains_base O (by omega_using [hkn])
        (by omega_using [hn, hkn])⟩))
    fun s₁ ⟨m₁, g₁, _, rd₁, wr₁, v₁⟩ => ?_
  rw [ha, hoo] at m₁
  have hst := dataInvM_store1 hn hkn hinv
    (v := s.v (B k) ^^^ s.mem.readW (D + BitVec.ofNat 64 (16 * (8 * g + k))) 128) fun t ht => by
      rw [vbyte_xor, vbyte_readW _ _ ht,
        Offset.add_add_eq D (show 16 * (8 * g + k) + t = 16 * (8 * g + k) + t from rfl),
        hsrc _ (by omega_using []) (by omega_using [hkn, ht]), hks t ht]
  rw [← m₁] at hst
  exact ⟨hst.1, hst.2, fun i h1 h2 => src_keep (m₃ := s.mem) (j := 8 * g + k) hDO hn hsrc hst.2
    hst.1 i h1 (by omega_using [h1]) h2, g₁, rd₁, wr₁, v₁⟩

/-- The keystream blocks `k`, … of group `g` XORed into the data, while
there are blocks left. -/
theorem xorFrom_wp (to : Bool) (fuel : Nat) : ∀ (k : Nat), k + fuel = 7 → ∀ {s : State} {m₀ : Mem}
    {D O : Addr} {n g : Nat} {ks : Nat → Byte} {P : State → Prop},
    (O = D ∨ Region.Disjoint ⟨D, 16 * n⟩ ⟨O, 16 * n⟩) →
    s.gpr .x3 = D + BitVec.ofNat 64 (16 * (8 * g)) →
    s.gpr (outR to) = O + BitVec.ofNat 64 (16 * (8 * g)) →
    s.gpr .x4 = BitVec.ofNat 64 (n - 8 * g) →
    8 * g + k < n → 16 * n < 2 ^ 64 → (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr →
    (⟨O, 16 * n⟩ : Region) ∈ s.wr → DataInvM m₀ s.mem D O n (8 * g + k) ks →
    (∀ i, 16 * (8 * g + k) ≤ i → i < 16 * n →
      s.mem (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i)) →
    (∀ i, k ≤ i → i < 8 → 8 * g + i < n → ∀ t < 16,
      vbyte (s.v (B i)) t = ks (16 * (8 * g + i) + t)) →
    (∀ s', DataInvM m₀ s'.mem D O n (min n (8 * g + 8)) ks → Frame [⟨O, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ .x6 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') →
    WP isa (xorFrom to fuel k) s P := by
  induction fuel with
  | zero =>
    intro k hk s m₀ D O n g ks P hDO h3 ho h4 hkn hn hrd hwr hinv hsrc hks hP
    have hk7 : k = 7 := by omega_using [hk]
    subst hk7
    simp only [xorFrom]
    refine WP.mono (xorStep to hDO h3 ho (by decide) hkn hn hrd hwr hinv hsrc
      (hks 7 (Nat.le_refl _) (by decide) hkn)) fun s₁ ⟨d₁, f₁, _, g₁, rd₁, wr₁, _⟩ => ?_
    refine hP s₁ ?_ f₁ (fun r _ => by rw [g₁]) rd₁ wr₁
    rw [show min n (8 * g + 8) = 8 * g + 7 + 1 by omega_using [hkn]]
    exact d₁
  | succ fuel ih =>
    intro k hk s m₀ D O n g ks P hDO h3 ho h4 hkn hn hrd hwr hinv hsrc hks hP
    have hk8 : k < 8 := by omega_using [hk]
    simp only [xorFrom]
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine WP.mono (xorStep to hDO h3 ho hk8 hkn hn hrd hwr hinv hsrc
      (hks k (Nat.le_refl _) hk8 hkn)) fun s₁ ⟨d₁, f₁, src₁, g₁, rd₁, wr₁, v₁⟩ => ?_
    let t := s₁.write .x .x6 (s₁.read .x .x4 - BitVec.ofNat 64 (k + 1))
    refine WP.of_runBlock ⟨t, by
      rw [runBlock_cons, exec_subImm_x (by omega_using [hk8]), runStep_some, runBlock_nil], ?_⟩
    have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
      show (if r = Reg.x6 then _ else s₁.gpr r) = _
      rw [ite_eq_right hr, g₁]
    have t6 : t.gpr .x6 = BitVec.ofNat 64 (n - 8 * g - (k + 1)) := by
      have e : t.gpr .x6 = s₁.gpr .x4 - BitVec.ofNat 64 (k + 1) := by
        simp [t, State.write, State.read]
      rw [e, g₁, h4, Offset.ofNat_sub_ofNat (by omega_using [hkn])]
    refine WP.ite _ (eval_nz t6 (by omega_using [hn])) (fun hb => ?_) (fun hb => ?_)
    · have hlt : 8 * g + (k + 1) < n := by
        have : n - 8 * g - (k + 1) ≠ 0 := by simpa using hb
        omega_using [this]
      refine ih (k + 1) (by omega_using [hk]) (s := t) (m₀ := m₀) (D := D) (O := O) (n := n)
        (g := g) (ks := ks) hDO ((tg .x3 (by decide)).trans h3)
        ((tg _ (outR_ne to).1).trans ho) ((tg .x4 (by decide)).trans h4) hlt hn
        (by show _ ∈ s₁.rd ++ s₁.wr; rw [rd₁, wr₁]; exact hrd)
        (by show _ ∈ s₁.wr; rw [wr₁]; exact hwr) d₁ src₁
        (fun i hki hi8 hin tt ht => by
          show vbyte (s₁.v (B i)) tt = _
          rw [v₁ _ (fun h => by
            have := B_inj i hi8 k hk8 h
            omega_using [this, hki]) (B_ne31 i hi8)]
          exact hks i (by omega_using [hki]) hi8 hin tt ht)
        fun s' hd hf hg hrd' hwr' => hP s' hd (f₁.trans hf)
          (fun r hr => (hg r hr).trans (tg r hr)) (hrd'.trans rd₁) (hwr'.trans wr₁)
    · have heq : n = 8 * g + k + 1 := by
        have : n - 8 * g - (k + 1) = 0 := by simpa using hb
        omega_using [this, hkn]
      refine WP.block_nil (hP t ?_ f₁ tg rd₁ wr₁)
      rw [show min n (8 * g + 8) = 8 * g + k + 1 by omega_using [heq, hk8]]
      exact d₁

/-- On to the next group, if more than eight blocks were left (`c`), with
the counter past the blocks done. -/
theorem ctrAdvance_wp (to : Bool) {s : State} {c : Nat} (h4 : s.gpr .x4 = BitVec.ofNat 64 c)
    (hc : 0 < c) (hc64 : c < 2 ^ 64) {P : State → Prop}
    (h : ∀ s', (8 < c → s'.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 128 ∧
        s'.gpr (outR to) = s.gpr (outR to) + BitVec.ofNat 64 128 ∧
        s'.gpr .x4 = BitVec.ofNat 64 (c - 8) ∧
        s'.read .w .x10 = s.read .w .x10 + BitVec.ofNat 32 8) →
      (¬ 8 < c → s'.gpr .x4 = BitVec.ofNat 64 0 ∧
        s'.read .w .x10 = s.read .w .x10 + BitVec.ofNat 32 c) →
      (∀ g, g ≠ .x6 → g ≠ .x3 → g ≠ .x4 → g ≠ .x10 → g ≠ .x14 → s'.gpr g = s.gpr g) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (ctrAdvance to) s P := by
  unfold ctrAdvance
  let u := s.write .x .x6 (s.read .x .x4 - BitVec.ofNat 64 1)
  let t := u.write .x .x6 (u.read .x .x6 >>> 3)
  have ht : runBlock isa [.subImm .x .x6 .x4 1, .lsr .x .x6 .x6 3] s = some t := by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil]
  have tg : ∀ r, r ≠ .x6 → t.gpr r = s.gpr r := fun r hr => by
    simp [t, u, State.write, hr]
  have t6 : t.gpr .x6 = BitVec.ofNat 64 (c - 1) >>> 3 := by
    have e : t.gpr .x6 = (s.gpr .x4 - BitVec.ofNat 64 1) >>> 3 := by
      simp [t, u, State.write, State.read]
    rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [hc])]
  have hev : AArch64.eval (.nonzero .x .x6) t = some (decide (8 ≤ c - 1)) := by
    simp only [AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, t6,
      shr3_ne _ (show c - 1 < 2 ^ 64 by omega_using [hc64])]
  refine WP.seq (WP.of_runBlock ⟨t, ht, ?_⟩)
  refine WP.ite _ hev (fun hb => ?_) (fun hb => ?_)
  · have h8 : 8 < c := by
      have : 8 ≤ c - 1 := by simpa using hb
      omega_using [this]
    let w₁ := t.write .w .x10 (t.read .w .x10 + BitVec.ofNat 32 8)
    let w₂ := w₁.write .x .x3 (w₁.read .x .x3 + BitVec.ofNat 64 128)
    let w₃ := w₂.write .x .x4 (w₂.read .x .x4 - BitVec.ofNat 64 8)
    rw [WP.block_append_iff (M := isa)]
    refine WP.of_runBlock ⟨w₃, by
      rw [runBlock_cons, Aese.exec_addImm_w (by decide), runStep_some, runBlock_cons,
        exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have w3 : w₃.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 128 := by
      simp [w₃, w₂, w₁, State.write, State.read, tg .x3 (by decide)]
    have w4 : w₃.gpr .x4 = BitVec.ofNat 64 (c - 8) := by
      have e : w₃.gpr .x4 = s.gpr .x4 - BitVec.ofNat 64 8 := by
        simp [w₃, w₂, w₁, State.write, State.read, tg .x4 (by decide)]
      rw [e, h4, Offset.ofNat_sub_ofNat (by omega_using [h8])]
    have w10 : w₃.gpr .x10 = (s.read .w .x10 + BitVec.ofNat 32 8).setWidth 64 := by
      simp [w₃, w₂, w₁, State.write, State.read, tg .x10 (by decide)]
    have wg : ∀ g, g ≠ .x6 → g ≠ .x3 → g ≠ .x4 → g ≠ .x10 → w₃.gpr g = s.gpr g :=
      fun g g6 g3 g4 g10 => by simp [w₃, w₂, w₁, State.write, g3, g4, g10, tg g g6]
    refine WP.mono (Aese.advO_ok to 128 (by decide) w₃) fun s' ⟨hg, ho, _, hm, hrd, hwr⟩ => ?_
    refine h s' (fun _ => ⟨(hg _ (by decide)).trans w3, ?_, (hg _ (by decide)).trans w4, ?_⟩)
      (fun hn => absurd h8 hn) (fun g g6 g3 g4 g10 g14 => (hg g g14).trans (wg g g6 g3 g4 g10))
      hm hrd hwr
    · cases to with
      | false => exact (hg _ (by decide)).trans w3
      | true =>
        show s'.gpr .x14 = s.gpr .x14 + _
        rw [ho rfl, wg _ (by decide) (by decide) (by decide) (by decide)]
    · show (s'.gpr .x10).setWidth 32 = _
      rw [hg _ (by decide), w10, Aese.sw32]
  · have h8 : ¬ 8 < c := by
      have : ¬ 8 ≤ c - 1 := by simpa using hb
      omega_using [this]
    let w₁ := t.write .w .x10 (t.read .w .x10 + t.read .w .x4)
    refine WP.of_runBlock ⟨w₁.write .x .x4 0, by
      rw [runBlock_cons, exec_add, runStep_some, runBlock_cons, exec_movz_x0, runStep_some,
        runBlock_nil], h _ (fun hn => absurd hn h8) (fun _ => ⟨?_, ?_⟩)
      (fun g g6 g3 g4 g10 g14 => ?_) rfl rfl rfl⟩
    · simp [State.write]
    · have e : (w₁.write .x .x4 0).read .w .x10 = s.read .w .x10 + (s.gpr .x4).setWidth 32 := by
        simp only [w₁, State.write, State.read, ite_true, reduceCtorEq, ite_false,
          tg .x10 (by decide), tg .x4 (by decide)]
        exact Aese.sw32 _
      rw [e, h4, sw_ofNat]
    · simp [w₁, State.write, g4, g10, tg g g6]

/-! ## The precondition and the groups -/

/-- The precondition of both contracts: `Aese.Pre`, and that the scratch
buffer overlaps nothing. -/
structure PreS (to : Bool) (s₀ : State) : Prop where
  pre : Pre to s₀
  s_b : Region.Disjoint ⟨s₀.gpr .x0, 240⟩ ⟨s₀.gpr .x5, 2048⟩
  c_b : Region.Disjoint ⟨cp s₀, 16⟩ ⟨s₀.gpr .x5, 2048⟩
  d_b : Region.Disjoint (dR s₀) ⟨s₀.gpr .x5, 2048⟩
  o_b : Region.Disjoint (oR s₀ to) ⟨s₀.gpr .x5, 2048⟩

theorem preS_of {s₀ : State} (h : Proof.Aes.ctr32AArch64.pre s₀) : PreS false s₀ := by
  have hp := Aese.pre_of h
  obtain ⟨_, _, _, _, h5, _, h7, h8, _, _⟩ := h
  exact ⟨hp, h5, h7, h8, h8⟩

theorem preSTo_of {s₀ : State} (h : Proof.Aes.ctr32ToAArch64.pre s₀) : PreS true s₀ := by
  have hp := Aese.preTo_of h
  obtain ⟨_, _, _, _, h5, _, _, h8, _, h10, h11, _, _, _⟩ := h
  exact ⟨hp, h5, h8, h10, h11⟩

namespace PreS
variable {to : Bool} {s₀ : State} (hp : PreS to s₀)
include hp

theorem scr : (⟨s₀.gpr .x5, 2048⟩ : Region) ∈ s₀.wr := by rw [hp.pre.wr]; simp

theorem sched : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hp.pre.rd]; simp

/-- Memory that only differs from the initial memory in the output and the
scratch buffer. -/
theorem cbF {m : Mem} (hf : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem m) :
    Spec.Gcm.blockAt m (cp s₀) = cb s₀ :=
  Proof.Gcm.blockAt_congr fun _ hk => hf.bytes (R := ⟨cp s₀, 16⟩)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hp.pre.c_o, hp.c_b⟩)
    (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

/-- The data not yet done is as it was. -/
theorem srcF {m : Mem} {c : Nat} (hf : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem m)
    (hd : DataInvM s₀.mem m (dp s₀) (op s₀ to) (nb s₀) c (kst s₀)) :
    ∀ i, 16 * c ≤ i → i < 16 * nb s₀ →
      m (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  have hn := hp.pre.nb16
  cases to with
  | false =>
    intro i h1 h2
    have := hd i h2
    rw [ite_eq_right (by omega_using [h1])] at this
    exact this
  | true =>
    intro i _ h2
    exact hf.bytes (R := dR s₀)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hp.pre.src rfl, hp.d_b⟩)
      hn h2

end PreS

/-- Before group `g`. -/
structure CInv (to : Bool) (s₀ : State) (g : Nat) (s : State) : Prop where
  hg : 8 * g < nb s₀
  x1 : s.gpr .x1 = BitVec.ofNat 64 (nr s₀)
  x2 : s.gpr .x2 = cp s₀
  x3 : s.gpr .x3 = dp s₀ + BitVec.ofNat 64 (16 * (8 * g))
  xo : s.gpr (outR to) = op s₀ to + BitVec.ofNat 64 (16 * (8 * g))
  x4 : s.gpr .x4 = BitVec.ofNat 64 (nb s₀ - 8 * g)
  x5 : s.gpr sb = s₀.gpr .x5
  x10 : s.read .w .x10 = c0 s₀ + BitVec.ofNat 32 (8 * g)
  frame : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem s.mem
  keys : KeysAt s.mem (s₀.gpr .x5) (nr s₀) (sch s₀)
  data : DataInvM s₀.mem s.mem (dp s₀) (op s₀ to) (nb s₀) (8 * g) (kst s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- After the last group. -/
structure CDone (to : Bool) (s₀ : State) (s : State) : Prop where
  x2 : s.gpr .x2 = cp s₀
  x10 : s.read .w .x10 = c0 s₀ + BitVec.ofNat 32 (nb s₀)
  frame : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem s.mem
  data : DataInvM s₀.mem s.mem (dp s₀) (op s₀ to) (nb s₀) (nb s₀) (kst s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- One group: from before group `g`, to after the last group (`x4` zero) or
before group `g + 1`. -/
theorem ctrGroup_ok {to : Bool} {s₀ : State} (hp : PreS to s₀) {g : Nat} {s : State}
    (hi : CInv to s₀ g s) :
    WP isa (ctrGroup to) s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧ CDone to s₀ s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ CInv to s₀ (g + 1) s') := by
  have hR := hp.pre.rounds
  have hR14 : nr s₀ ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have n16 := hp.pre.n16
  have hg := hi.hg
  have hne := outR_ne to
  unfold ctrGroup
  -- The counter blocks.
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 16 := by
    rw [hi.rd, hi.wr, hi.x2]; exact hp.pre.ctr_in
  refine WP.seq (WP.mono (Aese.ctrs_ok regs8 0 s (by decide) (by decide) hin) fun s₁ ⟨e₁, f₁⟩ => ?_)
  -- Their encryption.
  have hb₁ : s₁.gpr sb = s₀.gpr .x5 := (f₁.gpr _ (by decide)).trans hi.x5
  have hpe : EncPre s₁ (nr s₀) (sch s₀) :=
    ⟨by rw [hb₁, f₁.wr, hi.wr]; exact .of_mem hp.scr, hR, (f₁.gpr _ (by decide)).trans hi.x1,
      by rw [f₁.mem, hb₁]; exact hi.keys⟩
  refine WP.seq (WP.mono (encrypt8_cryptOk hpe (inRel_st (QA s₁))) fun s₂ h₂ => ?_)
  obtain ⟨hc₂, hin₂⟩ := h₂
  have keep₂ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → r ≠ cnt → r ≠ .x12 → s₂.gpr r = s.gpr r :=
    fun r h6 h7 hk hc h12 => (hc₂.keep r h6 h7 hk hc).trans (f₁.gpr r (by simpa using h12))
  have fr₂ : Frame [⟨s₀.gpr .x5, 96⟩] s.mem s₂.mem := by
    have := hc₂.frame
    rwa [hb₁, f₁.mem] at this
  have data₂ : DataInvM s₀.mem s₂.mem (dp s₀) (op s₀ to) (nb s₀) (8 * g) (kst s₀) :=
    dataInvM_frame fr₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.o_b.sub_right (Region.sub_prefix (by omega_using []))) n16 hi.data
  have frame₂ : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem s₂.mem :=
    hi.frame.trans (fr₂.sub fun r hr => ⟨⟨s₀.gpr .x5, 2048⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_using [])⟩)
  have hks : ∀ i, 0 ≤ i → i < 8 → 8 * g + i < nb s₀ → ∀ t < 16,
      vbyte (s₂.v (B i)) t = kst s₀ (16 * (8 * g + i) + t) := by
    intro i _ hi8 _ t ht
    have hA : s₁.v (A i) = ctrVec s.mem (s.gpr .x2) (s.read .w .x10) (0 + i) := by
      have := e₁ i (by simpa [regs8_eq] using hi8)
      simpa [regs8_eq] using this
    show _ = keyStream _ _ _ _
    rw [Aese.keyStream_eq ht, vbyte_of_inRel hin₂ hi8 ht]
    show (Spec.Aes.cipher _ _ (st (s₁.v (A i)))).getD t 0 = _
    rw [hA, hi.x10, hi.x2, ctrVec, c0, Nat.zero_add, BitVec.add_assoc, ← BitVec.ofNat_add,
      ← hp.cbF hi.frame, Aese.ctrVec_st]
  -- The XOR into the data.
  have x3₂ : s₂.gpr .x3 = dp s₀ + BitVec.ofNat 64 (16 * (8 * g)) :=
    (keep₂ .x3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.x3
  have xo₂ : s₂.gpr (outR to) = op s₀ to + BitVec.ofNat 64 (16 * (8 * g)) :=
    (keep₂ _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1).trans hi.xo
  have x4₂ : s₂.gpr .x4 = BitVec.ofNat 64 (nb s₀ - 8 * g) :=
    (keep₂ .x4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.x4
  refine WP.seq (xorFrom_wp to 7 0 rfl hp.pre.dDO x3₂ xo₂ x4₂ (by omega_using [hg]) n16
    (by rw [hc₂.rd, hc₂.wr, f₁.rd, f₁.wr, hi.rd, hi.wr]; exact hp.pre.dat)
    (by rw [hc₂.wr, f₁.wr, hi.wr]; exact hp.pre.out) data₂ (hp.srcF frame₂ data₂) hks
    fun s₃ d₃ f₃ g₃ rd₃ wr₃ => ?_)
  -- On to the next group.
  have x10₃ : s₃.read .w .x10 = c0 s₀ + BitVec.ofNat 32 (8 * g) := by
    show (s₃.gpr .x10).setWidth 32 = _
    rw [g₃ _ (by decide), keep₂ .x10 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hi.x10
  refine ctrAdvance_wp to (c := nb s₀ - 8 * g) ((g₃ .x4 (by decide)).trans x4₂)
    (by omega_using [hg]) (by omega_using [n16]) fun s₄ hmore hlast g₄ m₄ rd₄ wr₄ => ?_
  have frame₄ : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem s₄.mem := by
    rw [m₄]; exact frame₂.trans (f₃.mono (by simp))
  have hrd₄ : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hc₂.rd, f₁.rd, hi.rd]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, wr₃, hc₂.wr, f₁.wr, hi.wr]
  have x2₄ : s₄.gpr .x2 = cp s₀ := by
    rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide),
      keep₂ .x2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hi.x2
  by_cases h8 : 8 < nb s₀ - 8 * g
  · obtain ⟨x3₄, xo₄, x4₄, x10₄⟩ := hmore h8
    refine .inr ⟨(eval_nz x4₄ (by omega_using [n16])).trans (by
        simp [show nb s₀ - 8 * g - 8 ≠ 0 by omega_using [h8]]),
      { hg := by omega_using [h8]
        x1 := by
          rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide),
            keep₂ .x1 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hi.x1
        x2 := x2₄
        x3 := by
          rw [x3₄, g₃ .x3 (by decide), x3₂, BitVec.add_assoc, ← BitVec.ofNat_add,
            show 16 * (8 * g) + 128 = 16 * (8 * (g + 1)) by omega_using []]
        xo := by
          rw [xo₄, g₃ _ hne.1, xo₂, BitVec.add_assoc, ← BitVec.ofNat_add,
            show 16 * (8 * g) + 128 = 16 * (8 * (g + 1)) by omega_using []]
        x4 := by rw [x4₄, show nb s₀ - 8 * g - 8 = nb s₀ - 8 * (g + 1) by omega_using []]
        x5 := by
          rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide),
            keep₂ sb (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hi.x5
        x10 := by
          rw [x10₄, x10₃, BitVec.add_assoc, ← BitVec.ofNat_add,
            show 8 * g + 8 = 8 * (g + 1) by omega_using []]
        frame := frame₄
        keys := by
          rw [m₄]
          refine keysAt_frame hR14 f₃ (fun r hr => ?_) (keysAt_frame hR14 fr₂ (fun r hr => ?_) hi.keys)
          · simp only [List.mem_singleton] at hr; subst hr
            exact (hp.o_b.sub_right (Offset.sub_base _ (by omega_using []))).symm
          · simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
        data := by
          rw [m₄]
          have := d₃
          rwa [show min (nb s₀) (8 * g + 8) = 8 * (g + 1) by omega_using [h8]] at this
        rd := hrd₄
        wr := hwr₄ }⟩
  · obtain ⟨x4₄, x10₄⟩ := hlast h8
    refine .inl ⟨(eval_nz x4₄ (by decide)).trans (by simp), x2₄, ?_, frame₄, ?_, hrd₄, hwr₄⟩
    · rw [x10₄, x10₃, BitVec.add_assoc, ← BitVec.ofNat_add,
        show 8 * g + (nb s₀ - 8 * g) = nb s₀ by omega_using [hg]]
    · rw [m₄]
      have := d₃
      rwa [show min (nb s₀) (8 * g + 8) = nb s₀ by omega_using [h8, hg]] at this

/-- The loop over the groups. -/
theorem ctrGroups_ok {to : Bool} {s₀ : State} (hp : PreS to s₀) {s : State}
    (hi : CInv to s₀ 0 s) :
    WP isa (.loop (ctrGroup to) (.nonzero .x .x4)) s (CDone to s₀) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = nb s₀ - 8 * g ∧ CInv to s₀ g s)
    (fun k s hs => ?_) (nb s₀) s ⟨0, by simp, hi⟩
  obtain ⟨g, rfl, hi⟩ := hs
  refine WP.mono (ctrGroup_ok hp hi) fun s' h => ?_
  rcases h with ⟨hz, hd⟩ | ⟨hz, hi'⟩
  · exact .inl ⟨hz, hd⟩
  · exact .inr ⟨hz, nb s₀ - 8 * (g + 1), by have := hi'.hg; omega_using [this], g + 1, rfl, hi'⟩

/-! ## The whole function -/

/-- The final counter written back. -/
theorem ctrStore_ok {to : Bool} {s₀ : State} (hp : PreS to s₀) {s : State} (hI : CDone to s₀ s) :
    WP isa (.block ctrStore) s (Post to s₀) := by
  have hn := hp.pre.n16
  have hw : InRegions s.wr (cp s₀ + BitVec.ofNat 64 12) 4 :=
    ⟨⟨cp s₀, 16⟩, by rw [hI.wr, hp.pre.wr]; simp,
      Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  rw [ctrStore, WP.block_cons_iff]; refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, exec_str_w (off := 12) (by decide) (by
    simp only [State.write, reduceCtorEq, ite_false, hI.x2]; exact hw), WP.block_nil ?_⟩
  simp only [State.write, State.read, ite_true, reduceCtorEq, ite_false, hI.x2, Aese.sw32]
  rw [show BitVec.setWidth 32 (s.gpr .x10) = s.read .w .x10 from rfl, hI.x10]
  have hf : Frame [⟨cp s₀ + BitVec.ofNat 64 12, 4⟩] s.mem
      (s.mem.writeW (cp s₀ + BitVec.ofNat 64 12) (rev32 (c0 s₀ + BitVec.ofNat 32 (nb s₀)))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hd : ∀ r ∈ [(⟨cp s₀ + BitVec.ofNat 64 12, 4⟩ : Region)], Region.Disjoint (oR s₀ to) r := by
    simp only [List.mem_singleton, forall_eq]
    exact hp.pre.c_o.symm.sub_right (Offset.sub_base _ (by omega_using []))
  refine ⟨ctr32_of_dataInvM (dataInvM_frame hf hd hn hI.data), ctr_after fun k hk => ?_⟩
  show (s.mem.writeW (cp s₀ + BitVec.ofNat 64 12) (rev32 (c0 s₀ + BitVec.ofNat 32 (nb s₀)))) _ = _
  rw [writeW_apply, off_toNat _ (by omega_using [hk]) (by omega_using [])]
  by_cases h : 12 ≤ k
  · rw [ite_eq_left h, ite_eq_left (show k - 12 < 32 / 8 by omega_using [hk]),
      ite_eq_right (show ¬ k < 12 by omega_using [h]), icb_lo, BitVec.setWidth_eq]
    congr 3
    apply BitVec.eq_of_toNat_eq; simp
  · rw [ite_eq_right h, ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_using []),
      ite_eq_left (show k < 12 by omega_using [h])]
    exact hI.frame.bytes (R := ⟨cp s₀, 16⟩)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hp.pre.c_o, hp.c_b⟩)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem correct {to : Bool} {s₀ : State} (hp : PreS to s₀) (hn0 : nb s₀ ≠ 0) :
    WP isa (ctr32Gen to) s₀ (Post to s₀) := by
  have n16 := hp.pre.n16
  have hR := hp.pre.rounds
  have hR14 : nr s₀ ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  unfold ctr32Gen
  -- The destination and the counter.
  refine WP.seq (WP.mono (Q := fun (s : State) =>
      (∀ r, r ≠ .x14 → r ≠ .x10 → s.gpr r = s₀.gpr r) ∧ (to = true → s.gpr .x14 = s₀.gpr .x6) ∧
      s.read .w .x10 = c0 s₀ ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr) ?_
    fun s₁ ⟨g₁, o₁, x10₁, m₁, rd₁, wr₁⟩ => ?_)
  · unfold ctrSetup
    rw [WP.block_append_iff (M := isa)]
    refine WP.mono (Aese.movO_ok to s₀) ?_
    rintro s ⟨hg, ho, _, hm, hrd, hwr⟩
    rw [WP.block_cons_iff]; refine ⟨_, exec_ldr_w (off := 12) (by decide) (by
      rw [hrd, hwr, hg _ (by decide)]
      exact ⟨⟨cp s₀, 16⟩, by rw [hp.pre.wr]; simp,
        Offset.contains_base _ (by omega_using []) (by omega_using [])⟩), ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, exec_rev32, WP.block_nil ⟨fun r h14 h10 => ?_, fun h => ?_,
      ?_, hm, hrd, hwr⟩⟩
    · simp [State.write, h10, hg r h14]
    · simp [State.write, ho h]
    · simp only [State.write, State.read, ite_true, Aese.sw32, hg .x2 (by decide), hm]
      exact icb_lo _ _
  have x4₁ : s₁.gpr .x4 = BitVec.ofNat 64 (nb s₀) := by
    rw [g₁ _ (by decide) (by decide)]; simp [nb]
  have x2₁ : s₁.gpr .x2 = cp s₀ := g₁ _ (by decide) (by decide)
  refine WP.seq (WP.mono (Q := CDone to s₀) ?_ fun s₆ hd => ctrStore_ok hp hd)
  -- The masks, and where the round keys go.
  refine WP.seq ?_
  simp only [keySetup]
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₂, h₂, mask₂, -, g₂, m₂, rd₂, wr₂, sp₂⟩ := keyMasks_ok 8 (Nat.le_refl 8) s₁
  refine WP.of_runBlock ⟨s₂, h₂, ?_⟩
  let s₃ := s₂.write .x .x7 (s₂.read .x sb + BitVec.ofNat 64 128)
  let s₄ := s₃.write .x kp (s₃.read .x .x1 + BitVec.ofNat 64 1)
  refine WP.of_runBlock ⟨s₄, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have g₄ : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₄.gpr r = s₁.gpr r := fun r h6 h7 hk => by
    simp [s₄, s₃, State.write, h7, hk, g₂ r h6]
  have x7₄ : s₄.gpr .x7 = s₀.gpr .x5 + BitVec.ofNat 64 128 := by
    have e : s₄.gpr .x7 = s₂.gpr sb + BitVec.ofNat 64 128 := by
      simp [s₄, s₃, State.write, State.read, kp]
    rw [e, g₂ sb (by decide)]; exact congrArg (· + _) (g₁ _ (by decide) (by decide))
  have kp₄ : s₄.gpr kp = BitVec.ofNat 64 (nr s₀ + 1) := by
    have e : s₄.gpr kp = s₂.gpr .x1 + BitVec.ofNat 64 1 := by
      simp [s₄, s₃, State.write, State.read, kp]
    rw [e, g₂ .x1 (by decide), g₁ .x1 (by decide) (by decide), BitVec.ofNat_add,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi₀ : KInv s₄ (s₀.gpr .x0) (s₀.gpr .x5) (nr s₀) (sch s₀) 0 s₄ :=
    { hx0 := by
        rw [g₄ .x0 (by decide) (by decide) (by decide), g₁ .x0 (by decide) (by decide)]
        simp
      hx7 := x7₄
      hkp := kp₄
      keep := fun _ _ _ _ => rfl
      mask := mask₂
      rd := rfl
      wr := rfl
      sp := rfl
      keys := fun i hi => absurd hi (by omega_using [])
      frame := Frame.refl _ _ }
  have m₄ : s₄.mem = s₀.mem := m₂.trans m₁
  have rd₄ : s₄.rd = s₀.rd := rd₂.trans rd₁
  have wr₄ : s₄.wr = s₀.wr := wr₂.trans wr₁
  refine WP.seq (WP.mono (keyLoop_ok (S := s₀.gpr .x0) (b := s₀.gpr .x5) (R := nr s₀)
    (w := sch s₀) (by rw [rd₄]; exact hp.sched) (by rw [wr₄]; exact .of_mem hp.scr) hp.s_b hR14
    (by rw [m₄]) hi₀) fun s₅ hk₅ => ?_)
  -- The groups.
  have g₅ : ∀ r, r ≠ .x0 → r ≠ .x6 → r ≠ .x7 → r ≠ kp → s₅.gpr r = s₁.gpr r :=
    fun r h0 h6 h7 hk => (hk₅.keep r h0 h7 hk).trans (g₄ r h6 h7 hk)
  have fr₅ : Frame [oR s₀ to, ⟨s₀.gpr .x5, 2048⟩] s₀.mem s₅.mem :=
    (m₄ ▸ hk₅.frame).mono (by simp)
  have hi : CInv to s₀ 0 s₅ :=
    { hg := by omega_using [hn0]
      x1 := by
        rw [g₅ .x1 (by decide) (by decide) (by decide) (by decide), g₁ .x1 (by decide) (by decide)]
        simp [nr]
      x2 := (g₅ .x2 (by decide) (by decide) (by decide) (by decide)).trans x2₁
      x3 := by
        rw [g₅ .x3 (by decide) (by decide) (by decide) (by decide), g₁ .x3 (by decide) (by decide)]
        simp
      xo := by
        cases to with
        | false =>
          show s₅.gpr .x3 = _
          rw [g₅ .x3 (by decide) (by decide) (by decide) (by decide),
            g₁ .x3 (by decide) (by decide)]
          simp only [Nat.mul_zero, BitVec.add_zero]; rfl
        | true =>
          show s₅.gpr .x14 = _
          rw [g₅ .x14 (by decide) (by decide) (by decide) (by decide), o₁ rfl]
          simp only [Nat.mul_zero, BitVec.add_zero]; rfl
      x4 := (g₅ .x4 (by decide) (by decide) (by decide) (by decide)).trans (by rw [x4₁]; simp)
      x5 := (g₅ sb (by decide) (by decide) (by decide) (by decide)).trans
        (g₁ _ (by decide) (by decide))
      x10 := by
        show (s₅.gpr .x10).setWidth 32 = _
        rw [g₅ .x10 (by decide) (by decide) (by decide) (by decide)]
        exact x10₁.trans (by simp)
      frame := fr₅
      keys := fun j hj => hk₅.keys j (by omega_using [hj])
      data := dataInvM_frame (m₄ ▸ hk₅.frame) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.o_b) n16 fun i hi => by simp
      rd := hk₅.rd.trans rd₄
      wr := hk₅.wr.trans wr₄ }
  exact ctrGroups_ok hp hi

/-- `ctr32N`: nothing for no block, one to four blocks one at a time by the
tables (`OneBlock.ctrFew_wp`), any other number of blocks bitsliced. -/
theorem ctr32N_wp {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa ctr32N s₀ fun s' => Proof.Aes.ctr32AArch64.post s₀ s' := by
  unfold ctr32N
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil (OneBlock.ctr32_none (OneBlock.toNat_of_beq_zero hz))) (fun hz => ?_)
  have hn0 : (s₀.gpr .x4).toNat ≠ 0 := fun h => by
    have : s₀.gpr .x4 = 0 := BitVec.eq_of_toNat_eq h
    simp [this] at hz
  let u := s₀.write .x .x6 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  let s₁ := u.write .x .x6 (u.read .x .x6 >>> 2)
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have hp₁ : Proof.Aes.ctr32AArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, u, State.write, hr]
  refine WP.ite ((s₀.gpr .x4 - BitVec.ofNat 64 1) >>> 2 == 0)
    (by simp [AArch64.eval, State.read, s₁, u, State.write]) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (OneBlock.ctrFew_wp (OneBlock.prec_of hp₁) hn0) fun s' h => h.2
  · exact WP.mono (correct (preS_of hp₁) hn0) fun s' h => h

/-- `ctr32ToN`: as `ctr32N`, out of place. -/
theorem ctr32ToN_wp {s₀ : State} (hp : Proof.Aes.ctr32ToAArch64.pre s₀) :
    WP isa ctr32ToN s₀ fun s' => Proof.Aes.ctr32ToAArch64.post s₀ s' := by
  unfold ctr32ToN
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil (OneBlock.ctr32To_none (OneBlock.toNat_of_beq_zero hz))) (fun hz => ?_)
  have hn0 : (s₀.gpr .x4).toNat ≠ 0 := fun h => by
    have : s₀.gpr .x4 = 0 := BitVec.eq_of_toNat_eq h
    simp [this] at hz
  let u := s₀.write .x .x7 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  let s₁ := u.write .x .x7 (u.read .x .x7 >>> 2)
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have hp₁ : Proof.Aes.ctr32ToAArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x7 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, u, State.write, hr]
  refine WP.ite ((s₀.gpr .x4 - BitVec.ofNat 64 1) >>> 2 == 0)
    (by simp [AArch64.eval, State.read, s₁, u, State.write]) (fun _ => ?_) (fun _ => ?_)
  · exact WP.mono (OneBlock.ctrFew_wp (OneBlock.precTo_of hp₁) hn0) fun s' h => h.2
  · exact WP.mono (correct (preSTo_of hp₁) hn0) fun s' h => h

theorem ctr32N_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32N s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₃⟩ :=
    WP.gprs (rs := preserved) (ctr32N_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ctr32N_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub ctr32N := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32ToN_correct (s : State) (hs : Proof.Aes.ctr32ToAArch64.pre s) :
    ∃ t s', Exec isa ctr32ToN s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToAArch64.post s s' := by
  obtain ⟨t, s', he, h₂, h₃⟩ :=
    WP.gprs (rs := preserved) (ctr32ToN_wp hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₃, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩

theorem ctr32ToN_ct :
    ConstantTime isa Proof.Aes.ctr32ToAArch64.pre Proof.Aes.ctr32ToAArch64.pub ctr32ToN := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.AArch64.Neon
