module

import VerifiedGarbage.Proof.Dsa.Arm.Gen.Intro
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Generation.Search
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PArith
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Dsa.Generation.QShapeMemory
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Dsa.Arm.Gen.PPart`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.PAttempt`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.PX`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.PHash`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.Add`, which only this module used -/

section

/-! # DSA parameter generation on ARMv7: `seed + offset + j`

`addBE n` adds `r1` to the `n` big-endian bytes ending at `r0`, a byte at a
time from the last, the carry and the addend's higher bytes on in `r1`:
`addBE_ok`, against `Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_subs wp_ldrb wp_strb op2_imm op2_reg op2_lsr dpVal
  ofNat_beq_zero toNat_shr)

/-- One step: the byte at `r0` := its sum with `r1`, `r1` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hw : InRegions s.wr a 1) (hc : (s.mem a).toNat + (s.gpr .r1).toNat < 2 ^ 32) :
    WP isa (.block addStep) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .r1).toNat)) ∧
      t.gpr .r1 = BitVec.ofNat 32 (((s.mem a).toNat + (s.gpr .r1).toNat) / 256) ∧
      t.gpr .r0 = s.gpr .r0 - 1 ∧ t.gpr .r2 = s.gpr .r2 - 1 ∧ t.z = (s.gpr .r2 - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  have hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold addStep
  refine wp_ldrb (by decide) ha hr fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have v : s₂.gpr .r3 = BitVec.ofNat 32 ((s.mem a).toNat + (s.gpr .r1).toNat) := by
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r1 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega_arith : (s.mem a).toNat < 2 ^ 32)]
  refine wp_strb (a := a) (by decide) (by rw [u₂.other .r0 (by decide), u₁.other .r0 (by decide)]; exact ha)
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ u₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun t u₆ z₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · rw [u₆.other .r1 (by decide), u₅.other .r1 (by decide), u₄.gpr, u₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt (by omega_arith)]
  · rw [u₆.other .r0 (by decide), u₅.gpr, dpVal, u₄.other .r0 (by decide), u₃.gpr, u₂.other .r0 (by decide),
      u₁.other .r0 (by decide)]
  · rw [u₆.gpr, u₅.other .r2 (by decide), u₄.other .r2 (by decide), u₃.gpr, u₂.other .r2 (by decide),
      u₁.other .r2 (by decide)]
  · rw [z₆, u₅.other .r2 (by decide), u₄.other .r2 (by decide), u₃.gpr, u₂.other .r2 (by decide),
      u₁.other .r2 (by decide)]
  · exact ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest _).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : BitVec 32) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  r0 : t.gpr .r0 + BitVec.ofNat 32 i = base + BitVec.ofNat 32 (n - 1)
  r1 : t.gpr .r1 = BitVec.ofNat 32 c
  cle : c ≤ add
  r2 : t.gpr .r2 = BitVec.ofNat 32 (n - i)
  frame : Frame [⟨State.addr base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (State.addr base + BitVec.ofNat 64 j) = s₀.mem (State.addr base + BitVec.ofNat 64 j)
  eq : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem (State.addr base) n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem (State.addr base) n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (State.addr base + BitVec.ofNat 64 (n - i)) i
  rest : Rest [.r0, .r1, .r2, .r3] s₀ t

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  have e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by rw [bytesAt_length']; exact hk)]
    simp [Spec.Rsa.bytesAt]
  have l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by rw [List.length_take, bytesAt_length']; omega_arith
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem ofNat_sub_one {a : Nat} (h : 0 < a) (h2 : a < 2 ^ 32) :
    BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  show (2 ^ 32 - 1 + a) % 2 ^ 32 = _
  omega_arith

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega_arith

theorem addBody_ok {s₀ t : State} {base : BitVec 32} {n add i c : Nat} (hn256 : n < 256)
    (hfit : base.toNat + n ≤ 2 ^ 32)
    (hadd : add < 2 ^ 24) (hw : InRegions s₀.wr (State.addr base) n) (h : AddInv s₀ base n add i c t)
    (hi : i < n) :
    WP isa (.block addStep) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (State.addr base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        u.z = decide (i + 1 = n) := by
  have hj : n - 1 - i < n := by omega_arith
  have ea : State.addr (t.gpr .r0 + BitVec.ofNat 32 0) = State.addr base + BitVec.ofNat 64 (n - 1 - i) := by
    rw [BitVec.add_zero, ← addr_add (show base.toNat + (n - 1 - i) < 2 ^ 32 by omega_arith)]
    congr 1
    have e := h.r0
    rw [show n - 1 = (n - 1 - i) + i by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 32 i) e
    simpa only [BitVec.add_sub_cancel] using this
  have hw1 : InRegions t.wr (State.addr base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.rest.wr]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have bl := (t.mem (State.addr base + BitVec.ofNat 64 (n - 1 - i))).isLt
  have c24 : c < 2 ^ 24 := by have := h.cle; omega_arith
  refine WP.mono (addStep_ok ea hw1 (by rw [h.r1, BitVec.toNat_ofNat]; omega_arith)) ?_
  rintro u ⟨mu, r1, r0, r2, z, Ru⟩
  rw [h.r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at mu r1
  refine ⟨⟨by omega_arith, ?_, r1, ?_, ?_, ?_, ?_, ?_, h.rest.trans Ru⟩, ?_⟩
  · rw [r0, ← h.r0]
    have : ∀ (x : BitVec 32) (y : Nat), x - 1 + BitVec.ofNat 32 (y + 1) = x + BitVec.ofNat 32 y := fun x y => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (x - 1), BitVec.add_comm (BitVec.ofNat 32 y),
        ← BitVec.add_assoc]
      congr 1
      exact BitVec.sub_add_cancel x 1
    exact this _ _
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega_arith
  · rw [r2, h.r2, ofNat_sub_one (by omega_arith) (by have := h.le; omega_arith)]; congr 1
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne (State.addr base) (a := j) (b := n - 1 - i) (by omega_arith) (by omega_arith) (by omega_arith)
      exact this e)]
    exact h.pre j (by omega_arith)
  · rw [h.eq, show n - i = (n - 1 - i) + 1 by omega_arith, encode_step _ _ (by omega_arith), ← h.pre (n - 1 - i) (by omega_arith),
      show n - (i + 1) = n - 1 - i by omega_arith, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      have hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne (State.addr base) (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega_arith) (by omega_arith)
          (by omega_arith) e)]
  · rw [z, h.r2, ofNat_sub_one (by omega_arith) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

/-- `addBE n`: the `n` big-endian bytes at `base`, `r0` at their last, plus `r1`. -/
theorem addBE_ok {s : State} {base : BitVec 32} {n add : Nat} (hn : 0 < n) (hn256 : n < 256)
    (hfit : base.toNat + n ≤ 2 ^ 32) (hadd : add < 2 ^ 24) (hw : InRegions s.wr (State.addr base) n)
    (h0 : s.gpr .r0 = base + BitVec.ofNat 32 (n - 1)) (h1 : s.gpr .r1 = BitVec.ofNat 32 add) :
    WP isa (addBE n) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr base) n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr base) n) + add) ∧
      Frame [⟨State.addr base, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  unfold addBE
  refine WP.seq (wp_mov (op2_imm (VG.Proof.Rsa.Arm.Keys.encodable_lt hn256)) fun s₁ u₁ => WP.block_nil ?_)
  let inv := fun k t => ∃ i c, i + k = n ∧ 0 < k ∧ AddInv s base n add i c t
  refine WP.loop (M := isa) inv ?_ n s₁ ⟨0, add, by omega_arith, hn, ?_⟩
  · intro k t ⟨i, c, hik, hk, hi⟩
    refine WP.mono (addBody_ok hn256 hfit hadd hw hi (by omega_arith)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], ?_⟩
      have e := hu.eq
      rw [he, Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
      exact ⟨e.symm, hu.frame, hu.rest⟩
    · right
      refine ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
        k - 1, by omega_arith, i + 1, _, by omega_arith, by omega_arith, hu⟩
  · refine ⟨by omega_arith, by rw [u₁.other _ (by decide), h0, BitVec.add_zero], by rw [u₁.other _ (by decide), h1],
      Nat.le_refl _, by rw [u₁.gpr]; rfl, by rw [u₁.mem]; exact Frame.refl _ _, fun j _ => by rw [u₁.mem], ?_,
      u₁.rest (by simp)⟩
    rw [Nat.sub_zero, List.take_of_length_le (by rw [bytesAt_length'])]
    simp [Spec.Rsa.bytesAt]

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: one hash of X

`pHash j` (`pHash_vp`): the seed copied to `sMsg`, `offset + j` added to it
(`seedAdd_vp`, big-endian modulo `2^(8 seedlen)`), and its hash into its
place in X.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- `seed + v` (big-endian, `seedlen` bytes). -/
abbrev seedPlus (G : GP) (sd : List Byte) (v : Nat) : List Byte := Spec.Dsa.encodeBE G.qLen (Spec.Dsa.decodeBE sd + v)

theorem addBE_cert {n : Nat} (hn : n = 20 ∨ n = 32) :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (addBE n) hc).isSome = true := by
  rcases hn with rfl | rfl
  · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (addBE 20), by kernel_rfl⟩
  · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (addBE 32), by kernel_rfl⟩

/-- `offset + j` added to the seed at `sMsg`. -/
theorem seedAdd_vp {L j off : Nat} (hL : L = G.pLen) (hq : G.qLen = 20 ∨ G.qLen = 32)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hj : j < 256) (hoff : off + j < 2 ^ 24)
    {sd : List Byte} (hsd : (sMsg, sd) ∈ c.cl) (hsl : sd.length = G.qLen) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sMsg G.qLen x) :
    VP (St G c X) (seedAdd L G.qLen j)
      (St G { c with cl := (sMsg, seedPlus G sd (off + j)) :: cl' } X) := by
  subst hL
  unfold seedAdd
  have hq0 : 0 < G.qLen := by omega_arith
  have e0 : sMsg + G.qLen - 1 = G.qLen - 1 := by simp only [sMsg]; omega_arith
  refine VP.seq (G := fun σ s => St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ?_
    (VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ∧
      s.gpr .r1 = BitVec.ofNat 32 off) ?_
    (VP.seq (G := fun σ s => (St G c X σ s ∧ s.gpr .r0 = G.scr + BitVec.ofNat 32 (G.qLen - 1)) ∧
      s.gpr .r1 = BitVec.ofNat 32 (off + j)) ?_ ?_))
  · refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block (scr 128 .r0 19)), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8]) fun σ s ⟨h, x⟩ => ?_
    rw [← List.append_nil (scr _ _ _)]
    have := h.gi.scrBig
    exact scr_ok h.r8 rfl h.lens (by simp only [sK, sA, sMsg]; omega_arith) fun t v R M => WP.block_nil
      ⟨⟨h.of_rest R M, x⟩, by rw [v, e0]⟩
  · exact ld_vp (c := fun _ => c) (fun σ s h => h.1.1) (by decide) (by decide) (x := BitVec.ofNat 32 off)
      (fun σ s h => (h.1.1.slotV hO).trans hOv) fun σ s t ⟨⟨h, x⟩, r0⟩ u =>
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r0]⟩, u.gpr⟩
  · refine VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
        (.block [.dp .add .r1 .r1 (.imm (BitVec.ofNat 32 0))]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => ?_
    refine wp_dp (op2_imm (encodable_lt hj)) fun t u => WP.block_nil
      ⟨⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r0]⟩, ?_⟩
    rw [u.gpr, dpVal, r1, BitVec.ofNat_add]
  · refine VP.taint [.r0] (addBE_cert hq)
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2, h₂.1.2]) fun σ s ⟨⟨⟨h, x⟩, r0⟩, r1⟩ => ?_
    have gi := h.gi
    have big := gi.scrBig
    have fit := gi.scrFit
    have hsK : 4096 ≤ sK G.pLen := by simp only [sK, sA]; omega_arith
    have hq32 : G.qLen ≤ 32 := by omega_arith
    have a0 : G.sa sMsg = State.addr G.scr := by simp only [GP.sa, sMsg]; rw [BitVec.add_zero]
    have hw : InRegions s.wr (State.addr G.scr) G.qLen := a0 ▸ gi.inScr (o := sMsg) (by simp only [sMsg]; omega_arith)
    refine (addBE_ok (base := G.scr) hq0 (by omega_arith) (by omega_arith) hoff hw r0 r1).mono fun t ⟨e, f, R⟩ => ⟨?_, x⟩
    rw [← a0] at e f
    have b := h.sb (sMsg, sd) hsd
    rw [hsl] at b
    rw [b] at e
    refine h.of_scr R (o := sMsg) (n := G.qLen) (by simp only [sMsg]; omega_arith) (f.mono (by simp)) fun y hy => ?_
    rcases List.mem_cons.mp hy with rfl | hy
    · exact .inr ⟨by rw [VG.Proof.Dsa.encodeBE_length]; exact e,
        by simp only [sMsg, VG.Proof.Dsa.encodeBE_length]; omega_arith⟩
    · exact .inl (hcl y hy)

/-- The block at `sMsg`: a message of `qLen` bytes and its padding. -/
theorem SS.blk_bytes {σ s : State} (h : SS G σ c s) {B N L : Nat} {md : MdStream.Md B N L} {m : List Byte}
    (hL : L = 8) (hq56 : G.qLen < 56) (hm : (sMsg, m) ∈ c.cl) (hml : m.length = G.qLen)
    (hpad : (G.qLen, padTail md G.qLen) ∈ c.cl) :
    Spec.Rsa.bytesAt s.mem (G.sa sMsg) 64 = blk md m := by
  have b1 := h.sb _ hm
  have b2 := h.sb _ hpad
  have pl := padTail_length md hq56 hL
  rw [show (64 : Nat) = m.length + (padTail md G.qLen).length by omega_arith, VG.Proof.Dsa.Generation.bytesAt_append,
    b1]
  have a : VG.Proof.Bignum.off (G.sa sMsg) m.length = G.sa G.qLen := by
    simp only [VG.Proof.Bignum.off, GP.sa, sMsg, hml]; rw [BitVec.add_zero]
  rw [a]
  simp only at b2
  rw [b2]
  simp only [blk, padTail, hml, List.append_assoc]

/-- The hash of the seed at `k` plus `off + j`, to `dst`. -/
theorem pHash_vp {g : Geo} (HO : HashOk g.G) {j : Nat}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hj : j < 256) (hoff : off + j < 2 ^ 24)
    (hd1 : 96 ≤ sX + G.pLen - (j + 1) * G.qLen) (hd2 : sX + G.pLen - (j + 1) * G.qLen + G.qLen ≤ sA)
    (hpad : (G.qLen, padTail HO.md G.qLen) ∈ c.cl) {cl' : Claims}
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (sX + G.pLen - (j + 1) * G.qLen) G.qLen x) :
    VP (St G c X) (g.pHash j)
      (St G { c with cl := (G.qLen, padTail HO.md G.qLen) :: (sX + G.pLen - (j + 1) * G.qLen,
        HO.H (seedPlus G (seedAt G k) (off + j))) :: cl' } X) := by
  have hq0 : 0 < G.qLen := by omega_arith
  have hq56 : G.qLen < 56 := by omega_arith
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have spl : (seedPlus G (seedAt G k) (off + j)).length = G.qLen := VG.Proof.Dsa.encodeBE_length _ _
  have hHl : (HO.H (seedPlus G (seedAt G k) (off + j))).length = G.qLen := by
    rw [HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  generalize hpd : padTail HO.md G.qLen = pad at hpad pl
  unfold Geo.pHash
  rw [hq, hp]
  let c1 : Cfg := { c with cl := (sMsg, seedAt G k) :: (G.qLen, pad) :: cl' }
  let c2 : Cfg := { c with cl := (sMsg, seedPlus G (seedAt G k) (off + j)) :: (G.qLen, pad) :: cl' }
  refine VP.seq (G := St G c1 X) ?_ (VP.seq (G := St G c2 X) ?_ ?_)
  · exact seedCopy_vp rfl hk hq0 (by omega_arith) (by omega_arith) hsb hS hSv fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hpad, .inr (by simp only [sMsg]; omega_arith)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨m, by simp only [Apart, sMsg] at a ⊢; omega_arith⟩
  · exact seedAdd_vp (c := c1) rfl (by omega_arith) hO hOv hj hoff (by simp [c1]) hsl fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨by simp [c1], .inr (by simp only [sMsg]; omega_arith)⟩
      · obtain ⟨m, a, _⟩ := hcl y hy; exact ⟨by simp [c1, hy], by simp only [Apart, sMsg] at a ⊢; omega_arith⟩
  · refine hash_vp HO (c := fun _ => c2) (fun σ s h => h.1) rfl (msg := fun _ => seedPlus G (seedAt G k) (off + j))
      (dst := sX + G.pLen - (j + 1) * G.qLen) (fun σ s ⟨h, _⟩ => ⟨by omega_arith, ?_⟩) (by simp only [sState]; omega_arith)
      (by rw [hk4]; omega_arith) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
    · exact h.blk_bytes HO.hL hq56 (by simp [c2]) spl (by rw [hpd]; simp [c2])
    refine h.of_scrs R (os := [(sState, 32), (sA, 112), (sX + G.pLen - (j + 1) * G.qLen, 4 * g.G.k)]) (fun p hp => ?_)
      (f.mono fun r hr => List.mem_append_left _ (by simpa [GP.rss] using hr)) fun y hy => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [sState, sA, hk4] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · refine .inl ⟨by simp [c2], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, pl, sState, sA] <;> omega_arith
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hk4] at e
      exact .inr ⟨by rw [hHl]; exact e, by simp only [hHl]; omega_arith⟩
    · obtain ⟨m, a, b, d⟩ := hcl y hy
      refine .inl ⟨by simp [c2, hy], fun p hp => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp only [Apart, sState, sA, hk4] at a b d ⊢ <;> omega_arith

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: X

`pHashes m` (`pHashes_vp`): the first `m` hashes of X, each just below the
one before, in one claim (`accB`) whose value is the sum of the
contributions (`accB_value`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_dp wp_ldrb wp_strb op2_imm dpVal)
open VG.Proof.Ffdh.ParameterCandidate (topCut topByte)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Dsa.Generation (contributions pDigest)

section
variable {G : GP} {Gh : Hash}

/-- Hash `j` of X, from the seed at `k` and the offset `off`. -/
abbrev hX (HO : HashOk Gh) (G : GP) (k off j : Nat) : List Byte := HO.H (seedPlus G (seedAt G k) (off + j))

/-- The first `m` hashes of X, the last first. -/
def accB (HO : HashOk Gh) (G : GP) (k off : Nat) : Nat → List Byte
  | 0 => []
  | m + 1 => hX HO G k off m ++ accB HO G k off m

/-- Where the first `m` hashes of X start. -/
abbrev pStart (G : GP) (m : Nat) : Nat := sX + G.pLen - m * G.qLen

theorem accB_length (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen) :
    ∀ m, (accB HO G k off m).length = m * G.qLen
  | 0 => by simp [accB]
  | m + 1 => by rw [accB, List.length_append, hl, accB_length HO hl m, Nat.succ_mul]; omega_arith

theorem accB_value (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen) :
    ∀ m, Spec.Dsa.decodeBE (accB HO G k off m) = contributions (8 * G.qLen) (pDigest (8 * G.qLen) (seedAt G k) off) m
  | 0 => rfl
  | m + 1 => by
    rw [accB, VG.Proof.Dsa.Generation.prepend_digest, accB_value HO hl hH hsl m,
      VG.Proof.Dsa.Generation.contributions_succ, accB_length HO hl m]
    congr 1
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, show 8 * (m * G.qLen) = m * (8 * G.qLen) by
      rw [Nat.mul_left_comm]]
    congr 1
    simp only [hX, hH, pDigest, seedPlus, hsl, Nat.add_assoc]

/-- Other claims, which the memory holds. -/
theorem SS.reclaim {σ s : State} {c : Cfg} (h : SS G σ c s) {cl' : Claims}
    (hcl : ∀ x ∈ cl', Spec.Rsa.bytesAt s.mem (G.sa x.1) x.2.length = x.2 ∧ x.1 + x.2.length ≤ sK G.pLen) :
    SS G σ { c with cl := cl' } s :=
  ⟨h.gi, h.r7, h.r8, h.r9, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2, h.arrs, h.liveOk, h.ksl, h.kslOk⟩

/-- Two claims side by side, as one. -/
theorem SB.join {m : Mem} {cl : Claims} (h : SB G m cl) {o : Nat} {a b : List Byte} (ha : (o, a) ∈ cl)
    (hb : (o + a.length, b) ∈ cl) : Spec.Rsa.bytesAt m (G.sa o) (a ++ b).length = a ++ b := by
  rw [List.length_append, VG.Proof.Dsa.Generation.bytesAt_append, h _ ha]
  have e : VG.Proof.Bignum.off (G.sa o) a.length = G.sa (o + a.length) := by
    simp only [VG.Proof.Bignum.off, GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e, h _ hb]

/-- The claims during X. -/
abbrev pCfg (c : Cfg) (HO : HashOk Gh) (G : GP) (k off m : Nat) (rest : Claims) : Cfg :=
  { c with cl := (G.qLen, padTail HO.md G.qLen) :: (pStart G m, accB HO G k off m) :: rest }

/-- The first `m` hashes of X. -/
theorem pHashes_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off n : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hn : n < 256) (hoff : off + n < 2 ^ 24)
    (hnq : n * G.qLen ≤ G.pLen + 96) {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (pStart G n) (n * G.qLen) x) :
    ∀ m ≤ n, VP (St G (pCfg c HO G k off 0 rest) X) (g.pHashes m) (St G (pCfg c HO G k off m rest) X)
  | 0, _ => VP.block_nil fun _ _ h => h
  | m + 1, hm => by
    have ih := pHashes_vp (X := X) HO hlq hp hq hk4 hsb hk hS hSv hO hOv hn hoff hnq hrest m (by omega_arith)
    refine VP.seq ih ?_
    have hXv : sX = 192 := rfl
    have hAv : sA = 4096 := rfl
    have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
    have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
      rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
    have al := accB_length HO hHl m
    have hm1 : (m + 1) * G.qLen = m * G.qLen + G.qLen := Nat.succ_mul _ _
    have hmn : (m + 1) * G.qLen ≤ n * G.qLen := Nat.mul_le_mul_right _ hm
    have e1 : pStart G (m + 1) + G.qLen = pStart G m := by
      simp only [pStart]; omega_arith
    refine (pHash_vp (c := pCfg c HO G k off m rest) (j := m) HO hlq hp hq hk4 hsb hk hS hSv hO hOv (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by simp) (cl' := (pStart G m, accB HO G k off m) :: rest) fun x hx => ?_).mono
      (fun _ _ h => h) fun σ s ⟨h, x⟩ => ⟨h.reclaim fun y hy => ?_, x⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨by simp, ?_, ?_, ?_⟩ <;> simp only [Apart, al, pStart] <;> omega_arith
      · obtain ⟨a, b, d⟩ := hrest x hx
        refine ⟨by simp [hx], a, b, ?_⟩
        simp only [Apart, pStart] at d ⊢
        omega_arith
    · have sb := h.sb
      have cl := h.clOk
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact ⟨sb _ (by simp), cl _ (by simp)⟩
      · have j := sb.join (o := pStart G (m + 1)) (a := hX HO G k off m) (b := accB HO G k off m)
          (by simp [pStart]) (by rw [hHl, e1]; simp)
        refine ⟨j, ?_⟩
        show pStart G (m + 1) + (accB HO G k off (m + 1)).length ≤ _
        rw [accB_length HO hHl]
        simp only [pStart]; omega_arith
      · exact ⟨sb _ (by simp [hy]), cl _ (by simp [hy])⟩

theorem top_memory {m : Mem} {op : Addr} {n : Nat} (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (m.writeW op (m op ||| 128#8)) op n = topCut (Spec.Rsa.bytesAt m op n) 7 := by
  have hne : Spec.Rsa.bytesAt m op n ≠ [] := by
    intro h; have := bytesAt_length' m op n; rw [h] at this; simp at this; omega_arith
  apply List.ext_getElem
  · rw [bytesAt_length', VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, bytesAt_length']
  · intro i hi hi'
    have hil : i < n := by simpa only [bytesAt_length'] using hi
    have hget : (topCut (Spec.Rsa.bytesAt m op n) 7)[i] = (topCut (Spec.Rsa.bytesAt m op n) 7).getD i 0 := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hget, VG.Proof.Ffdh.ParameterCandidate.topCut_getD, VG.Proof.Dsa.Generation.topByte_seven]
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeW8_apply]
    by_cases hiz : i = 0
    · subst i; simp [show 0 < n by omega_arith]
    · have hne0 : op + BitVec.ofNat 64 i ≠ op := by
        simpa using Offset.add_ofNat_ne op (by omega_arith : i < 2 ^ 64) (by decide : 0 < 2 ^ 64) hiz
      simp [hiz, hne0, hil]

/-- X's top bit set. -/
theorem topX_vp {P Q : State → State → Prop} {c : State → Cfg} {L N : Nat} {bs : List Byte}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (hN : 1 ≤ N) (hN' : sX + N ≤ sK G.pLen)
    (hb : ∀ σ s, P σ s → Spec.Rsa.bytesAt s.mem (G.sa sX) N = bs)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r12] s t → Frame [G.rs sX N] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa sX) N = topCut bs 7 → Q σ t) :
    VP P (.block (scr L .r0 sX ++ ([.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0] : List Instr))) Q := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sX ++ [.ldrb .r1 .r0 0, .dp .orr .r1 .r1 (.imm 0x80), .strb .r1 .r0 0])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_
  · simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).r8, (hF _ _ h₂).r8]
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl h.lens (by omega_arith) fun s₁ v₁ R₁ M₁ => ?_
  have aq := h.addr (o := sX) (n := N) (by omega_arith) (by omega_arith)
  have c0 : (G.rs sX N).Contains (G.sa sX) 1 := by
    show (_ - _ : Addr).toNat + 1 ≤ N
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  have w0 : InRegions s.wr (G.sa sX) 1 :=
    Covers.one (gi.inScr (o := sX) (n := N) (by omega_arith)) _ _ ⟨_, List.mem_singleton_self _, c0⟩
  have r0 : InRegions (s.rd ++ s.wr) (G.sa sX) 1 := let ⟨r, hr, hc⟩ := w0; ⟨r, List.mem_append_right _ hr, hc⟩
  have a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sX := by rw [BitVec.add_zero, v₁, aq]
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; exact r0) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_strb (a := G.sa sX) (by decide) (by rw [u₃.other .r0 (by decide), u₂.other .r0 (by decide)]; exact a0)
    (by rw [u₃.wr, u₂.wr, R₁.wr]; exact w0) fun t u₄ => WP.block_nil ?_
  have R : Rest [.r0, .r1, .r12] s t := ((R₁.mono (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))).trans
    (u₄.rest _)
  have mt : t.mem = s.mem.writeW (G.sa sX) (s.mem (G.sa sX) ||| 128#8) := by
    rw [u₄.mem, u₃.mem, u₂.mem, M₁, u₃.gpr, dpVal, u₂.gpr, M₁, orr_byte]; rfl
  refine k σ s t hs R ?_ ?_
  · rw [mt]
    exact (Frame.refl [G.rs sX N] s.mem).writeW List.mem_cons_self (w := 8) _ c0
  · rw [mt, top_memory hN (by omega_arith), hb σ s hs]

/-- `(L − 1) / N`, the number of whole hashes below X's top one. -/
abbrev cnt (G : GP) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

/-- X's bytes: the low `pLen` bytes of the hashes, the top bit set. -/
abbrev xBytes (HO : HashOk Gh) (G : GP) (k off : Nat) : List Byte :=
  topCut ((accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen)) 7

theorem decodeBE_drop (bs : List Byte) (d : Nat) :
    Spec.Dsa.decodeBE (bs.drop d) = Spec.Dsa.decodeBE bs % 256 ^ (bs.length - d) := by
  have e := VG.Proof.Dsa.decodeBE_append (bs.take d) (bs.drop d)
  rw [List.take_append_drop, List.length_drop] at e
  rw [e, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := VG.Proof.Dsa.decodeBE_lt (bs.drop d); rwa [List.length_drop] at this)]

/-- X's value. -/
theorem xBytes_value {A : List Byte} {d n : Nat} (hA : A.length = d + n) (hn : 1 ≤ n) :
    Spec.Dsa.decodeBE (topCut (A.drop d) 7) = Spec.Dsa.decodeBE A % 2 ^ (8 * n - 1) + 2 ^ (8 * n - 1) := by
  have hne : A.drop d ≠ [] := by
    intro h; have := congrArg List.length h; rw [List.length_drop] at this; simp at this; omega_arith
  rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Ffdh.ParameterCandidate.topCut_value hne (by decide),
    ← VG.Proof.Dsa.decodeBE_os2ip, decodeBE_drop, List.length_drop, hA,
    show d + n - d = n by omega_arith, show 8 * (n - 1) + 7 = 8 * n - 1 by omega_arith,
    show (256 : Nat) ^ n = 2 ^ (8 * n) by rw [Nat.pow_mul],
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_arith))]

/-- The candidate p of the spec, from X's value. -/
theorem pCandidate_xBytes (HO : HashOk Gh) {k off : Nat} (hl : ∀ j, (hX HO G k off j).length = G.qLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hsl : (seedAt G k).length = G.qLen)
    (hlen : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * G.qLen) bs).length = 8 * G.qLen)
    (hp1 : 1 ≤ G.pLen) (hc : G.pLen ≤ (cnt G + 1) * G.qLen) (q : Nat) :
    Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) q (seedAt G k) off =
      Spec.Dsa.decodeBE (xBytes HO G k off) + 1 - Spec.Dsa.decodeBE (xBytes HO G k off) % (2 * q) := by
  rw [VG.Proof.Dsa.Generation.pCandidate_shaped (by omega_arith) hlen,
    VG.Proof.Ffdh.ParameterCandidate.candidate_low_high (by omega_arith),
    VG.Proof.Dsa.Generation.pReduction_orOne, xBytes,
    xBytes_value (by rw [accB_length HO hl]; omega_arith) hp1, accB_value HO hl hH hsl]

/-- X, from the seed at `k` and the offset `off`, at `sX`. -/
theorem pX_vp {g : Geo} (HO : HashOk g.G) {c : Cfg} {X : State → Prop}
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    {k off : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hoff : off + (cnt G + 1) < 2 ^ 24)
    {rest : Claims}
    (hrest : ∀ x ∈ rest, Apart 0 96 x ∧ Apart sA 112 x ∧ Apart (pStart G (cnt G + 1)) ((cnt G + 1) * G.qLen) x) :
    VP (St G (pCfg c HO G k off 0 rest) X) g.pX
      (St G { c with cl := (G.qLen, padTail HO.md G.qLen) :: (sX, xBytes HO G k off) :: rest } X) := by
  have hc : (cnt G + 1) * G.qLen ≤ G.pLen + 96 ∧ G.pLen ≤ (cnt G + 1) * G.qLen ∧ cnt G + 1 < 256 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have hcount : g.count = cnt G := by simp only [Geo.count, hp, hq]
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hsK : 4096 + 17024 ≤ sK G.pLen := by simp only [sK, sA, wa]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have al := accB_length HO hHl (cnt G + 1)
  have hd : pStart G (cnt G + 1) + ((cnt G + 1) * G.qLen - G.pLen) = sX := by simp only [pStart]; omega_arith
  unfold Geo.pX
  rw [hcount, hp]
  refine VP.seq (pHashes_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hc.2.2 (by omega_arith) hc.1 hrest _ (Nat.le_refl _)) ?_
  refine topX_vp (c := fun _ => pCfg c HO G k off (cnt G + 1) rest) (fun σ s h => h.1) rfl (N := G.pLen)
    (by omega_arith) (by omega_arith) (bs := (accB HO G k off (cnt G + 1)).drop ((cnt G + 1) * G.qLen - G.pLen))
    (fun σ s ⟨h, _⟩ => ?_) fun σ s t ⟨h, x⟩ R f e => ⟨?_, x⟩
  · have b := h.sb (pStart G (cnt G + 1), accB HO G k off (cnt G + 1)) (by simp)
    simp only at b
    rw [al] at b
    have a : G.sa sX = G.sa (pStart G (cnt G + 1)) + BitVec.ofNat 64 ((cnt G + 1) * G.qLen - G.pLen) := by
      simp only [GP.sa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, hd]
    rw [a, bytesAt_slice' _ _ (len := (cnt G + 1) * G.qLen) (by omega_arith), b, List.take_of_length_le (by
      rw [List.length_drop, al]; omega_arith)]
  refine h.of_scr R (o := sX) (n := G.pLen) (by omega_arith) (f.mono (by simp)) fun y hy => ?_
  rcases List.mem_cons.mp hy with rfl | hy
  · exact .inl ⟨by simp, .inl (by simp only [padTail_length HO.md (show G.qLen < 56 by omega_arith) HO.hL]; omega_arith)⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · have hl : (xBytes HO G k off).length = G.pLen := by
      rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
        rw [← List.length_pos_iff, List.length_drop, al]; omega_arith), List.length_drop, al]; omega_arith
    exact .inr ⟨by rw [hl]; exact e, by rw [hl]; omega_arith⟩
  · obtain ⟨_, _, d⟩ := hrest y hy
    exact .inl ⟨by simp [hy], by simp only [Apart, pStart] at d ⊢; omega_arith⟩

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: one candidate p

`pAttempt` (`pAttempt_vp`): X, p from it, and unless p is below
`2^(L − 1)` (`topBit_vp`) its probable-prime test: `fP` := 0 if the
witnesses ran out, 1 if p is a probable prime, else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Fupd wp_dp wp_ldrb wp_cmp op2_imm dpVal eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)

theorem top_bit (b : BitVec 8) : ((b.setWidth 32 &&& (128 : BitVec 32)) - 0 == 0) = true ↔ b.toNat < 128 := by
  revert b; decide

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- Z iff the `pLen` big-endian bytes of `pv` at `sPBE` are below `2^(8 pLen − 1)`. -/
theorem topBit_vp {L pv : Nat} (hL : L = G.pLen) (hc : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c.cl)
    (hpv : pv < 256 ^ G.pLen) :
    VP (St G c X) (.block (scr L .r0 sPBE ++ ([.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.imm 0x80), .cmp .r1 (.imm 0)] : List Instr)))
      (fun σ t => St G c X σ t ∧ isa.eval .eq t = some (decide (pv < 2 ^ (8 * G.pLen - 1)))) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sPBE ++ [.ldrb .r1 .r0 0, .dp .and .r1 .r1 (.imm 0x80), .cmp .r1 (.imm 0)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8]) fun σ s ⟨h, x⟩ => ?_
  subst hL
  have gi := h.gi
  have big := gi.scrBig
  have l := h.lens
  have hsK : sPBE + G.pLen ≤ sK G.pLen := by simp only [sPBE, sK, sA, wa]; omega_using []
  refine scr_ok (d := .r0) (o := sPBE) h.r8 rfl l (by omega_using [hsK]) fun s₁ v₁ R₁ M₁ => ?_
  have a0 : State.addr (s₁.gpr .r0 + BitVec.ofNat 32 0) = G.sa sPBE := by
    rw [BitVec.add_zero, v₁]; exact h.addr (by omega) (by omega_using [l])
  have c0 : (G.rs sPBE G.pLen).Contains (G.sa sPBE) 1 := by
    show (_ - _ : Addr).toNat + 1 ≤ G.pLen
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_using [l]
  have w0 : InRegions (s.rd ++ s.wr) (G.sa sPBE) 1 :=
    let ⟨r, hr, hcn⟩ := Covers.one (gi.inScr (o := sPBE) (n := G.pLen) (by omega_using [big, hsK])) _ _
      ⟨_, List.mem_singleton_self _, c0⟩
    ⟨r, List.mem_append_right _ hr, hcn⟩
  refine wp_ldrb (by decide) a0 (by rw [R₁.rd, R₁.wr]; exact w0) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ⟨⟨h.of_rest
    (((R₁.mono (by simp)).trans ((u₂.rest (ws := [.r0, .r1, .r12]) (by simp)).trans (u₃.rest (by simp)))).trans
      (f.rest _)) (by rw [f.mem, u₃.mem, u₂.mem, M₁]), x⟩, ?_⟩
  -- The byte: p's first.
  have b := h.sb _ hc
  simp only at b
  rw [VG.Proof.Rsa.i2osp_length] at b
  have byte : s.mem (G.sa sPBE) = (Spec.Rsa.i2osp pv G.pLen).getD 0 0 := by
    rw [← b]; simp [Spec.Rsa.bytesAt, show 0 < G.pLen by omega_using [l]]
  rw [eval_eq, z, u₃.gpr, dpVal, u₂.gpr, M₁, byte]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, top_bit,
    ← VG.Proof.Dsa.encodeBE_i2osp]
  exact VG.Proof.Dsa.Generation.candidate_firstByte (by omega_using [l]) hpv

theorem varOk_fP : VarOk G fP := varOk_of (by decide)

/-- The stage after a test's result recorded in `fP`. -/
def pRes (c0 : Cfg) (wl : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => (testCfg c0 c0.cl wl none).setV fP 0
  | some (true, r) => (testCfg c0 c0.cl wl (some (true, r))).setV fP 1
  | some (false, r) => testCfg c0 c0.cl wl (some (false, r))

/-- `fP` := 0 if the witnesses ran out, 1 for a probable prime. -/
theorem pDecide_vp {c0 : Cfg} {wl : Nat} (res : Option (Bool × Spec.RsaKeyGen.Rand)) :
    VP (St G (testCfg c0 c0.cl wl res) X)
      (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fRes 0), .ite .eq (.block (stImm fP 0))
        (VG.Impl.Rsa.Arm.Keys.seqs [.block (cmpF fRes 1), .ite .eq (.block (stImm fP 1)) (.block [])])])
      (St G (pRes c0 wl res) X) := by
  have vres : ∀ σ s, St G (testCfg c0 c0.cl wl res) X σ s →
      fw s.mem G fRes = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := fun σ s h => by
    rw [h.1.slotV (by unfold testCfg; split <;> simp)]
    unfold testCfg Proof.Dsa.ProbablePrime.status
    split
    · simp [upd]
    · rename_i b r
      simp only [upd, ite_true]
      cases b <;> rfl
  refine VP.seq (cmpF_vp (fun σ s h => h.1) (by decide) (by decide) (by decide) vres
    fun σ s t h R m e => (⟨⟨h.1.of_rest R m, h.2⟩, e⟩ :
      St G (testCfg c0 c0.cl wl res) X σ t ∧ _)) ?_
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · rcases res with _ | ⟨b, r⟩
    · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl none) (fun σ s h => h.1.1.1) (by decide) varOk_fP
        fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · refine VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => ?_
      rw [e] at z
      unfold Proof.Dsa.ProbablePrime.status at z
      cases b <;> simp at z
  · rcases res with _ | ⟨b, r⟩
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z
    refine VP.seq (cmpF_vp (fun σ s h => h.1.1.1) (by decide) (by decide) (by decide)
      (fun σ s h => vres σ s h.1.1) fun σ s t h R m e => (⟨⟨h.1.1.1.of_rest R m, h.1.1.2⟩, e⟩ :
        St G (testCfg c0 c0.cl wl (some (b, r))) X σ t ∧ _)) ?_
    refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
    · cases b
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z
      · exact stImm_vp (c := fun _ => testCfg c0 c0.cl wl (some (true, r))) (fun σ s h => h.1.1.1) (by decide)
          varOk_fP fun σ s t h h' _ => ⟨h', h.1.1.2⟩
    · cases b
      · exact VP.block_nil fun σ s h => h.1.1
      · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [Proof.Dsa.ProbablePrime.status] at z

/-- The claims kept through a candidate p: the padding and q. -/
abbrev pRest {B N L : Nat} (md : MdStream.Md B N L) (G : GP) (k : Nat) : Claims :=
  [(G.qLen, padTail md G.qLen), (sQ, qBytes G k)]

/-- The stage after a candidate p from X (`xv`) and q (`qv`), tested with the
witnesses from `u` unless it is too short. -/
def pAttCfg (c : Cfg) (G : GP) (xv qv : Nat) (rest : Claims) (u : Nat) : Cfg :=
  if pVal xv qv < 2 ^ (8 * G.pLen - 1) then pOut c G xv qv rest
  else pRes (pOut c G xv qv rest) G.witLen (Spec.Dsa.probablePrime (pVal xv qv) (G.witB.drop u))

theorem pAttempt_vp {g : Geo} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    {k off u : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hu : u ≤ G.witLen)
    (hS : fSeed ∈ c.LS) (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hO : fOffset ∈ c.LS) (hOv : c.V fOffset = BitVec.ofNat 32 off) (hoff : off + (cnt G + 1) < 2 ^ 24)
    (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS) :
    VP (St G (pCfg c HO G k off 0 [(sQ, qBytes G k)]) X) g.pAttempt
      (St G (pAttCfg c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
        (pRest HO.md G k) u) X) := by
  have hq56 : G.qLen < 56 := by omega_arith
  have pl := padTail_length HO.md hq56 HO.hL
  have hsl : (seedAt G k).length = G.qLen := by
    simp only [seedAt, List.length_take, List.length_drop, hsb]; omega_arith
  have hHl : ∀ j, (hX HO G k off j).length = G.qLen := fun j => by
    rw [hX, HO.hash _ (by rw [VG.Proof.Dsa.encodeBE_length]; omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hc : (cnt G + 1) * G.qLen + G.qLen ≤ G.pLen + 64 ∧ G.pLen ≤ (cnt G + 1) * G.qLen := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  have xl : (xBytes HO G k off).length = G.pLen := by
    rw [xBytes, VG.Proof.Ffdh.ParameterCandidate.topCut_length (by
      rw [← List.length_pos_iff, List.length_drop, accB_length HO hHl]; omega_arith), List.length_drop,
      accB_length HO hHl]; omega_arith
  have hHq : (Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k)).length = G.qLen := by
    rw [← hH, HO.hash _ (by omega_arith), HO.md.digest_length, HO.hN, hk4]
  have hne : Spec.Dsa.seedHash (8 * G.qLen) (seedAt G k) ≠ [] := fun e => by rw [e] at hHq; simp at hHq; omega_arith
  have ql : (qBytes G k).length = G.qLen := by
    rw [qBytes, VG.Proof.Ffdh.ParameterCandidate.shapedOctets, VG.Proof.Ffdh.ParameterCandidate.lastOne_length
      (by rw [← List.length_pos_iff, VG.Proof.Ffdh.ParameterCandidate.topCut_length hne]; omega_arith),
      VG.Proof.Ffdh.ParameterCandidate.topCut_length hne, hHq]
  have hqv : Spec.Dsa.decodeBE (qBytes G k) = Spec.Dsa.qCandidate (8 * G.qLen) (seedAt G k) :=
    VG.Proof.Dsa.Generation.qCandidate_octets (by omega_arith) _ (by rw [hHq])
  have qpos : 0 < Spec.Dsa.decodeBE (qBytes G k) := by
    rw [hqv]; have := (VG.Proof.Dsa.Generation.qCandidate_shape (n := 8 * G.qLen) (by omega_arith) (seedAt G k)).2.1
    have : 0 < 2 ^ (8 * G.qLen - 1) := Nat.two_pow_pos _
    omega_arith
  have hXv : sX = 192 := rfl
  have hAv : sA = 4096 := rfl
  have hQv : sQ = 128 := rfl
  have hPBE : sPBE = 576 := rfl
  unfold Geo.pAttempt
  rw [hp, hq]
  refine VP.seq (pX_vp HO hlq hp hq hk4 hsb hk hS hSv hO hOv hoff (rest := [(sQ, qBytes G k)]) fun y hy => by
    rw [List.mem_singleton] at hy; subst hy
    simp only [Apart, ql, pStart]; omega_arith) ?_
  refine VP.seq (pArith_vp certs hlq (by simp) xl (by simp) ql qpos (rest := pRest HO.md G k) fun y hy => by
    simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨by simp, by simp only [Apart, pl]; omega_arith⟩
    · exact ⟨by simp, by simp only [Apart, ql]; omega_arith⟩) ?_
  have xlt : Spec.Dsa.decodeBE (xBytes HO G k off) < 2 ^ (8 * G.pLen) := by
    have := VG.Proof.Dsa.decodeBE_lt (xBytes HO G k off)
    rwa [xl, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  have plt := pVal_lt (q := Spec.Dsa.decodeBE (qBytes G k)) (show 1 ≤ 8 * G.pLen by omega_arith) xlt
  have plt' : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) < 256 ^ G.pLen := by
    rwa [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  refine VP.seq (topBit_vp rfl (by simp) plt') ?_
  generalize hpv : pVal (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k)) = pv at plt plt'
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · refine VP.block_nil fun σ s ⟨⟨h, _⟩, _⟩ => ?_
      unfold pAttCfg
      rw [hpv, ite_eq_left (by exact hcnd)]
      exact h
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
  · by_cases hcnd : pv < 2 ^ (8 * G.pLen - 1)
    · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp [hcnd] at z
    have pb : Spec.Dsa.decodeBE (Spec.Rsa.i2osp pv G.pLen) = pv := by
      rw [VG.Proof.Dsa.decodeBE_os2ip, VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt plt']
    have podd : pv % 2 = 1 := hpv ▸ VG.Proof.Dsa.Generation.pReduction_odd _ _
    have pbl : Spec.Dsa.bitLength pv = 8 * G.pLen :=
      (VG.Proof.Dsa.bitLength_iff_bounds (by omega_arith)).mpr ⟨by omega_arith, plt⟩
    unfold pAttCfg
    rw [hpv]
    simp only [hcnd, ↓reduceIte]
    generalize hc0 : pOut c G (Spec.Dsa.decodeBE (xBytes HO G k off)) (Spec.Dsa.decodeBE (qBytes G k))
      (pRest HO.md G k) = c0
    have cl0 : c0.cl = (sPBE, Spec.Rsa.i2osp pv G.pLen) :: pRest HO.md G k := by rw [← hc0, ← hpv]
    have eLS : c0.LS = c.LS := by rw [← hc0]
    have eV : c0.V = c.V := by rw [← hc0]
    have big : ∀ y ∈ c0.cl, y.1 + y.2.length ≤ 4096 := fun y hy => by
      rw [cl0] at hy
      simp only [pRest, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · simp only [VG.Proof.Rsa.i2osp_length]; omega_arith
      · simp only [pl]; omega_arith
      · simp only [ql]; omega_arith
    have pin : (sPBE, Spec.Rsa.i2osp pv G.pLen) ∈ c0.cl := by rw [cl0]; simp
    let c1 : Cfg := { c0 with cl := (sA, Spec.Rsa.i2osp pv G.pLen) :: c0.cl }
    refine VP.seq (G := St G c1 X) (copyS_vp (c := fun _ => c0) (fun σ s h => h.1.1.1) rfl (dst := sA) (src := sPBE)
      (n := G.pLen) (by omega_arith) (by omega_arith) (by simp only [sK, sA, wa]; omega_arith) (by simp only [sK, sA, wa]; omega_arith)
      (.inr (by omega_arith)) fun σ s t h R f e => ⟨?_, h.1.1.2⟩) ?_
    · have b := h.1.1.1.sb _ pin
      simp only [VG.Proof.Rsa.i2osp_length] at b
      refine h.1.1.1.of_scr R (o := sA) (n := G.pLen) (by simp only [sK, sA, wa]; omega_arith) (f.mono (by simp))
        fun y hy => ?_
      rcases List.mem_cons.mp hy with rfl | hy
      · exact .inr ⟨by rw [VG.Proof.Rsa.i2osp_length, e, b], by simp only [VG.Proof.Rsa.i2osp_length, sK, sA, wa]; omega_arith⟩
      · exact .inl ⟨hy, .inl (by have := big y hy; omega_arith)⟩
    refine VP.seq (test_vp (c := c1) (cb := Spec.Rsa.i2osp pv G.pLen) okp rfl hu (by simp only [c1, eLS]; exact hU)
      (by simp only [c1, eV]; exact hUv) hwl hsize (by simp only [wa]; omega_arith) (by simp [c1])
      (by rw [VG.Proof.Rsa.i2osp_length]; omega_arith) (by rw [pb]; exact podd) (by rw [pb]; exact pbl) (by simp only [c1, eLS]; exact h88) (by simp only [c1, eLS]; exact h92)
      (cl' := c0.cl) fun y hy => ⟨by simp [c1, hy], .inl (by have := big y hy; omega_arith)⟩) ?_
    rw [pb, show testCfg c1 c0.cl G.witLen (Spec.Dsa.probablePrime pv (G.witB.drop u)) =
      testCfg c0 c0.cl G.witLen (Spec.Dsa.probablePrime pv (G.witB.drop u)) by unfold testCfg; split <;> rfl]
    exact pDecide_vp _

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: the search for p

`pPart_vp`: the candidates of the counters 0, 1, … from a seed, until one is
a probable prime (`fP` := 1, p at `sPBE` and its arrays), the witnesses run
out (`fP` := 0) or the `4 L` counters are done (`fP` := 2), as
`Spec.Dsa.primeFromSeed` searches them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw wp_cmp op2_reg op2_imm dpVal eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

section
variable {G : GP} {X : State → Prop}

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and Z when the counter
reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 256) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 32 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 32 off)
    (hj : j + 1 < 2 ^ 16) :
    VP (St G d X) (VG.Impl.Rsa.Arm.Keys.seqs [
        .block [ld .r1 fCounter], .block [.dp .add .r1 .r1 (.imm 1)], .block (st .r1 fCounter),
        .block [ld .r2 fOffset], .block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 C))],
        .block (st .r2 fOffset), .block [.movw .r2 (BitVec.ofNat 16 (32 * G.pLen)), .cmp .r1 (.reg .r2)]])
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))) X σ s ∧
        isa.eval .eq s = some (decide (j + 1 = 32 * G.pLen))) := by
  have taint1 : ∀ σ₁ σ₂ (s₁ s₂ : State) (P : State → State → Prop) (v : BitVec 32), (P σ₁ s₁ ∧ s₁.gpr .r1 = v) →
      (P σ₂ s₂ ∧ s₂.gpr .r1 = v) → ∀ r ∈ [Reg.r1], s₁.gpr r = s₂.gpr r := fun _ _ _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  -- The counter.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hCt).trans hCv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .add .r1 .r1 (.imm 1)]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt (by decide : 1 < 256))) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by
          rw [u.gpr, dpVal, r1]; exact (BitVec.ofNat_add _ _).symm⟩) ?_
  have d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 32 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.seq (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' R => ⟨⟨r1 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  -- The offset.
  refine VP.seq (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1)) ∧ s.gpr .r2 = BitVec.ofNat 32 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 32 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => (h.1.1.slotV d1O).trans (by show upd d.V fCounter (BitVec.ofNat 32 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨h, x⟩, r1⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1)) ∧ s.gpr .r2 = BitVec.ofNat 32 (off + C))
    (VP.taint [.r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r2])
      (.block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r1⟩, r2⟩ => wp_dp (op2_imm (encodable_lt hC)) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, by
          rw [u.gpr, dpVal, r2]; exact (BitVec.ofNat_add _ _).symm⟩) ?_
  refine VP.seq (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
      (BitVec.ofNat 32 (off + C))) X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 32 (j + 1))) (fun σ s h => h.1.1.1) (by decide)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨h, x⟩, r1⟩, r2⟩ h' R => ⟨⟨r2 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  -- The end of the counters.
  refine VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.movw .r2 (BitVec.ofNat 16 1), .cmp .r1 (.reg .r2)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
    fun σ s ⟨⟨h, x⟩, r1⟩ => wp_movw fun t u => wp_cmp (op2_reg _ _) fun t' f z => WP.block_nil ?_
  have l := h.lens
  have r2 : t.gpr .r2 = BitVec.ofNat 32 (32 * G.pLen) := by rw [u.gpr, setWidth_ofNat16 (by omega_using [l])]
  refine ⟨⟨h.of_rest ((u.rest (ws := [.r2]) (by simp)).trans (f.rest _)) (by rw [f.mem, u.mem]), x⟩, ?_⟩
  rw [eval_eq, z, u.other _ (by decide), r1, r2, beq_sub_zero]
  congr 1
  by_cases e : j + 1 = 32 * G.pLen
  · simp [e]
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [hj, l, this]

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.seqs [
      .block [ld .r1 fCounter], .block [.dp .add .r1 .r1 (.imm 1)], .block (st .r1 fCounter),
      .block [ld .r2 fOffset], .block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 C))],
      .block (st .r2 fOffset), .block [.movw .r2 (BitVec.ofNat 16 (32 * L)), .cmp .r1 (.reg .r2)]],
    .ite .eq (.block (stImm fP 2)) (.block [])]) (.block [])) (.block (cmpF fP 4)))

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 256) (hP : fP ∈ d.LS) (hPv : d.V fP = 4)
    (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 32 j) (hOf : fOffset ∈ d.LS)
    (hOv : d.V fOffset = BitVec.ofNat 32 off) (hj : j + 1 < 2 ^ 16) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))).setV fP
            (BitVec.ofNat 32 2)) X σ s ∧ isa.eval .eq s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))) X σ s ∧
          isa.eval .eq s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval .eq s = some true)
    (cmpF_vp (c := fun _ => d) (x := 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
  have hO2 : fOffset ∈ (d.setV fCounter (BitVec.ofNat 32 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))).setV fP (BitVec.ofNat 32 2)) X σ s ∧ isa.eval .eq s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))).setV fP (BitVec.ofNat 32 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
              (BitVec.ofNat 32 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp))
      fun σ s t ⟨h, x⟩ R m e' => ⟨⟨h.of_rest R m, x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))) X σ s ∧ isa.eval .eq s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 32 (j + 1))) fOffset (BitVec.ofNat 32 (off + C)) fP = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨h, x⟩ R m e' => ⟨⟨h.of_rest R m, x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 32 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval .eq s = some false) := by
  have ne : (BitVec.ofNat 32 v == BitVec.ofNat 32 4) = false := by
    refine beq_false_of_ne fun h' => ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega_using [hv, this]
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval .eq s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 32 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 32 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t h R m e => ⟨⟨h.1.of_rest R m, h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The witnesses read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.witLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega_using [this]
    · split <;> omega_arith

/-- The search's frame words at counter `j`, with `u` witnesses read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 32 u)).setV fCounter (BitVec.ofNat 32 j)).setV fOffset
    (BitVec.ofNat 32 (1 + j * (cnt G + 1)))).setV fP 4

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.witB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aP, aE, aPm1, aOne]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) => ((pFound c HO G k p).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV fP 1
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 32 (G.witLen - r.length))).setV fP 2
  | none => (pNone c HO G).setV fP 0

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.witLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    fUsedOut + 4 ∉ c.LS

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 32} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = 4) (vO : V fOffset = BitVec.ofNat 32 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 32 j) (vU : V fUsed = BitVec.ofNat 32 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! # DSA parameter generation on ARMv7: an iteration of the search for p

`pGo_vp`: after a candidate that is not p, the next counter (or `fP` := 2
after the last); `pStop_vp`: after one that ends the search; `pBody_vp`:
the iteration, by the cases of `Spec.Dsa.primeFromSeed.search`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords)

section
variable {G : GP} {X : State → Prop} {Gh : Hash}

/-- The loop's postcondition after an iteration with `r` left. -/
abbrev pPost (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  isa.eval .eq s = some (decide (0 < r)) ∧ (r = 0 → St G (pFin c HO G k (pSpec HO G k u0 0)) X σ s) ∧
    (0 < r → pInv c HO G k u0 N X r σ s)

/-- After a candidate that is not p, the next counter (`u'` witnesses read). -/
theorem pGo_vp {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {k u0 N r j u' : Nat} {d : Cfg}
    (hjj : N - (r + 1) = j) (hr : r + 1 ≤ N) (hj : j < 32 * G.pLen) (hl : G.pLen ≤ 384)
    (hcnt : cnt G + 1 < 256) (hwl : G.witB.length = G.witLen)
    (hc : pCount HO G k u0 (32 * G.pLen - 1 - j) j = N) (hR : pSpec HO G k u0 j = pSpec HO G k u0 0)
    (hstep : ∀ m, pCount HO G k u0 (m + 1) j = pCount HO G k u0 m (j + 1))
    (hpu : pU HO G k u0 (j + 1) = u')
    (hspec : pSpec HO G k u0 j = VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen)
      (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (j + 1) (G.witB.drop u'))
    (hu' : u' ≤ G.witLen)
    (dP : fP ∈ d.LS) (dPv : d.V fP = 4) (dC : fCounter ∈ d.LS) (dCv : d.V fCounter = BitVec.ofNat 32 j)
    (dO : fOffset ∈ d.LS) (dOv : d.V fOffset = BitVec.ofNat 32 (1 + j * (cnt G + 1)))
    (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 32 u')
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) (pTail (cnt G + 1) G.pLen) (pPost c HO G k u0 N X r) := by
  refine (pCont_vp (X := X) hcnt dP dPv dC dCv dO dOv (by omega_arith)).mono (fun _ _ h => h) fun σ s h => ?_
  split at h
  · -- The last counter: `fP` := 2.
    rename_i e
    obtain hN : N = j + 1 := by
      rw [show 32 * G.pLen - 1 - j = 0 by omega_arith] at hc; simp only [pCount] at hc; omega_arith
    obtain r0 : r = 0 := by omega_arith
    subst r0
    refine ⟨by rw [h.2]; rfl, fun _ => ⟨?_, h.1.2⟩, fun h0 => absurd h0 (by decide)⟩
    obtain hd : pSpec HO G k u0 0 = some (none, G.witB.drop u') := by
      rw [← hR, hspec, VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega_arith)]
    rw [hd]; simp only [pFin]
    obtain lu : G.witLen - (G.witB.drop u').length = u' := by rw [List.length_drop, hwl]; omega_arith
    refine h.1.1.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp))
      (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: fUsed :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | rfl | ho
      · exact ⟨by simp, by simp [upd]⟩
      · refine ⟨by simp [dU], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide),
          upd_self, dUv, lu]
      · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
        refine ⟨by simp [(dLS o ho).1], ?_⟩
        dsimp only [Cfg.setV]
        rw [upd_ne _ _ n4, upd_ne _ _ n3, upd_ne _ _ n2, upd_ne _ _ n4, upd_ne _ _ n1, (dLS o ho).2]
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact dpad
  · -- The next counter.
    rename_i e
    obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨32 * G.pLen - 1 - j - 1, by omega_arith⟩
    rw [hm, hstep] at hc
    obtain hgt := pCount_gt HO G k u0 m (j + 1)
    obtain rpos : 0 < r := by omega_arith
    obtain hNr : N - r = j + 1 := by omega_arith
    refine ⟨by rw [h.2]; simp [rpos], fun h0 => absurd h0 (by omega_arith), fun _ => ?_⟩
    show (_ ∧ _) ∧ _
    rw [hNr, hpu]
    refine ⟨⟨by omega_arith, by omega_arith, by rw [show 32 * G.pLen - 1 - (j + 1) = m by omega_arith]; exact hc,
      by rw [← hR, hspec]; simp only [pSpec, hpu], hu'⟩, ?_, h.1.2⟩
    have h1 := h.1.1
    have gi := h1.gi
    have big := gi.scrBig
    obtain r1 := h1.reclaim (cl' := [(G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)])
      fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨h1.sb _ dpad, h1.clOk _ dpad⟩
        · exact ⟨by simp [Spec.Rsa.bytesAt], by simp only [pStart, sX, sK, sA, wa, List.length_nil]; omega_arith⟩
        · exact ⟨h1.sb _ dq, h1.clOk _ dq⟩
    obtain eo : 1 + j * (cnt G + 1) + (cnt G + 1) = 1 + (j + 1) * (cnt G + 1) := by rw [Nat.succ_mul]; omega_arith
    refine r1.mono (pCfgJ_V hn (fun o ho => ?_) (by simp [dP]) (by simp) (by simp [dC]) (by simp [dU]) ?_ ?_ ?_ ?_ ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · simp [(dLS o ho).1]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dPv]
    · dsimp only [Cfg.setV]
      rw [upd_self, eo]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_self]
    · dsimp only [Cfg.setV]
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), dUv]
    · intro o ho
      obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
      dsimp only [Cfg.setV]
      rw [upd_ne _ _ n3, upd_ne _ _ n2, (dLS o ho).2]

/-- After a candidate that ends the search. -/
theorem pStop_vp {c : Cfg} {HO : HashOk Gh} {k u0 N r j v C : Nat} {d : Cfg} (hjj : N - (r + 1) = j)
    (hr : r + 1 ≤ N) (hN : N = j + 1) (dP : fP ∈ d.LS) (dPv : d.V fP = BitVec.ofNat 32 v) (hv : v < 4)
    (fin : ∀ σ s, SS G σ d s → SS G σ (pFin c HO G k (pSpec HO G k u0 0)) s) :
    VP (St G d X) (pTail C G.pLen) (pPost c HO G k u0 N X r) := by
  obtain r0 : r = 0 := by omega_arith
  subst r0
  exact (pExit_vp dP dPv hv).mono (fun _ _ h => h) fun σ s ⟨⟨h, x⟩, e⟩ =>
    ⟨by rw [e]; rfl, fun _ => ⟨fin σ s h, x⟩, fun h0 => absurd h0 (by decide)⟩

theorem pBody_vp {g : Geo} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    {c : Cfg} (hn : PNot c) {k u0 N : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j) (r : Nat) :
    VP (pInv c HO G k u0 N X (r + 1)) (VG.Impl.Rsa.Arm.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
        .ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [g.pAdvance, .ite .eq (.block (stImm fP 2)) (.block [])]) (.block []),
        .block (cmpF fP 4)])
      (pPost c HO G k u0 N X r) := by
  refine VG.Proof.Dsa.Arm.Gen.VP.intro fun ⟨hr, hj, hc, hR, hu⟩ => ?_
  generalize hjj : N - (r + 1) = j at hj hc hR hu
  obtain hl : G.pLen ≤ 384 := by omega_arith
  obtain hcnt : cnt G + 1 ≤ 12 := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [cnt, e1, e2] <;> decide
  obtain hcount : g.count = cnt G := by simp only [Geo.count, hp, hq, cnt]
  obtain ecode : VG.Impl.Rsa.Arm.Keys.seqs [g.pAttempt, .block (cmpF fP 4),
      .ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [g.pAdvance, .ite .eq (.block (stImm fP 2)) (.block [])]) (.block []),
      .block (cmpF fP 4)] = .seq g.pAttempt (pTail (cnt G + 1) G.pLen) := by
    simp only [Geo.pAdvance, hcount, hp]; rfl
  rw [ecode]
  obtain hoffb : 1 + j * (cnt G + 1) + (cnt G + 1) < 2 ^ 24 := by
    have := Nat.mul_le_mul (Nat.le_of_lt hj) hcnt; omega_arith
  have nn := hn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nn
  -- The spec's step.
  obtain hstepS := VG.Proof.Dsa.Generation.primeSearch_step (l := 8 * G.pLen) (n := 8 * G.qLen)
    (q := Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) (G.witB.drop (pU HO G k u0 j)) (by omega_arith : j < 4 * (8 * G.pLen))
  dsimp only at hstepS
  rw [hcand j] at hstepS
  change pSpec HO G k u0 j = _ at hstepS
  -- The candidate.
  refine VP.seq ((pAttempt_vp (X := X) (c := pCfgJ c HO G k j (pU HO G k u0 j)) (off := 1 + j * (cnt G + 1))
    HO okp certs hlq hp hq hk4 hsb hH hwl hsize hk hu (by simp [hS]) (by simp [upd, hn.ne hS]; exact hSv) (by simp)
    (by simp [upd, fOffset, fP]) hoffb (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, n6⟩)
    (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, by decide, by decide, n7⟩)).mono (fun _ _ h => h) fun _ _ h => h) ?_
  obtain hN1 : ∀ (hlast : ∀ m, pCount HO G k u0 (m + 1) j = j + 1), N = j + 1 := fun hlast => by
    rw [← hc]
    rcases Nat.eq_zero_or_pos (32 * G.pLen - 1 - j) with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨m, hm⟩ : ∃ m, 32 * G.pLen - 1 - j = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, hlast]
  obtain padIn : ∀ x : Nat × List Byte, (G.qLen, padTail HO.md G.qLen) ∈ x :: pRest HO.md G k := by simp [pRest]
  obtain qIn : ∀ x : Nat × List Byte, (sQ, qBytes G k) ∈ x :: pRest HO.md G k := by simp [pRest]
  by_cases hs : pShort HO G k j
  · -- Too short: the next counter.
    rw [pAttCfg, ite_eq_left_of_eq_true _ _ (eq_true hs)]
    refine pGo_vp hn hjj (by omega_arith) hj hl (by omega_arith) hwl hc hR
      (fun m => by simp only [pCount]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by simp only [pU]; exact ite_eq_left_of_eq_true _ _ (eq_true hs))
      (by rw [hstepS]; exact ite_eq_left_of_eq_true _ _ (eq_true hs)) hu
      (by simp) (by simp [upd]) (by simp) (by simp [upd, fCounter, fOffset, fP]) (by simp)
      (by simp [upd, fOffset, fP]) (by simp) (by simp [upd, fUsed, fCounter, fOffset, fP])
      (fun o ho => ⟨by simp [ho], by obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho; simp [upd, m1, m2, m3, m4]⟩)
      (padIn _) (qIn _)
  rw [pAttCfg, ite_eq_right_of_eq_false _ _ (eq_false hs)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at hstepS
  rcases hpp : Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with _ | ⟨b, rr⟩
  · -- The witnesses ran out: `fP` := 0.
    rw [hpp] at hstepS
    refine pStop_vp (v := 0) hjj (by omega_arith) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte]) (by simp [pRes])
      (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => ?_) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    · change o ∈ fP :: c.LS at ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
      · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
        exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩
    · change y ∈ [(G.qLen, padTail HO.md G.qLen)] at hy
      rw [List.mem_singleton] at hy; subst hy; exact padIn _
  rcases b
  · -- Not a prime: the next counter.
    rw [hpp] at hstepS
    simp only [Bool.false_eq_true, ↓reduceIte] at hstepS
    refine pGo_vp (u' := G.witLen - rr.length) hn hjj (by omega_arith) hj hl (by omega_arith) hwl hc hR
      (fun m => by simp only [pCount, hs, hpp, ↓reduceIte])
      (by simp only [pU, hs, hpp, ↓reduceIte])
      (by rw [hstepS, ← hwl, VG.Proof.Dsa.Generation.probablePrime_cursor hpp]) (by omega_arith)
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fCounter, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd, fOffset, fP, fRes, fUsed])
      (by simp [pRes, testCfg]) (by simp [pRes, testCfg, upd])
      (fun o ho => ⟨by simp [pRes, testCfg, ho], by
        obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho; simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩)
      (by simp [pRes, testCfg, pRest]) (by simp [pRes, testCfg, pRest])
  · -- A probable prime: `fP` := 1.
    rw [hpp] at hstepS
    simp only [↓reduceIte] at hstepS
    refine pStop_vp (v := 1) hjj (by omega_arith) (hN1 fun m => by simp only [pCount, hs, hpp, ↓reduceIte]) (by simp [pRes])
      (by simp [pRes, upd]) (by decide) fun σ s h => ?_
    rw [← hR, hstepS]; simp only [pFin]
    refine h.mono (fun o ho => ?_) (fun y hy => hy) (fun _ h' => ⟨h', rfl⟩) (fun _ h' => absurd h' (by simp))
    change o ∈ fP :: fUsed :: c.LS at ho
    simp only [List.mem_cons] at ho
    rcases ho with rfl | rfl | ho
    · exact ⟨by simp [pRes], by simp [pRes, upd]⟩
    · exact ⟨by simp [pRes, testCfg], by simp [pRes, testCfg, upd, fUsed, fP]⟩
    · obtain ⟨m1, m2, m3, m4, m5⟩ := hn.ne ho
      exact ⟨by simp [pRes, testCfg, ho], by simp [pRes, testCfg, upd, m1, m2, m3, m4, m5]⟩

/-- The search for p from the seed at `k`, with `u0` witnesses read. -/
theorem pPart_vp {g : Geo} (HO : HashOk g.G) (okp : PrimeOk (8 * G.pLen) g.pCode)
    (certs : PArithCerts G.pLen G.qLen)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hp : g.pLen = G.pLen) (hq : g.qLen = G.qLen) (hk4 : 4 * g.G.k = G.qLen) (hsb : G.seedsB.length = G.seedsLen)
    (hH : ∀ m, HO.H m = Spec.Dsa.seedHash (8 * G.qLen) m) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords (8 * G.pLen) ≤ wa G.pLen)
    {c : Cfg} (hn : PNot c) {k u0 : Nat} (hk : k + G.qLen ≤ G.seedsLen) (hS : fSeed ∈ c.LS)
    (hSv : c.V fSeed = G.seeds + BitVec.ofNat 32 k) (hu0 : u0 ≤ G.witLen)
    (hcand : ∀ j, Spec.Dsa.pCandidate (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k)
      (1 + j * ((8 * G.pLen - 1) / (8 * G.qLen) + 1)) = pCand HO G k j)
    {d : Cfg} (dU : fUsed ∈ d.LS) (dUv : d.V fUsed = BitVec.ofNat 32 u0)
    (dLS : ∀ o ∈ c.LS, o ∈ d.LS ∧ d.V o = c.V o)
    (dpad : (G.qLen, padTail HO.md G.qLen) ∈ d.cl) (dq : (sQ, qBytes G k) ∈ d.cl) :
    VP (St G d X) g.pPart (St G (pFin c HO G k (pSpec HO G k u0 0)) X) := by
  unfold Geo.pPart
  obtain hN := pCount_gt HO G k u0 (32 * G.pLen - 1) 0
  generalize hNN : pCount HO G k u0 (32 * G.pLen - 1) 0 = N at hN
  obtain hl : G.pLen ≤ 384 := by omega_arith
  obtain hpL : 0 < G.pLen := by omega_arith
  refine VP.seq (G := St G (d.setV fCounter (BitVec.ofNat 32 0)) X)
    (stImm_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (varOk_of (by decide))
      fun σ s t h h' _ => ⟨h', h.2⟩) ?_
  refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 32 0)).setV fOffset (BitVec.ofNat 32 1)) X)
    (stImm_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 32 0)) (fun σ s h => h.1) (by decide)
      (varOk_of (by decide)) fun σ s t h h' _ => ⟨h', h.2⟩) ?_
  refine VP.seq (G := pInv c HO G k u0 N X N)
    (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 32 0)).setV fOffset (BitVec.ofNat 32 1))
      (fun σ s h => h.1) (by decide) (varOk_of (by decide)) fun σ s t h h' _ => ⟨⟨Nat.le_refl _, by simp; omega_arith,
        by simp only [Nat.sub_self, Nat.sub_zero]; exact hNN, by rw [Nat.sub_self], by simp only [Nat.sub_self]; exact hu0⟩, ?_, h.2⟩) ?_
  · have gi := h'.gi
    have big := gi.scrBig
    obtain r1 := h'.reclaim (cl' := [(G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)])
      fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨h'.sb _ dpad, h'.clOk _ dpad⟩
        · exact ⟨by simp [Spec.Rsa.bytesAt], by simp only [pStart, sX, sK, sA, wa, List.length_nil]; omega_arith⟩
        · exact ⟨h'.sb _ dq, h'.clOk _ dq⟩
    rw [Nat.sub_self]
    refine r1.mono (pCfgJ_V hn (fun o ho => by simp [(dLS o ho).1]) (by simp) (by simp) (by simp) (by simp [dU])
      (by simp [upd]) (by simp [upd, fOffset, fP]) (by simp [upd, fCounter, fOffset, fP])
      (by simp [upd, fUsed, fCounter, fOffset, fP, pU]; exact dUv) fun o ho => ?_)
      (fun y hy => hy) (fun _ h' => absurd h' (by simp)) (fun _ h' => absurd h' (by simp))
    obtain ⟨m1, m2, m3, m4, -⟩ := hn.ne ho
    simp [upd, m2, m3, m4]; exact (dLS o ho).2
  rw [show N = N - 1 + 1 by omega_arith]
  exact VP.loop (I := pInv c HO G k u0 (N - 1 + 1) X)
    (pBody_vp HO okp certs hlq hp hq hk4 hsb hH hwl hsize hn hk hS hSv hcand) _

end

end VG.Proof.Dsa.Arm.Gen
