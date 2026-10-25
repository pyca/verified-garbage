module

public import VerifiedGarbage.Proof.RsaPss.Arm.VfAcc
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.VfAcc
meta import VerifiedGarbage.Proof.RsaPss.VerifyCases
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS verification with a precomputed public key on ARMv7: the end of the padding

`scan_vp`: the scan of `DB` finds the index (`pzF`) and the value (`vzF`) of
its first byte that is not zero, if any (`nfW`), without a branch; then
`acc` takes in that this byte is `0x01` and, if a salt length is expected,
that the salt after it has that length (`pos_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Vf

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.RsaPss.Arm.Sg (add_ofNat_sub_one)

variable (h : PssHash)

/-- `DB`, as a list. -/
abbrev dbL (P : EP) (τ : State) : List Byte := (List.range (dbN h P)).map (dbF h P τ)

/-- Where the padding ends. -/
abbrev lzF (P : EP) (τ : State) : Nat := RsaPss.lz (dbL h P τ)

/-- The index and value of `DB`'s first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzJ (P : EP) (τ : State) (j : Nat) : Nat := if lzF h P τ < j then lzF h P τ else 0
abbrev vzJ (P : EP) (τ : State) (j : Nat) : Byte := if lzF h P τ < j then dbF h P τ (lzF h P τ) else 0
abbrev nfJ (P : EP) (τ : State) (j : Nat) : BitVec 32 := if lzF h P τ < j then 0 else BitVec.allOnes 32

theorem bz : ∀ b : Byte, (b.setWidth 32 - 1) >>> 31 = if b = 0 then 1 else 0 := by decide

/-- After `j` bytes of the scan. -/
structure SC (P : EP) (τ : State) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + j)
  r1 : s.gpr .r1 = BitVec.ofNat 32 j
  lr : s.gpr .lr = BitVec.ofNat 32 (dbN h P - j)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (pzJ h P τ j)
  r5 : s.gpr .r5 = (vzJ h P τ j).setWidth 32
  r6 : s.gpr .r6 = nfJ h P τ j
  r7 : s.gpr .r7 = 0

theorem scanBody_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block scanBody) hc).isSome = true := ⟨_, by taint_decide⟩

theorem dbL_getD {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) : (dbL h P τ).getD j 0 = dbF h P τ j := by
  simp [dbL, List.getD_eq_getElem?_getD, hj]

/-- One byte of the scan. -/
theorem scan_step {P : EP} {τ : State} {j : Nat} (hj : j < dbN h P) (b : Byte) (hb : b = dbF h P τ j) :
    let r3 : BitVec 32 := if b = 0 then 1 else 0
    let r8 := (r3 - 1) &&& nfJ h P τ j
    BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&& r8 = BitVec.ofNat 32 (pzJ h P τ (j + 1)) ∧
    (vzJ h P τ j).setWidth 32 ||| b.setWidth 32 &&& r8 = (vzJ h P τ (j + 1)).setWidth 32 ∧
    nfJ h P τ j &&& (0 - r3) = nfJ h P τ (j + 1) := by
  intro r3 r8
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt : lzF h P τ ≤ dbN h P := by
    have e := RsaPss.lz_le (dbL h P τ)
    rw [show (dbL h P τ).length = dbN h P by simp [dbL]] at e
    exact e
  rcases Nat.lt_trichotomy (lzF h P τ) j with hl | hl | hl
  · have h8 : r8 = 0 := by simp only [r8, nfJ, ite_eq_left hl, az]
    simp only [h8, az, oz, pzJ, vzJ, nfJ, ite_eq_left hl, ite_eq_left (by omega_arith : lzF h P τ < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← dbL_getD h (by omega_arith)]
      exact RsaPss.getD_lz_ne (by
        show lzF h P τ < (dbL h P τ).length
        rw [show (dbL h P τ).length = dbN h P by simp [dbL]]; omega_arith)
    have h3 : r3 = 0 := by simp only [r3, hne, ite_false]
    have h8 : r8 = BitVec.allOnes 32 := by
      simp only [r8, h3, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith)]; decide
    simp only [h8, h3, BitVec.and_allOnes, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith),
      ite_eq_left (show lzF h P τ < j + 1 by omega_arith)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← dbL_getD h hj]; exact RsaPss.getD_lt_lz hl
    have h3 : r3 = 1 := by simp only [r3, hz, ite_true]
    have h8 : r8 = 0 := by
      simp only [r8, h3]; rw [show (1 : BitVec 32) - 1 = 0 by decide, za]
    simp only [h8, h3, az, oz, pzJ, vzJ, nfJ, ite_eq_right (show ¬ lzF h P τ < j by omega_arith),
      ite_eq_right (show ¬ lzF h P τ < j + 1 by omega_arith)]
    exact ⟨trivial, trivial, by decide⟩

/-- The scan of `DB`. -/
theorem scan_vp (P : EP) (hP : ∃ σ, In h.D P σ) {X : State → Mem → Prop}
    (hX : ∀ τ m, X τ m → ∀ i < dbN h P, m (sa P.scr (oEm + lo P + i)) = dbF h P τ i) :
    VP (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧ fits h P ∧ SC h P τ 0 s)
      (countLoop scanBody)
      (fun τ s => Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧ fits h P ∧ SC h P τ (dbN h P) s) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.2.2.1
  obtain ⟨hlo, hdb, hsum, hK, hD, hD0, hK0⟩ := fitB h hi₀ hf
  have e1 : oEm = 1024 := rfl
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k τ s => k ≤ dbN h P ∧ Ctx (P.lay h.D) P.scr τ s ∧ X τ s.mem ∧
    fits h P ∧ SC h P τ (dbN h P - k) s
  refine (VP.loop (I := I) (fun k => ?_) (dbN h P - 1)).mono (fun τ s ⟨hc, hx, hf', hs⟩ => ⟨by omega_arith, hc, hx, hf',
    by rw [show dbN h P - (dbN h P - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun τ s ⟨hk, hc, hx, hf', hs⟩ => ?_
  · obtain ⟨-, -, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : dbN h P - (k + 1) = j at hs
  have hjn : j < dbN h P := by omega_arith
  have ad : State.addr (P.scr + BitVec.ofNat 32 (oEm + lo P + j)) = sa P.scr (oEm + lo P + j) := hg.addr (by omega_arith)
  have rd : InRegions (s.rd ++ s.wr) (sa P.scr (oEm + lo P + j)) 1 := hg.rd hc.st (by omega_arith)
  have lr1 : BitVec.ofNat 32 (dbN h P - j) - 1 = BitVec.ofNat 32 (dbN h P - (j + 1)) := by
    rw [show dbN h P - j = (dbN h P - (j + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  have hw : WP isa (.block scanBody) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + lo P + (j + 1)) ∧ t.gpr .r1 = BitVec.ofNat 32 (j + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (dbN h P - (j + 1)) ∧
      t.gpr .r4 = BitVec.ofNat 32 (pzJ h P τ j) ||| BitVec.ofNat 32 j &&&
        ((if dbF h P τ j = 0 then 1 else 0) - 1 &&& nfJ h P τ j) ∧
      t.gpr .r5 = (vzJ h P τ j).setWidth 32 ||| (dbF h P τ j).setWidth 32 &&&
        ((if dbF h P τ j = 0 then 1 else 0) - 1 &&& nfJ h P τ j) ∧
      t.gpr .r6 = nfJ h P τ j &&& (0 - if dbF h P τ j = 0 then 1 else 0) ∧ t.gpr .r7 = 0 ∧
      t.z = decide (dbN h P - (j + 1) = 0) := by
    prun [scanBody, hs.r0, hs.r1, hs.lr, hs.r4, hs.r5, hs.r6, hs.r7, ad, rd, hX τ s.mem hx j hjn, bz, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 _
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  refine WP.mono hw fun t ⟨m, rd', wr, sp, r0, r1, lr, r4, r5, r6, r7, z⟩ => ?_
  have st := scan_step h hjn _ rfl (τ := τ)
  have hc' : Ctx (P.lay h.D) P.scr τ t := hc.regs rd' wr sp m
  have hx' : X τ t.mem := m ▸ hx
  have sk : SC h P τ (j + 1) t :=
    ⟨r0, r1, lr, by rw [r4]; exact st.1, by rw [r5]; exact st.2.1, by rw [r6]; exact st.2.2, r7⟩
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show dbN h P - (j + 1) = k by omega_arith]; cases k <;> simp,
    fun h0 => ⟨hc', hx', hf', by rw [show dbN h P = j + 1 by omega_arith]; exact sk⟩,
    fun hpos => ⟨by omega_arith, hc', hx', hf', by rw [show dbN h P - k = j + 1 by omega_arith]; exact sk⟩⟩

end VG.Proof.RsaPss.Arm.Vf
