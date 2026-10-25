module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# An FFDH parameter candidate on AArch64: the candidate `p`

`shapeP` (`shapeP_ok`): the first `out_len` octets of the tape into `aN`
(`loadA`), then its top word and'ed with `fTop = 2^k − 1` and bit `k − 1`
set, and its low bit set: `candidateOf bits` of their number (`wv_shape`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- A prefix of a source. -/
theorem src_take {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) (n : Nat) :
    Src s B Z p (bs.take n) :=
  ⟨fun i hi => h.rd i (by rw [List.length_take] at hi; omega_arith), fun i hi => by
    rw [List.getElem_take]; exact h.val i (by rw [List.length_take] at hi; omega_arith),
    fun i hi => h.out i (by rw [List.length_take] at hi; omega_arith)⟩

/-- A suffix of a source, at its offset. -/
theorem src_drop {s : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs) (n : Nat) :
    Src s B Z (p + BitVec.ofNat 64 n) (bs.drop n) := by
  have e : ∀ i, p + BitVec.ofNat 64 n + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (n + i) := fun i => by
    rw [BitVec.add_assoc, ofNat_add_ofNat]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [e]; exact h.rd (n + i) (by rw [List.length_drop] at hi; omega_arith)
  · rw [e, List.getElem_drop]; exact h.val (n + i) (by rw [List.length_drop] at hi; omega_arith)
  · rw [e]; exact h.out (n + i) (by rw [List.length_drop] at hi; omega_arith)

theorem shr1_add1 {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64) :
    BitVec.ofNat 64 (2 ^ k - 1) >>> 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 ^ (k - 1)) := by
  rw [shr_ofNat, Nat.mod_eq_of_lt (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk; omega_arith),
    ofNat_add_ofNat]
  congr 1
  have e : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← Nat.pow_succ']; congr 1; omega_arith
  have := Nat.two_pow_pos (k - 1)
  rw [e]; omega_arith

/-- The shaping block, from `aN` holding the loaded number. -/
theorem shapeBlock_ok {s : State} {B : Addr} {Z w k : Nat} (h : Ws s B Z w) (hk1 : 1 ≤ k) (hk : k ≤ 64)
    (hT : word s.mem B (8 * fTop) = BitVec.ofNat 64 (2 ^ k - 1)) :
    WP isa (.block (ws ++ base aN .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8,
      ldh .x4 fTop, ld .x3 .x16, ld .x6 .x5, movi .x9 1, .logic .orr .x .x3 .x3 .x9, .logic .and .x .x6 .x6 .x4,
      .lsr .x .x9 .x4 1, .addImm .x .x9 .x9 1, .logic .orr .x .x6 .x6 .x9, st .x3 .x16, st .x6 .x5] : List Instr))) s fun t =>
      wv t.mem B (slot w aN) w = Spec.Ffdh.candidateOf (64 * (w - 1) + k) (wv s.mem B (slot w aN) w) ∧
      Frm B [(slot w aN, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have hTs : 8 * fTop + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  have one16 : (1#16).setWidth 64 = (1 : BitVec 64) := rfl
  have hsel := shr1_add1 hk1 hk
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x9] (Q := fun t => t.mem =
      (s.mem.writeW (off B (slot w aN)) (bot ||| 1)).writeW (off B (slot w aN + 8 * (w - 1)))
        ((top &&& BitVec.ofNat 64 (2 ^ k - 1)) ||| BitVec.ofNat 64 (2 ^ (k - 1)))) (by
    brun [hm₂, h16, e12, h0₂, one16, hb, ht, hT, hsel,
      top_addr B (d := slot w aN) (w := w) (by omega_arith) (by omega_arith),
      hs₂.ld (d := slot w aN) (by omega_arith), hs₂.st (d := slot w aN) (by omega_arith),
      hs₂.ld (d := slot w aN + 8 * (w - 1)) (by omega_arith), hs₂.st (d := slot w aN + 8 * (w - 1)) (by omega_arith),
      hdr_enc (show fTop < 32 by decide), hs₂.ld (d := 8 * fTop) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm]
    refine VG.Proof.Ffdh.ParameterCandidate.wv_shape (by omega_arith) hk1 hk ?_ ?_ ?_
    · rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), word_writeW_self, hb]
    · rw [word_writeW_self, ht]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith),
      writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega_arith)]

/-- `shapeP`: `p` into `aN`. -/
theorem shapeP_ok {s : State} {p : PP} (h : PSt p (mW p.bits) s)
    (hK : word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.L)
    (hT : word s.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1)) (hr : p.L ≤ p.r.length) :
    WP isa (seqs shapeP) s fun t =>
      PSt p (mW p.bits) t ∧
      wv t.mem p.B (slot (mW p.bits) aN) (mW p.bits) =
        Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)) ∧
      Frm p.B [(slot (mW p.bits) aN, 8 * (mW p.bits + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hws := h.ws
  have hn := hws.scr.nowrap
  have sN := hws.sl (show aN < 16 by decide)
  have hTs : 8 * fTop + 8 ≤ slot (mW p.bits) aN := hdr_lt_slot _ aN (by decide)
  unfold shapeP
  refine wp_seqs_append (by simp [loadA]) (by simp) ?_
  refine WP.mono (loadA_ok hws (j := aN) (sPtr := kRand) (sLen := kLen) (len := p.L) (bs := p.r.take p.L)
    (by decide) (by decide) (by decide) h.args.rand hK (src_take h.src p.L) (by rw [List.length_take]; omega_arith)
    (by simp only [PP.L]; omega_arith) (by simp only [PP.L, mW]; omega_arith)) fun s₁ ⟨hv₁, o₁, _, _, k₁⟩ => ?_
  have f₁ : Frm p.B [(slot (mW p.bits) aN, 8 * (mW p.bits + 2))] s.mem s₁.mem := Frm.of_outside o₁ (by simp)
  have st₁ : PSt p (mW p.bits) s₁ :=
    h.step (hws.congr' f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k₁ (by decide))
      f₁ (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) k₁
  have hT₁ : word s₁.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1) := by
    rw [f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl hTs) (by omega_arith)]; exact hT
  rw [seqs_one]
  refine WP.mono (shapeBlock_ok st₁.ws (by simp only [mK, mW]; omega_arith) (by simp only [mK, mW]; omega_arith) hT₁)
    fun t ⟨hv, f₂, k₂⟩ => ⟨st₁.step (st₁.ws.congr' f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact KMut.ofSlot _ _ _) k₂ (by decide)) f₂
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.ofSlot _ _ _)
      (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) k₂, ?_, f₁.trans f₂,
      (k₁.trans k₂).mono (by decide)⟩
  rw [hv, hv₁, show 64 * (mW p.bits - 1) + mK p.bits = p.bits by simp only [mK, mW]; omega_arith]

end VG.Proof.Ffdh.AArch64.ParameterCandidate
