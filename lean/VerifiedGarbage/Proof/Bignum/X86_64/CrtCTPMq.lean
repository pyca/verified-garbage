module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTPSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# RSA with the CRT on x86-64: constant time, `m_q G mod n`

`mqSteps` (`mqPart_ok`) is constant time (`mq_ct`) for a predicate (`Mq0`)
that carries, before each piece, its claim's hypotheses and what
correctness gives after it; `mq_chain` proves it from `mqPart_ok`'s
hypotheses, as `mqPart_ok` runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `mqSteps`: the modulus' workspace and `q`'s. -/
structure MqPub where
  B : Addr
  Z : Nat
  w : Nat
  oq : Nat
  wq : Nat

/-- The modulus' workspace. -/
abbrev MqPub.ws (p : MqPub) : Ws := ⟨p.B, p.Z, p.w⟩

/-- `mqSteps`' block loading `q`'s `Y`: `q`'s base, then from it. -/
def mqBlk1 : List Instr := [.mov .rax (.mem (hdr sWsQ))]

def mqBlk2 : List Instr :=
  [.mov .rsi (.mem (ws .rax (sArr Public.aY))), .mov .r12 (.mem (ws .rax sW)), .mov .rbx (.mem (hdr (sArr Public.aX)))]

theorem mqSteps_eq (mul : Nat → Nat → Nat → Prog isa) :
    seqs (mqSteps mul) = .seq (zeroArr Public.aX) (.seq (.block (mqBlk1 ++ mqBlk2)) (.seq copyWords
      (.seq (mul Public.aX Public.aX Public.aR2) (mul Public.aX Public.aX Public.aY)))) := rfl

/-- Before `X := X R² R⁻¹`. -/
def Mq3 (M : Mont) (p : MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (M.mm Public.aX Public.aX Public.aR2) s (GoodW p.ws)

/-- Before the copy of `m_q`. -/
def Mq2 (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .rsi = off (off p.B p.oq) (slot p.wq Public.aY) ∧ s.gpr .r12 = BitVec.ofNat 64 p.wq ∧
    s.gpr .rbx = off p.B (slot p.w Public.aX) ∧ WP isa copyWords s (Mq3 M p)

/-- Before the loads from `q`'s workspace. -/
def Mq1b (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .rax = off p.B p.oq ∧ s.gpr .rdi = p.B ∧ WP isa (.block mqBlk2) s (Mq2 M p)

/-- Before the load of `q`'s base. -/
def Mq1 (M : Mont) (p : MqPub) (s : State) : Prop :=
  s.gpr .rdi = p.B ∧ WP isa (.block mqBlk1) s (Mq1b M p)

/-- Before `mqSteps`. -/
def Mq0 (M : Mont) (p : MqPub) (s : State) : Prop :=
  GoodW p.ws s ∧ WP isa (zeroArr Public.aX) s (Mq1 M p)

/-- `mqSteps` is constant time. -/
theorem mq_ct (M : Mont) : RelCT isa (Two (Mq0 M)) (seqs (mqSteps M.mm)) fun _ _ => True := by
  rw [mqSteps_eq]
  refine ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (zeroArr_ct (by decide) (by taint_decide)) ?_
  have b1 : RelCT isa (Two (Mq1 M)) (.block mqBlk1) (Two (Mq1b M)) :=
    two_piece [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) fun _ _ h => h.2
  have b2 : RelCT isa (Two (Mq1b M)) (.block mqBlk2) (Two (Mq2 M)) :=
    two_piece [.rax, .rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]) (by taint_decide) fun _ _ h => h.2.2
  refine RelCT.seq (RelCT.block_append (RelCT.seq b1 b2)) ?_
  refine ct_taint [.rsi, .r12, .rbx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]) (by taint_decide) (fun _ _ h => h.2.2.2) ?_
  exact ct_step MqPub.ws (fun _ _ h => h.1) (fun _ _ h => h.2) (M.ct (by unfold MmUse; decide))
    (ct_last MqPub.ws (fun _ _ h => h) (M.ct (by unfold MmUse; decide)))

/-- `mqPart_ok`'s hypotheses give `Mq0`. -/
theorem mq_chain (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv mq : BitVec 64} {N oq wq : Nat}
    (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hN : NVals s B w minv N)
    (hq : word s.mem B (8 * sWsQ) = off B oq) (hws : WsAt s.mem B oq wq mq) (hlo : slot w 8 ≤ oq)
    (hhi : oq + slot wq 8 + wsTab wq ≤ Z) (hwq : 1 ≤ wq) (hwq' : wq ≤ w) : Mq0 M ⟨B, Z, w, oq, wq⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have lX := slot_le (w := w) (show Public.aX < 8 by decide)
  have hX0 := hdr_lt_slot w Public.aX (show 31 < 32 by decide)
  have hY8 := slot_le (w := wq) (show Public.aY < 8 by decide)
  have hq8 : 8 * 32 ≤ slot wq 8 := by unfold slot hdrBytes; omega
  have hqo : oq < 2 ^ 64 := by omega
  -- `X := 0`.
  refine ⟨⟨minv, hg, show slot w 8 ≤ Z by omega⟩, WP.mono (zeroArr_ok hg (by omega) (by omega) (by omega)
    (show Public.aX < 8 by decide)) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_⟩
  have hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega)
  have hq₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega)) hd'
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hsq : Scr s₁ (off B oq) (slot wq 8) := hs₁.sub (by omega) (by omega)
  have hqw : ∀ i < 32, word s₁.mem (off B oq) (8 * i) = word s.mem (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hq₁ _ (by omega) (by omega)
  refine ⟨hdi₁, WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = off B oq ∧ t.mem = s₁.mem)
    (by xrun [mqBlk1, State.ea, hdr, hdi₁, hdrOff, hs₁.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega),
      hb₁ sWsQ (by decide), hq]) rfl) fun s₁' ⟨⟨hax, hm₁'⟩, k₁'⟩ =>
    ⟨hax, (k₁'.gpr (by decide)).trans hdi₁, ?_⟩⟩
  have hs₁' := hs₁.congr k₁'.2.2
  have hsq' : Scr s₁' (off B oq) (slot wq 8) := hsq.congr k₁'.2.2
  have hdi₁' : s₁'.gpr .rdi = B := (k₁'.gpr (by decide)).trans hdi₁
  have hb₁' : ∀ i < 32, word s₁'.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by rw [hm₁']; exact hb₁ i hi
  have hqw' : ∀ i < 32, word s₁'.mem (off B oq) (8 * i) = word s.mem (off B oq) (8 * i) := fun i hi => by
    rw [hm₁']; exact hqw i hi
  refine WP.mono (WP.keep [.rsi, .r12, .rbx] (Q := fun t =>
      t.gpr .rsi = off (off B oq) (slot wq Public.aY) ∧ t.gpr .r12 = BitVec.ofNat 64 wq ∧
      t.gpr .rbx = off B (slot w Public.aX) ∧ t.mem = s₁.mem)
    (by xrun [mqBlk2, State.ea, hdr, ws, hdi₁', hax, hdrOff, hm₁', hsq'.ld (d := 8 * sArr Public.aY) (by unfold sArr Public.aY; omega),
      hqw (sArr Public.aY) (by decide), hws.hdr.harr Public.aY (by decide),
      hsq'.ld (d := 8 * sW) (by unfold sW; omega), hqw sW (by decide), hws.hdr.hw,
      hs₁'.ld (d := 8 * sArr Public.aX) (by unfold sArr Public.aX; omega), hb₁ (sArr Public.aX) (by decide),
      hg.hdr.harr Public.aX (by decide)]) rfl) fun s₂ ⟨⟨hsi₂, h12₂, hbx₂, hm₂⟩, k₂⟩ =>
    ⟨hsi₂, h12₂, hbx₂, ?_⟩
  have k₂ := k₁'.trans k₂
  have hs₂ := hs₁.congr k₂.2.2
  have hsq₂ := hsq.congr k₂.2.2
  -- `X := m_q`.
  refine WP.mono (copyWords_ok (S := off B oq) (eS := slot wq Public.aY) (D := B) (eD := slot w Public.aX)
    (w := wq) hsi₂ hbx₂ h12₂ hwq (by omega) (by omega) (fun j hj => hsq₂.ld (by omega))
    (fun j hj => hs₂.st (by omega)) (fun j hj b hb => Or.inr (by
      rw [off_off, ofs_off B (by omega)]; omega))) fun s₃ ⟨_, _, ho₃, k₃⟩ => ?_
  have hn₃ : ∀ j < 8, j ≠ Public.aX → wv s₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj hjx => by
    have := slot_sep (w := w) hjx
    have := slot_le (w := w) hj
    rw [ho₃.wv (by omega) (by omega), hm₂, ho₁.wv (by omega) (by omega)]
  have hg₃ : Good s₃ B Z w minv := ⟨hs.congr ((k₁.trans k₂).trans k₃).2.2,
    ((k₂.trans k₃).gpr (by decide)).trans hdi₁, by
      have : ∀ i < 32, word s₃.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
        rw [ho₃.word (Or.inl (by have := hdr_lt_slot w Public.aX hi; omega)) (by omega), hm₂, hb₁ i hi]
      exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
        fun j hj => (this _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩
  have hw0 : word s₃.mem B (slot w Public.aN) = word s.mem B (slot w Public.aN) := by
    have := slot_sep (w := w) (show Public.aN ≠ Public.aX by decide)
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    rw [ho₃.word (by omega) (by omega), hm₂, ho₁.word (by omega) (by omega)]
  -- `X := m_q R`.
  refine ⟨⟨minv, hg₃, show slot w 8 ≤ Z by omega⟩, WP.mono (mmN_ok M hg₃ (by omega) (by omega) (by omega) (o := Public.aX)
    (a := Public.aX) (b := Public.aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ((hn₃ _ (by decide) (by decide)).trans hN.n) (by rw [hw0]; exact hN.inv)
    (by rw [hn₃ _ (by decide) (by decide)]; exact hN.r2lt)) fun s₄ h₄ => ⟨minv, h₄.1, show slot w 8 ≤ Z by omega⟩⟩

end VG.Proof.Bignum.X86_64
