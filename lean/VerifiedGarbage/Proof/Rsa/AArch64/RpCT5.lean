module
public import VerifiedGarbage.Proof.Rsa.AArch64.RpCT1
public import VerifiedGarbage.Proof.Rsa.AArch64.RpExp

import VerifiedGarbage.Proof.Rsa.AArch64.RpCT4
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Rsa.AArch64.RpSkip
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCT1
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpExp
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpCT4
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Rsa.AArch64.RpSkip
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes` on AArch64: constant time, the exponentiation

`Bw` words of 64 bits each, public counts (`expLoop_ct`): the counters in
`sC1` and `sC3` are pinned by correctness, and so is the address of the
word `wordHead` loads.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.Recover
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt sMask)

/-- `wordHead` up to the address of the word: `x16` at word `i` of `M`, for
`sC1 = i + 1`. -/
theorem wordHeadA_ok {u : State} {B : Addr} {Z w : Nat} (h : Ws u B Z w) {i : Nat}
    (hc1 : word u.mem B (8 * sC1) = BitVec.ofNat 64 (i + 1)) (hi' : i + 1 < 2 ^ 60) :
    WP isa (.block (ws ++ (base aM .x16 ++ [ldh .x3 sC1, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3,
      .add .x .x16 .x16 .x3]))) u fun u' => ∀ r ∈ [Reg.x0, .x16], u'.gpr r =
        (fun | .x0 => B | .x16 => off B (slot w aM + 8 * i) | _ => 0 : Reg → BitVec 64) r := by
  have h256 := h.h256
  have hn := h.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun u₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun u₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.wr
  have h0₂ : u₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have ea : off B (slot w aM) + BitVec.ofNat 64 (i * 2 ^ 3) = off B (slot w aM + 8 * i) := by
    rw [off_add, show slot w aM + i * 2 ^ 3 = slot w aM + 8 * i by omega_using []]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun u' => u'.gpr .x16 = off B (slot w aM + 8 * i)) (by
    brun [h0₂, h16, hdr_enc (show sC1 < 32 by decide), hs₂.ld (d := 8 * sC1) (by simp only [sC1, sFn]; omega_using [h256]),
      m₂, m₁, hc1, ofNat_sub_one' (show 1 ≤ i + 1 by omega_using []) (by omega_using [hi']), Nat.add_sub_cancel,
      shl_ofNat (show i * 2 ^ 3 < 2 ^ 64 by omega_using [hi']), ea])
    (by decide) (by decide) (by decide +kernel)) fun u' ⟨h16', k₃⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (k₃.gpr .x0 (by decide)).trans h0₂
  · exact h16'

namespace Rp

/-- The words of `r`. -/
abbrev bW (p : RpP) : Nat := wk p.k + (p.el + 7) / 8

/-! ## A bit -/

/-- In a bit: the constants, `Y < n`, `G < n`, and `Xm < n` if `hx`. -/
def BT (hx : Bool) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) < N ∧ wv s.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    (hx = true → wv s.mem p.B (slot (wk p.k) aXm) (wk p.k) < N)

theorem BT.ws {hx : Bool} {p : RpP} {s : State} (h : BT hx p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨_, _, _, _, hc, -⟩ := h
  exact hc.ws

/-- `bitSel`'s and the selection's registers. -/
def selVal (p : RpP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wk p.k) aG)
  | .x17 => off p.B (slot (wk p.k) aXm)
  | .x14 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The bit, and the multiplicand `G` or `R mod n`. -/
theorem bitSel_ct : RelCT isa (Two (BT true)) (.seq (.block bitSel) VG.Impl.Rsa.AArch64.Crt.selLoop)
    (Two (BT true)) := by
  refine pin_ct [.x0] [.x0, .x16, .x17, .x14] selVal (pins_ws RpP.B RpP.Z (fun p => wk p.k) fun _ _ h => h.ws)
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have hw := h.ws
    refine WP.mono (bitSel_ok hw (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨⟨_, h16, h17, h14, _⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans hw.x0
    · exact h16
    · exact h17
    · exact h14
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    refine WP.seq (WP.mono (bitSel_ok hc.ws (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun u₂ ⟨⟨h15, h16, h17, h14, m₂⟩, k₂⟩ => ?_)
    have hf₂ : Frm p.B (rg (wk p.k) [] [sC2]) s.mem u₂.mem := by
      rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega_using [])) _ _
        (List.mem_singleton_self _)
    have hc₂ := hc.congr hf₂ (by decide) (by decide) k₂ (by decide)
    have sXm := hc₂.ws.sl (j := aXm) (by decide)
    have sG := hc₂.ws.sl (j := aG) (by decide)
    refine WP.mono (selLoop_ok hc₂.ws.scr h16 h17 h14 h15 (by omega_using [hw1]) (by omega_using [hw2]) (by omega_using [sG]) (by omega_using [sXm])
      (by have := slot_sep (w := wk p.k) (show aXm ≠ aG by decide); omega_using [this])) fun u₃ ⟨hx₃, o₃, k₃⟩ => ?_
    have hf₃ : Frm p.B (rg (wk p.k) [aXm] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega_using []) _ _ (by decide)
    have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
    have e₂ : ∀ j, j < 16 → j ≠ aXm →
        wv u₃.mem p.B (slot (wk p.k) j) (wk p.k) = wv s.mem p.B (slot (wk p.k) j) (wk p.k) := fun j hj hne => by
      rw [hf₃.rg_wv hZ16 (by simp) hj (by simpa using hne) (by omega_using []),
        hf₂.rg_wv hZ16 (by decide) hj (by simp) (by omega_using [])]
    refine ⟨minv, N, r, t, hc₃, by rw [e₂ _ (by decide) (by decide)]; exact hY,
      by rw [e₂ _ (by decide) (by decide)]; exact hG, fun _ => ?_⟩
    rw [hx₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega_using []),
      hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega_using [])]
    split
    · exact hG
    · exact hX rfl

/-- A bit leaks the same in runs that agree on the public data. -/
theorem bitBody_ct (M : Mont) : RelCT isa (Two (BT false)) (bitBody M.mm) fun _ _ => True := by
  have hB : ∀ (hx : Bool) p s, BT hx p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  simp only [bitBody, seqs]
  refine RelCT.seq (R := Two (BT true)) (copyA_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) (by taint_decide)
    fun p s h => ?_) ?_
  · obtain ⟨minv, N, r, t, hc, hY, hG, -⟩ := h
    have hZ16 := hc.hZ16
    have hN : 0 < N := by have := hc.n1; omega_using [this]
    refine WP.mono (copyA_ok hc.ws (o := aXm) (a := aO) (by decide) (by decide) (by decide))
      fun u ⟨hx, o, _, _, k⟩ => ?_
    have hf : Frm p.B (rg (wk p.k) [aXm] []) s.mem u.mem := Frm.rg_of_out o (by omega_using []) _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), ?_, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hY
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hG
    · rw [hx, hc.ho]; exact Nat.mod_lt _ hN
  refine RelCT.assoc (RelCT.seq bitSel_ct (RelCT.seq (R := Two (BT true)) (mm_gct RpP.B RpP.Z (fun p => wk p.k)
    (hB true) M (o := aY) (a := aY) (b := aY) (by unfold MmUse; decide) fun p s h => ?_)
    (RelCT.seq (R := Two (BT false)) (mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB true) M (o := aY) (a := aY)
      (b := aXm) (by unfold MmUse; decide) fun p s h => ?_)
    (two_taint [.x0] (pins_ws RpP.B RpP.Z (fun p => wk p.k) (hB false)) (by taint_decide)))))
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega_using [hw2]) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hY)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun _ => ?_⟩
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hG
    · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hX rfl
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega_using [hw2]) (o := aY) (a := aY) (b := aXm) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hX rfl)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun e => by cases e⟩
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hG

/-- The bits' invariant: `j` bits of the word `V` from `t₀`, for a candidate
`g` that `G` allows. -/
def BI (G : Nat → Prop) (p : RpP) (j : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g e V : Nat), Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧ V = e % 2 ^ 64 ∧
    BitInv t₀ p.B (wk p.k) N g e V j u ∧ G g

/-- What the exponentiation needs of a bit's code `body` for the candidates
`G` allows. -/
structure BitCode (G : Nat → Prop) (body : Prog isa) : Prop where
  ok : ∀ {B : Addr} {Z w : Nat} {minv : BitVec 64} {N el r t g : Nat}, G g → BitOk body B Z w minv N el r t g
  ct : RelCT isa (Two (BT false)) body fun _ _ => True

theorem bitBody_code (M : Mont) : BitCode (fun _ => True) (bitBody M.mm) :=
  ⟨fun _ => bitBody_bitOk M, bitBody_ct M⟩

/-! ## A bit for the candidates 2 and 3 -/

theorem addMod_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x9 (sArr a), ldh .x17 (sArr b), ldh .x10 (sArr Public.aN),
      ldh .x8 (sArr Public.aAcc), ldh .x6 (sArr Public.aTmp), ldh .x5 (sArr o), ldh .x12 sW, movi .x7 0,
      mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7]) hc).isSome = true)
    (hw : ∀ x s, Φ x s → WP isa (VG.Impl.Rsa.AArch64.Crt.addMod o a b) s (Ψ x)) :
    RelCT isa (Two Φ) (VG.Impl.Rsa.AArch64.Crt.addMod o a b) (Two Ψ) :=
  two_post (two_map (fun x => (⟨B x, Z x, w x⟩ : VG.Proof.Bignum.AArch64.Ws)) (fun x s h => ⟨_, (hws x s h).good⟩)
    (addMod_ct ho ha hb hT)) hw

/-- `[aXm] := [a] + Y mod n` keeps `BT`, with `Xm < n`. -/
theorem addY_bt {p : RpP} {s : State} {a : Nat} (ha : a = aY ∨ a = aXm) {hx : Bool}
    (hA : hx = true ∨ a = aY) (h : BT hx p s) :
    WP isa (VG.Impl.Rsa.AArch64.Crt.addMod aXm a aY) s (BT true p) := by
  obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
  have hZ16 := hc.hZ16
  have hN : 0 < N := by have := hc.n1; omega_using [this]
  have hAlt : wv s.mem p.B (slot (wk p.k) a) (wk p.k) < N := by
    rcases ha with rfl | rfl
    · exact hY
    · rcases hA with h | h
      · exact hX h
      · cases h
  refine WP.mono (addY_ok hc ha hAlt hY) fun u ⟨hf, k, hv⟩ => ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k
    (by decide), ?_, ?_, fun _ => ?_⟩
  · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hY
  · rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hG
  · rw [hv]; exact Nat.mod_lt _ hN

theorem twice_ct : RelCT isa (Two (BT false)) (seqs twice) (Two (BT true)) := by
  simp only [twice, seqs]
  exact addMod_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by decide) (by decide) (by decide)
    (by taint_decide) fun _ _ h => addY_bt (Or.inl rfl) (Or.inr rfl) h

theorem three_ct : RelCT isa (Two (BT false)) (seqs three) (Two (BT true)) := by
  simp only [three, seqs]
  exact RelCT.seq (addMod_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by decide) (by decide) (by decide)
    (by taint_decide) fun _ _ h => addY_bt (Or.inl rfl) (Or.inr rfl) h)
    (addMod_gct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by decide) (by decide) (by decide)
      (by taint_decide) fun _ _ h => addY_bt (Or.inr rfl) (Or.inl rfl) h)

/-- `bitSelS`'s and the selection's registers. -/
def selValS (p : RpP) : Reg → BitVec 64
  | .x0 => p.B
  | .x16 => off p.B (slot (wk p.k) aXm)
  | .x17 => off p.B (slot (wk p.k) aY)
  | .x14 => BitVec.ofNat 64 (wk p.k)
  | _ => 0

/-- The bit, and `Y := Y g` if it is set. -/
theorem bitSelS_ct : RelCT isa (Two (BT true)) (.seq (.block bitSelS) VG.Impl.Rsa.AArch64.Crt.selLoop)
    (Two (BT false)) := by
  refine pin_ct [.x0] [.x0, .x16, .x17, .x14] selValS (pins_ws RpP.B RpP.Z (fun p => wk p.k) fun _ _ h => h.ws)
    (by taint_decide) (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have hw := h.ws
    refine WP.mono (bitSelS_ok hw (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨⟨_, h16, h17, h14, _⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans hw.x0
    · exact h16
    · exact h17
    · exact h14
  · obtain ⟨minv, N, r, t, hc, hY, hG, hX⟩ := h
    have hZ16 := hc.hZ16
    have hw1 := hc.ws.w1
    have hw2 := hc.ws.w2
    have h256 := hc.ws.h256
    refine WP.seq (WP.mono (bitSelS_ok hc.ws (V := (word s.mem p.B (8 * sC2)).toNat) (by rw [BitVec.ofNat_toNat,
      BitVec.setWidth_eq]) (BitVec.isLt _)) fun u₂ ⟨⟨h15, h16, h17, h14, m₂⟩, k₂⟩ => ?_)
    have hf₂ : Frm p.B (rg (wk p.k) [] [sC2]) s.mem u₂.mem := by
      rw [m₂]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega_using [])) _ _
        (List.mem_singleton_self _)
    have hc₂ := hc.congr hf₂ (by decide) (by decide) k₂ (by decide)
    have sXm := hc₂.ws.sl (j := aXm) (by decide)
    have sY := hc₂.ws.sl (j := aY) (by decide)
    refine WP.mono (selLoop_ok hc₂.ws.scr h16 h17 h14 h15 (by omega_using [hw1]) (by omega_using [hw2])
      (by omega_using [sXm]) (by omega_using [sY])
      (by have := slot_sep (w := wk p.k) (show aY ≠ aXm by decide); omega_using [this])) fun u₃ ⟨hy₃, o₃, k₃⟩ => ?_
    have hf₃ : Frm p.B (rg (wk p.k) [aY] []) u₂.mem u₃.mem := Frm.rg_of_out o₃ (by omega_using []) _ _ (by decide)
    have hc₃ := hc₂.congr hf₃ (by decide) (by simp) k₃ (by decide)
    refine ⟨minv, N, r, t, hc₃, ?_, ?_, fun e => by cases e⟩
    · rw [hy₃, hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega_using []),
        hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega_using [])]
      split
      · exact hX rfl
      · exact hY
    · rw [hf₃.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using []),
        hf₂.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega_using [])]; exact hG

/-- A bit for a small candidate leaks the same in runs that agree on the public data. -/
theorem bitSmall_ct (M : Mont) {times : List (Prog isa)} (hnil : times ≠ [])
    (ht : RelCT isa (Two (BT false)) (seqs times) (Two (BT true))) :
    RelCT isa (Two (BT false)) (bitSmall M.mm times) fun _ _ => True := by
  have hB : ∀ (hx : Bool) p s, BT hx p s → Ws s p.B p.Z (wk p.k) := fun _ _ _ h => h.ws
  unfold bitSmall
  rw [show [M.mm aY aY aY] ++ times ++ [.block bitSelS, VG.Impl.Rsa.AArch64.Crt.selLoop, .block bitNext] =
    [M.mm aY aY aY] ++ (times ++ [.block bitSelS, VG.Impl.Rsa.AArch64.Crt.selLoop, .block bitNext]) by
      simp only [List.append_assoc]]
  refine RelCT.seqs_append (by simp) (by simp [hnil]) (RelCT.seq (R := Two (BT false)) ?_
    (RelCT.seqs_append hnil (by simp) (RelCT.seq ht ?_)))
  · simp only [seqs]
    refine mm_gct RpP.B RpP.Z (fun p => wk p.k) (hB false) M (o := aY) (a := aY) (b := aY)
      (by unfold MmUse; decide) fun p s h => ?_
    obtain ⟨minv, N, r, t, hc, hY, hG, -⟩ := h
    have hZ16 := hc.hZ16
    have hg := hc.good
    have hw2 := hc.ws.w2
    refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 (by omega_using [hw2]) (o := aY) (a := aY) (b := aY) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.hinv
      (by rw [hc.hn]; exact hY)) fun u ⟨_, hlt, _, ha, k⟩ => ?_
    rw [hc.hn] at hlt
    have hf : Frm p.B (rg (wk p.k) [aAcc, aTmp, aY] []) s.mem u.mem := Frm.rg_of_arrays ha _ _ (by decide)
    refine ⟨minv, N, r, t, hc.congr hf (by decide) (by simp) k (by decide), hlt, ?_, fun e => by cases e⟩
    rw [hf.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega_using [])]; exact hG
  · simp only [seqs]
    exact RelCT.assoc (RelCT.seq bitSelS_ct
      (two_taint [.x0] (pins_ws RpP.B RpP.Z (fun p => wk p.k) (hB false)) (by taint_decide)))

theorem bitSmall_two_code (M : Mont) : BitCode (· = 2) (bitSmall M.mm twice) :=
  ⟨fun h => by subst h; exact bitSmall_two M, bitSmall_ct M (by simp [twice]) twice_ct⟩

theorem bitSmall_three_code (M : Mont) : BitCode (· = 3) (bitSmall M.mm three) :=
  ⟨fun h => by subst h; exact bitSmall_three M, bitSmall_ct M (by simp [three]) three_ct⟩

theorem bitLoop_ct {G : Nat → Prop} {body : Prog isa} (hb : BitCode G body) :
    RelCT isa (Two fun (p : RpP) s => 0 < 64 ∧ BI G p 0 s)
    (.loop body (.nonzero .x .x3)) (Two fun p s => BI G p 64 s) :=
  two_loop (fun _ => 64) (two_map (fun q => q.1) (fun q s hq => by
      obtain ⟨-, t₀, minv, N, r, t, g, e, V, hc, hGlt, -, -, hI, -⟩ := hq
      have hZ16 := hc.hZ16
      have hcu := hc.congr hI.frm (by decide) bit_hs hI.keep (by decide)
      refine ⟨minv, N, r, t, hcu, hI.ylt, ?_, fun e => by cases e⟩
      rw [hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]; exact hGlt) hb.ct)
    fun p j s hj ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI, hGg⟩ =>
      WP.mono (hb.ok hGg hc hGlt hG hV hj hI) fun s' ⟨hI', hz⟩ =>
        ⟨by rw [eval_nonzero, ne_zero_iff]; exact congrArg some (decide_eq_decide.mpr (by rw [hz]; omega_using [hj])),
          fun _ => ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI', hGg⟩,
          fun h => h ▸ ⟨t₀, minv, N, r, t, g, e, V, hc, hGlt, hG, hV, hI', hGg⟩⟩

/-! ## A word -/

/-- The words' invariant: `k` words of `r` from `t₀`. -/
def WI (G : Nat → Prop) (p : RpP) (k : Nat) (u : State) : Prop :=
  ∃ (t₀ : State) (minv : BitVec 64) (N r t g : Nat), Cst t₀ p.B p.Z (wk p.k) minv N p.el r t ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv t₀.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    WordInv t₀ p.B (wk p.k) N g r (bW p) k u ∧ G g

theorem wordHead_eq : wordHead = (ws ++ (base aM .x16 ++ [ldh .x3 sC1, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3,
    .add .x .x16 .x16 .x3])) ++ [ld .x3 .x16, sth .x3 sC2, movi .x3 64, sth .x3 sC3] := by
  simp only [wordHead, List.append_assoc, List.cons_append, List.nil_append]

/-- `wordHead`'s registers before its load of the word. -/
def headVal (q : RpP × Nat) : Reg → BitVec 64
  | .x0 => q.1.B
  | .x16 => off q.1.B (slot (wk q.1.k) aM + 8 * (bW q.1 - q.2 - 1))
  | _ => 0

theorem wordHead_ct (G : Nat → Prop) : RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI G q.1 q.2 s)
    (.block wordHead) (Two fun (q : RpP × Nat) s => 0 < 64 ∧ BI G q.1 0 s) := by
  rw [wordHead_eq]
  refine RelCT.block_append (ws_pin_ct (fun q : RpP × Nat => q.1.B) (fun q => q.1.Z) (fun q => wk q.1.k)
    (fun (q : RpP × Nat) s ⟨_, t₀, minv, N, r, t, g, hc, _, _, hI, _⟩ => (hc.congr hI.frm (by decide) word_hs hI.keep
      (by decide)).ws) (by taint_decide) [.x0, .x16] headVal (fun q s h => ?_) (by taint_decide)
    fun q s h => ?_)
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, _, _, hI, _⟩ := h
    have hcu := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    obtain ⟨i, hi₀⟩ : ∃ i, wk q.1.k + (q.1.el + 7) / 8 - q.2 = i + 1 := ⟨wk q.1.k + (q.1.el + 7) / 8 - q.2 - 1, by omega_using [hk']⟩
    have hc1 : word s.mem q.1.B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by rw [← hi₀]; exact hI.c1
    refine WP.mono (wordHeadA_ok hcu.ws hc1 (by omega_using [he2, hw2, hi₀])) fun u hu r hr => ?_
    rw [hu r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rfl
    · show off q.1.B (slot (wk q.1.k) aM + 8 * i) = off q.1.B (slot (wk q.1.k) aM + 8 * (bW q.1 - q.2 - 1))
      rw [show bW q.1 - q.2 - 1 = i by simp only [bW]; omega_using [hi₀]]
  · obtain ⟨hk, t₀, minv, N, r, t, g, hc, hGlt, hG, hI, hGg⟩ := h
    have hZ16 := hc.hZ16
    have he2 := hc.e2
    have hw2 := hc.ws.w2
    have hm := hc.hm
    have hk' : q.2 < wk q.1.k + (q.1.el + 7) / 8 := hk
    have hBw2 : wk q.1.k + (q.1.el + 7) / 8 ≤ 2 * (wk q.1.k + 2) := by unfold wk at *; omega_using [he2]
    have hcu := hc.congr hI.frm (by decide) word_hs hI.keep (by decide)
    obtain ⟨i, hi₀⟩ : ∃ i, wk q.1.k + (q.1.el + 7) / 8 - q.2 = i + 1 := ⟨wk q.1.k + (q.1.el + 7) / 8 - q.2 - 1, by omega_using [hk']⟩
    have hi : bW q.1 - q.2 = i + 1 := hi₀
    have hc1 : word s.mem q.1.B (8 * sC1) = BitVec.ofNat 64 (i + 1) := by rw [← hi]; exact hI.c1
    have sM := slot_lt (w := wk q.1.k) (show aM + 1 < 16 by decide)
    have eM1 := slot_aM1 (wk q.1.k)
    have hZ := hcu.ws.hZ
    rw [WP.seq_iff, ← WP.block_append_iff, ← wordHead_eq]
    refine WP.mono (wordHead_ok hcu.ws hc1 (by omega_using [hBw2, hi₀, sM, eM1, hZ]) (by omega_using [hw2, hBw2, hi₀])) fun u₁ ⟨m₁, k₁⟩ => ⟨by decide, ?_⟩
    have hW : (word s.mem q.1.B (slot (wk q.1.k) aM + 8 * i)).toNat = r / 2 ^ (64 * i) % 2 ^ 64 := by
      have := word_of_wv s.mem q.1.B (slot (wk q.1.k) aM) (bW q.1) (q := i) (by omega_using [hi])
      rw [hcu.hm] at this
      exact this
    have hf₁ : Frm q.1.B (rg (wk q.1.k) [] [sC2, sC3]) s.mem u₁.mem := by
      rw [m₁]
      exact (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC2, sFn]; omega_using [])) [] [sC2, sC3]
        (by decide)).trans (Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC3, sFn]; omega_using [])) [] [sC2, sC3]
          (by decide))
    have hc₁ := hcu.congr hf₁ (by decide) (by decide) k₁ (by decide)
    have hGu : wv u₁.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) = wv t₀.mem q.1.B (slot (wk q.1.k) aG) (wk q.1.k) := by
      rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []),
        hI.frm.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]
    have hpow : r / 2 ^ (64 * i) / 2 ^ (64 - 0) = r / 2 ^ (64 * (bW q.1 - q.2)) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hi, Nat.sub_zero, Nat.mul_succ]
    have hW' : word s.mem q.1.B (slot (wk q.1.k) aM + 8 * i) =
        BitVec.ofNat 64 (r / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ 0 % 2 ^ 64) := by
      rw [← hW, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    refine ⟨u₁, minv, N, r, t, g, r / 2 ^ (64 * i), r / 2 ^ (64 * i) % 2 ^ 64, hc₁, by rw [hGu]; exact hGlt,
      by rw [hGu]; exact hG, rfl, ⟨Frm.refl _ _ _, Keep.refl _ _, ?_, ?_, ?_, ?_⟩, hGg⟩
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using [])]; exact hI.ylt
    · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hpow]; exact hI.y
    · rw [m₁, (writeW_outside _ q.1.B _ (d := 8 * sC3) (by simp only [sC3, sFn]; omega_using [])).word
        (Or.inl (by simp only [sC2, sC3, sFn]; omega_using [])) (by simp only [sC2, sFn]; omega_using []), word_writeW_self, hW']
    · rw [m₁, word_writeW_self]

theorem pins_BI (G : Nat → Prop) : Pins (fun (p : RpP) s => BI G p 64 s) [.x0] := fun _ _ _ h₁ h₂ r hr => by
  obtain ⟨_, _, _, _, _, _, _, _, hc₁, _, _, _, hI₁, _⟩ := h₁
  obtain ⟨_, _, _, _, _, _, _, _, hc₂, _, _, _, hI₂, _⟩ := h₂
  simp only [List.mem_singleton] at hr; subst hr
  rw [(hc₁.congr hI₁.frm (by decide) bit_hs hI₁.keep (by decide)).ws.x0,
    (hc₂.congr hI₂.frm (by decide) bit_hs hI₂.keep (by decide)).ws.x0]

/-- A word leaks the same in runs that agree on the public data. -/
theorem wordBody_ct {G : Nat → Prop} {body : Prog isa} (hb : BitCode G body) :
    RelCT isa (Two fun (q : RpP × Nat) s => q.2 < bW q.1 ∧ WI G q.1 q.2 s)
    (.seq (.block wordHead) (.seq (.loop body (.nonzero .x .x3)) (.block wordNext))) fun _ _ => True :=
  RelCT.seq (wordHead_ct G) (RelCT.seq (two_map (fun q => q.1) (fun _ _ h => h) (bitLoop_ct hb))
    (two_taint [.x0] (pins_BI G) (by taint_decide)))

theorem wordLoop_ct {G : Nat → Prop} {body : Prog isa} (hb : BitCode G body) :
    RelCT isa (Two fun p s => 0 < bW p ∧ WI G p 0 s)
    (.loop (.seq (.block wordHead) (.seq (.loop body (.nonzero .x .x3)) (.block wordNext)))
      (.nonzero .x .x3))
    (Two fun p s => WI G p (bW p) s) :=
  two_loop bW (wordBody_ct hb) fun _ _ _ hk ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI, hGg⟩ =>
    WP.mono (wordStep_ok (hb.ok hGg) hc hGlt hG hk hI) fun _ ⟨hI', hz⟩ =>
      ⟨by
        rw [eval_nonzero, ne_zero_iff]
        have := hk
        simp only [bW] at this ⊢
        exact congrArg some (decide_eq_decide.mpr (by rw [hz]; omega_using [this])),
        fun _ => ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI', hGg⟩,
        fun h => h ▸ ⟨t₀, minv, N, r, t, g, hc, hGlt, hG, hI', hGg⟩⟩

/-- `expLoop`'s hypotheses, for a candidate `g` that `G` allows. -/
def EX (G : Nat → Prop) (p : RpP) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (N r t g : Nat), Cst s p.B p.Z (wk p.k) minv N p.el r t ∧
    wv s.mem p.B (slot (wk p.k) aG) (wk p.k) < N ∧
    wv s.mem p.B (slot (wk p.k) aG) (wk p.k) % N = g * 2 ^ (64 * wk p.k) % N ∧
    wv s.mem p.B (slot (wk p.k) aY) (wk p.k) = 2 ^ (64 * wk p.k) % N ∧ G g

/-- The exponentiation leaks the same in runs that agree on the public data. -/
theorem expLoopWith_ct {G : Nat → Prop} {body : Prog isa} (hb : BitCode G body) :
    RelCT isa (Two (EX G)) (expLoopWith body) (Two fun p s => WI G p (bW p) s) := by
  unfold expLoopWith
  refine RelCT.seq (blk_gct RpP.B RpP.Z (fun p => wk p.k) (fun p s ⟨_, _, _, _, _, hc, _⟩ => hc.ws)
    (by taint_decide) fun p s h => ?_) (wordLoop_ct hb)
  obtain ⟨minv, N, r, t, g, hc, hGlt, hG, hY, hGg⟩ := h
  have hZ16 := hc.hZ16
  have he2 := hc.e2
  have hw1 := hc.ws.w1
  have hw2 := hc.ws.w2
  have h256 := hc.ws.h256
  have hn := hc.ws.scr.nowrap
  have hN : 0 < N := by have := hc.n1; omega_using [this]
  unfold expInit
  refine WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono hc.ws.ws_ok
    fun s₀ ⟨⟨h12, _, m₀, _⟩, k₀⟩ => ?_))
  have h0₀ : s₀.gpr .x0 = p.B := (k₀.gpr .x0 (by decide)).trans hc.ws.x0
  refine WP.mono (bw_ok (el := p.el) (hc.ws.scr.congr k₀.wr) h0₀ h256 (by rw [m₀]; exact hc.hel) (by omega_using [he2, hw2]) h12)
    fun s₁' ⟨⟨h14, m₁', _⟩, k₁'⟩ => ?_
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off p.B (8 * sC1))
      (BitVec.ofNat 64 (bW p))) (by
    brun [(k₁'.gpr .x0 (by decide)).trans h0₀, h14, hdr_enc (show sC1 < 32 by decide),
      (hc.ws.scr.congr (k₀.trans k₁').wr).st (d := 8 * sC1) (by simp only [sC1, sFn]; omega_using [h256]), m₁', m₀])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨mu, k₂⟩ =>
      ⟨by simp only [bW]; unfold wk at *; omega_using [hw1], s, minv, N, r, t, g, hc, hGlt, hG, ?_⟩
  have k₁ : Keep mmRegs s u := ((k₀.trans k₁').trans k₂).mono (by decide)
  have hf₁ : Frm p.B (rg (wk p.k) [] [sC1]) s.mem u.mem := by
    rw [mu]; exact Frm.rg_of_hdr (writeW_outside _ _ _ (by simp only [sC1, sFn]; omega_using [])) _ _
      (List.mem_singleton_self _)
  have hr : r < 2 ^ (64 * bW p) := hc.hm ▸ wv_lt _ _ _ _
  refine ⟨⟨hf₁.rg_mono (by decide) (by decide), k₁, ?_, ?_, ?_⟩, hGg⟩
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hY]; exact Nat.mod_lt _ hN
  · rw [hf₁.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_using []), hY, Nat.sub_zero,
      Nat.div_eq_of_lt hr, Nat.pow_zero, Nat.one_mul, Nat.mod_mod]
  · rw [mu, word_writeW_self, Nat.sub_zero]

theorem expLoop_ct (M : Mont) : RelCT isa (Two (EX fun _ => True)) (expLoop M.mm)
    (Two fun p s => WI (fun _ => True) p (bW p) s) :=
  expLoopWith_ct (bitBody_code M)

end Rp

end VG.Proof.Rsa.AArch64
