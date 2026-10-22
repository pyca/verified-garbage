module

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Parity
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

/-! # Check the recovered root's square and parity -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86_64 (QY QYM R2P W1 W2 W3)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

def checkN : List FOp := [.mul QYM QY R2P, .mul W1 QYM QYM, .sub W3 W1 W2]
abbrev checkSlots : List Nat := [QY, R2P, W2, QYM, W1, W3]

theorem checkOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.checkRootOps c =
    checkN.map (FOp.rename c.sl) := rfl

theorem checkN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps checkN e W3 = (e QY * e R2P) * (e QY * e R2P) - e W2 := by
  simp only [checkN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [QYM, QY, R2P, W1, W2, X, RR, DM, TT, SM, Nat.reduceEqDiff, ↓reduceIte]

theorem checkN_reads : readsOk checkN [QY, R2P, W2] = true := by decide
theorem checkN_slots : ∀ op ∈ checkN, ∀ x ∈ op.out :: op.ins, x ∈ checkSlots := by decide
theorem checkN_out : ∀ op ∈ checkN, op.out ∈ [QYM, W1, W3, TMP] := by decide

theorem raw_r2_mul {c : Cfg} (hc : BaseCfgOk c) (a : Nat) :
    toM c.C.p (2 ^ (64 * c.n)) a *
      toM c.C.p (2 ^ (64 * c.n)) (c.R * c.R % c.C.p) = Fin.ofNat c.C.p a := by
  change toM c.C.p (2 ^ (64 * c.n)) a * toM c.C.p (2 ^ (64 * c.n)) (c.mont c.R) = _
  rw [toM_cmont hc]
  unfold toM
  have hu := mul_rinv (unitMod_pow_two hc.p_odd (64 * c.n))
  change Fin.ofNat c.C.p c.R * rinv c.C.p (2 ^ (64 * c.n)) = 1 at hu
  grind

structure CheckPolyPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W3) =
    Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)

theorem checkPoly_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (Impl.Weierstrass.X86_64.fprogB c.MP'
      (Impl.EcKey.Compressed.X86_64.checkRootOps c)).inline s (CheckPolyPost c base s) := by
  have h7 := hc.n10
  have hL : Lay c.MP' size (· ∈ checkSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have I : Inv c.MP' base size c.C.p (· ∈ checkSlots.map c.sl) ([QY, R2P, W2].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, ?_, ?_, fun _ _ => rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QY, R2P, W2], i ∈ checkSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy
      · show sv c base s R2P < _
        rw [hr2]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega)
      · exact hr
  rw [checkOps_eq]
  refine WP.mono (fprogB_ok hL (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_) (readsOk_rename c.sl checkN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (checkN_slots _ h₀ _ hi)
  have hw : c.sl W3 ∈ validAfter (checkN.map (FOp.rename c.sl)) ([QY, R2P, W2].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [checkN, FOp.rename, FOp.out]))
  have vt := IT.val _ hw
  rw [congrFun (runOps_rename c.sl checkN _ fun _ _ y h => sl_inj c hc.n0 h) W3, checkN_run] at vt
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, IT.lt _ hw, ?_⟩
  · apply PK.unch.mono
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_map.mpr ⟨op₀.out, checkN_out _ h₀, by rw [FOp.out_rename]; rfl⟩
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_map_of_mem (by decide)
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base t W3) =
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QY) *
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s R2P)) -
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) at vt
    simpa only [hr2, raw_r2_mul hc] using vt

structure CheckRootPost (c : Cfg) (base : Addr) (P : Prop) [Decidable P] (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (clob c.n) s s'
  unch : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s'.mem
  flag : word s'.mem base (c.sl FLAG) = mask
    ((P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) ∧
      sv c base s QY % 2 = (word s.mem base (c.sl D)).toNat % 2)

theorem checkRoot_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hy : sv c base s QY < c.C.p) (hr : sv c base s W2 < c.C.p)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (Impl.EcKey.Compressed.X86_64.checkRoot c).inline s (CheckRootPost c base P s) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have hW := sl_le c h7 (i := W3) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  change WP isa (.seq
    (Impl.Weierstrass.X86_64.fprogB c.MP' (Impl.EcKey.Compressed.X86_64.checkRootOps c)).inline
    (.block (Impl.EcKey.Compressed.X86_64.checkRootChecks c))) s _
  refine WP.seq (WP.mono (checkPoly_ok hc hs hM hy hr hr2) fun s₁ I => ?_)
  have flag₁ : word s₁.mem base (c.sl FLAG) = mask P := by
    rw [flag_unch I.unch h7 h0 hn (by decide), hf]
  have hz : sv c base s₁ W3 = 0 ↔
      Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) I.lt, I.val]
    constructor <;> intro h <;> grind
  rw [Impl.EcKey.Compressed.X86_64.checkRootChecks, WP.block_append_iff]
  refine WP.mono (checkZero_ok c I.scr h0 hW (by omega)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have hs₂ := I.scr.of_keepRegs k₂ (by decide)
  have flag₂ : word s₂.mem base (c.sl FLAG) = mask
      (P ∧ Fin.ofNat c.C.p (sv c base s QY) * Fin.ofNat c.C.p (sv c base s QY) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2)) := by
    rw [f₂, flag₁, show wordsVal s₁.mem base (c.sl W3) c.n = sv c base s₁ W3 from rfl, mask_and]
    simp only [mask, hz]
  have y₂ : sv c base s₂ QY = sv c base s QY := by
    rw [sv, sv_flag O₂ h0 h7 hn (by decide) (by decide)]
    exact sv_unch I.unch h7 hn (by decide) (apart_slW (by decide))
  have tag₂ : word s₂.mem base (c.sl D) = word s.mem base (c.sl D) := by
    rw [O₂.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega)]
    exact I.unch.word (fun w hw => by
      have := apart_slW (c := c) (by decide : D ∉ [QYM, W1, W3, TMP]) w hw
      omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (parityMask_ok hs₂ h0 (by omega) (by omega)) fun s₃ ⟨mask₃, k₃⟩ => ?_
  rw [y₂, tag₂] at mask₃
  rw [WP.block_append_iff]
  refine WP.mono (invertMask_ok s₃ _ mask₃) fun s₄ ⟨mask₄, k₄⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  refine WP.mono (andFlag_ok' c hs₄ (by omega)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_⟩
  · exact (((I.keep.trans (k₂.mono (by simp [clob]))).trans
      ((Keeps.regs k₃).mono (by simp [clob]))).trans
      ((Keeps.regs k₄).mono (by simp [clob]))).trans (k₅.mono (by simp [clob]))
  · have U₁ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s.mem s₁.mem := I.unch.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi))
    have U₂ : Unch base (slW c [QYM, W1, W3, TMP, FLAG]) s₁.mem s₄.mem := by
      rw [k₄.2.1, k₃.2.1]
      exact slot_frame (by simp) (by omega) O₂
    exact unch_same (unch_same U₁ U₂) (slot_frame (by simp) (by omega) O₅)
  · rw [flag₅, k₄.2.1, k₃.2.1, flag₂, mask₄]
    simp only [not_not]
    exact mask_and _ _

end VG.Proof.EcKey.Compressed.X86_64
