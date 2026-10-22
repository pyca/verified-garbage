module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.EcKey.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Finish
import VerifiedGarbage.Proof.Framework.Offset

/-! # Write the checked uncompressed encoding and restore the ABI -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.EcKey.X86_64 (lead_ok)

theorem decompressFinish_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.decompressFinish c =
    ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (([.mov32 .rax (.imm 4), .alu .and .rax (.reg .rcx), .store8 { base := .rsi, disp := 0 } .rax] :
      List Instr) ++
    (storeBytes c.C.len c.n .rsi 1 (c.sl E) ++ (storeBytes c.C.len c.n .rsi (1 + c.C.len) (c.sl Impl.Ecdh.X86_64.QY) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved)))) := by
  simp only [Impl.EcKey.Compressed.X86_64.decompressFinish, List.append_assoc]; rfl

/-- The result, the return value and the callee-saved registers. -/
theorem decompressFinish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hrsi : s.gpr .rsi = out) (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩) (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.X86_64.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hn := hs.nowrap
  have hX := sl_le c h7 (i := E) (by decide)
  have hY := sl_le c h7 (i := Impl.Ecdh.X86_64.QY) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  have h1 : ∀ e, out + BitVec.ofNat 64 1 + BitVec.ofNat 64 e = out + BitVec.ofNat 64 (1 + e) := fun e => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have hq : ∀ d, d + c.C.len ≤ 1 + 2 * c.C.len → (out + BitVec.ofNat 64 d).toNat + c.C.len ≤ 2 ^ 64 :=
    fun d hd => by
      rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hwr : ∀ {t : State} {d : Nat}, (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ t.wr →
      d + c.C.len ≤ 1 + 2 * c.C.len →
      ∀ e m, e + m ≤ c.C.len → InRegions t.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m :=
    fun hw' hd e m hm => ⟨_, hw', by rw [Offset.add_add]; exact Offset.contains_base out (by omega) (by omega)⟩
  have hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  have hscd : ∀ {d k : Nat}, d + k ≤ 1 + 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, k⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  have hout : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [decompressFinish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hrsi₁ : s₁.gpr .rsi = out := by rw [k₁.1 _ (by decide), hrsi]
  rw [WP.block_append_iff]
  have hc0 : (⟨out, 1 + 2 * c.C.len⟩ : Region).Contains out 1 := by
    have := Offset.contains_base out (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega) (by omega)
    rwa [hout] at this
  refine WP.mono (lead_ok hrsi₁ ⟨_, by rw [k₁.2.2.2]; exact hw, hc0⟩ b (by rw [e₁, hf]))
    fun s₂ ⟨e₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₂ := O₂.unch_far (by have := hscd (d := 0) (k := 1) (by omega); rwa [hout] at this)
  have hrsi₂ : s₂.gpr .rsi = out := by rw [k₂.gpr _ (by decide), hrsi₁]
  have hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  have x₂ : wordsVal s₂.mem base (c.sl E) c.n = sv c base s E := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .rsi) (d := 1) (a := c.sl E) (by decide) (by decide) b
    hrcx₂ hX (by omega) hc.len_lo hc.len_hi (by rw [hrsi₂]; exact hq 1 (by omega))
    (by rw [hrsi₂]; exact hwr (by rw [k₂.wr, k₁.2.2.2]; exact hw) (by omega))
    (by rw [hrsi₂]; exact hdsc hX (by omega))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ := O₃.unch_far (hscd (d := 1) (by omega))
  have hrsi₃ : s₃.gpr .rsi = out := by rw [k₃.gpr _ (by decide), hrsi₂]
  have hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  have y₃ : wordsVal s₃.mem base (c.sl Impl.Ecdh.X86_64.QY) c.n = sv c base s Impl.Ecdh.X86_64.QY := by
    rw [U₃.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega),
      U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega) (by omega), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₃ (dst := .rsi) (d := 1 + c.C.len) (a := c.sl Impl.Ecdh.X86_64.QY)
    (by decide) (by decide) b hrcx₃ hY (by omega) hc.len_lo hc.len_hi (by rw [hrsi₃]; exact hq _ (by omega))
    (by rw [hrsi₃]; exact hwr (by rw [k₃.wr, k₂.wr, k₁.2.2.2]; exact hw) (by omega))
    (by rw [hrsi₃]; exact hdsc hY (by omega))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hrsi₃] at e₄ O₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ := O₄.unch_far (hscd (d := 1 + c.C.len) (by omega))
  have hrcx₄ : s₄.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₄.gpr _ (by decide), hrcx₃]
  have lead : Spec.Ecdsa.bytesAt s₄.mem out 1 = [if b then 4 else 0] := by
    rw [bytesAt_keep O₄ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega),
      bytesAt_keep O₃ (Offset.base_disjoint out (by omega) (by omega)) (by omega) (by omega)]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, hout, e₂]
  have first : Spec.Ecdsa.bytesAt s₄.mem (out + BitVec.ofNat 64 1) c.C.len =
      if b then toBytes c.C.len (sv c base s E) else List.replicate c.C.len 0 := by
    rw [bytesAt_keep O₄ (Offset.disjoint out (by omega) (by omega) (by omega)) (by omega) (by omega), e₃, x₂]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₄) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hsv₅ : Spill.Saved s₅.mem base g Cfg.saved := by
    rw [k₅.2.1]
    have h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃) h48 U₄
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₅ (by decide) (fun p hp => ?_)
    (by rw [hs₅.rdi]; exact hsv₅)) fun s₆ ⟨g₆, r₆, m₆, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₅.rdi]; exact ⟨_, List.mem_append_right _ hs₅.wr, hs₅.contains (by have : size = 8192 := rfl; omega) (by decide)⟩
  refine ⟨?_, ?_, g₆, fun r hr => ?_⟩
  · rw [m₆, k₅.2.1, bytesAt_add, show 2 * c.C.len = c.C.len + c.C.len by omega, bytesAt_add, lead, first,
      BitVec.add_assoc, BitVec.ofNat_add_ofNat, e₄, y₃]
    cases b
    · simp only [Bool.false_eq_true, ite_false, ← List.replicate_append_replicate]; rfl
    · simp only [ite_true]; rfl
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₆ _ hra, e₅, hrcx₄, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₆ r (by simp [Cfg.saved, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      k₅.1 r (by simp [hr.1]), k₄.gpr r (by simp [hr.1, hr.2.2.1]), k₃.gpr r (by simp [hr.1, hr.2.2.1]),
      k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2.1])]

end VG.Proof.EcKey.Compressed.X86_64
