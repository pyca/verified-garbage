import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.HInvBits
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZP

/-!
# Converting the powers of a key context, two at a time

Untrusted: everything here is checked by Lean. `StitchZP.cvtPair j d`
loads the blocks at `ctx + 256 + 16 j` and `ctx + 240 + 16 j` into the two
lanes of `ymm7` (`cvtLoad_ok`), byte-reversed, and leaves in each lane of
`d` the block loaded times `x⁻¹` (`hInvF`, `cvtPair_ok`): lane by lane
(`WP.lanes`), `StitchZP.hInvY` is `Pclmul.hInv`'s computation (`hInvS_ok`,
from `Pclmul.shl1` and `mask_eq`; `Pclmul.x_φ_hInv` says it is `· x⁻¹` in
the field), with the constants `StitchZP.cvtConsts` leaves (`consts_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Only shl1 mask_eq eval_pxor ea_at)
open VG.Proof.Gcm.X86_64.Vpclmul (yframe_of_lanes)
open VG.Impl.Gcm.X86_64.Pclmul (at_ xInv poly revMask)
open VG.Impl.Gcm.X86_64.StitchZP (cvtConsts hInvY cvtPair)

/-- All ones, as `Pclmul.hInv` builds it. -/
def ones : BitVec 128 := XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))
  ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64))

theorem eval_mov (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

theorem pcmpeqd_self (v : BitVec 128) : XBinOp.eval .pcmpeqd v v = ones := by
  simp only [XBinOp.eval, ↓reduceIte]; decide

/-! ## The constants -/

/-- `cvtConsts`, on one lane. -/
def constsS : List Instr :=
  [.xop (.bin .pcmpeqd .xmm9 .xmm9), .xop (.bin .movdqa .xmm8 .xmm9), .xop (.shift .psrlq .xmm8 63),
   .xop (.shift .pslldq .xmm8 8), .xop (.shift .psrldq .xmm8 8), .xop (.bin .pxor .xmm8 .xmm1)]

theorem lane_consts : laneSseBlock cvtConsts = some constsS := rfl

theorem constsS_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block constsS) s fun s' => s'.xmm .xmm8 = xInv ∧ s'.xmm .xmm9 = ones ∧ Only [.xmm8, .xmm9] s s' := by
  apply WP.of_runBlock
  simp only [constsS, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, h1, pcmpeqd_self, eval_mov, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

theorem consts_ok (s : State) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block cvtConsts) s fun s' => (∀ l < 2, s'.lane .xmm8 l = xInv) ∧ (∀ l < 2, s'.lane .xmm9 l = ones) ∧
      YFrame [.xmm8, .xmm9] s s' :=
  WP.mono (WP.lanes lane_consts fun l hl => constsS_ok (s.proj l) (by simpa using h1 l hl))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => by simpa using (hq l hl).1, fun l hl => by simpa using (hq l hl).2.1,
      yframe_of_lanes hk fun l hl r hr => (hq l hl).2.2.xmm r hr⟩

/-! ## `H · x⁻¹`, lane by lane -/

/-- `v · x⁻¹`, as `Pclmul.hInv` computes it: `v` shifted left by one bit, and
`x⁻¹` added if the bit shifted out was set (`Pclmul.x_φ_hInv`). -/
def hInvF (v : BitVec 128) : BitVec 128 := (v <<< 1) ^^^ (if v.getMsbD 0 then xInv else 0)

/-- `hInvY d xmm7 xmm10`, on one lane. -/
def hInvS (d : XReg) : List Instr :=
  [.xop (.bin .movdqa d .xmm7), .xop (.shift .psllq d 1), .xop (.bin .movdqa .xmm10 .xmm7),
   .xop (.shift .psrlq .xmm10 63), .xop (.shift .pslldq .xmm10 8), .xop (.bin .por d .xmm10),
   .xop (.pshufd .xmm10 .xmm7 0xff), .xop (.shift .psrld .xmm10 31), .xop (.bin .paddd .xmm10 .xmm9),
   .xop (.bin .pandn .xmm10 .xmm8), .xop (.bin .pxor d .xmm10)]

theorem lane_hInv {d : XReg} (h7 : d ≠ .xmm7) : laneSseBlock (hInvY d .xmm7 .xmm10) = some (hInvS d) := by
  simp only [hInvY, hInvS, laneSseBlock, laneSse, laneSseV, ne_eq, not_true_eq_false, ↓reduceIte,
    reduceCtorEq, Ne.symm h7, VBinOp.sse, List.cons_append, List.nil_append]

theorem hInvS_ok (d : XReg) (h7 : d ≠ .xmm7) (h8 : d ≠ .xmm8) (h9 : d ≠ .xmm9) (h10 : d ≠ .xmm10) (s : State)
    (c8 : s.xmm .xmm8 = xInv) (c9 : s.xmm .xmm9 = ones) :
    WP isa (.block (hInvS d)) s fun s' => s'.xmm d = hInvF (s.xmm .xmm7) ∧ Only [d, .xmm10] s s' := by
  apply WP.of_runBlock
  simp only [hInvS, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, h10, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, c8, c9,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [show XBinOp.eval .movdqa (s.xmm d) (s.xmm .xmm7) = s.xmm .xmm7 from rfl,
      show XBinOp.eval .movdqa (s.xmm .xmm10) (s.xmm .xmm7) = s.xmm .xmm7 from rfl, eval_pxor,
      show XBinOp.eval .por (XShiftOp.eval .psllq (s.xmm .xmm7) 1)
        (XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) =
        XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
          XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8 from rfl,
      shl1, ones, mask_eq]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]

/-- `hInvY d xmm7 xmm10`: `d = ymm7 · x⁻¹` in each lane. -/
theorem hInvY_ok (d : XReg) (h7 : d ≠ .xmm7) (h8 : d ≠ .xmm8) (h9 : d ≠ .xmm9) (h10 : d ≠ .xmm10) (s : State)
    (c8 : ∀ l < 2, s.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s.lane .xmm9 l = ones) :
    WP isa (.block (hInvY d .xmm7 .xmm10)) s fun s' =>
      (∀ l < 2, s'.lane d l = hInvF (s.lane .xmm7 l)) ∧ YFrame [d, .xmm10] s s' :=
  WP.mono (WP.lanes (lane_hInv h7) fun l hl => hInvS_ok d h7 h8 h9 h10 (s.proj l)
      (by simpa using c8 l hl) (by simpa using c9 l hl))
    fun s' ⟨hk, hq⟩ => ⟨fun l hl => by simpa using (hq l hl).1,
      yframe_of_lanes hk fun l hl r hr => (hq l hl).2.xmm r hr⟩

/-! ## Two blocks of the key context -/

/-- The blocks at `rdi + 256 + 16 j` and `rdi + 240 + 16 j`, byte-reversed, in
the lanes of `ymm7`. -/
theorem cvtLoad_ok (j : Nat) (s : State) (h0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (hin₀ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int)) 16) :
    WP isa (.block [.vmovdquLoad .l128 .xmm7 (at_ .rdi (256 + 16 * j)),
      .vmovdquLoad .l128 .xmm10 (at_ .rdi (240 + 16 * j)), .vop (.vinserti128 .xmm7 .xmm7 .xmm10 1),
      .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)]) s fun s' =>
      s'.lane .xmm7 0 = Spec.Gcm.blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int)) ∧
      s'.lane .xmm7 1 = Spec.Gcm.blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int)) ∧
      YFrame [.xmm7, .xmm10] s s' := by
  have m0 : s.lane .xmm0 0 = revMask := h0 0 (by decide)
  have m1 : s.lane .xmm0 1 = revMask := h0 1 (by decide)
  simp only [State.lane, ite_true, Nat.one_ne_zero, ite_false] at m0 m1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.load128, ea_at, hin₀, hin₁,
    Option.map_some, State.setV, State.lane, VBinOp.sse, reduceCtorEq, ↓reduceIte,
    Nat.one_ne_zero, Option.some.injEq, exists_eq_left', show (1 : BitVec 8).getLsbD 0 = true from rfl,
    m0, m1]
  refine ⟨(VG.Proof.Gcm.X86_64.blockAt_eq ..).symm, (VG.Proof.Gcm.X86_64.blockAt_eq ..).symm, rfl, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [State.lane, hr.1, hr.2]

/-- `cvtPair j d`: in each lane of `d` the block at `rdi + 256 + 16 j`
(lane 0) or `rdi + 240 + 16 j` (lane 1), times `x⁻¹`. -/
theorem cvtPair_ok (j : Nat) (d : XReg) (h7 : d ≠ .xmm7) (h8 : d ≠ .xmm8) (h9 : d ≠ .xmm9)
    (h10 : d ≠ .xmm10) (s : State) (m0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (c8 : ∀ l < 2, s.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s.lane .xmm9 l = ones)
    (hin₀ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int)) 16) :
    WP isa (.block (cvtPair j d)) s fun s' =>
      s'.lane d 0 = hInvF (Spec.Gcm.blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((256 + 16 * j : Nat) : Int))) ∧
      s'.lane d 1 = hInvF (Spec.Gcm.blockAt s.mem (s.gpr .rdi + BitVec.ofInt 64 ((240 + 16 * j : Nat) : Int))) ∧
      YFrame [.xmm7, .xmm10, d] s s' := by
  rw [cvtPair, WP.block_append_iff]
  refine WP.mono (cvtLoad_ok j s m0 hin₀ hin₁) fun s₁ ⟨l0, l1, f₁⟩ => ?_
  refine WP.mono (hInvY_ok d h7 h8 h9 h10 s₁ (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact c8 l hl)
    (fun l hl => by rw [f₁.lane _ (by decide) l hl]; exact c9 l hl)) fun s' ⟨v, f'⟩ => ?_
  refine ⟨by rw [v 0 (by decide), l0], by rw [v 1 (by decide), l1],
    ⟨f'.gpr.trans f₁.gpr, f'.mem.trans f₁.mem, f'.rd.trans f₁.rd, f'.wr.trans f₁.wr, fun r hr l hl => ?_⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [f'.lane r (by simp [hr.2.1, hr.2.2]) l hl, f₁.lane r (by simp [hr.1, hr.2.1]) l hl]

end VG.Proof.Gcm.X86_64.StitchZP
