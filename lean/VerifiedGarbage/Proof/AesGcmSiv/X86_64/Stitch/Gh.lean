module
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Stitch
public import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
public import VerifiedGarbage.Proof.Framework.X86_64.YFrame
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec

import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM-SIV's interleaved loop: the POLYVAL loads

`ghLoad_ok`: `ghLoad k` loads the `k`-th pair of powers from the working
space into `ymm12`, then blocks `2k` and `2k + 1` as they are (`ldR`, with
no byte reversal: POLYVAL's field element of 16 bytes is them as a
little-endian number, `Spec.GcmSiv.ofBytes`), `Y` added to block 0, and
their products with the powers, as `Proof.Gcm.X86_64.Stitch.ghLoad_ok`
states for GHASH's loads.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only acc_ok pxor72_ok ea_at)
open VG.Proof.Gcm.X86_64.Vpclmul (load256_lo load256_hi PReg)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Vpclmul (acc)
open VG.Impl.AesGcmSiv.X86_64Stitch (ldR ghLoad)

/-- The SSE block of a load's lane-wise instructions: `Y` added to the
block, if `first`, and the products. -/
def accR (first : Bool) (b : XReg) : List Instr :=
  (if first then [.xop (.bin .pxor .xmm7 .xmm2)] else []) ++ Impl.Gcm.X86_64.Pclmul.acc .xmm7 b

theorem accR_ok (first : Bool) (b : XReg) (t : State) (hb7 : b ≠ .xmm7) (hb8 : b ≠ .xmm8)
    (hb9 : b ≠ .xmm9) (hb10 : b ≠ .xmm10) (hb11 : b ≠ .xmm11) :
    WP isa (.block (accR first b)) t fun t' =>
      prod t' = (prod t).acc ((if first then t.xmm .xmm2 else 0) ^^^ t.xmm .xmm7) (t.xmm b) ∧
      Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  rw [accR, WP.block_append_iff]
  have fin : ∀ t₂, Only [.xmm7] t t₂ → t₂.xmm .xmm7 = (if first then t.xmm .xmm2 else 0) ^^^ t.xmm .xmm7 →
      WP isa (.block (Impl.Gcm.X86_64.Pclmul.acc .xmm7 b)) t₂ fun t' =>
        prod t' = (prod t).acc ((if first then t.xmm .xmm2 else 0) ^^^ t.xmm .xmm7) (t.xmm b) ∧
        Only [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
    intro t₂ o₂ e₂
    refine WP.mono (acc_ok .xmm7 b t₂ (by decide) (by decide) (by decide) (by decide) hb8 hb9 hb10 hb11)
      fun t' ⟨p', o'⟩ => ⟨?_, ?_⟩
    · rw [p', o₂.prod (by decide) (by decide) (by decide), e₂, o₂.xmm b (by simp [hb7])]
    · exact (o₂.trans o').weaken fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | (h | h | h | h) <;> simp [h]
  cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at fin ⊢
  · exact WP.block_nil (fin t ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (by simp))
  · exact WP.mono (pxor72_ok t) fun t₂ ⟨e₂, o₂⟩ => fin t₂ o₂ e₂

/-- The lane-wise instructions of a load. -/
abbrev restR (k : Nat) (p : XReg) : List Instr :=
  (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 p

theorem ldR_eq (k : Nat) (p : XReg) : ldR k p = .vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k)) :: restR k p := by
  simp only [ldR, restR, List.cons_append, List.nil_append]

theorem lane_ldR12 {k : Nat} (hk : k < 8) : laneSseBlock (restR k .xmm12) = some (accR (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Blocks `2k` and `2k + 1` at `rdx + 32 k`, as they are, added to the
lanes' products with the powers in `ymm12`. -/
theorem loadR_ok {k : Nat} (hk : k < 8) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ldR k .xmm12)) s fun s' =>
      (∀ l < 2, prod (s'.proj l) = (prod (s.proj l)).acc
        ((if k = 0 then s.lane .xmm2 l else 0) ^^^
          s.mem.readW (s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)
        (s.lane .xmm12 l)) ∧
      YFrame [.xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  let a := s.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := s.mem.readW a 256
  let s₁ := s.setV .l256 .xmm7 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ldR_eq, WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_at, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have l7 : ∀ l < 2, s₁.lane .xmm7 l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [s₁, State.lane_setV256, v, load256_lo]
    · simp [s₁, State.lane_setV256, v, load256_hi]
  have keep : ∀ r, r ≠ .xmm7 → ∀ l < 2, s₁.lane r l = s.lane r l := fun r hr l _ => by
    simp [s₁, State.lane_setV256, hr]
  refine WP.mono (WP.lanes (lane_ldR12 hk) fun l _ =>
      accR_ok _ .xmm12 (s₁.proj l) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (s₁.proj l) = prod (s.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    simp only [hp, State.proj_xmm, keep .xmm12 (by decide) l hl, l7 l hl, keep .xmm2 (by decide) l hl]
    by_cases h : k = 0 <;> simp only [a, h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r hr
    simp only [State.proj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-- The `k`-th pair of powers into `ymm12`, and blocks `2k` and `2k + 1` at
`rdx + 32 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 8) (t : State)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 2, prod (t'.proj l) = (prod (t.proj l)).acc
        ((if k = 0 then t.lane .xmm2 l else 0) ^^^
          t.mem.readW (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let a := t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := t.mem.readW a 256
  let t₁ := t.setV .l256 .xmm12 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ghLoad, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load256, ea_at, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → ∀ l < 2, t₁.lane r l = t.lane r l := fun r hr l _ => by
    simp [t₁, State.lane_setV256, hr]
  have l12 : ∀ l < 2, t₁.lane .xmm12 l = t.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [t₁, State.lane_setV256, v, load256_lo]
    · simp [t₁, State.lane_setV256, v, load256_hi]
  refine WP.mono (loadR_ok hk t₁ (by simpa [t₁] using hin)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [p' l hl, l12 l hl, keep _ (by decide) l hl]
    have hp : prod (t₁.proj l) = prod (t.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    rw [hp]; rfl
  · refine ⟨f'.gpr, f'.mem, f'.rd, f'.wr, fun r hr l hl => ?_⟩
    rw [f'.lane r (fun h => hr (List.mem_cons_of_mem _ h)) l hl, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

end VG.Proof.AesGcmSiv.X86_64.Stitch
