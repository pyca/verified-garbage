import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Vpclmul.Exec

/-!
# Interleaved counter mode and GHASH: the GHASH loads

`ghLoad_ok`: `ghLoad k` loads the `k`-th pair of powers from the working
space into `ymm12`, and then does what `vg_ghash_vpclmul`'s `k`-th load does
(`Vpclmul.load_ok`). The products after the loads of a body, in the order of
an encryption body (`ordE`: the product with `Y` last) or of a decryption
body (`ordD`), are `accN`. That, reduced, the two lanes' add up to `GHASH`
over the sixteen blocks for the powers the setup stores (`FinOk`) needs the
field: `Stitch/Ok.lean` proves it (`finE`, `finD`).
-/

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Proof.Gcm.X86_64.Vpclmul (restV ldacc load_ok load256_lo load256_hi)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (ghLoad)
open VG.Spec.Gcm (Block blockAt)

theorem lane_ld12 {k : Nat} (hk : k < 8) :
    laneSseBlock (restV k .xmm12) = some (ldacc (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The `k`-th pair of powers into `ymm12`, and blocks `2k` and `2k + 1` at
`rdx + 32 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 8) (t : State) (h0 : ∀ l < 2, t.lane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)) 32) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 2, prod (t'.proj l) = (prod (t.proj l)).acc
        ((if k = 0 then t.lane .xmm2 l else 0) ^^^
          blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      YFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let a := t.gpr .r11 + BitVec.ofInt 64 ((32 * k : Nat) : Int)
  let v := t.mem.readW a 256
  let t₁ := t.setV .l256 .xmm12 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  rw [ghLoad, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load256, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hpin, ite_true,
    Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → ∀ l < 2, t₁.lane r l = t.lane r l := fun r hr l _ => by
    simp [t₁, State.lane_setV256, hr]
  have l12 : ∀ l < 2, t₁.lane .xmm12 l = t.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [t₁, State.lane_setV256, v, load256_lo]
    · simp [t₁, State.lane_setV256, v, load256_hi]
  refine WP.mono (load_ok (lane_ld12 hk) (by decide) t₁ (fun l hl => by rw [keep _ (by decide) l hl]; exact h0 l hl)
    (by simpa [t₁] using hin)) fun t' ⟨p', f'⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [p' l hl, l12 l hl, keep _ (by decide) l hl]
    have hp : prod (t₁.proj l) = prod (t.proj l) := by
      simp only [prod, State.proj_xmm, keep .xmm8 (by decide) l hl, keep .xmm9 (by decide) l hl,
        keep .xmm10 (by decide) l hl]
    rw [hp]; rfl
  · refine ⟨f'.gpr, f'.mem, f'.rd, f'.wr, fun r hr l hl => ?_⟩
    rw [f'.lane r (fun h => hr (List.mem_cons_of_mem _ h)) l hl, keep r (fun h => hr (h ▸ List.mem_cons_self)) l hl]

/-! ## The products of a body -/

/-- The input of the `k`-th load in lane `l`: block `2k + l`, with `Y` (`yl l`)
added to block 0. -/
def inp (X : Nat → Block) (yl : Nat → Block) (k l : Nat) : Block := (if k = 0 then yl l else 0) ^^^ X (2 * k + l)

/-- The products of lane `l` after the first `n` loads, in the order `ord`. -/
def accN (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (inp X yl (ord i) l) (P (ord i) l)) Prod.zero

theorem accN_zero (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l : Nat) :
    accN ord X P yl l 0 = Prod.zero := rfl

theorem accN_succ (ord : Nat → Nat) (X : Nat → Block) (P : Nat → Nat → Block) (yl : Nat → Block) (l n : Nat) :
    accN ord X P yl l (n + 1) = (accN ord X P yl l n).acc (inp X yl (ord n) l) (P (ord n) l) := by
  simp only [accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem zero_xor_b (a : Block) : (0 : Block) ^^^ a = a := by simp

end VG.Proof.Gcm.X86_64.Stitch
