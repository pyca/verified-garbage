module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Setup
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on PPC64LE, the whole derivation: a block, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `r23` points past them and `r24` counts the bytes left,
and `scratch` holds `INT (k + 1)`, byte-reversed. A block copies the key's
inner state into the working state (`HashOK.reloc`: it represents a whole
block), absorbs the salt and `INT (k + 1)` into it (`update`), and computes
`U₁` with HMAC's `finalize` (`u1_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.PPC64LE

open VG.PPC64LE
open VG.Impl.Pbkdf2.Whole.PPC64LE (Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK Saved)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_mov wp_addi wp_li)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem blockKey_length (hH : HashOK F.H) (k : List Byte) : (blockKey hH.SH.H k).length = F.H.B := by
  have hB := hH.hB; have := hH.hDB
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hH.hashLen]; omega
  · omega

/-! ## After `k` blocks -/

section
variable (hF : FnsOK F) (s₀ : State)

/-- The salt. -/
abbrev saltB : List Byte := bytesAt s₀.mem (salt s₀) (sl s₀)
/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (K0 hF s₀)
/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (k : Nat) : List Byte := Whole.G (prf hF s₀) (saltB s₀) (cc s₀) k
abbrev Tk (i : Nat) : List Byte := Whole.Tb (prf hF s₀) (saltB s₀) (cc s₀) i
abbrev nbk : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

end

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR F hF.X s₀ s
  st : States hF s₀ s.mem
  r23 : s.gpr .r23 = out s₀ + BitVec.ofNat 64 (dn s₀ (F := F) k)
  r24 : s.gpr .r24 = BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k)
  intW : s.mem.readW (sA s₀ F.intO) 32 = rev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (out s₀) (dn s₀ (F := F) k) = (Gk hF s₀ k).take (dn s₀ (F := F) k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := .r23 :: .r24 :: kregs

/-- Where a block writes, before it copies `T` out: the working space of the
functions we call, the parts of `scratch` from the working state up to
`INT (i)`, and the stack below the frame. -/
def Wb (F : Fns) (X : Nat) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ 48 ≤ o ∧ o + n ≤ F.st0O) ∨ (∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO) ∨
    ∃ n, r = below (s₀.sp - 48) n ∧ n + 48 ≤ X + 144

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

theorem Wb.ok {r : Region} (h : Wb F hF.X s₀ r) :
    Wk F hF.X s₀ r ∧ (sR s₀ F.st0O (2 * F.H.S)).Disjoint r ∧ (sR s₀ F.intO 4).Disjoint r ∧
      (outR s₀).Disjoint r := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | ⟨o, n, rfl, h₁, h₂⟩ | ⟨n, rfl, hn⟩
  · exact ⟨.inl ⟨o, n, rfl, h₁, by omega⟩, part_disj hb (.inr h₂) (by omega) (by omega),
      part_disj hb (.inr (by omega)) (by omega) (by omega), hp.o_s.sub_right (part_sub (by omega))⟩
  · exact ⟨.inl ⟨o, n, rfl, by omega, by omega⟩, part_disj hb (.inl (by omega)) (by omega) (by omega),
      part_disj hb (.inr h₂) (by omega) (by omega), hp.o_s.sub_right (part_sub (by omega))⟩
  · have hsub := below_stk hp hn
    exact ⟨.inr ⟨n, rfl, hn⟩, (hp.b_s.sub_left hsub |>.sub_right (part_sub (by omega))).symm,
      (hp.b_s.sub_left hsub |>.sub_right (part_sub (by omega))).symm, (hp.b_o.sub_left hsub).symm⟩

/-- `Inv` survives writes where a block writes. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wb F hF.X s₀ r) : Inv hF s₀ k s' := by
  have hz := sizes hF; have hb := hz.reach
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) hf
      (fun r hr => (Wk.ok hp hb (Wb.ok hp (hw r hr)).1).1) (fun r hr => (Wk.ok hp hb (Wb.ok hp (hw r hr)).1).2),
    h.st.keep hf (fun r hr => (Wb.ok hp (hw r hr)).2.1), by rw [hg _ (by simp), h.r23],
    by rw [hg _ (by simp), h.r24], ?_, h.glen, ?_⟩
  · rw [← h.intW]
    exact hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => (Wb.ok hp (hw r hr)).2.2.1)
      (by decide)
  · rw [← h.outB]
    have osub : Region.Sub ⟨out s₀, dn s₀ (F := F) k⟩ (outR s₀) := Region.sub_prefix (Nat.min_le_right _ _)
    exact Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨out s₀, dn s₀ (F := F) k⟩)
      (fun r hr => ((Wb.ok hp (hw r hr)).2.2.2).sub_left osub)
      (by have e1 : dn s₀ (F := F) k ≤ ol s₀ := Nat.min_le_right _ _
          have e2 : ol s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
          show dn s₀ (F := F) k ≤ 2 ^ 64; omega) hi

end

/-! ## A block, up to `U₁` -/

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- Copying `n` words from offset `a` of `scratch` to offset `b`, where a
block writes. -/
theorem copy_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {a b n : Nat} (hab : a + 4 * n ≤ b ∨ b + 4 * n ≤ a)
    (ha : a + 4 * n ≤ F.bytes) (hw : Wb F hF.X s₀ (sR s₀ b (4 * n))) (hbo : b + 4 * n ≤ F.bytes)
    {rest : List Instr} {Q : State → Prop}
    (hk : ∀ t, Inv hF s₀ k t → (∀ r, r ≠ .r8 → t.gpr r = s.gpr r) →
      t.mem = writeBytes s.mem (sA s₀ b) (bytesAt s.mem (sA s₀ a) (4 * n)) → WP isa (.block rest) t Q) :
    WP isa (.block ((List.range n).flatMap (Impl.Hmac.Stream.PPC64LE.Hash.cp32 .r21 .r21 a b) ++ rest)) s Q := by
  have hz := sizes hF; have hb := hz.reach
  have e : ∀ o j, s.gpr .r21 + BitVec.ofNat 64 o + BitVec.ofNat 64 j = sA s₀ (o + j) := fun o j => by
    rw [h.kr.r21, ← VG.Proof.Hmac.Stream.PPC64LE.add_off]
  refine VG.Proof.Hmac.Stream.PPC64LE.copy32_ok (src := .r21) (dst := .r21) (by decide) (by decide) (by decide)
    (by decide) a b n ⟨by omega, by omega⟩ rest s Q
    (fun j hj => by rw [e]; exact in_sc' hp hb h.kr.wr (by omega))
    (fun j hj => by rw [e]; exact in_sc hp hb h.kr.wr (by omega))
    (by rw [h.kr.r21]; exact Offset.sep _ hab (by have := hp.nsc; omega) (by have := hp.nsc; omega))
    fun t g rd wr sp m => ?_
  rw [h.kr.r21] at m
  refine hk t (h.keep hp rd wr sp (fun r hr => g r (by revert r; decide)) (rs := [sR s₀ b (4 * n)]) ?_
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hw)) g m
  rw [m]
  exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

/-- The key's inner state copied into the working state, which then
represents `K₀ ⊕ ipad`, and `update`'s arguments for the salt. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block (F.copyW ++ F.saltArgs)) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad) ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = BitVec.ofNat 64 F.H.B ∧ t.gpr .r5 = salt s₀ ∧ t.gpr .r6 = s₀.gpr .r6 ∧
      t.gpr .r7 = sA s₀ 48 := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hS4 : 4 * (F.H.S / 4) = F.H.S := by have := hz.N4; have := hz.S; rcases hz.B with h | h <;> omega
  unfold Fns.copyW Fns.saltArgs
  refine copy_ok hp h (a := F.st0O) (b := F.stWO) (n := F.H.S / 4) (by omega) (by omega)
    (.inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩)) (by omega) fun t ht g m => ?_
  refine wp_addi (by omega) fun s₁ u₁ => wp_li (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨ht.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm]
    have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    refine hF.hH.reloc s.mem t.mem _ _ _ (by rw [xorPad_length, hK]; exact Nat.mod_self _) (fun i hi => ?_) h.st.1
    have := hz.S
    rw [hS4] at m
    rw [m, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [bytesAt_length]; omega)
      (by rw [bytesAt_length]; omega), VG.Proof.Hmac.Common.bytesAt_getD' _ _ (by omega)]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r25]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r20]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.r21]; rfl

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
