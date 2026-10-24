module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Setup
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Offset
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

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- The salt and `scratch` fit in the address space together. -/
theorem sl_bytes : sl s₀ + F.bytes ≤ 2 ^ 64 :=
  Whole.len_add_le hp.sa_s hp.nsa hp.nsc

theorem below48 {s : State} (h : KR F hF.X s₀ s) {n : Nat} (hn : n + 48 ≤ hF.X + 144) :
    Region.Sub (below s.sp n) (stk hF.X s₀) := by
  rw [h.sp]; exact below_stk hp hn

/-- `update`'s arguments for the working state, with the `len` bytes at `dat`. -/
theorem updW_args {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat}
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h5 : s.gpr .r5 = dat) (h6 : (s.gpr .r6).toNat = len)
    (h7 : s.gpr .r7 = sA s₀ 48) (hd₂ : Region.Disjoint ⟨dat, len⟩ (sR s₀ F.stWO F.H.S))
    (hd₃ : Region.Disjoint ⟨dat, len⟩ (sR s₀ 48 F.H.W)) (hs₂ : (stk hF.X s₀).Disjoint ⟨dat, len⟩)
    (hcd : ∃ r' ∈ s.rd ++ s.wr, ∃ off, dat = r'.base + BitVec.ofNat 64 off ∧ off + len ≤ r'.len) :
    UpdArgs F s (sA s₀ F.stWO) dat (sA s₀ 48) len := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hD := hz.D; have hN := hz.N; have hSS := hz.S; have hB := hz.B
  have hsp := sp_toNat hp
  have bs := below48 hp h.kr (n := 48) (by omega)
  refine ⟨h3, h5, h6, h7, part_disj hb (.inr (by omega)) (by omega) (by omega), hd₂, hd₃,
    by rw [h.kr.sp, hsp]; have := hp.sp; omega, hp.b_s.sub_left bs |>.sub_right (part_sub (by omega)),
    hs₂.sub_left bs, hp.b_s.sub_left bs |>.sub_right (part_sub (by omega)), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hcd
    · exact ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), F.stWO, rfl,
        by show F.stWO + F.H.S ≤ F.bytes; omega⟩
    · exact ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), 48, rfl, by show 48 + F.H.W ≤ F.bytes; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, F.stWO, rfl, by show F.stWO + F.H.S ≤ F.bytes; omega⟩
    · exact ⟨scR F s₀, sc_wr hp h.kr.wr, 48, rfl, by show 48 + F.H.W ≤ F.bytes; omega⟩

/-- `update` of the working state, from `m`, with the `len` bytes at `dat`. -/
theorem updW_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat} {m : List Byte}
    (ha : UpdArgs F s (sA s₀ F.stWO) dat (sA s₀ 48) len)
    (hm : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) (h4 : s.gpr .r4 = BitVec.ofNat 64 m.length) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (m ++ bytesAt s.mem dat len) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hWc := hz.Wc; have hD := hz.D; have hSS := hz.S
  refine upd_call hF.hH ha fun t a hu => ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide))
    a.frame fun r hr => ?_, hu m hm h4⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
  · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩
  · exact .inr (.inr ⟨48, by rw [h.kr.sp], by omega⟩)

end

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- `update`'s arguments for the salt. -/
theorem b2_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h5 : s.gpr .r5 = salt s₀) (h6 : s.gpr .r6 = s₀.gpr .r6) (h7 : s.gpr .r7 = sA s₀ 48) :
    UpdArgs F s (sA s₀ F.stWO) (salt s₀) (sA s₀ 48) (sl s₀) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hWc := hz.Wc; have hSS := hz.S
  exact updW_args hp h h3 h5 (by rw [h6]) h7
    (hp.sa_s.sub_right (part_sub (by omega))) (hp.sa_s.sub_right (part_sub (by omega))) hp.b_sa
    ⟨saltR s₀, List.mem_append_left _ (by rw [h.kr.rd, hp.rd]; simp), 0, by simp, by simp⟩

/-- The salt absorbed into the working state. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad)) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 F.H.B) (h5 : s.gpr .r5 = salt s₀) (h6 : s.gpr .r6 = s₀.gpr .r6)
    (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hWc := hz.Wc; have hSS := hz.S
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine WP.mono (updW_ok hp h (b2_args hp h h3 h5 h6 h7) hr
    (by rw [h4, xorPad_length, hK])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [h.kr.saltBytes hp] at hu

/-- `update`'s arguments for `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = BitVec.ofNat 64 (F.H.B + sl s₀) ∧ t.gpr .r5 = sA s₀ F.intO ∧ t.gpr .r6 = BitVec.ofNat 64 4 ∧
      t.gpr .r7 = sA s₀ 48 := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  unfold Fns.updArgs
  refine wp_addi (by omega) fun s₁ u₁ => wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_addi (by omega) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r20]
    have hsum : F.H.B + sl s₀ < 2 ^ 64 := by
      have := sl_bytes hp; have := hz.S; have := hz.Wc; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .r6).toNat + F.H.B % 2 ^ 64) % 2 ^ 64 = (F.H.B + (s₀.gpr .r6).toNat) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B) (by omega), Nat.add_comm]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]; rfl

/-- `update`'s arguments for `INT (k + 1)`. -/
theorem b4_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h3 : s.gpr .r3 = sA s₀ F.stWO)
    (h5 : s.gpr .r5 = sA s₀ F.intO) (h6 : s.gpr .r6 = BitVec.ofNat 64 4) (h7 : s.gpr .r7 = sA s₀ 48) :
    UpdArgs F s (sA s₀ F.stWO) (sA s₀ F.intO) (sA s₀ 48) 4 := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  have hsub : Region.Sub ⟨sA s₀ F.intO, 4⟩ (scR F s₀) := part_sub (by omega)
  exact updW_args hp h h3 h5 (by rw [h6]; rfl) h7
    (part_disj hb (.inr (by omega)) (by omega) (by omega)) (part_disj hb (.inr (by omega)) (by omega) (by omega))
    (hp.b_s.sub_right hsub) ⟨scR F s₀, List.mem_append_right _ (sc_wr hp h.kr.wr), F.intO, rfl,
      by show F.intO + 4 ≤ F.bytes; omega⟩

/-- `INT (k + 1)` absorbed into the working state. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀))
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = BitVec.ofNat 64 (F.H.B + sl s₀))
    (h5 : s.gpr .r5 = sA s₀ F.intO) (h6 : s.gpr .r6 = BitVec.ofNat 64 4) (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hsub : Region.Sub ⟨sA s₀ F.intO, 4⟩ (scR F s₀) := part_sub (by omega)
  refine WP.mono (updW_ok hp h (b4_args hp h h3 h5 h6 h7) hr
    (by rw [h4, List.length_append, xorPad_length, hK, bytesAt_length])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [Whole.bytes_rev_int (i := k + 1) (by rw [h.intW]; rfl)] at hu

end

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F hF.X s₀)
include hp

/-- HMAC's `finalize`'s arguments. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .r3 = sA s₀ F.stWO ∧
      t.gpr .r4 = sA s₀ F.st1O ∧ t.gpr .r5 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧ t.gpr .r6 = sA s₀ F.uO ∧
      t.gpr .r7 = sA s₀ 48 := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  unfold Fns.finArgs
  refine wp_addi (by omega) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ =>
    wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₃ u₃ => wp_addi (by omega) fun s₄ u₄ =>
    wp_addi (by decide) fun s₅ u₅ => WP.block_nil ?_
  have mm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₅.other r (by revert r; decide), u₄.other r (by revert r; decide), u₃.other r (by revert r; decide),
        u₂.other r (by revert r; decide), u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r20]
    have hsum : F.H.B + (sl s₀ + 4) < 2 ^ 64 := by
      have := sl_bytes hp; have := hz.S; have := hz.Wc; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .r6).toNat + (F.H.B + 4) % 2 ^ 64) % 2 ^ 64 = (F.H.B + ((s₀.gpr .r6).toNat + 4)) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B + 4) (by omega)]
    congr 1; omega
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]
  · upd_simp [u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.r21]; rfl

/-- HMAC's `finalize`'s arguments. -/
theorem b6_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = sA s₀ F.st1O) (h6 : s.gpr .r6 = sA s₀ F.uO)
    (h7 : s.gpr .r7 = sA s₀ 48) : HfArgs F s (sA s₀ F.stWO) (sA s₀ F.st1O) (sA s₀ F.uO) (sA s₀ 48) := by
  have hz := sizes hF; have hl := layout (F := F); have hb := hz.reach
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D; have hN := hz.N; have hB := hz.B
  have hsp := sp_toNat hp
  have bs := below48 hp h.kr (n := 96) (by omega)
  have pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ F.bytes → b + n ≤ F.bytes →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj hb h₁ h₂ h₃
  have bp : ∀ {o n : Nat}, o + n ≤ F.bytes → (below s.sp 96).Disjoint (sR s₀ o n) := fun h' =>
    hp.b_s.sub_left bs |>.sub_right (part_sub h')
  have cv : ∀ {o n : Nat}, o + n ≤ F.bytes → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun {o n} h' => ⟨scR F s₀, sc_wr hp h.kr.wr, o, rfl, h'⟩
  refine ⟨h3, h4, h6, h7, by rw [h.kr.sp, hsp]; have := hp.sp; omega,
    pd (.inr (by omega)) (by omega) (by omega), pd (.inl (by omega)) (by omega) (by omega),
    pd (.inr (by omega)) (by omega) (by omega), pd (.inl (by omega)) (by omega) (by omega),
    pd (.inr (by omega)) (by omega) (by omega), pd (.inr (by omega)) (by omega) (by omega),
    bp (by omega), bp (by omega), bp (by omega), bp (by omega), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have cv' : ∀ o n, o + n ≤ F.bytes → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
        (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
      obtain ⟨r', hr', off, e, l⟩ := cv h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
    rcases hr with rfl | rfl | rfl | rfl
    · exact cv' F.st1O F.H.S (by omega)
    · exact cv' F.stWO F.H.S (by omega)
    · exact cv' F.uO F.H.D (by omega)
    · exact cv' 48 (F.H.W + 48 + F.H.FD) (by omega)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cv (o := F.stWO) (n := F.H.S) (by omega)
    · exact cv (o := F.uO) (n := F.H.D) (by omega)
    · exact cv (o := 48) (n := F.H.W + 48 + F.H.FD) (by omega)

/-- `U₁`, with HMAC's `finalize`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (h3 : s.gpr .r3 = sA s₀ F.stWO) (h4 : s.gpr .r4 = sA s₀ F.st1O)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4))) (h6 : s.gpr .r6 = sA s₀ F.uO)
    (h7 : s.gpr .r7 = sA s₀ 48) :
    WP isa F.callHf s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hWc := hz.Wc; have hSS := hz.S; have hD := hz.D
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine hf_call hF (b6_args hp h h3 h4 h6 h7) fun t a hf => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact .inr (.inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
    · exact .inr (.inl ⟨_, _, rfl, by omega, by omega⟩)
    · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩
    · exact .inr (.inr ⟨96, by rw [h.kr.sp], by omega⟩)
  · have hl' : (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)).length = sl s₀ + 4 := by
      simp [bytesAt_length, Spec.Pbkdf2.int]
    refine hf (K0 hF s₀) _ (by rw [hK]) (by rw [hK, hl']; have := sl_bytes hp; omega)
      (by rw [← List.append_assoc]; exact hr) (by rw [h5, hl']) h.st.2

end

end VG.Proof.Pbkdf2.Whole.PPC64LE
