module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Setup
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Common
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2 over any streaming hash function on RISC-V, the whole derivation: a block, up to `U₁`

After `k` blocks of the output (`Inv`), `out` holds the first `done k` bytes
of `T₁ ‖ … ‖ T_k`, `s4` points past them, `s5` counts the bytes left and
`s7` is `k + 1`. A block copies the key's inner state into the working
state (`HashOK.reloc`: it represents a whole block), absorbs the salt and
`INT (k + 1)` (written from `s7`) into it with `update`, and computes `U₁`
with HMAC's `finalize` (`b6_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_mv wp_addi wp_li wp_srl wp_sb)
open VG.Impl.Pbkdf2.Whole.RISCV64 (Fns)
open VG.Impl.Pbkdf2.RISCV64 (It)
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)
open Spec.Sha256 (bytesAt)

variable {F : Fns}

theorem blockKey_length (hH : HashOK F.H) (k : List Byte) : (blockKey hH.SH.H k).length = F.H.B := by
  have hB := hH.hB
  have hDB : F.H.D ≤ F.H.B := by have := hH.hD64; rcases hH.hB64 with h | h <;> omega
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
  kr : KR F s₀ s
  st : States hF s₀ s.mem
  s4 : s.gpr .s4 = out s₀ + BitVec.ofNat 64 (dn s₀ (F := F) k)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (ol s₀ - dn s₀ (F := F) k)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (k + 1)
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (out s₀) (dn s₀ (F := F) k) = (Gk hF s₀ k).take (dn s₀ (F := F) k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := .s4 :: .s5 :: .s7 :: kregs

/-- Where a block writes, before it copies `T` out: the parts of the inner
frame from the working state on, `iterate`'s working space, and the stack
below the frames. -/
def Wb (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.frB) ∨ Region.Sub r (itR F s₀) ∨
    ∃ n, r = below s₀.sp n ∧ n ≤ F.X

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

include hF in
theorem Wb.ok {r : Region} (h : Wb F s₀ r) :
    Wk F s₀ r ∧ (sR s₀ Fns.st0O (2 * F.H.S)).Disjoint r ∧ (outR s₀).Disjoint r := by
  have hz := sizes hF; have hl := layout (F := F); have := hz.frB; have := hz.itB
  have p0 : Region.Sub (sR s₀ Fns.st0O (2 * F.H.S)) (frR F s₀) := part_sub (by omega)
  rcases h with ⟨o, n, rfl, h₁, h₂⟩ | h | ⟨n, rfl, hn⟩
  · exact ⟨.inl ⟨o, n, rfl, by omega, h₂⟩, part_disj (.inl (by omega)) (by omega) (by omega),
      hp.f_o.symm.sub_right (part_sub h₂)⟩
  · exact ⟨.inr (.inl h), ((f_i hp).sub_left p0).sub_right h, hp.i_o.symm.sub_right h⟩
  · have hsub := below_stk hp hn
    exact ⟨.inr (.inr ⟨n, rfl, hn⟩), ((f_s hp).sub_left p0).sub_right hsub, (hp.b_o.symm).sub_right hsub⟩

/-- `Inv` survives writes where a block writes. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wb F s₀ r) : Inv hF s₀ k s' := by
  have hz := sizes hF
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))) hf
      (fun r hr => (Wk.ok hp hz (Wb.ok (hF := hF) hp (hw r hr)).1).1) (fun r hr => (Wk.ok hp hz (Wb.ok (hF := hF) hp (hw r hr)).1).2),
    h.st.keep hf (fun r hr => (Wb.ok (hF := hF) hp (hw r hr)).2.1), by rw [hg _ (by simp), h.s4],
    by rw [hg _ (by simp), h.s5], by rw [hg _ (by simp), h.s7], h.glen, ?_⟩
  rw [← h.outB]
  have osub : Region.Sub ⟨out s₀, dn s₀ (F := F) k⟩ (outR s₀) := Region.sub_prefix (Nat.min_le_right _ _)
  exact Proof.Sha256.Stream.bytesAt_congr fun _ hi => hf.bytes (R := ⟨out s₀, dn s₀ (F := F) k⟩)
    (fun r hr => ((Wb.ok (hF := hF) hp (hw r hr)).2.2).sub_left osub)
    (by have e1 : dn s₀ (F := F) k ≤ ol s₀ := Nat.min_le_right _ _
        have e2 : ol s₀ < 2 ^ 64 := (s₀.gpr .a6).isLt
        show dn s₀ (F := F) k ≤ 2 ^ 64; omega) hi

/-- `n` bytes copied from offset `a` of the inner frame to offset `b`, where a
block writes. -/
theorem copy_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {a b n : Nat} (hab : a + n ≤ b ∨ b + n ≤ a)
    (ha : a + n ≤ F.frB) (hbo : F.stWO ≤ b) (hb : b + n ≤ F.frB) {rest : List Instr} {Q : State → Prop}
    (hk : ∀ t, Inv hF s₀ k t → (∀ r, r ≠ .t1 → t.gpr r = s.gpr r) →
      t.mem = writeBytes s.mem (sA s₀ b) (bytesAt s.mem (sA s₀ a) n) → WP isa (.block rest) t Q) :
    WP isa (.block (It.cp .s1 .s1 a b n ++ rest)) s Q := by
  have hz := sizes hF; have hfr := hz.frB
  have e : ∀ o j, s.gpr .s1 + BitVec.ofNat 64 o + BitVec.ofNat 64 j = sA s₀ (o + j) := fun o j => by
    rw [h.kr.s1, sA_add]
  refine VG.Proof.Pbkdf2.RISCV64.cp_ok (src := .s1) (dst := .s1) (by decide) (by decide) a b n (by omega)
    (by omega) rest s Q
    (fun j hj => by rw [e]; exact in_fr' hp h.kr.wr (by omega) (by omega))
    (fun j hj => by rw [e]; exact in_fr hp h.kr.wr (by omega) (by omega))
    (by rw [h.kr.s1]; exact Offset.sep _ hab (by have := hp.top; omega) (by have := hp.top; omega))
    fun t g rd wr sp m => ?_
  rw [h.kr.s1] at m
  refine hk t (h.keep hp rd wr sp (fun r hr => g r (by revert r; decide)) (rs := [sR s₀ b n]) ?_
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨b, n, rfl, hbo, hb⟩)) g m
  rw [m]
  exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)

/-- The key's inner state copied into the working state, which then
represents `K₀ ⊕ ipad`, and `update`'s arguments for the salt. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.saltArgs) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad) ∧ t.gpr .a0 = sA s₀ F.stWO ∧
      t.gpr .a1 = BitVec.ofNat 64 F.H.B ∧ t.gpr .a2 = salt s₀ ∧ t.gpr .a3 = s₀.gpr .a3 := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  unfold Fns.saltArgs
  refine copy_ok hp h (a := Fns.st0O) (b := F.stWO) (n := F.H.S) (by omega) (by omega) (Nat.le_refl _)
    (by omega) fun t ht g m => ?_
  refine wp_addi (by omega) fun s₁ u₁ => wp_li (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₂ u₂ =>
    wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  have mm : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨ht.keep hp (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₄.other r (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide),
        u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · rw [mm]
    have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
    refine hF.hH.reloc s.mem t.mem _ _ _ (by rw [xorPad_length, hK]; exact Nat.mod_self _) (fun i hi => ?_) h.st.1
    have := hz.S
    rw [m, VG.Proof.Hmac.Common.writeBytes_at _ _ _ (by rw [bytesAt_length]; omega)
      (by rw [bytesAt_length]; omega), VG.Proof.Hmac.Common.bytesAt_getD' _ _ (by omega)]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s6]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [g _ (by decide), h.kr.s2]

/-- The salt and the inner frame fit in the address space together. -/
theorem sl_bytes : sl s₀ + F.frB ≤ 2 ^ 64 :=
  Whole.len_add_le hp.f_sa.symm hp.nsa (by have := hp.top; show s₀.sp.toNat + F.frB ≤ 2 ^ 64; omega)

/-- `update`'s arguments for the working state, with the `len` bytes at `dat`. -/
theorem updW_args {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat}
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h2 : s.gpr .a2 = dat) (h3 : (s.gpr .a3).toNat = len)
    (hd : Region.Disjoint ⟨dat, len⟩ (sR s₀ F.stWO F.H.S)) (hs : (stk F s₀).Disjoint ⟨dat, len⟩)
    (hcd : ∃ r' ∈ s.rd ++ s.wr, ∃ off, dat = r'.base + BitVec.ofNat 64 off ∧ off + len ≤ r'.len) :
    UpdArgs F s (sA s₀ F.stWO) dat len := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  have bs : Region.Sub (below s.sp F.H.F) (stk F s₀) := by rw [h.kr.sp]; exact below_stk hp (by omega)
  have pw : Region.Sub (sR s₀ F.stWO F.H.S) (frR F s₀) := part_sub (by omega)
  refine ⟨h0, h2, h3, hd, by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega,
    ((f_s hp).sub_left pw).symm.sub_left bs, hs.sub_left bs, ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hcd
    · exact ⟨frR F s₀, List.mem_append_right _ (fr_wr hp h.kr.wr), F.stWO, rfl,
        by show F.stWO + F.H.S ≤ F.frB; omega⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    exact ⟨frR F s₀, fr_wr hp h.kr.wr, F.stWO, rfl, by show F.stWO + F.H.S ≤ F.frB; omega⟩

/-- `update` of the working state, from `m`, with the `len` bytes at `dat`. -/
theorem updW_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {dat : Addr} {len : Nat} {m : List Byte}
    (ha : UpdArgs F s (sA s₀ F.stWO) dat len)
    (hm : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) (h1 : s.gpr .a1 = BitVec.ofNat 64 m.length) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (m ++ bytesAt s.mem dat len) := by
  have hz := sizes hF; have hl := layout (F := F); have hX := hz.X
  refine upd_call hF.hH ha fun t a hu => ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide))
    a.frame fun r hr => ?_, hu m hm h1⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩
  · exact .inr (.inr ⟨F.H.F, by rw [h.kr.sp], by omega⟩)

/-- The salt absorbed into the working state. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad)) (h0 : s.gpr .a0 = sA s₀ F.stWO)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 F.H.B) (h2 : s.gpr .a2 = salt s₀) (h3 : s.gpr .a3 = s₀.gpr .a3) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hz := sizes hF; have hl := layout (F := F)
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine WP.mono (updW_ok hp h (updW_args hp h h0 h2 (by rw [h3]) (hp.f_sa.symm.sub_right (part_sub (by omega)))
      hp.b_sa ⟨saltR s₀, List.mem_append_left _ (by rw [h.kr.rd, hp.rd]; simp), 0, by simp, by simp⟩) hr
    (by rw [h1, xorPad_length, hK])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [h.kr.saltBytes hp] at hu

end

/-! ## `INT (i)` -/

theorem byte_shift (i n : Nat) (hi : i < 2 ^ 64) :
    (BitVec.ofNat 64 i >>> n).setWidth 8 = BitVec.ofNat 8 (i / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hi]

theorem write4 (m : Mem) (q : Addr) (b₀ b₁ b₂ b₃ : Byte) :
    (((m.writeW (q + BitVec.ofNat 64 0) b₀).writeW (q + BitVec.ofNat 64 1) b₁).writeW (q + BitVec.ofNat 64 2)
      b₂).writeW (q + BitVec.ofNat 64 3) b₃ = writeBytes m q [b₀, b₁, b₂, b₃] := by
  rw [show [b₀, b₁, b₂, b₃] = (([] ++ [b₀]) ++ [b₁]) ++ [b₂] ++ [b₃] from rfl,
    VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp),
    VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp),
    VG.WriteBytes.writeBytes_nil]
  rfl

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀)
include hp

/-- `INT (k + 1)`, and `update`'s arguments for it. -/
theorem b3_ok {k : Nat} (hk : k + 1 < 2 ^ 32) {s : State} (h : Inv hF s₀ k s) {m : List Byte}
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) m) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) m ∧ bytesAt t.mem (sA s₀ F.intO) 4 = Spec.Pbkdf2.int (k + 1) ∧
      t.gpr .a0 = sA s₀ F.stWO ∧ t.gpr .a1 = BitVec.ofNat 64 (F.H.B + sl s₀) ∧ t.gpr .a2 = sA s₀ F.intO ∧
      t.gpr .a3 = BitVec.ofNat 64 4 := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  have e : ∀ j, s.gpr .s1 + BitVec.ofNat 64 (F.intO + j) = sA s₀ F.intO + BitVec.ofNat 64 j := fun j => by
    rw [h.kr.s1, sA_add]
  have hin : ∀ {t : State}, t.wr = s.wr → ∀ j < 4, InRegions t.wr (sA s₀ F.intO + BitVec.ofNat 64 j) 1 :=
    fun hw j hj => by rw [sA_add]; exact in_fr hp (hw.trans h.kr.wr) (by omega) (by omega)
  unfold Fns.updArgs
  refine wp_srl (by decide) fun s₁ u₁ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 0) (by omega)
    (by rw [u₁.other _ (by decide), h.kr.s1, sA_add]; rfl) (hin (by rw [u₁.wr]) 0 (by decide)) fun s₂ m₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 1) (by omega)
    (by rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [u₃.wr, m₂.wr, u₁.wr]) 1 (by decide)) fun s₄ m₄ => ?_
  refine wp_srl (by decide) fun s₅ u₅ => wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 2) (by omega)
    (by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr]) 2 (by decide)) fun s₆ m₆ => ?_
  refine wp_sb (a := sA s₀ F.intO + BitVec.ofNat 64 3) (by omega)
    (by rw [m₆.gpr, u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), e])
    (hin (by rw [m₆.wr, u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr]) 3 (by decide)) fun s₇ m₇ => ?_
  refine wp_addi (by omega) fun s₈ u₈ => wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₉ u₉ =>
    wp_addi (by omega) fun s₁₀ u₁₀ => wp_li (by decide) fun s₁₁ u₁₁ => WP.block_nil ?_
  have g7 : ∀ r, r ≠ .t1 → s₇.gpr r = s.gpr r := fun r hr => by
    rw [m₇.gpr, m₆.gpr, u₅.other r hr, m₄.gpr, u₃.other r hr, m₂.gpr, u₁.other r hr]
  have v7 : s.gpr .s7 = BitVec.ofNat 64 (k + 1) := h.s7
  have hk64 : k + 1 < 2 ^ 64 := by omega
  -- The memory.
  have ne : Reg.s7 ≠ .t1 := by decide
  have v1 : s₁.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 24 := by rw [u₁.gpr, v7]
  have v3 : s₃.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 16 := by rw [u₃.gpr, m₂.gpr, u₁.other _ ne, v7]
  have v5 : s₅.gpr .t1 = BitVec.ofNat 64 (k + 1) >>> 8 := by
    rw [u₅.gpr, m₄.gpr, u₃.other _ ne, m₂.gpr, u₁.other _ ne, v7]
  have v6 : s₆.gpr .s7 = BitVec.ofNat 64 (k + 1) := by
    rw [m₆.gpr, u₅.other _ ne, m₄.gpr, u₃.other _ ne, m₂.gpr, u₁.other _ ne, v7]
  have mm : s₁₁.mem = writeBytes s.mem (sA s₀ F.intO) (Spec.Pbkdf2.int (k + 1)) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇.mem, v6, m₆.mem, v5, u₅.mem, m₄.mem, v3, u₃.mem, m₂.mem, v1, u₁.mem,
      write4]
    simp only [Spec.Pbkdf2.int, byte_shift _ _ hk64, VG.Proof.Pbkdf2.RISCV64.setWidth_ofNat8]
  have fr : Frame [sR s₀ F.intO 4] s.mem s₁₁.mem := by
    rw [mm]; exact writeBytes_frame _ _ _ (by simp only [Spec.Pbkdf2.int]; exact Region.contains_self _ _)
  have g : ∀ r, r ≠ .t1 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₁₁.gpr r = s.gpr r := fun r a b c d f => by
    rw [u₁₁.other r f, u₁₀.other r d, u₉.other r c, u₈.other r b, g7 r a]
  refine ⟨h.keep hp (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, m₇.rd, m₆.rd, u₅.rd, m₄.rd, u₃.rd, m₂.rd, u₁.rd])
    (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, m₇.wr, m₆.wr, u₅.wr, m₄.wr, u₃.wr, m₂.wr, u₁.wr])
    (by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, m₇.sp, m₆.sp, u₅.sp, m₄.sp, u₃.sp, m₂.sp, u₁.sp])
    (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) fr
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl ⟨_, _, rfl, by omega, by omega⟩),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hF.hH.congr s.mem s₁₁.mem _ _ (fun i hi => ?_) hr
    exact fr.bytes (R := sR s₀ F.stWO F.H.S) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj (.inl (by omega)) (by omega) (by omega)) (by show F.H.S ≤ 2 ^ 64; omega) hi
  · rw [mm]
    have := VG.Proof.Hmac.Common.bytesAt_writeBytes_self s.mem (sA s₀ F.intO) (Spec.Pbkdf2.int (k + 1))
      (by simp [Spec.Pbkdf2.int])
    simpa [Spec.Pbkdf2.int] using this
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s1]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s2]
    have hsum : F.H.B + sl s₀ < 2 ^ 64 := by have := sl_bytes hp; have := hz.S; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .a3).toNat + F.H.B % 2 ^ 64) % 2 ^ 64 = (F.H.B + (s₀.gpr .a3).toNat) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B) (by omega), Nat.add_comm]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]
    rw [g7 _ (by decide), h.kr.s1]
  · upd_simp [u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other]

/-- `INT (k + 1)` absorbed into the working state. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀))
    (hi : bytesAt s.mem (sA s₀ F.intO) 4 = Spec.Pbkdf2.int (k + 1))
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = BitVec.ofNat 64 (F.H.B + sl s₀))
    (h2 : s.gpr .a2 = sA s₀ F.intO) (h3 : s.gpr .a3 = BitVec.ofNat 64 4) :
    WP isa F.H.callUpd s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  have hsub : Region.Sub (sR s₀ F.intO 4) (frR F s₀) := part_sub (by omega)
  refine WP.mono (updW_ok hp h (updW_args hp h h0 h2 (by rw [h3]; rfl)
      (part_disj (.inr (by omega)) (by omega) (by omega)) ((f_s hp).symm.sub_right hsub)
      ⟨frR F s₀, List.mem_append_right _ (fr_wr hp h.kr.wr), F.intO, rfl, by show F.intO + 4 ≤ F.frB; omega⟩)
    hr (by rw [h1, List.length_append, xorPad_length, hK, bytesAt_length])) fun t ⟨ht, hu⟩ => ⟨ht, ?_⟩
  rwa [hi] at hu

/-- HMAC's `finalize`'s arguments. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.mem = s.mem ∧ t.gpr .a0 = sA s₀ F.stWO ∧
      t.gpr .a1 = sA s₀ F.st1O ∧ t.gpr .a2 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧
      t.gpr .a3 = sA s₀ F.uO := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB
  unfold Fns.finArgs
  refine wp_addi (by omega) fun s₁ u₁ => wp_addi (by omega) fun s₂ u₂ =>
    wp_addi (by rcases hz.B with h | h <;> rw [h] <;> decide) fun s₃ u₃ => wp_addi (by omega) fun s₄ u₄ =>
    WP.block_nil ?_
  have mm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨h.keep hp (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (fun r hr => by
      rw [u₄.other r (by revert r; decide), u₃.other r (by revert r; decide), u₂.other r (by revert r; decide),
        u₁.other r (by revert r; decide)]) (rs := [])
    (by rw [mm]; exact Frame.refl _ _) (by simp), mm, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s2]
    have hsum : F.H.B + (sl s₀ + 4) < 2 ^ 64 := by have := sl_bytes hp; have := hz.S; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    show ((s₀.gpr .a3).toNat + (F.H.B + 4) % 2 ^ 64) % 2 ^ 64 = (F.H.B + ((s₀.gpr .a3).toNat + 4)) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (a := F.H.B + 4) (by omega)]
    congr 1; omega
  · upd_simp [u₄.gpr, u₄.other, u₃.gpr, u₃.other, u₂.gpr, u₂.other, u₁.gpr, u₁.other]
    rw [h.kr.s1]

/-- HMAC's `finalize`'s arguments. -/
theorem b6_args {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = sA s₀ F.st1O) (h3 : s.gpr .a3 = sA s₀ F.uO) :
    HfArgs F s (sA s₀ F.stWO) (sA s₀ F.st1O) (sA s₀ F.uO) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  have bs : Region.Sub (below s.sp (F.H.fbytes + F.H.F)) (stk F s₀) := by
    rw [h.kr.sp]; exact below_stk hp (by omega)
  have pd : ∀ {a m b n : Nat}, a + m ≤ b ∨ b + n ≤ a → a + m ≤ 4096 → b + n ≤ 4096 →
      Region.Disjoint (sR s₀ a m) (sR s₀ b n) := fun h₁ h₂ h₃ => part_disj h₁ h₂ h₃
  have bp : ∀ {o n : Nat}, o + n ≤ F.frB → (below s.sp (F.H.fbytes + F.H.F)).Disjoint (sR s₀ o n) := fun h' =>
    ((f_s hp).sub_left (part_sub h')).symm.sub_left bs
  have cv : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len :=
    fun o n h' => ⟨frR F s₀, fr_wr hp h.kr.wr, o, rfl, h'⟩
  have cv' : ∀ o n, o + n ≤ F.frB → ∃ r' ∈ s.rd ++ s.wr, ∃ off,
      (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + n ≤ r'.len := fun o n h' => by
    obtain ⟨r', hr', off, e, l⟩ := cv o n h'; exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
  refine ⟨h0, h1, h3, by rw [h.kr.sp]; exact hp.al, by rw [h.kr.sp]; have := hp.spX; omega,
    pd (.inr (by omega)) (by omega) (by omega), pd (.inl (by omega)) (by omega) (by omega),
    pd (.inl (by omega)) (by omega) (by omega), bp (by omega), bp (by omega), bp (by omega), ?_, ?_⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cv' F.st1O F.H.S (by omega)
    · exact cv' F.stWO F.H.S (by omega)
    · exact cv' F.uO F.H.D (by omega)
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cv F.stWO F.H.S (by omega)
    · exact cv F.uO F.H.D (by omega)

/-- `U₁`, with HMAC's `finalize`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s)
    (hr : hF.hH.SH.Repr s.mem (sA s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (h0 : s.gpr .a0 = sA s₀ F.stWO) (h1 : s.gpr .a1 = sA s₀ F.st1O)
    (h2 : s.gpr .a2 = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4))) (h3 : s.gpr .a3 = sA s₀ F.uO) :
    WP isa F.callHf s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (sA s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hz := sizes hF; have hl := layout (F := F); have hfr := hz.frB; have hX := hz.X
  have hK := blockKey_length hF.hH (bytesAt s₀.mem (pw s₀) (pwl s₀))
  refine hf_call hF (b6_args hp h h0 h1 h3) fun t a hf => ?_
  refine ⟨h.keep hp a.rd a.wr a.sp (fun r hr => a.cs r (by revert r; decide)) a.frame fun r hr => ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl ⟨_, _, rfl, Nat.le_refl _, by omega⟩
    · exact .inl ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr (.inr ⟨_, by rw [h.kr.sp], by omega⟩)
  · have hl' : (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)).length = sl s₀ + 4 := by
      simp [bytesAt_length, Spec.Pbkdf2.int]
    refine hf (K0 hF s₀) _ (by rw [hK]) (by rw [hK, hl']; have := sl_bytes hp; have := hz.S; omega)
      (by rw [← List.append_assoc]; exact hr) (by rw [h2, hl']) h.st.2

end

end VG.Proof.Pbkdf2.Whole.RISCV64
