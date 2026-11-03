module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Sg.Spec
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSASSA-PSS signing on RISC-V: `M'` and `EM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Sg/Em.lean`, `Sg/EnView.lean`): the writes to our part
of `scratch`, each keeping `Base`: `M' = 0⁸ ‖ mHash ‖ salt` at `oY`
(`mPrime_ok`, its bytes `mPrime_bytes`); `EM`'s place cleared (`clearEm_ok`),
`0x01` and the salt (`putSalt_ok`), `H` and `0xbc` (`putH_ok`), which leave
`EM` before masking (`emPre_of`); and `EM` after MGF1's mask and the mask of
its first byte is `emT` (`emT_of`). `Spilled.of_view`: the saved arguments
are kept by writes elsewhere.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64.Sg

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64.Sign VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (oEm oDig oRsa argBase clearEm)
open VG.Impl.RsaPss.RISCV64 (oY yBase clearY)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_wb view_w8 sc_in sc_inR sc_inW sc_w rd_in
  ne_of_dis bytes_entry kR)
open VG.Proof.RsaOaep (mixV range_ext)
open VG.Proof.RsaPss.RISCV64 (wp_yBase)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_sb wp_addSp
  wp_nil eval_nonzero ne_zero_iff fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPss (getD_app)

/-! ## Views -/

theorem getD_rep0 (n i : Nat) : (List.replicate n (0 : Byte)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem bytesAt_eq_view (m : Mem) (S : Addr) (d n : Nat) :
    Spec.Rsa.bytesAt m (off S d) n = (List.range n).map fun i => view m S (d + i) := by
  simp only [Spec.Rsa.bytesAt, view]
  exact List.map_congr_left fun i _ => by rw [← off_off]

/-- The saved arguments, kept by memory that is the same at `oP`. -/
theorem Spilled.of_view {s : State} {m m' : Mem} (h : Spilled s m)
    (hv : ∀ o, oP ≤ o → o < oP + 40 → view m' (Ss s) o = view m (Ss s) o) : Spilled s m' := by
  have e : ∀ j < 5, m'.readW (off (Ss s) (oP + 8 * j)) 64 = m.readW (off (Ss s) (oP + 8 * j)) 64 := fun j hj =>
    Mem.readW_congr fun i hi => by
      have := hv (oP + 8 * j + i) (by omega) (by omega)
      unfold view at this
      show m' (off (off (Ss s) (oP + 8 * j)) i) = m (off (off (Ss s) (oP + 8 * j)) i)
      rw [off_off]; exact this
  exact ⟨(e 0 (by decide)).trans h.n, (e 1 (by decide)).trans h.e, (e 2 (by decide)).trans h.el,
    (e 3 (by decide)).trans h.p, (e 4 (by decide)).trans h.pl⟩

/-- `M'` after `mPrime`. -/
theorem mPrime_bytes (m : Mem) (S : Addr) {D : Nat} (dig salt : List Byte) (hd : dig.length = D)
    (hl : oY + 8 + D + salt.length ≤ oRsa) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes (writeBytes m (off S oY) (List.replicate 8 0)) (off S (oY + 8)) dig)
      (off S (oY + 8 + D)) salt) (off S oY) (8 + D + salt.length) = Spec.RsaPss.zeros 8 ++ dig ++ salt := by
  rw [bytesAt_eq_view]
  refine range_ext (by simp [Spec.RsaPss.zeros, hd]; omega) fun i hi => ?_
  rw [view_wb _ _ (by omega) (by omega), view_wb _ _ (by rw [hd]; omega) (by omega),
    view_wb _ _ (by simp; omega) (by omega), getD_app, getD_app]
  simp only [List.length_replicate, hd, Spec.RsaPss.zeros, List.length_append, getD_rep0]
  by_cases h1 : i < 8
  · rw [ifn (by omega), ifn (by omega), ifp ⟨by omega, by omega⟩, ifp (by omega), ifp h1]
  by_cases h2 : i < 8 + D
  · rw [ifn (by omega), ifp ⟨by omega, by omega⟩, ifp (by omega), ifn h1, show oY + i - (oY + 8) = i - 8 by omega]
  · rw [ifp ⟨by omega, by omega⟩, ifn (by omega), show oY + i - (oY + 8 + D) = i - (8 + D) by omega,
      show i - (8 + D) = i - 8 - D by omega]

/-- `EM` before masking, at offset `o < k`: zeros, `0x01`, the salt, `H` and
`0xbc`. -/
def emPre (k D sl : Nat) (salt h : List Byte) (o : Nat) : Byte :=
  if o = k - 1 then 0xbc else if k - D - 1 ≤ o then h.getD (o - (k - D - 1)) 0
  else if k - sl - D - 1 ≤ o then salt.getD (o - (k - sl - D - 1)) 0 else if o = k - sl - D - 2 then 1 else 0

/-- `EM` before masking, from the writes of `clearEm`, `putSalt` and `putH`. -/
theorem emPre_of {m m₁ m₂ m₃ : Mem} {S : Addr} {k D sl : Nat} {salt h : List Byte} (hs : salt.length = sl)
    (hh : h.length = D) (hk : k ≤ 1024) (hfit : sl + D + 2 ≤ k)
    (h₁ : m₁ = writeBytes m (off S 0) (List.replicate 1024 0))
    (h₂ : m₂ = writeBytes (m₁.writeW (off S (k - sl - D - 2))  (1 : Byte)) (off S (k - sl - D - 1)) salt)
    (h₃ : m₃ = (writeBytes m₂ (off S (k - D - 1)) h).writeW (off S (k - 1)) (0xbc : Byte))
    {o : Nat} (ho : o < k) : view m₃ S o = emPre k D sl salt h o := by
  have hR : oRsa = 8192 := rfl
  subst h₁ h₂ h₃
  rw [view_w8 _ _ (by omega) (by omega), view_wb _ _ (by rw [hh]; omega) (by omega),
    view_wb _ _ (by rw [hs]; omega) (by omega), view_w8 _ _ (by omega) (by omega),
    view_wb _ _ (by rw [List.length_replicate]; omega) (by omega)]
  simp only [emPre, hs, hh, List.length_replicate, getD_rep0]
  rcases (by omega : o = k - 1 ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨
      o = k - sl - D - 2 ∨ o < k - sl - D - 2) with h | h | h | h | h <;>
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-- `EM` after the mask with `mk` on `DB` (at `lo`, `db` bytes) and its first
byte ANDed with `c`: `emT`. -/
theorem emT_of {k D sl lo db : Nat} (salt h mk : List Byte) (c : Byte) (hh : h.length = D) (hlo : lo ≤ 1)
    (hdb : db = k - lo - D - 1) (hfit : sl + D + 2 ≤ k - lo) {V : Nat → Byte}
    (hV : ∀ o < k, V o = emPre k D sl salt h o) {o : Nat} (ho : o < k) :
    (if o = lo then mixV V mk lo db o &&& c else mixV V mk lo db o) = RsaPss.emT lo db sl salt h mk c o := by
  simp only [RsaPss.emT, mixV, hV o ho, emPre, hh]
  rcases (by omega : o < lo ∨ (lo ≤ o ∧ o < k - sl - D - 2) ∨ o = k - sl - D - 2 ∨
      (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ o = k - 1) with h | h | h | h | h | h
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - sl - D - 1) = o - lo - (db - sl) by omega]
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - D - 1) = o - lo - db by omega]
    simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [↓ite_eq_left, ↓ite_eq_right]

/-! ## The writes -/

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem scR_contains {o n : Nat} (h : o + n ≤ oRsa) : (scR s).Contains (off (Ss s) o) n :=
  Offset.contains_base _ (by have := scLen P; omega) (by unfold oRsa at h; omega)

/-- Our stack argument `j` into `r`, through `t6`. -/
theorem ldArg_ok {t : State} (h : Base Ss vS s t) {r : Reg} {j : Nat} (hj : j < 13) {is : List Instr}
    {Q : State → Prop} (k : ∀ t', Only [.t6, r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : 8 * j < 2048 := by decide) :
    WP isa (.block (argBase :: .load .d r .t6 (8 * j) :: is)) t Q := by
  refine wp_addSp fun t₁ o₁ e₁ => ?_
  have g6 : t₁.gpr .t6 = s.sp := by rw [e₁, h.sp, BitVec.sub_add_cancel]
  exact wp_arg P hj g6 (o₁.rd.trans h.rd) (by rw [o₁.mem]; exact h.mem) (fun t' o e => k t' (o₁.trans o) e) ho

/-- `copySalt`: the salt to `S + d`, from `a1`. -/
theorem copySalt_ok {t : State} (h : Base Ss vS s t) {d : Nat} (h1 : t.gpr .a1 = off (Ss s) d)
    (hd : d + (stackArg s 10).toNat ≤ oRsa) :
    WP isa copySalt t fun t' => Base Ss vS s t' ∧ t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by
  have F := fits P
  generalize hL : (stackArg s 10).toNat = sl at hd
  refine WP.seq (ldArg_ok P h (r := .a4) (j := 9) (by decide) fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.t6, .a4, .a5] t t₃ := (o₂.trans o₃).mono
  have b₃ := h.only F k₃
  have g4 : t₃.gpr .a4 = stackArg s 9 := by rw [o₃.get .a4, e₂]
  have g5 : t₃.gpr .a5 = BitVec.ofNat 64 sl := by
    rw [e₃, o₂.get .s4, Base.ssl h, ← hL, ofNat_toNat]
  have g1 : t₃.gpr .a1 = off (Ss s) d := by rw [k₃.get .a1, h1]
  have hb : Spec.Rsa.bytesAt t₃.mem (stackArg s 9) sl = saltB s := by
    rw [← hL, k₃.mem]
    exact bytes_entry h.mem (P.ksl.sub_left kR_sub) ((P.sls.symm).sub_left (sc_sub P)) (by have := P.wsl; omega)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hs0 : sl ≠ 0 := by intro h0; rw [g5, ne_zero_iff, h0] at hc; simp at hc
    refine WP.mono (copy_ok (q := stackArg s 9) (p := off (Ss s) d) (n := sl) (by omega) (by unfold oRsa at hd; omega)
      g1 g4 g5 (rd_in (s := s) (t := t₃) b₃.rd (R := sR s) (by rw [P.hrd]; simp) P.wsl
        (by show sl ≤ (stackArg s 10).toNat; omega))
      (sc_w F b₃.wr (d := d) hd)
      (fun j hj i hi => ne_of_dis P.sls (Offset.contains_base _ (by omega) (by have := P.wsl; omega))
        (by have := scR_contains P (o := d + i) (n := 1) (by omega); rwa [← off_off] at this)))
      fun t' ⟨hk', hm⟩ => ?_
    have hm' : t'.mem = writeBytes t.mem (off (Ss s) d) (saltB s) := by rw [hm, hb, k₃.mem]
    exact ⟨b₃.wb F hk' (d := d) (xs := saltB s) (by rw [bytesAt_length, hL]; exact hd) (by rw [hm, hb]), hm'⟩
  · have hs0 : sl = 0 := by
      rw [g5, ne_zero_iff] at hc
      simp only [BitVec.toNat_ofNat, ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hc
      unfold oRsa at hd; omega
    refine wp_nil ⟨b₃, ?_⟩
    rw [k₃.mem, show saltB s = [] by simp [saltB, Spec.Rsa.bytesAt, hL, hs0], writeBytes_nil]

/-- `M' = 0⁸ ‖ mHash ‖ salt` at `S + oY`. -/
theorem mPrime_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hsl : (stackArg s 10).toNat + 8 + D ≤ 2048) :
    WP isa (mPrime H) t fun t' => Base Ss vS s t' ∧
      t'.mem = writeBytes (writeBytes (writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0))
        (off (Ss s) (oY + 8)) (digB D s)) (off (Ss s) (oY + 8 + D)) (saltB s) := by
  have F := fits P
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  -- `0⁸`.
  have hB : WP isa (.block (yBase .a1 ++ [.li .t5 8] ++ [.li .t0 0])) t fun t₃ => Only [.a1, .t5, .t0] t t₃ ∧
      t₃.gpr .a1 = off (Ss s) oY ∧ t₃.gpr .t5 = BitVec.ofNat 64 8 ∧ t₃.gpr .t0 = 0#64 := by
    rw [List.append_assoc]
    exact wp_yBase h.s0 fun t₁ o₁ e₁ => wp_li (imm := 8) (by decide) fun t₂ o₂ e₂ =>
      wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ =>
      wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .a1, o₂.get .a1, e₁], by rw [o₃.get .t5, e₂], e₃⟩
  refine WP.seq (WP.seq (WP.mono hB fun t₃ ⟨k₃, a₃, n₃, z₃⟩ => ?_))
  refine WP.mono (fill_ok (p := off (Ss s) oY) (n := 8) (b := 0) (by decide) (by decide) a₃ n₃
    (by rw [z₃]; rfl) (sc_w F (by rw [k₃.wr, h.wr]) (d := oY) (by omega))) fun t₄ ⟨hk₄, hm₄⟩ => ?_
  have m₄ : t₄.mem = writeBytes t.mem (off (Ss s) oY) (List.replicate 8 0) := by rw [hm₄, k₃.mem]
  have b₄ : Base Ss vS s t₄ := h.wb F (k₃.keep.trans hk₄) (by rw [List.length_replicate]; omega) m₄
  -- `mHash`.
  refine WP.seq (WP.seq (ldArg_ok P b₄ (r := .a4) (j := 8) (by decide) fun t₅ o₅ e₅ =>
    wp_yBase (by rw [o₅.get .s0, b₄.s0]) fun t₆ o₆ e₆ => wp_addi (imm := 8) fun t₇ o₇ e₇ =>
    wp_li (imm := H.D) (by omega) fun t₈ o₈ e₈ => wp_nil ?_))
  have k₈ : Only [.t6, .a4, .a1, .a5] t₄ t₈ := (o₅.trans (o₆.trans (o₇.trans o₈))).mono
  have hdg : ∀ j < D, ∀ i < D, stackArg s 8 + BitVec.ofNat 64 j ≠ off (Ss s) (oY + 8) + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis P.dgs (Offset.contains_base _ (by omega) (by have := P.wdg; omega))
      (by have := scR_contains P (o := oY + 8 + i) (n := 1) (by omega); rwa [← off_off] at this)
  refine WP.mono (copy_ok (q := stackArg s 8) (p := off (Ss s) (oY + 8)) (n := D) hD0 (by omega)
    (by rw [o₈.get .a1, e₇, e₆]; exact off_off _ _ _) (by rw [o₈.get .a4, o₇.get .a4, o₆.get .a4, e₅])
    (by rw [e₈, hD]) (rd_in (s := s) (t := t₈) (by rw [k₈.rd, b₄.rd]) (R := dgR D s) (by rw [P.hrd]; simp) P.wdg (Nat.le_refl _))
    (sc_w F (by rw [k₈.wr, b₄.wr]) (d := oY + 8) (by omega)) hdg) fun t₉ ⟨hk₉, hm₉⟩ => ?_
  have hb : Spec.Rsa.bytesAt t₈.mem (stackArg s 8) D = digB D s := by
    rw [k₈.mem]
    exact bytes_entry b₄.mem (P.kdg.sub_left kR_sub) ((P.dgs.symm).sub_left (sc_sub P)) (by have := P.wdg; omega)
  have m₉ : t₉.mem = writeBytes t₄.mem (off (Ss s) (oY + 8)) (digB D s) := by rw [hm₉, hb, k₈.mem]
  have b₉ : Base Ss vS s t₉ := b₄.wb F (k₈.keep.trans hk₉) (by rw [bytesAt_length]; omega) m₉
  -- The salt.
  refine WP.seq (wp_yBase (by rw [b₉.s0]) fun t₁₀ o₁₀ e₁₀ =>
    wp_addi (imm := 8 + H.D) (h := by omega) fun t₁₁ o₁₁ e₁₁ => wp_nil ?_)
  have k₁₁ : Only [.a1] t₉ t₁₁ := (o₁₀.trans o₁₁).mono
  refine WP.mono (copySalt_ok P (b₉.only F k₁₁) (d := oY + 8 + D)
    (by rw [e₁₁, e₁₀, hD]; exact (off_off _ _ _).trans (congrArg _ (Nat.add_assoc _ _ _).symm)) (by omega)) fun t' ⟨b', m'⟩ => ⟨b', ?_⟩
  rw [m', k₁₁.mem, m₉, m₄]

/-- `clearEm`: 1024 zeros at `S`. -/
theorem clearEm_ok {t : State} (h : Base Ss vS s t) :
    WP isa clearEm t fun t' => Base Ss vS s t' ∧
      t'.mem = writeBytes t.mem (off (Ss s) 0) (List.replicate 1024 0) := by
  have F := fits P
  refine WP.seq (wp_addi (imm := oEm) fun t₁ o₁ e₁ => wp_li (imm := 1024) (by decide) fun t₂ o₂ e₂ =>
    wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a1, .t5, .t0] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (fill_ok (p := off (Ss s) 0) (n := 1024) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .a1, o₂.get .a1, e₁, h.s0]; rfl) (by rw [o₃.get .t5, e₂]) (by rw [e₃]; rfl)
    (sc_w F (by rw [k₃.wr, h.wr]) (d := 0) (by decide))) fun t' ⟨hk, hm⟩ => ?_
  have hm' : t'.mem = writeBytes t.mem (off (Ss s) 0) (List.replicate 1024 0) := by rw [hm, k₃.mem]
  exact ⟨h.wb F (k₃.keep.trans hk) (by rw [List.length_replicate]; decide) hm', hm'⟩

theorem addr_k {t : State} (h : Base Ss vS s t) {a : Nat} (ha : a ≤ kk s) :
    t.gpr .s0 + t.gpr .s1 - BitVec.ofNat 64 a = off (Ss s) (kk s - a) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  have ek : (s.gpr .a3).toNat = kk s := rfl
  rw [h.s0, Base.sk h]
  apply BitVec.eq_of_toNat_eq
  have := F.wS
  simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at this ⊢
  unfold oRsa at this; omega

/-- `putSalt`: `0x01` at `S + k - sLen - hLen - 2`, and the salt after it. -/
theorem putSalt_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : (stackArg s 10).toNat + D + 2 ≤ kk s) :
    WP isa (putSalt H) t fun t' => Base Ss vS s t' ∧
      t'.mem = writeBytes (t.mem.writeW (off (Ss s) (kk s - (stackArg s 10).toNat - D - 2)) (1 : Byte))
        (off (Ss s) (kk s - (stackArg s 10).toNat - D - 1)) (saltB s) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  have hR : oRsa = 8192 := rfl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_sub fun t₂ o₂ e₂ => wp_subi (imm := H.D + 2) (h := by omega)
    fun t₃ o₃ e₃ => wp_li (imm := 1) (by decide) fun t₄ o₄ e₄ => ?_)
  have k₄ : Only [.a1, .t1] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a₃ : t₃.gpr .a1 = off (Ss s) (kk s - (stackArg s 10).toNat - D - 2) := by
    rw [e₃, e₂, e₁, o₁.get .s4, Base.ssl h, h.s0, Base.sk h, hD]
    apply BitVec.eq_of_toNat_eq
    have := (stackArg s 10).isLt
    have := F.wS
    have ek : (s.gpr .a3).toNat = kk s := rfl
    simp only [off, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, ek] at this ⊢
    unfold oRsa at this; omega
  have hA : InRegions t₄.wr (t₄.gpr .a1 + BitVec.ofNat 64 0) 1 := by
    rw [o₄.get .a1, a₃, BitVec.add_zero, k₄.wr, h.wr]; exact sc_inW F (by omega)
  refine wp_sb rfl hA fun t₅ m₅ => wp_addi (imm := 1) fun t₆ o₆ e₆ => wp_nil ?_
  have hv : (t₄.gpr .t1).setWidth 8 = (1 : Byte) := by rw [e₄]; rfl
  have m₆ : t₆.mem = t.mem.writeW (off (Ss s) (kk s - (stackArg s 10).toNat - D - 2)) (1 : Byte) := by
    rw [o₆.mem, m₅.mem, o₄.get .a1, a₃, BitVec.add_zero, hv, k₄.mem]
  have b₆ : Base Ss vS s t₆ := (h.only F k₄).keep F (m₅.keep.trans o₆.keep)
    (R := [⟨off (Ss s) (kk s - (stackArg s 10).toNat - D - 2), 1⟩])
    (by rw [m₆, ← k₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega)))
  have a₆ : t₆.gpr .a1 = off (Ss s) (kk s - (stackArg s 10).toNat - D - 1) := by
    rw [e₆, m₅.gpr, o₄.get .a1, a₃]
    show off (off (Ss s) _) 1 = _
    rw [off_off]; congr 2; omega
  refine WP.mono (copySalt_ok P b₆ a₆ (by omega)) fun t' ⟨b', m'⟩ => ⟨b', by rw [m', m₆]⟩

/-- `putH`: the `hLen` bytes at `S + oDig` to `S + k - hLen - 1`, and `0xbc`
at `S + k - 1`. -/
theorem putH_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) (hD0 : 0 < D) (hD64 : D ≤ 64) {t : State}
    (h : Base Ss vS s t) (hfit : D + 2 ≤ kk s) :
    WP isa (putH H) t fun t' => Base Ss vS s t' ∧
      t'.mem = (writeBytes t.mem (off (Ss s) (kk s - D - 1))
        (Spec.Rsa.bytesAt t.mem (off (Ss s) oDig) D)).writeW (off (Ss s) (kk s - 1)) (0xbc : Byte) := by
  have F := fits P
  have k2 : kk s ≤ 1024 := P.k2
  have hR : oRsa = 8192 := rfl
  have hG : oDig = 1280 := rfl
  refine WP.seq (WP.seq (wp_addi (imm := oDig) fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ =>
    wp_subi (imm := H.D + 1) (h := by omega) fun t₃ o₃ e₃ => wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ =>
    wp_nil ?_))
  have k₄ : Only [.a4, .a1, .a5] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a₄ : t₄.gpr .a1 = off (Ss s) (kk s - D - 1) := by
    rw [o₄.get .a1, e₃, e₂, o₁.get .s0, o₁.get .s1, addr_k P h (by omega), hD, Nat.sub_add_eq]
  refine WP.mono (copy_ok (q := off (Ss s) oDig) (p := off (Ss s) (kk s - D - 1)) (n := D) hD0 (by omega)
    a₄ (by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0]) (by rw [e₄, hD])
    (fun j hj => by
      have := sc_inR F (o := oDig + j) (n := 1) (by omega) t₄.rd
      rw [k₄.wr, h.wr]; rwa [← off_off] at this)
    (sc_w F (by rw [k₄.wr, h.wr]) (d := kk s - D - 1) (by omega))
    (fun j hj i hi => by
      show off (off (Ss s) oDig) j ≠ off (off (Ss s) (kk s - D - 1)) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))) fun t₅ ⟨k₅, m₅⟩ => ?_
  have m₅' : t₅.mem = writeBytes t.mem (off (Ss s) (kk s - D - 1)) (Spec.Rsa.bytesAt t.mem (off (Ss s) oDig) D) := by
    rw [m₅, k₄.mem]
  have b₅ := h.wb F (k₄.keep.trans k₅) (d := kk s - D - 1) (by rw [bytesAt_length]; omega) m₅'
  refine wp_add fun t₆ o₆ e₆ => wp_subi (imm := 1) fun t₇ o₇ e₇ => wp_li (imm := 0xbc) (by decide)
    fun t₈ o₈ e₈ => ?_
  have k₈ : Only [.a1, .t1] t₅ t₈ := (o₆.trans (o₇.trans o₈)).mono
  have a₇ : t₇.gpr .a1 = off (Ss s) (kk s - 1) := by rw [e₇, e₆, addr_k P b₅ (by omega)]
  have hA : InRegions t₈.wr (t₈.gpr .a1 + BitVec.ofNat 64 0) 1 := by
    rw [o₈.get .a1, a₇, BitVec.add_zero, k₈.wr, b₅.wr]; exact sc_inW F (by omega)
  refine wp_sb rfl hA fun t' m' => wp_nil ?_
  have hv : (t₈.gpr .t1).setWidth 8 = (0xbc : Byte) := by rw [e₈]; rfl
  have mm : t'.mem = t₅.mem.writeW (off (Ss s) (kk s - 1)) (0xbc : Byte) := by
    rw [m'.mem, o₈.get .a1, a₇, BitVec.add_zero, hv, k₈.mem]
  refine ⟨(b₅.only F k₈).keep F m'.keep (R := [⟨off (Ss s) (kk s - 1), 1⟩])
    (by rw [mm, ← k₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega))), by rw [mm, m₅']⟩

end

end VG.Proof.RsaPss.RISCV64.Sg
